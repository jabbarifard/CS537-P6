#include "param.h"
#include "types.h"
#include "defs.h"
#include "x86.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "elf.h"

extern char data[];  // defined by kernel.ld
pde_t *kpgdir;  // for use in scheduler()

struct node
{
    //virtual address, pte
    //used bit for the array
    int data;
    struct node *next;
}node;

//struct array nodes[CLOCKSIZE];

struct queue
{
    int length;
    int size;
    node* head;
    node* tail;
    node* array;
}queue;

void qInit(char *virtual_addr)
{
    struct queue* q = (struct queue*)malloc(sizeof(struct queue*));
    q->length = CLOCKSIZE;
    q->size = 0;
    q->head= 0;
    q->tail = q->size -1;
    q->array = (node*)malloc(q->length * sizeof(node));
    return q;
}

int isFull(struct Queue* q)
{
    return (q->size == q->length);
}

// Queue is empty when size is 0
int isEmpty(struct Queue* q)
{
    return (q->size == 0);
}

// Function to add an item to the queue.
// It changes tail and size
void enqueue(struct Queue* q, node node)
{
    if (isFull(q))
        return;
    q->tail = (q->tail + 1)
                  % q->length;
    q->array[q->tail] = node;
    q->size = q->size + 1;
    //printf("%d enqueued to queue\n", node);
}
 
// Function to remove an item from queue.
// It changes head and size
void dequeue(struct Queue* q)
{
    if (isEmpty(q))
        return INT_MIN;
    int item = q->array[q->head];
    q->head = (q->head + 1)
                   % q->length;
    q->size = q->size - 1;
    //printf("%d dequeued from queue\n", item);
}

// Set up CPU's kernel segment descriptors.
// Run once on entry on each CPU.
void
seginit(void)
{
  struct cpu *c;

  // Map "logical" addresses to virtual addresses using identity map.
  // Cannot share a CODE descriptor for both kernel and user
  // because it would have to have DPL_USR, but the CPU forbids
  // an interrupt from CPL=0 to DPL=3.
  c = &cpus[cpuid()];
  c->gdt[SEG_KCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, 0);
  c->gdt[SEG_KDATA] = SEG(STA_W, 0, 0xffffffff, 0);
  c->gdt[SEG_UCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, DPL_USER);
  c->gdt[SEG_UDATA] = SEG(STA_W, 0, 0xffffffff, DPL_USER);
  lgdt(c->gdt, sizeof(c->gdt));
}

static 
enqueue(char *virtual_addr){
	if (queue.size()< CLOCKSIZE){
		add to the tail}
	else{

}

// Return the address of the PTE in page table pgdir
// that corresponds to virtual address va.  If alloc!=0,
// create any required page table pages.
static pte_t *
walkpgdir(pde_t *pgdir, const void *va, int alloc)
{
  pde_t *pde;
  pte_t *pgtab;

  pde = &pgdir[PDX(va)];
  if(*pde & PTE_P){
    pgtab = (pte_t*)P2V(PTE_ADDR(*pde));
  } else {
    if(!alloc || (pgtab = (pte_t*)kalloc()) == 0)
      return 0;
    // Make sure all those PTE_P bits are zero.
    memset(pgtab, 0, PGSIZE);
    // The permissions here are overly generous, but they can
    // be further restricted by the permissions in the page table
    // entries, if necessary.
    *pde = V2P(pgtab) | PTE_P | PTE_W | PTE_U;
  }
  return &pgtab[PTX(va)];
}

// Create PTEs for virtual addresses starting at va that refer to
// physical addresses starting at pa. va and size might not
// be page-aligned.
static int
mappages(pde_t *pgdir, void *va, uint size, uint pa, int perm)
{
  char *a, *last;
  pte_t *pte;

  a = (char*)PGROUNDDOWN((uint)va);
  last = (char*)PGROUNDDOWN(((uint)va) + size - 1);
  for(;;){
    // int encrypted = 0;
    if((pte = walkpgdir(pgdir, a, 1)) == 0)
      return -1;
    if(*pte & PTE_P){
      if((*pte & PTE_E) >> 9){
        panic("remap");
      } else {
        // encrypted = 1;
      }
    }

    *pte = pa | perm | PTE_P;
    if(((*pte & PTE_E) >> 9) != 0)
    {
      *pte &= ~PTE_P;
    }

    if(a == last)
      break;
    a += PGSIZE;
    pa += PGSIZE;
  }
  return 0;
}

// There is one page table per process, plus one that's used when
// a CPU is not running any process (kpgdir). The kernel uses the
// current process's page table during system calls and interrupts;
// page protection bits prevent user code from using the kernel's
// mappings.
//
// setupkvm() and exec() set up every page table like this:
//
//   0..KERNBASE: user memory (text+data+stack+heap), mapped to
//                phys memory allocated by the kernel
//   KERNBASE..KERNBASE+EXTMEM: mapped to 0..EXTMEM (for I/O space)
//   KERNBASE+EXTMEM..data: mapped to EXTMEM..V2P(data)
//                for the kernel's instructions and r/o data
//   data..KERNBASE+PHYSTOP: mapped to V2P(data)..PHYSTOP,
//                                  rw data + free physical memory
//   0xfe000000..0: mapped direct (devices such as ioapic)
//
// The kernel allocates physical memory for its heap and for user memory
// between V2P(end) and the end of physical memory (PHYSTOP)
// (directly addressable from end..P2V(PHYSTOP)).

// This table defines the kernel's mappings, which are present in
// every process's page table.
static struct kmap {
  void *virt;
  uint phys_start;
  uint phys_end;
  int perm;
} kmap[] = {
 { (void*)KERNBASE, 0,             EXTMEM,    PTE_W}, // I/O space
 { (void*)KERNLINK, V2P(KERNLINK), V2P(data), 0},     // kern text+rodata
 { (void*)data,     V2P(data),     PHYSTOP,   PTE_W}, // kern data+memory
 { (void*)DEVSPACE, DEVSPACE,      0,         PTE_W}, // more devices
};

// Set up kernel part of a page table.
pde_t*
setupkvm(void)
{
  pde_t *pgdir;
  struct kmap *k;

  if((pgdir = (pde_t*)kalloc()) == 0)
    return 0;
  memset(pgdir, 0, PGSIZE);
  if (P2V(PHYSTOP) > (void*)DEVSPACE)
    panic("PHYSTOP too high");
  for(k = kmap; k < &kmap[NELEM(kmap)]; k++)
    if(mappages(pgdir, k->virt, k->phys_end - k->phys_start,
                (uint)k->phys_start, k->perm) < 0) {
      freevm(pgdir);
      return 0;
    }
  return pgdir;
}

// Allocate one page table for the machine for the kernel address
// space for scheduler processes.
void
kvmalloc(void)
{
  kpgdir = setupkvm();
  switchkvm();
}

// Switch h/w page table register to the kernel-only page table,
// for when no process is running.
void
switchkvm(void)
{
  lcr3(V2P(kpgdir));   // switch to the kernel page table
}

// Switch TSS and h/w page table to correspond to process p.
void
switchuvm(struct proc *p)
{
  if(p == 0)
    panic("switchuvm: no process");
  if(p->kstack == 0)
    panic("switchuvm: no kstack");
  if(p->pgdir == 0)
    panic("switchuvm: no pgdir");

  pushcli();
  mycpu()->gdt[SEG_TSS] = SEG16(STS_T32A, &mycpu()->ts,
                                sizeof(mycpu()->ts)-1, 0);
  mycpu()->gdt[SEG_TSS].s = 0;
  mycpu()->ts.ss0 = SEG_KDATA << 3;
  mycpu()->ts.esp0 = (uint)p->kstack + KSTACKSIZE;
  // setting IOPL=0 in eflags *and* iomb beyond the tss segment limit
  // forbids I/O instructions (e.g., inb and outb) from user space
  mycpu()->ts.iomb = (ushort) 0xFFFF;
  ltr(SEG_TSS << 3);
  lcr3(V2P(p->pgdir));  // switch to process's address space
  popcli();
}

// Load the initcode into address 0 of pgdir.
// sz must be less than a page.
void
inituvm(pde_t *pgdir, char *init, uint sz)
{
  char *mem;

  if(sz >= PGSIZE)
    panic("inituvm: more than a page");
  mem = kalloc();
  memset(mem, 0, PGSIZE);
  mappages(pgdir, 0, PGSIZE, V2P(mem), PTE_W|PTE_U);
  memmove(mem, init, sz);
}

// Load a program segment into pgdir.  addr must be page-aligned
// and the pages from addr to addr+sz must already be mapped.
int
loaduvm(pde_t *pgdir, char *addr, struct inode *ip, uint offset, uint sz)
{
  uint i, pa, n;
  pte_t *pte;

  if((uint) addr % PGSIZE != 0)
    panic("loaduvm: addr must be page aligned");
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, addr+i, 0)) == 0)
      panic("loaduvm: address should exist");
    pa = PTE_ADDR(*pte);
    if(sz - i < PGSIZE)
      n = sz - i;
    else
      n = PGSIZE;
    if(readi(ip, P2V(pa), offset+i, n) != n)
      return -1;
  }
  return 0;
}

// Allocate page tables and physical memory to grow process from oldsz to
// newsz, which need not be page aligned.  Returns new size or 0 on error.
int
allocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  char *mem;
  uint a;

  if(newsz >= KERNBASE)
    return 0;
  if(newsz < oldsz)
    return oldsz;

  a = PGROUNDUP(oldsz);
  for(; a < newsz; a += PGSIZE){
    mem = kalloc();
    if(mem == 0){
      cprintf("allocuvm out of memory\n");
      deallocuvm(pgdir, newsz, oldsz);
      return 0;
    }
    memset(mem, 0, PGSIZE);
    if(mappages(pgdir, (char*)a, PGSIZE, V2P(mem), PTE_W|PTE_U) < 0){
      cprintf("allocuvm out of memory (2)\n");
      deallocuvm(pgdir, newsz, oldsz);
      kfree(mem);
      return 0;
    }
  }
  return newsz;
}

// Deallocate user pages to bring the process size from oldsz to
// newsz.  oldsz and newsz need not be page-aligned, nor does newsz
// need to be less than oldsz.  oldsz can be larger than the actual
// process size.  Returns the new process size.
int
deallocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  pte_t *pte;
  uint a, pa;

  if(newsz >= oldsz)
    return oldsz;

  a = PGROUNDUP(newsz);
  for(; a  < oldsz; a += PGSIZE){
    pte = walkpgdir(pgdir, (char*)a, 0);
    if(!pte)
      a = PGADDR(PDX(a) + 1, 0, 0) - PGSIZE;
    else if((*pte & PTE_P) != 0 || (*pte & PTE_E) != 0){
      // if(((*pte & PTE_E) >> 9) != 1){
        pa = PTE_ADDR(*pte);
        if(pa == 0)
          panic("kfree");
        char *v = P2V(pa);
        kfree(v);
        *pte = 0;
      // }
    }
  }
  return newsz;
}

// Free a page table and all the physical memory pages
// in the user part.
void
freevm(pde_t *pgdir)
{
  uint i;

  if(pgdir == 0)
    panic("freevm: no pgdir");
  deallocuvm(pgdir, KERNBASE, 0);
  for(i = 0; i < NPDENTRIES; i++){
    if(pgdir[i] & PTE_P){
      if(pgdir[i] & PTE_E){
        char * v = P2V(PTE_ADDR(pgdir[i]));
        kfree(v);
      }
    }
  }
  kfree((char*)pgdir);
}

// Clear PTE_U on a page. Used to create an inaccessible
// page beneath the user stack.
void
clearpteu(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  if(pte == 0)
    panic("clearpteu");
  *pte &= ~PTE_U;
}

// Given a parent process's page table, create a copy
// of it for a child.
pde_t*
copyuvm(pde_t *pgdir, uint sz)
{
  pde_t *d;
  pte_t *pte;
  uint pa, i, flags;
  char *mem;

  if((d = setupkvm()) == 0)
    return 0;
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, (void *) i, 0)) == 0)
      panic("copyuvm: pte should exist");
    if((*pte & PTE_P) == 0)
      if(((*pte & PTE_E) >> 9) == 0)    
        panic("copyuvm: page not present");
    pa = PTE_ADDR(*pte);
    flags = PTE_FLAGS(*pte);
    if((mem = kalloc()) == 0)
      goto bad;
    memmove(mem, (char*)P2V(pa), PGSIZE);
    if(mappages(d, (void*)i, PGSIZE, V2P(mem), flags) < 0) {
      kfree(mem);
      goto bad;
    }
  }
  return d;

bad:
  freevm(d);
  return 0;
}

//PAGEBREAK!
// Map user virtual address to kernel address.
char*
uva2ka(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  // Modified to check for PTE_E    
  if((*pte & PTE_P) == 0)
    if(((*pte & PTE_E) >> 9) == 0)                    
      return 0;
  if((*pte & PTE_U) == 0)
    return 0;
  return (char*)P2V(PTE_ADDR(*pte));
}

// Copy len bytes from p to user address va in page table pgdir.
// Most useful when pgdir is not the current page table.
// uva2ka ensures this only works for PTE_U pages.
int
copyout(pde_t *pgdir, uint va, void *p, uint len)
{
  char *buf, *pa0;
  uint n, va0;

  buf = (char*)p;
  while(len > 0){
    va0 = (uint)PGROUNDDOWN(va);
    pa0 = uva2ka(pgdir, (char*)va0);
    if(pa0 == 0)
      return -1;
    n = PGSIZE - (va - va0);
    if(n > len)
      n = len;
    memmove(pa0 + (va - va0), buf, n);
    len -= n;
    buf += n;
    va = va0 + PGSIZE;
  }
  return 0;
}

//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.


// USER ADDED
int
mencrypt(char *virtual_addr, int len)
{  
  
  // Start of ERROR CHECKS
  // cprintf("encypting\n");

  // cprintf("len is %d\n", len);
  
  // Check if len is zero
  if(len == 0){
    // cprintf("len is 0\n");
    return len;  
  }

  cprintf("len is not 0\n");

  // Check if len is negative
  if(len < 0)
    return -1;

  // Check PTE_E bit
  // #define PTE_E           0x006      // Encrypted
    
  // pte_t* pgdir = myproc()->pgdir;    // pgdir is an array of pages, 
  pde_t* pgdir = myproc()->pgdir;       // pagetable entry      //array of pointers to pagetables

  int slider = PGROUNDDOWN((int) virtual_addr);

  // cprintf("checks done 0\n");


  int lenCount = 0;
  for (int i = 0; i < len; i++) {
    pte_t* mypte = walkpgdir(pgdir, (void*)(slider + i * PGSIZE), 0);    //each pagetable in pdet
  
    // Check if pages are present
    if((*mypte & PTE_P) == 0)
      if(((*mypte & PTE_E) >> 9) == 0)                    
        return -1;
      
    // Check if pages within range are already encrypted
    if (((*mypte & PTE_E) >> 9) == 1) {
      lenCount++;
    }

  }

  // Check if pages within range are already encrypted
  if (lenCount == len)
  {
    return 0;
  }

  // cprintf("checks done 1\n");
  	
  // Check if calling proc has access to this range
  // Check if virtual_addr is within range
  // len is number of pages I want encrypt
  if (uva2ka(pgdir, (char*) slider) == 0) { 
    return -1;
  }

  // CANNOT exceed page table length
  // if (uva2ka(pgdir, (char*) (slider + len * PGSIZE)) == 0) {
  //   return -1;
  // }

  // cprintf("checks done 2\n");

  // End of ERROR CHECKS

  for(int j = 0; j < len; j++){                             //iterating through 1 pagetable containing many ptes
    pte_t* mypte = walkpgdir(pgdir, (void*) slider, 0);     //each pagetable in a directory

    if ((*mypte & PTE_P) == 0) {                            //encryption bit 1 if encrypted and 0 if not
      
    } else {
      int i;
      for (i = 0; i < PGSIZE; i++){                         //page size 4k, for encrypting content of 1 pte whose size is 4k
        *(char*)(slider + i) = *(char*)(slider + i) ^ 0xFF;
        // cprintf("%d: encryptying\n", i);
      }

      *mypte = *mypte & ~PTE_P;                             // set P bit to 0
      *mypte = *mypte |  PTE_E;                             // set E bit to 1
      
      // Flush TLB
      struct proc *curproc = myproc();
      switchuvm(curproc);
    }
    
    slider += PGSIZE;    
  }

  // if((*pte & PTE_P) && (*pte & PTE_P)

  // Set PDE to have correct values as well

  // Successful encryption
  return 0;
};

int
decrypt(char *virtual_addr){
  // cprintf("decrypting\n");
  
  int slider = PGROUNDDOWN((int) virtual_addr);

	pde_t* pgdir = myproc()->pgdir;                        // pagetable entry -> array of pointers to pagetables

  // Normal page fault, not encrypted
  // if (uva2ka(pgdir, (char*) slider) == 0){
  //   return -1;
  // }
  
  pte_t* mypte = walkpgdir(pgdir, (void*) slider, 0);    // each pagetable in pdet
  if (((*mypte & PTE_E) >> 9) == 0) {
    // cprintf("failed to decrypt\n");
    return -1;
  }

  *mypte = *mypte & ~PTE_E;                              // reset E bit to 0
  *mypte = *mypte |  PTE_P;                              // reset P bit to 1

  // Otherwise, decrypt page
  for (int i=0; i < PGSIZE; i++){                        //page size 4k, for encrypting content of 1 pte whose size is 4k
    *(char*)(slider + i) = *(char*)(slider + i) ^ 0xFF;
  }


  // Flush TLB
  struct proc *curproc = myproc();
  switchuvm(curproc);
  //if we get page fault
  // End of ERROR CHECKS
  return 0;
}


int
getpgtable(struct pt_entry *entries, int num)
{
  pde_t* pgdir = myproc()->pgdir;
  uint   size  = myproc()->sz;

  // Get topmost page
  int slider = PGROUNDDOWN((uint) size);

  while (uva2ka(pgdir, (char*) slider) == 0){
    slider -= PGSIZE;
  }

  // TODO
  // Fill up a pt_entry array of num entries 
  // Starting from the highest PTE_E first
  int i = 0;
  int valid = 0;
  for(i = 0; i < num; i++){
    // Copy information from current page
    pte_t* mypte = walkpgdir(pgdir, (void*) slider, 0);
    if (uva2ka(pgdir, (char*) slider) != 0){
      valid++;
  
      (entries + i)->pdx       = PDX(slider);
      (entries + i)->ptx       = PTX(slider);
      (entries + i)->ppage     = (PTE_ADDR(*mypte)) >> PTXSHIFT;
      (entries + i)->present   = (*mypte & PTE_P) >> 0;
      (entries + i)->writable  = (*mypte & PTE_W) >> 1;
      (entries + i)->encrypted = (*mypte & PTE_E) >> 9;
    }

    // Go to next highest page
    slider -= PGSIZE;
  }

  return valid;
};

int
dump_rawphymem(uint physical_addr, char * buffer)
{
  // TODO
  // Use copyout() to dump mem
  int addr = PGROUNDDOWN((int) physical_addr);
  pde_t* pgdir = myproc()->pgdir;

  // CLARIFY
  // copyout copies from p to va -> we want to copy 1 PAGE from phy_add to buffer
  // pgdir = myproc()->pgdir
  // va    = buffer?
  // p     = (roudned down) addr?
  // len   = PGSIZE (since 1 page is copied)
  // return copyout(pgdir, (uint) buffer, (void *) addr, PGSIZE);
  // copyout(pde_t *pgdir, uint va, void *p, uint len)

  return copyout(pgdir, (uint) buffer, (void *) P2V(addr), PGSIZE);
};


// IMPORTANT METHODS
// walkpgdir(pde_t *pgdir, const void *va, int alloc)
// uva2ka(pde_t *pgdir, char *uva)
// copyout(pde_t *pgdir, uint va, void *p, uint len)
