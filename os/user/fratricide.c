#include <inc/lib.h>

#define OK 42
#define BROTHERS 10

static uint8_t heapBuffer[4*BROTHERS*PGSIZE];

Proof receive_proof() {
  size_t offset = (size_t) ipc_recv(NULL, UTEMP, NULL);
  Proof p = proof_cp((Proof)((uint8_t *)UTEMP + offset));
  sys_page_unmap(0, UTEMP);
  return p;
}

void send_proof(envid_t to, Proof p) {
  // Copy the proof to UTEMP
  sys_page_alloc(0, UTEMP, PTE_U | PTE_W);
  Heap tempHeap;
  init_heap(&tempHeap, UTEMP, PGSIZE);
  Heap *oldHeap = set_heap(&tempHeap);
  Proof copy = proof_cp(p);
  size_t offset = (uintptr_t)copy - (uintptr_t)UTEMP;

  // Send the proof
  ipc_send(to, offset, UTEMP, PTE_U);
  sys_page_unmap(0, UTEMP);

  // Reset the heap
  set_heap(oldHeap);
}

void
umain(int argc, char **argv){
  Heap heap;
  init_heap(&heap, &heapBuffer, 4*BROTHERS*PGSIZE);
  set_heap(&heap);
  int i;
  envid_t who;
  Proof deligations[BROTHERS];
  envid_t whos[BROTHERS];

  for(i = 0; i < BROTHERS; i++){
    who = fork();
    if(who == 0){
      //child
      Proof del = delegate_from_signed(thisenv->env_id, thisenv->env_parent_id, OK);
      send_proof(thisenv->env_parent_id, del);
      Formula goal = formula_pred(OK, principal_var(0));
      sys_set_goal(goal);
      while(true) sys_yield();
    }
    //parent
    deligations[i] = receive_proof();
    whos[i] = who;
  }

  who = fork();
  if(who != 0) {
    // parent
    Formula pred = formula_pred(OK, principal_pcpl(who));
    Proof permission = says_from_signed(thisenv->env_id, pred);
    send_proof(who, permission);
  } else {
    // child
    Proof auth = receive_proof();
    for(i = 0; i < BROTHERS ; i++){
      Proof use_del = use_delegation(whos[i], thisenv->env_parent_id, thisenv->env_id, OK, deligations[i], auth);
      //proof_print(use_del);
      sys_set_proof(use_del);
      cprintf("Die brother %08x!!!\n", whos[i]);
      sys_env_destroy(whos[i]);
    }
    //Suicide
    cprintf("And now I must die.\n", whos[i]);
    sys_env_destroy(0);
  }
}


