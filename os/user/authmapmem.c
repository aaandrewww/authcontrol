#include <inc/lib.h>

#define OK 42
#define PAGESTOMAP 10

static uint8_t heapBuffer[4 * 2 * PGSIZE];

void umain(int argc, char **argv) {
  Heap heap;
  init_heap(&heap, &heapBuffer, 4 * 2 * PGSIZE);
  set_heap(&heap);
  envid_t who;
  envid_t whos[2] = { 0, 0 };
  int i, r;
  Proof del[2];
  Proof perm;
  Formula pred;
  Proof use_del;
  uintptr_t vaddr;

  for (i = 0; i < 2; i++) {
    who = fork();
    if (who == 0) {
      //child
      Proof del = delegate_from_signed(thisenv->env_id, thisenv->env_parent_id,
          OK);
      send_proof(thisenv->env_parent_id, del);
      Formula goal = formula_pred(OK, principal_var(0));
      sys_set_goal(goal);
      goto child;
    }
    //parent
    del[i] = receive_proof();
    whos[i] = who;
  }

  // Send the ids of each child to the other
  ipc_send(whos[1], whos[0], 0, 0);
  ipc_send(whos[0], whos[1], 0, 0);

  // Send the proof each child needs
  pred = formula_pred(OK, principal_pcpl(whos[0]));
  perm = says_from_signed(thisenv->env_id, pred);
  use_del = use_delegation(whos[1], thisenv->env_id, whos[0], OK, del[1], perm);
  send_proof(whos[0], use_del);

  pred = formula_pred(OK, principal_pcpl(whos[1]));
  perm = says_from_signed(thisenv->env_id, pred);
  use_del = use_delegation(whos[0], thisenv->env_id, whos[1], OK, del[0], perm);
  send_proof(whos[1], use_del);

  child:

  if (who == 0) {
    envid_t other_child = ipc_recv(0, 0, 0);
    Proof auth = receive_proof();
    sys_set_proof(auth);
    sys_proof_test(other_child);

    // second child
    if (whos[0] != 0) {
      cprintf("in env %u, mapping to %u\n", thisenv->env_id, other_child);
      for (i = 0; i < PAGESTOMAP; i++) {
        vaddr = (uintptr_t)UTEMP + i*PGSIZE;
        if (sys_page_alloc(0, UTEMP, PTE_U | PTE_W | PTE_P) < 0)
          cprintf("ERROR allocating");

        uint8_t *test = (uint8_t *) UTEMP;
        int i;
        for (i = 0; i < PGSIZE; i++)
          test[i] = i;

        r = sys_page_map(0, UTEMP, other_child, (void *)vaddr, PTE_U | PTE_W | PTE_P);
        if (r < 0)
          cprintf("ERROR mapping");
      }

      ipc_send(other_child, 55, 0, 0);
    }

    // first child
    if (whos[0] == 0) {
      do{
        r = ipc_recv(0,0,0);
      } while (r == -E_AGAIN);

      uint8_t *test = (uint8_t *) UTEMP;
      uint32_t count = 0;
      for (i = 0; i < PAGESTOMAP*PGSIZE; i++)
        if( test[i] >= 0)
          count++;

      cprintf("There were %u elements there should have been %u\n", count,  PAGESTOMAP*PGSIZE);
    }

  }
}
