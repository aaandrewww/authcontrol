#include <inc/lib.h>

#define OK 42
#define BROTHERS 10

static uint8_t heapBuffer[4*BROTHERS*PGSIZE];

void
umain(int argc, char **argv){
  Heap heap;
  init_heap(&heap, &heapBuffer, 4*BROTHERS*PGSIZE);
  set_heap(&heap);
  int i;
  envid_t who;
  Proof delegations[BROTHERS];
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
    delegations[i] = receive_proof();
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
      Proof use_del = use_delegation(whos[i], thisenv->env_parent_id, thisenv->env_id, OK, delegations[i], auth);
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


