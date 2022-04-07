#include <stdio.h>
#include <pthread.h>
#include <gc.h>
#include "chan.h"

void thread_function(void *ptr)
{
  chan_t *chan = (chan_t *)ptr;
  void *x = GC_malloc(sizeof(int));
  *(int *)x = 123;
  chan_send(chan, x);
}

int main()
{
  chan_t *chan = chan_init(0);
  pthread_t thread;
  pthread_create(&thread, NULL, (void *)thread_function, (void *)chan);

  void *msg;
  chan_recv(chan, &msg);
  printf("%d\n", *(int *)msg);

  GC_free(msg);
  chan_dispose(chan);

  return 0;
}
