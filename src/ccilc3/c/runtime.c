#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <pthread.h>
#include "chan.h"

#include "runtime.h"

void instr_mov(clc_ptr *x, clc_ptr v)
{
  *x = v;
}

void instr_clo(clc_ptr *x, clc_ptr (*f)(clc_ptr, clc_env), int size, ...)
{
  va_list ap;
  clc_clo tmp = (clc_clo)malloc(sizeof(_clc_clo));
  tmp->f = f;
  tmp->env = (clc_env)malloc(sizeof(clc_ptr) * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->env[i] = va_arg(ap, clc_ptr);
  }
  va_end(ap);

  *x = (clc_ptr)tmp;
}

void instr_call(clc_ptr *x, clc_ptr clo, clc_ptr v)
{
  clc_ptr (*f)(clc_ptr, clc_env) = ((clc_clo)clo)->f;
  clc_env env = ((clc_clo)clo)->env;
  env[0] = clo;
  *x = (*f)(v, env);
}

void instr_struct(clc_ptr *x, int tag, int size, ...)
{
  va_list ap;
  clc_node tmp = (clc_node)malloc(sizeof(_clc_node));
  tmp->tag = tag;
  tmp->data = (clc_ptr *)malloc(sizeof(clc_ptr) * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->data[i] = va_arg(ap, clc_ptr);
  }
  va_end(ap);

  *x = (clc_ptr)tmp;
}

void instr_open(
    clc_ptr *x,
    clc_ptr (*f)(clc_env),
    clc_ptr m,
    int tag,
    int size, ...)
{
  va_list ap;
  pthread_t th;
  clc_ptr ch = (clc_ptr)chan_init(0);
  clc_env env = (clc_env)malloc(sizeof(clc_ptr) * (size + 1));

  va_start(ap, size);
  env[0] = ch;
  for (int i = 0; i < size; i++)
  {
    env[i + 1] = va_arg(ap, clc_ptr);
  }
  va_end(ap);

  pthread_create(&th, m, (void *)f, env);
  instr_struct(x, tag, 2, ch, m);
}

clc_ptr proc_sender(clc_ptr x, clc_env env)
{
  int res = chan_send((chan_t *)env[1], x);
  return env[1];
}

void instr_send(clc_ptr *x, clc_ptr ch)
{
  instr_clo(x, &proc_sender, 2, 0, ch);
}

void instr_recv(clc_ptr *x, clc_ptr ch, int tag)
{
  clc_ptr msg;
  int res = chan_recv((chan_t *)ch, &msg);
  instr_struct(x, tag, 2, msg, ch);
}

void instr_close(clc_ptr *x, clc_ptr ch, int tag)
{
  chan_dispose((chan_t *)ch);
  instr_struct(x, tag, 0);
}

clc_ptr instr_to_bit(int i)
{
  clc_node x = (clc_node)malloc(sizeof(_clc_node));
  if (i)
  {
    x->tag = 2;
  }
  else
  {
    x->tag = 3;
  }
  return x;
}

clc_ptr instr_to_ascii(char c)
{
  clc_node x = (clc_node)malloc(sizeof(_clc_node));
  x->tag = 16;
  x->data = (clc_ptr *)malloc(sizeof(clc_ptr) * 8);
  int bit;
  for (int i = 0; i < 8; i++)
  {
    bit = (c & (1 << i)) >> i;
    x->data[7 - i] = instr_to_bit(bit);
  }
  return (clc_ptr)x;
}

clc_ptr instr_to_string(char *s)
{
  clc_node tmp;
  clc_node x = (clc_node)malloc(sizeof(_clc_node));
  x->tag = 17;
  int len = strlen(s);
  for (int i = 1; i <= len; i++)
  {
    tmp = (clc_node)malloc(sizeof(_clc_node));
    tmp->tag = 18;
    tmp->data = (clc_ptr *)malloc(sizeof(clc_ptr) * 2);
    tmp->data[0] = instr_to_ascii(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (clc_ptr)x;
}

char instr_from_ascii(clc_ptr x)
{
  char c;
  clc_ptr b;
  for (int i = 0; i < 8; i++)
  {
    b = ((clc_node)x)->data[7 - i];
    switch (((clc_node)b)->tag)
    {
    case 2:
      c |= 1 << i;
      break;
    case 3:
      c &= ~(1 << i);
      break;
    }
  }
  return c;
}

char *instr_from_string(clc_ptr x)
{
  char *str;
  int len = 0;
  clc_node tmp = (clc_node)x;
  while (tmp->tag != 17)
  {
    tmp = (clc_node)(tmp->data[1]);
    len++;
  }
  str = (char *)malloc(sizeof(char) * len + 1);
  tmp = (clc_node)x;
  for (int i = 0; i < len; i++)
  {
    str[i] = instr_from_ascii(tmp->data[0]);
    tmp = (clc_node)(tmp->data[1]);
  }
  return str;
}

clc_ptr proc_stdout(clc_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  clc_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = instr_from_string(msg);
      fputs(str, stdout);
      free(str);
      b = !b;
    }
    else
    {
      switch (((clc_node)msg)->tag)
      {
      case 2:
        b = !b;
        break;
      case 3:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

clc_ptr proc_stdin(clc_ptr ch)
{
  int b = 0, rep = 1;
  char *buffer;
  size_t len;
  clc_ptr msg;
  while (rep)
  {
    if (b)
    {
      getline(&buffer, &len, stdin);
      msg = instr_to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    }
    else
    {
      chan_recv((chan_t *)ch, &msg);
      switch (((clc_node)msg)->tag)
      {
      case 2:
        b = !b;
        break;
      case 3:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

clc_ptr proc_stderr(clc_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  clc_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = instr_from_string(msg);
      fputs(str, stderr);
      free(str);
      b = !b;
    }
    else
    {
      switch (((clc_node)msg)->tag)
      {
      case 2:
        b = !b;
        break;
      case 3:
        rep = !rep;
        break;
      }
    }
  }
  return NULL;
}

void instr_trg(clc_ptr *x, clc_ptr (*f)(clc_ptr))
{
  va_list ap;
  pthread_t th;
  clc_ptr ch = (clc_ptr)chan_init(0);
  pthread_create(&th, NULL, (void *)f, ch);
  *x = ch;
}
