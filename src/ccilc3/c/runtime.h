#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <pthread.h>
#include "chan.h"

typedef void *CLC_ptr;

typedef CLC_ptr *CLC_env;

typedef struct
{
  CLC_ptr (*f)(CLC_ptr, CLC_env);
  CLC_env env;
} CLC_CLO;

typedef struct
{
  int tag;
  CLC_ptr *data;
} CLC_NODE;

typedef CLC_CLO *CLC_clo;
typedef CLC_NODE *CLC_node;

void INSTR_mov(CLC_ptr *x, CLC_ptr v)
{
  *x = v;
}

void INSTR_clo(CLC_ptr *x, CLC_ptr (*f)(CLC_ptr, CLC_env), int size, ...)
{
  va_list ap;
  CLC_clo tmp = (CLC_clo)malloc(sizeof(CLC_CLO));
  tmp->f = f;
  tmp->env = (CLC_env)malloc(sizeof(CLC_ptr) * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->env[i] = va_arg(ap, CLC_ptr);
  }
  va_end(ap);

  *x = (CLC_ptr)tmp;
}

void INSTR_call(CLC_ptr *x, CLC_ptr clo, CLC_ptr v)
{
  CLC_ptr (*f)(CLC_ptr, CLC_env) = ((CLC_clo)clo)->f;
  CLC_env env = ((CLC_clo)clo)->env;
  env[0] = clo;
  *x = (*f)(v, env);
}

void INSTR_struct(CLC_ptr *x, int tag, int size, ...)
{
  va_list ap;
  CLC_node tmp = (CLC_node)malloc(sizeof(CLC_NODE));
  tmp->tag = tag;
  tmp->data = (CLC_ptr *)malloc(sizeof(CLC_ptr) * size);

  va_start(ap, size);
  for (int i = 0; i < size; i++)
  {
    tmp->data[i] = va_arg(ap, CLC_ptr);
  }
  va_end(ap);

  *x = (CLC_ptr)tmp;
}

void INSTR_open(
    CLC_ptr *x,
    CLC_ptr (*f)(CLC_env),
    CLC_ptr m,
    int tag,
    int size, ...)
{
  va_list ap;
  pthread_t th;
  CLC_ptr ch = (CLC_ptr)chan_init(0);
  CLC_env env = (CLC_env)malloc(sizeof(CLC_ptr) * (size + 1));

  va_start(ap, size);
  env[0] = ch;
  for (int i = 0; i < size; i++)
  {
    env[i + 1] = va_arg(ap, CLC_ptr);
  }
  va_end(ap);

  pthread_create(&th, m, (void *)f, env);
  INSTR_struct(x, tag, 2, ch, m);
}

CLC_ptr PROC_sender(CLC_ptr x, CLC_env env)
{
  int res = chan_send((chan_t *)env[1], x);
  return env[1];
}

void INSTR_send(CLC_ptr *x, CLC_ptr ch)
{
  INSTR_clo(x, &PROC_sender, 2, 0, ch);
}

void INSTR_recv(CLC_ptr *x, CLC_ptr ch, int tag)
{
  CLC_ptr msg;
  int res = chan_recv((chan_t *)ch, &msg);
  INSTR_struct(x, tag, 2, msg, ch);
}

void INSTR_close(CLC_ptr *x, CLC_ptr ch, int tag)
{
  chan_dispose((chan_t *)ch);
  INSTR_struct(x, tag, 0);
}

CLC_ptr INSTR_to_bit(int i)
{
  CLC_node x = (CLC_node)malloc(sizeof(CLC_NODE));
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

CLC_ptr INSTR_to_ascii(char c)
{
  CLC_node x = (CLC_node)malloc(sizeof(CLC_NODE));
  x->tag = 16;
  x->data = (CLC_ptr *)malloc(sizeof(CLC_ptr) * 8);
  int bit;
  for (int i = 0; i < 8; i++)
  {
    bit = (c & (1 << i)) >> i;
    x->data[7 - i] = INSTR_to_bit(bit);
  }
  return (CLC_ptr)x;
}

CLC_ptr INSTR_to_string(char *s)
{
  CLC_node tmp;
  CLC_node x = (CLC_node)malloc(sizeof(CLC_NODE));
  x->tag = 17;
  int len = strlen(s);
  for (int i = 1; i <= len; i++)
  {
    tmp = (CLC_node)malloc(sizeof(CLC_NODE));
    tmp->tag = 18;
    tmp->data = (CLC_ptr *)malloc(sizeof(CLC_ptr) * 2);
    tmp->data[0] = INSTR_to_ascii(s[len - i]);
    tmp->data[1] = x;
    x = tmp;
  }
  return (CLC_ptr)x;
}

char INSTR_from_ascii(CLC_ptr x)
{
  char c;
  CLC_ptr b;
  for (int i = 0; i < 8; i++)
  {
    b = ((CLC_node)x)->data[7 - i];
    switch (((CLC_node)b)->tag)
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

char *INSTR_from_string(CLC_ptr x)
{
  char *str;
  int len = 0;
  CLC_node tmp = (CLC_node)x;
  while (tmp->tag != 17)
  {
    tmp = (CLC_node)(tmp->data[1]);
    len++;
  }
  str = (char *)malloc(sizeof(char) * len + 1);
  tmp = (CLC_node)x;
  for (int i = 0; i < len; i++)
  {
    str[i] = INSTR_from_ascii(tmp->data[0]);
    tmp = (CLC_node)(tmp->data[1]);
  }
  return str;
}

CLC_ptr PROC_stdout(CLC_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  CLC_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = INSTR_from_string(msg);
      fputs(str, stdout);
      free(str);
      b = !b;
    }
    else
    {
      switch (((CLC_node)msg)->tag)
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

CLC_ptr PROC_stdin(CLC_ptr ch)
{
  int b = 0, rep = 1;
  char *buffer;
  size_t len;
  CLC_ptr msg;
  while (rep)
  {
    if (b)
    {
      getline(&buffer, &len, stdin);
      msg = INSTR_to_string(buffer);
      free(buffer);
      chan_send((chan_t *)ch, msg);
      b = !b;
    }
    else
    {
      chan_recv((chan_t *)ch, &msg);
      switch (((CLC_node)msg)->tag)
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

CLC_ptr PROC_stderr(CLC_ptr ch)
{
  int b = 0, rep = 1;
  char *str;
  CLC_ptr msg;
  while (rep)
  {
    chan_recv((chan_t *)ch, &msg);
    if (b)
    {
      str = INSTR_from_string(msg);
      fputs(str, stderr);
      free(str);
      b = !b;
    }
    else
    {
      switch (((CLC_node)msg)->tag)
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

void INSTR_trg(CLC_ptr *x, CLC_ptr (*f)(CLC_ptr))
{
  va_list ap;
  pthread_t th;
  CLC_ptr ch = (CLC_ptr)chan_init(0);
  pthread_create(&th, NULL, (void *)f, ch);
  *x = ch;
}
