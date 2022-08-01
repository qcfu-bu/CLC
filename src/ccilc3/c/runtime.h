#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

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