#ifndef runtime_h
#define runtime_h

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

CLC_ptr PROC_sender(CLC_ptr x, CLC_env env);
CLC_ptr PROC_stdout(CLC_ptr ch);
CLC_ptr PROC_stdin(CLC_ptr ch);
CLC_ptr PROC_stderr(CLC_ptr ch);

void INSTR_mov(CLC_ptr *x, CLC_ptr v);
void INSTR_clo(CLC_ptr *x, CLC_ptr (*f)(CLC_ptr, CLC_env), int size, ...);
void INSTR_call(CLC_ptr *x, CLC_ptr clo, CLC_ptr v);
void INSTR_struct(CLC_ptr *x, int tag, int size, ...);
void INSTR_open(CLC_ptr *x, CLC_ptr (*f)(CLC_env), CLC_ptr m, int tag, int size, ...);
void INSTR_send(CLC_ptr *x, CLC_ptr ch);
void INSTR_recv(CLC_ptr *x, CLC_ptr ch, int tag);
void INSTR_close(CLC_ptr *x, CLC_ptr ch, int tag);
void INSTR_trg(CLC_ptr *x, CLC_ptr (*f)(CLC_ptr));

#endif
