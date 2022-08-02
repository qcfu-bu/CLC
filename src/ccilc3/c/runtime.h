#ifndef runtime_h
#define runtime_h

typedef void *clc_ptr;

typedef clc_ptr *clc_env;

typedef struct
{
  clc_ptr (*f)(clc_ptr, clc_env);
  clc_env env;
} _clc_clo;

typedef struct
{
  int tag;
  clc_ptr *data;
} _clc_node;

typedef _clc_clo *clc_clo;
typedef _clc_node *clc_node;

clc_ptr proc_sender(clc_ptr x, clc_env env);
clc_ptr proc_stdout(clc_ptr ch);
clc_ptr proc_stdin(clc_ptr ch);
clc_ptr proc_stderr(clc_ptr ch);

void instr_init();
void instr_mov(clc_ptr *x, clc_ptr v);
void instr_clo(clc_ptr *x, clc_ptr (*f)(clc_ptr, clc_env), int size, ...);
void instr_call(clc_ptr *x, clc_ptr clo, clc_ptr v);
void instr_struct(clc_ptr *x, int tag, int size, ...);
void instr_open(clc_ptr *x, clc_ptr (*f)(clc_env), clc_ptr m, int size, ...);
void instr_send(clc_ptr *x, clc_ptr ch);
void instr_recv(clc_ptr *x, clc_ptr ch, int tag);
void instr_close(clc_ptr *x, clc_ptr ch);
void instr_trg(clc_ptr *x, clc_ptr (*f)(clc_ptr));

#endif
