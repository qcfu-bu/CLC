#include "runtime.h"

CLC_ptr _269(CLC_ptr _268, CLC_env env)
{
  
  
  return _268;
}

CLC_ptr _280(CLC_ptr _273, CLC_env env)
{
  CLC_ptr _274;
  CLC_ptr _275;
  CLC_ptr _276;
  CLC_ptr _277;
  CLC_ptr _278;
  CLC_ptr _279;
  switch(((CLC_node)_273)->tag){
    case 22:
      INSTR_struct(&_275, 23, 1, env[2]);
      INSTR_mov(&_274, _275);
      break;
    case 23:
      INSTR_mov(&_276, ((CLC_node)_273)->data[0]);
      INSTR_call(&_277, env[3], env[2]);
      INSTR_call(&_278, _277, _276);
      INSTR_struct(&_279, 23, 1, _278);
      INSTR_mov(&_274, _279);
      break;}
  return _274;
}

CLC_ptr maxn_282(CLC_ptr _265, CLC_env env)
{
  CLC_ptr _266;
  CLC_ptr _270;
  CLC_ptr _271;
  CLC_ptr _281;
  switch(((CLC_node)_265)->tag){
    case 22:
      INSTR_clo(&_270, &_269, 4, 0, _265, env[0], env[1]);
      INSTR_mov(&_266, _270);
      break;
    case 23:
      INSTR_mov(&_271, ((CLC_node)_265)->data[0]);
      INSTR_clo(&_281, &_280, 5, 0, _265, _271, env[0], env[1]);
      INSTR_mov(&_266, _281);
      break;}
  return _266;
}

int main()
{
  CLC_ptr _142;
  CLC_ptr _283;
  CLC_ptr _284;
  CLC_ptr _285;
  CLC_ptr _286;
  CLC_ptr _287;
  CLC_ptr _288;
  CLC_ptr _289;
  CLC_ptr _290;
  CLC_ptr foo_141;
  CLC_ptr maxn_134;
  INSTR_clo(&_283, &maxn_282, 2, 0, 0);
  INSTR_mov(&maxn_134, _283);
  INSTR_struct(&_284, 22, 0);
  INSTR_struct(&_285, 23, 1, _284);
  INSTR_call(&_286, maxn_134, _285);
  INSTR_struct(&_287, 22, 0);
  INSTR_struct(&_288, 23, 1, _287);
  INSTR_struct(&_289, 23, 1, _288);
  INSTR_call(&_290, _286, _289);
  INSTR_mov(&foo_141, _290);
  INSTR_mov(&_142, 0);
  return 0;
}
