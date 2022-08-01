#include "runtime.h"

CLC_ptr _4803(CLC_ptr _4802, CLC_env env)
{
  
  
  return _4802;
}

CLC_ptr _4811(CLC_ptr _4807, CLC_env env)
{
  CLC_ptr _4808;
  CLC_ptr _4809;
  CLC_ptr _4810;
  INSTR_call(&_4808, env[3], env[2]);
  INSTR_call(&_4809, _4808, _4807);
  INSTR_struct(&_4810, 5, 1, _4809);
  return _4810;
}

CLC_ptr addn_4813(CLC_ptr _4799, CLC_env env)
{
  CLC_ptr _4800;
  CLC_ptr _4804;
  CLC_ptr _4805;
  CLC_ptr _4812;
  switch(((CLC_node)_4799)->tag){
    case 4:
      INSTR_clo(&_4804, &_4803, 4, 0, _4799, env[0], env[1]);
      INSTR_mov(&_4800, _4804);
      break;
    case 5:
      INSTR_mov(&_4805, ((CLC_node)_4799)->data[0]);
      INSTR_clo(&_4812, &_4811, 5, 0, _4799, _4805, env[0], env[1]);
      INSTR_mov(&_4800, _4812);
      break;}
  return _4800;
}

CLC_ptr _4821(CLC_ptr _4819, CLC_env env)
{
  CLC_ptr _4820;
  INSTR_struct(&_4820, 4, 0);
  return _4820;
}

CLC_ptr _4831(CLC_ptr _4825, CLC_env env)
{
  CLC_ptr _4826;
  CLC_ptr _4827;
  CLC_ptr _4828;
  CLC_ptr _4829;
  CLC_ptr _4830;
  switch(((CLC_node)_4825)->tag){
    case 4:
      INSTR_struct(&_4827, 5, 1, env[2]);
      INSTR_mov(&_4826, _4827);
      break;
    case 5:
      INSTR_mov(&_4828, ((CLC_node)_4825)->data[0]);
      INSTR_call(&_4829, env[3], env[2]);
      INSTR_call(&_4830, _4829, _4828);
      INSTR_mov(&_4826, _4830);
      break;}
  return _4826;
}

CLC_ptr subn_4833(CLC_ptr _4816, CLC_env env)
{
  CLC_ptr _4817;
  CLC_ptr _4822;
  CLC_ptr _4823;
  CLC_ptr _4832;
  switch(((CLC_node)_4816)->tag){
    case 4:
      INSTR_clo(&_4822, &_4821, 5, 0, _4816, env[0], env[1], env[2]);
      INSTR_mov(&_4817, _4822);
      break;
    case 5:
      INSTR_mov(&_4823, ((CLC_node)_4816)->data[0]);
      INSTR_clo(&_4832, &_4831, 6, 0, _4816, _4823, env[0], env[1], env[2]);
      INSTR_mov(&_4817, _4832);
      break;}
  return _4817;
}

CLC_ptr _4840(CLC_ptr _4839, CLC_env env)
{
  
  
  return _4839;
}

CLC_ptr _4849(CLC_ptr _4845, CLC_env env)
{
  CLC_ptr _4846;
  CLC_ptr _4847;
  CLC_ptr _4848;
  INSTR_call(&_4846, env[4], env[3]);
  INSTR_call(&_4847, _4846, _4845);
  INSTR_struct(&_4848, 18, 2, env[2], _4847);
  return _4848;
}

CLC_ptr cat_4851(CLC_ptr _4836, CLC_env env)
{
  CLC_ptr _4837;
  CLC_ptr _4841;
  CLC_ptr _4842;
  CLC_ptr _4843;
  CLC_ptr _4850;
  switch(((CLC_node)_4836)->tag){
    case 17:
      INSTR_clo(&_4841, &_4840, 6, 0, _4836, env[0], env[1], env[2], env[3]);
      INSTR_mov(&_4837, _4841);
      break;
    case 18:
      INSTR_mov(&_4842, ((CLC_node)_4836)->data[0]);
      INSTR_mov(&_4843, ((CLC_node)_4836)->data[1]);
      INSTR_clo(&_4850, &_4849, 8, 0, _4836, _4842, _4843, env[0], env[1], env[2], env[3]);
      INSTR_mov(&_4837, _4850);
      break;}
  return _4837;
}

CLC_ptr strlen_4861(CLC_ptr _4854, CLC_env env)
{
  CLC_ptr _4855;
  CLC_ptr _4856;
  CLC_ptr _4857;
  CLC_ptr _4858;
  CLC_ptr _4859;
  CLC_ptr _4860;
  switch(((CLC_node)_4854)->tag){
    case 17: INSTR_struct(&_4856, 4, 0);
             INSTR_mov(&_4855, _4856);
             break;
    case 18:
      INSTR_mov(&_4857, ((CLC_node)_4854)->data[0]);
      INSTR_mov(&_4858, ((CLC_node)_4854)->data[1]);
      INSTR_call(&_4859, env[0], _4858);
      INSTR_struct(&_4860, 5, 1, _4859);
      INSTR_mov(&_4855, _4860);
      break;}
  return _4855;
}

CLC_ptr _4867(CLC_ptr _4866, CLC_env env)
{
  
  
  return 0;
}

CLC_ptr lt_4869(CLC_ptr _4864, CLC_env env)
{
  CLC_ptr _4868;
  INSTR_clo(&_4868, &_4867, 8, 0, _4864, env[0], env[1], env[2], env[3], env[4], env[5]);
  return _4868;
}

CLC_ptr stdin_rec_4874(CLC_ptr _4872, CLC_env env)
{
  CLC_ptr _4873;
  switch(((CLC_node)_4872)->tag){
    case 1: INSTR_mov(&_4873, 0);
            break;}
  return _4873;
}

CLC_ptr stdout_rec_4879(CLC_ptr _4877, CLC_env env)
{
  CLC_ptr _4878;
  switch(((CLC_node)_4877)->tag){
    case 1: INSTR_mov(&_4878, 0);
            break;}
  return _4878;
}

CLC_ptr stderr_rec_4884(CLC_ptr _4882, CLC_env env)
{
  CLC_ptr _4883;
  switch(((CLC_node)_4882)->tag){
    case 1: INSTR_mov(&_4883, 0);
            break;}
  return _4883;
}

CLC_ptr readline_4898(CLC_ptr _4893, CLC_env env)
{
  CLC_ptr _4894;
  CLC_ptr _4895;
  CLC_ptr _4896;
  CLC_ptr _4897;
  INSTR_send(&_4894, _4893);
  INSTR_struct(&_4895, 2, 0);
  INSTR_call(&_4896, _4894, _4895);
  INSTR_recv(&_4897, _4896, 13);
  return _4897;
}

CLC_ptr close_in_4906(CLC_ptr _4901, CLC_env env)
{
  CLC_ptr _4902;
  CLC_ptr _4903;
  CLC_ptr _4904;
  CLC_ptr _4905;
  INSTR_send(&_4903, _4901);
  INSTR_struct(&_4904, 3, 0);
  INSTR_call(&_4905, _4903, _4904);
  INSTR_close(&_4902, _4905, 1);
  return _4902;
}

CLC_ptr _4917(CLC_ptr _4911, CLC_env env)
{
  CLC_ptr _4912;
  CLC_ptr _4913;
  CLC_ptr _4914;
  CLC_ptr _4915;
  CLC_ptr _4916;
  INSTR_send(&_4912, env[1]);
  INSTR_struct(&_4913, 2, 0);
  INSTR_call(&_4914, _4912, _4913);
  INSTR_send(&_4915, _4914);
  INSTR_call(&_4916, _4915, _4911);
  return _4916;
}

CLC_ptr printline_4919(CLC_ptr _4909, CLC_env env)
{
  CLC_ptr _4918;
  INSTR_clo(&_4918, &_4917, 17, 0, _4909, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return _4918;
}

CLC_ptr close_out_4927(CLC_ptr _4922, CLC_env env)
{
  CLC_ptr _4923;
  CLC_ptr _4924;
  CLC_ptr _4925;
  CLC_ptr _4926;
  INSTR_send(&_4924, _4922);
  INSTR_struct(&_4925, 3, 0);
  INSTR_call(&_4926, _4924, _4925);
  INSTR_close(&_4923, _4926, 1);
  return _4923;
}

CLC_ptr _4938(CLC_ptr _4932, CLC_env env)
{
  CLC_ptr _4933;
  CLC_ptr _4934;
  CLC_ptr _4935;
  CLC_ptr _4936;
  CLC_ptr _4937;
  INSTR_send(&_4933, env[1]);
  INSTR_struct(&_4934, 2, 0);
  INSTR_call(&_4935, _4933, _4934);
  INSTR_send(&_4936, _4935);
  INSTR_call(&_4937, _4936, _4932);
  return _4937;
}

CLC_ptr printerr_4940(CLC_ptr _4930, CLC_env env)
{
  CLC_ptr _4939;
  INSTR_clo(&_4939, &_4938, 19, 0, _4930, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16]);
  return _4939;
}

CLC_ptr close_err_4948(CLC_ptr _4943, CLC_env env)
{
  CLC_ptr _4944;
  CLC_ptr _4945;
  CLC_ptr _4946;
  CLC_ptr _4947;
  INSTR_send(&_4945, _4943);
  INSTR_struct(&_4946, 3, 0);
  INSTR_call(&_4947, _4945, _4946);
  INSTR_close(&_4944, _4947, 1);
  return _4944;
}

CLC_ptr _4955(CLC_ptr _4954, CLC_env env)
{
  
  
  return _4954;
}

CLC_ptr _4966(CLC_ptr _4959, CLC_env env)
{
  CLC_ptr _4960;
  CLC_ptr _4961;
  CLC_ptr _4962;
  CLC_ptr _4963;
  CLC_ptr _4964;
  CLC_ptr _4965;
  switch(((CLC_node)_4959)->tag){
    case 4:
      INSTR_struct(&_4961, 5, 1, env[2]);
      INSTR_mov(&_4960, _4961);
      break;
    case 5:
      INSTR_mov(&_4962, ((CLC_node)_4959)->data[0]);
      INSTR_call(&_4963, env[3], env[2]);
      INSTR_call(&_4964, _4963, _4962);
      INSTR_struct(&_4965, 5, 1, _4964);
      INSTR_mov(&_4960, _4965);
      break;}
  return _4960;
}

CLC_ptr maxn_4968(CLC_ptr _4951, CLC_env env)
{
  CLC_ptr _4952;
  CLC_ptr _4956;
  CLC_ptr _4957;
  CLC_ptr _4967;
  switch(((CLC_node)_4951)->tag){
    case 4:
      INSTR_clo(&_4956, &_4955, 21, 0, _4951, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18]);
      INSTR_mov(&_4952, _4956);
      break;
    case 5:
      INSTR_mov(&_4957, ((CLC_node)_4951)->data[0]);
      INSTR_clo(&_4967, &_4966, 22, 0, _4951, _4957, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18]);
      INSTR_mov(&_4952, _4967);
      break;}
  return _4952;
}

CLC_ptr _4990(CLC_ptr _4988, CLC_env env)
{
  CLC_ptr _4989;
  switch(((CLC_node)_4988)->tag){
    case 1: INSTR_mov(&_4989, env[7]);
            break;}
  return _4989;
}

CLC_ptr _4994(CLC_ptr _4983, CLC_env env)
{
  CLC_ptr _4984;
  CLC_ptr _4986;
  CLC_ptr _4991;
  CLC_ptr _4992;
  CLC_ptr _4993;
  CLC_ptr x_4985;
  switch(((CLC_node)_4983)->tag){
    case 13:
      INSTR_mov(&x_4985, ((CLC_node)_4983)->data[0]);
      INSTR_mov(&_4986, ((CLC_node)_4983)->data[1]);
      INSTR_clo(&_4991, &_4990, 29, 0, _4983, x_4985, _4986, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24]);
      INSTR_struct(&_4992, 1, 0);
      INSTR_call(&_4993, _4991, _4992);
      INSTR_mov(&_4984, _4993);
      break;}
  return _4984;
}

CLC_ptr _4998(CLC_ptr _4978, CLC_env env)
{
  CLC_ptr _4979;
  CLC_ptr _4980;
  CLC_ptr _4981;
  CLC_ptr _4995;
  CLC_ptr _4996;
  CLC_ptr _4997;
  switch(((CLC_node)_4978)->tag){
    case 14:
      INSTR_mov(&_4980, ((CLC_node)_4978)->data[0]);
      INSTR_mov(&_4981, ((CLC_node)_4978)->data[1]);
      INSTR_clo(&_4995, &_4994, 25, 0, _4978, _4980, _4981, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20]);
      INSTR_recv(&_4996, _4980, 13);
      INSTR_call(&_4997, _4995, _4996);
      INSTR_mov(&_4979, _4997);
      break;}
  return _4979;
}

CLC_ptr _5006(CLC_env env)
{
  CLC_ptr _5002;
  CLC_ptr _5003;
  CLC_ptr _5004;
  CLC_ptr ch_5001;
  INSTR_send(&_5002, env[0]);
  INSTR_call(&_5003, _5002, env[1]);
  INSTR_mov(&ch_5001, _5003);
  INSTR_close(&_5004, ch_5001, 1);
  return _5004;
}

int main()
{
  CLC_ptr _141;
  CLC_ptr _4814;
  CLC_ptr _4834;
  CLC_ptr _4852;
  CLC_ptr _4862;
  CLC_ptr _4870;
  CLC_ptr _4875;
  CLC_ptr _4880;
  CLC_ptr _4885;
  CLC_ptr _4886;
  CLC_ptr _4887;
  CLC_ptr _4888;
  CLC_ptr _4889;
  CLC_ptr _4890;
  CLC_ptr _4891;
  CLC_ptr _4899;
  CLC_ptr _4907;
  CLC_ptr _4920;
  CLC_ptr _4928;
  CLC_ptr _4941;
  CLC_ptr _4949;
  CLC_ptr _4969;
  CLC_ptr _4970;
  CLC_ptr _4971;
  CLC_ptr _4972;
  CLC_ptr _4973;
  CLC_ptr _4974;
  CLC_ptr _4975;
  CLC_ptr _4976;
  CLC_ptr _4999;
  CLC_ptr _5005;
  CLC_ptr _5007;
  CLC_ptr addn_3;
  CLC_ptr cat_67;
  CLC_ptr close_err_130;
  CLC_ptr close_in_114;
  CLC_ptr close_out_122;
  CLC_ptr foo_140;
  CLC_ptr lt_84;
  CLC_ptr maxn_133;
  CLC_ptr printerr_125;
  CLC_ptr printline_117;
  CLC_ptr readline_109;
  CLC_ptr stderr_rec_102;
  CLC_ptr stderr_t_108;
  CLC_ptr stdin_rec_94;
  CLC_ptr stdin_t_106;
  CLC_ptr stdout_rec_98;
  CLC_ptr stdout_t_107;
  CLC_ptr strlen_74;
  CLC_ptr subn_9;
  INSTR_clo(&_4814, &addn_4813, 2, 0, 0);
  INSTR_mov(&addn_3, _4814);
  INSTR_clo(&_4834, &subn_4833, 3, 0, addn_3, 0);
  INSTR_mov(&subn_9, _4834);
  INSTR_clo(&_4852, &cat_4851, 4, 0, subn_9, addn_3, 0);
  INSTR_mov(&cat_67, _4852);
  INSTR_clo(&_4862, &strlen_4861, 5, 0, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&strlen_74, _4862);
  INSTR_clo(&_4870, &lt_4869, 6, 0, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&lt_84, _4870);
  INSTR_clo(&_4875, &stdin_rec_4874, 7, 0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdin_rec_94, _4875);
  INSTR_clo(&_4880, &stdout_rec_4879, 8, 0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdout_rec_98, _4880);
  INSTR_clo(&_4885, &stderr_rec_4884, 9, 0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stderr_rec_102, _4885);
  INSTR_struct(&_4886, 1, 0);
  INSTR_call(&_4887, stdin_rec_94, _4886);
  INSTR_mov(&stdin_t_106, _4887);
  INSTR_struct(&_4888, 1, 0);
  INSTR_call(&_4889, stdout_rec_98, _4888);
  INSTR_mov(&stdout_t_107, _4889);
  INSTR_struct(&_4890, 1, 0);
  INSTR_call(&_4891, stderr_rec_102, _4890);
  INSTR_mov(&stderr_t_108, _4891);
  INSTR_clo(&_4899, &readline_4898, 13, 0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&readline_109, _4899);
  INSTR_clo(&_4907, &close_in_4906, 14, 0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_in_114, _4907);
  INSTR_clo(&_4920, &printline_4919, 15, 0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printline_117, _4920);
  INSTR_clo(&_4928, &close_out_4927, 16, 0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_out_122, _4928);
  INSTR_clo(&_4941, &printerr_4940, 17, 0, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printerr_125, _4941);
  INSTR_clo(&_4949, &close_err_4948, 18, 0, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_err_130, _4949);
  INSTR_clo(&_4969, &maxn_4968, 19, 0, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&maxn_133, _4969);
  INSTR_struct(&_4970, 4, 0);
  INSTR_struct(&_4971, 5, 1, _4970);
  INSTR_call(&_4972, maxn_133, _4971);
  INSTR_struct(&_4973, 4, 0);
  INSTR_struct(&_4974, 5, 1, _4973);
  INSTR_struct(&_4975, 5, 1, _4974);
  INSTR_call(&_4976, _4972, _4975);
  INSTR_mov(&foo_140, _4976);
  INSTR_clo(&_4999, &_4998, 21, 0, foo_140, maxn_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_open(&_5005, &_5006, 0, 14, 20, foo_140, maxn_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_call(&_5007, _4999, _5005);
  INSTR_mov(&_141, _5007);
  return 0;
}
