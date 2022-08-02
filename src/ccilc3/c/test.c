#include "runtime.h"

CLC_ptr _4803(CLC_ptr _4802, CLC_env env)
{
  
  
  return _4802;
}

CLC_ptr _4811(CLC_ptr _4807, CLC_env env)
{
  CLC_ptr succ_c5_4810;
  CLC_ptr tmp_4808;
  CLC_ptr tmp_4809;
  INSTR_call(&tmp_4808, env[3], env[2]);
  INSTR_call(&tmp_4809, tmp_4808, _4807);
  INSTR_struct(&succ_c5_4810, 5, 1, tmp_4809);
  return succ_c5_4810;
}

CLC_ptr addn_4813(CLC_ptr _4799, CLC_env env)
{
  CLC_ptr _4805;
  CLC_ptr case_4800;
  CLC_ptr clo_4804;
  CLC_ptr clo_4812;
  switch(((CLC_node)_4799)->tag){
    case 4:
      INSTR_clo(&clo_4804, &_4803, 4, 0, _4799, env[0], env[1]);
      INSTR_mov(&case_4800, clo_4804);
      break;
    case 5:
      INSTR_mov(&_4805, ((CLC_node)_4799)->data[0]);
      INSTR_clo(&clo_4812, &_4811, 5, 0, _4799, _4805, env[0], env[1]);
      INSTR_mov(&case_4800, clo_4812);
      break;}
  return case_4800;
}

CLC_ptr _4821(CLC_ptr _4819, CLC_env env)
{
  CLC_ptr zero_c4_4820;
  INSTR_struct(&zero_c4_4820, 4, 0);
  return zero_c4_4820;
}

CLC_ptr _4831(CLC_ptr _4825, CLC_env env)
{
  CLC_ptr _4828;
  CLC_ptr case_4826;
  CLC_ptr succ_c5_4827;
  CLC_ptr tmp_4829;
  CLC_ptr tmp_4830;
  switch(((CLC_node)_4825)->tag){
    case 4:
      INSTR_struct(&succ_c5_4827, 5, 1, env[2]);
      INSTR_mov(&case_4826, succ_c5_4827);
      break;
    case 5:
      INSTR_mov(&_4828, ((CLC_node)_4825)->data[0]);
      INSTR_call(&tmp_4829, env[3], env[2]);
      INSTR_call(&tmp_4830, tmp_4829, _4828);
      INSTR_mov(&case_4826, tmp_4830);
      break;}
  return case_4826;
}

CLC_ptr subn_4833(CLC_ptr _4816, CLC_env env)
{
  CLC_ptr _4823;
  CLC_ptr case_4817;
  CLC_ptr clo_4822;
  CLC_ptr clo_4832;
  switch(((CLC_node)_4816)->tag){
    case 4:
      INSTR_clo(&clo_4822, &_4821, 5, 0, _4816, env[0], env[1], env[2]);
      INSTR_mov(&case_4817, clo_4822);
      break;
    case 5:
      INSTR_mov(&_4823, ((CLC_node)_4816)->data[0]);
      INSTR_clo(&clo_4832, &_4831, 6, 0, _4816, _4823, env[0], env[1], env[2]);
      INSTR_mov(&case_4817, clo_4832);
      break;}
  return case_4817;
}

CLC_ptr _4840(CLC_ptr _4839, CLC_env env)
{
  
  
  return _4839;
}

CLC_ptr _4849(CLC_ptr _4845, CLC_env env)
{
  CLC_ptr String_c18_4848;
  CLC_ptr tmp_4846;
  CLC_ptr tmp_4847;
  INSTR_call(&tmp_4846, env[4], env[3]);
  INSTR_call(&tmp_4847, tmp_4846, _4845);
  INSTR_struct(&String_c18_4848, 18, 2, env[2], tmp_4847);
  return String_c18_4848;
}

CLC_ptr cat_4851(CLC_ptr _4836, CLC_env env)
{
  CLC_ptr _4842;
  CLC_ptr _4843;
  CLC_ptr case_4837;
  CLC_ptr clo_4841;
  CLC_ptr clo_4850;
  switch(((CLC_node)_4836)->tag){
    case 17:
      INSTR_clo(&clo_4841, &_4840, 6, 0, _4836, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_4837, clo_4841);
      break;
    case 18:
      INSTR_mov(&_4842, ((CLC_node)_4836)->data[0]);
      INSTR_mov(&_4843, ((CLC_node)_4836)->data[1]);
      INSTR_clo(&clo_4850, &_4849, 8, 0, _4836, _4842, _4843, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_4837, clo_4850);
      break;}
  return case_4837;
}

CLC_ptr strlen_4861(CLC_ptr _4854, CLC_env env)
{
  CLC_ptr _4857;
  CLC_ptr _4858;
  CLC_ptr case_4855;
  CLC_ptr succ_c5_4860;
  CLC_ptr tmp_4859;
  CLC_ptr zero_c4_4856;
  switch(((CLC_node)_4854)->tag){
    case 17:
      INSTR_struct(&zero_c4_4856, 4, 0);
      INSTR_mov(&case_4855, zero_c4_4856);
      break;
    case 18:
      INSTR_mov(&_4857, ((CLC_node)_4854)->data[0]);
      INSTR_mov(&_4858, ((CLC_node)_4854)->data[1]);
      INSTR_call(&tmp_4859, env[0], _4858);
      INSTR_struct(&succ_c5_4860, 5, 1, tmp_4859);
      INSTR_mov(&case_4855, succ_c5_4860);
      break;}
  return case_4855;
}

CLC_ptr _4867(CLC_ptr _4866, CLC_env env)
{
  
  
  return 0;
}

CLC_ptr lt_4869(CLC_ptr _4864, CLC_env env)
{
  CLC_ptr clo_4868;
  INSTR_clo(&clo_4868, &_4867, 8, 0, _4864, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_4868;
}

CLC_ptr stdin_rec_4874(CLC_ptr _4872, CLC_env env)
{
  CLC_ptr case_4873;
  switch(((CLC_node)_4872)->tag){
    case 1: INSTR_mov(&case_4873, 0);
            break;}
  return case_4873;
}

CLC_ptr stdout_rec_4879(CLC_ptr _4877, CLC_env env)
{
  CLC_ptr case_4878;
  switch(((CLC_node)_4877)->tag){
    case 1: INSTR_mov(&case_4878, 0);
            break;}
  return case_4878;
}

CLC_ptr stderr_rec_4884(CLC_ptr _4882, CLC_env env)
{
  CLC_ptr case_4883;
  switch(((CLC_node)_4882)->tag){
    case 1: INSTR_mov(&case_4883, 0);
            break;}
  return case_4883;
}

CLC_ptr readline_4898(CLC_ptr _4893, CLC_env env)
{
  CLC_ptr recv_struct_4897;
  CLC_ptr send_clo_4894;
  CLC_ptr tmp_4896;
  CLC_ptr true_c2_4895;
  INSTR_send(&send_clo_4894, _4893);
  INSTR_struct(&true_c2_4895, 2, 0);
  INSTR_call(&tmp_4896, send_clo_4894, true_c2_4895);
  INSTR_recv(&recv_struct_4897, tmp_4896, 13);
  return recv_struct_4897;
}

CLC_ptr close_in_4903(CLC_ptr _4901, CLC_env env)
{
  CLC_ptr unit_struct_4902;
  INSTR_struct(&unit_struct_4902, 1, 0);
  return unit_struct_4902;
}

CLC_ptr _4914(CLC_ptr _4908, CLC_env env)
{
  CLC_ptr send_clo_4909;
  CLC_ptr send_clo_4912;
  CLC_ptr tmp_4911;
  CLC_ptr tmp_4913;
  CLC_ptr true_c2_4910;
  INSTR_send(&send_clo_4909, env[1]);
  INSTR_struct(&true_c2_4910, 2, 0);
  INSTR_call(&tmp_4911, send_clo_4909, true_c2_4910);
  INSTR_send(&send_clo_4912, tmp_4911);
  INSTR_call(&tmp_4913, send_clo_4912, _4908);
  return tmp_4913;
}

CLC_ptr printline_4916(CLC_ptr _4906, CLC_env env)
{
  CLC_ptr clo_4915;
  INSTR_clo(&clo_4915, &_4914, 17, 0, _4906, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_4915;
}

CLC_ptr close_out_4921(CLC_ptr _4919, CLC_env env)
{
  CLC_ptr unit_struct_4920;
  INSTR_struct(&unit_struct_4920, 1, 0);
  return unit_struct_4920;
}

CLC_ptr _4932(CLC_ptr _4926, CLC_env env)
{
  CLC_ptr send_clo_4927;
  CLC_ptr send_clo_4930;
  CLC_ptr tmp_4929;
  CLC_ptr tmp_4931;
  CLC_ptr true_c2_4928;
  INSTR_send(&send_clo_4927, env[1]);
  INSTR_struct(&true_c2_4928, 2, 0);
  INSTR_call(&tmp_4929, send_clo_4927, true_c2_4928);
  INSTR_send(&send_clo_4930, tmp_4929);
  INSTR_call(&tmp_4931, send_clo_4930, _4926);
  return tmp_4931;
}

CLC_ptr printerr_4934(CLC_ptr _4924, CLC_env env)
{
  CLC_ptr clo_4933;
  INSTR_clo(&clo_4933, &_4932, 19, 0, _4924, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16]);
  return clo_4933;
}

CLC_ptr close_err_4939(CLC_ptr _4937, CLC_env env)
{
  CLC_ptr unit_struct_4938;
  INSTR_struct(&unit_struct_4938, 1, 0);
  return unit_struct_4938;
}

CLC_ptr _4946(CLC_ptr _4945, CLC_env env)
{
  
  
  return _4945;
}

CLC_ptr _4957(CLC_ptr _4950, CLC_env env)
{
  CLC_ptr _4953;
  CLC_ptr case_4951;
  CLC_ptr succ_c5_4952;
  CLC_ptr succ_c5_4956;
  CLC_ptr tmp_4954;
  CLC_ptr tmp_4955;
  switch(((CLC_node)_4950)->tag){
    case 4:
      INSTR_struct(&succ_c5_4952, 5, 1, env[2]);
      INSTR_mov(&case_4951, succ_c5_4952);
      break;
    case 5:
      INSTR_mov(&_4953, ((CLC_node)_4950)->data[0]);
      INSTR_call(&tmp_4954, env[3], env[2]);
      INSTR_call(&tmp_4955, tmp_4954, _4953);
      INSTR_struct(&succ_c5_4956, 5, 1, tmp_4955);
      INSTR_mov(&case_4951, succ_c5_4956);
      break;}
  return case_4951;
}

CLC_ptr maxn_4959(CLC_ptr _4942, CLC_env env)
{
  CLC_ptr _4948;
  CLC_ptr case_4943;
  CLC_ptr clo_4947;
  CLC_ptr clo_4958;
  switch(((CLC_node)_4942)->tag){
    case 4:
      INSTR_clo(&clo_4947, &_4946, 21, 0, _4942, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18]);
      INSTR_mov(&case_4943, clo_4947);
      break;
    case 5:
      INSTR_mov(&_4948, ((CLC_node)_4942)->data[0]);
      INSTR_clo(&clo_4958, &_4957, 22, 0, _4942, _4948, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18]);
      INSTR_mov(&case_4943, clo_4958);
      break;}
  return case_4943;
}

CLC_ptr _4981(CLC_ptr _4979, CLC_env env)
{
  CLC_ptr case_4980;
  switch(((CLC_node)_4979)->tag){
    case 1: INSTR_mov(&case_4980, env[7]);
            break;}
  return case_4980;
}

CLC_ptr _4985(CLC_ptr _4974, CLC_env env)
{
  CLC_ptr _4977;
  CLC_ptr case_4975;
  CLC_ptr clo_4982;
  CLC_ptr tmp_4984;
  CLC_ptr unit_struct_4983;
  CLC_ptr x_4976;
  switch(((CLC_node)_4974)->tag){
    case 13:
      INSTR_mov(&x_4976, ((CLC_node)_4974)->data[0]);
      INSTR_mov(&_4977, ((CLC_node)_4974)->data[1]);
      INSTR_clo(&clo_4982, &_4981, 29, 0, _4974, x_4976, _4977, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24]);
      INSTR_close(&unit_struct_4983, _4977, 1);
      INSTR_call(&tmp_4984, clo_4982, unit_struct_4983);
      INSTR_mov(&case_4975, tmp_4984);
      break;}
  return case_4975;
}

CLC_ptr _4989(CLC_ptr _4969, CLC_env env)
{
  CLC_ptr _4971;
  CLC_ptr _4972;
  CLC_ptr case_4970;
  CLC_ptr clo_4986;
  CLC_ptr recv_struct_4987;
  CLC_ptr tmp_4988;
  switch(((CLC_node)_4969)->tag){
    case 14:
      INSTR_mov(&_4971, ((CLC_node)_4969)->data[0]);
      INSTR_mov(&_4972, ((CLC_node)_4969)->data[1]);
      INSTR_clo(&clo_4986, &_4985, 25, 0, _4969, _4971, _4972, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20]);
      INSTR_recv(&recv_struct_4987, _4971, 13);
      INSTR_call(&tmp_4988, clo_4986, recv_struct_4987);
      INSTR_mov(&case_4970, tmp_4988);
      break;}
  return case_4970;
}

CLC_ptr fork_proc_4997(CLC_env env)
{
  CLC_ptr ch_4992;
  CLC_ptr send_clo_4993;
  CLC_ptr tmp_4994;
  CLC_ptr unit_struct_4995;
  INSTR_send(&send_clo_4993, env[0]);
  INSTR_call(&tmp_4994, send_clo_4993, env[1]);
  INSTR_mov(&ch_4992, tmp_4994);
  INSTR_struct(&unit_struct_4995, 1, 0);
  return unit_struct_4995;
}

int main()
{
  CLC_ptr _141;
  CLC_ptr addn_3;
  CLC_ptr addn_4814;
  CLC_ptr cat_67;
  CLC_ptr cat_4852;
  CLC_ptr clo_4990;
  CLC_ptr close_err_130;
  CLC_ptr close_err_4940;
  CLC_ptr close_in_114;
  CLC_ptr close_in_4904;
  CLC_ptr close_out_122;
  CLC_ptr close_out_4922;
  CLC_ptr foo_140;
  CLC_ptr fork_res_4996;
  CLC_ptr lt_84;
  CLC_ptr lt_4870;
  CLC_ptr maxn_133;
  CLC_ptr maxn_4960;
  CLC_ptr printerr_125;
  CLC_ptr printerr_4935;
  CLC_ptr printline_117;
  CLC_ptr printline_4917;
  CLC_ptr readline_109;
  CLC_ptr readline_4899;
  CLC_ptr stderr_rec_102;
  CLC_ptr stderr_rec_4885;
  CLC_ptr stderr_t_108;
  CLC_ptr stdin_rec_94;
  CLC_ptr stdin_rec_4875;
  CLC_ptr stdin_t_106;
  CLC_ptr stdout_rec_98;
  CLC_ptr stdout_rec_4880;
  CLC_ptr stdout_t_107;
  CLC_ptr strlen_74;
  CLC_ptr strlen_4862;
  CLC_ptr subn_9;
  CLC_ptr subn_4834;
  CLC_ptr succ_c5_4962;
  CLC_ptr succ_c5_4965;
  CLC_ptr succ_c5_4966;
  CLC_ptr tmp_4887;
  CLC_ptr tmp_4889;
  CLC_ptr tmp_4891;
  CLC_ptr tmp_4963;
  CLC_ptr tmp_4967;
  CLC_ptr tmp_4998;
  CLC_ptr tt_c1_4886;
  CLC_ptr tt_c1_4888;
  CLC_ptr tt_c1_4890;
  CLC_ptr zero_c4_4961;
  CLC_ptr zero_c4_4964;
  INSTR_clo(&addn_4814, &addn_4813, 2, 0, 0);
  INSTR_mov(&addn_3, addn_4814);
  INSTR_clo(&subn_4834, &subn_4833, 3, 0, addn_3, 0);
  INSTR_mov(&subn_9, subn_4834);
  INSTR_clo(&cat_4852, &cat_4851, 4, 0, subn_9, addn_3, 0);
  INSTR_mov(&cat_67, cat_4852);
  INSTR_clo(&strlen_4862, &strlen_4861, 5, 0, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&strlen_74, strlen_4862);
  INSTR_clo(&lt_4870, &lt_4869, 6, 0, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&lt_84, lt_4870);
  INSTR_clo(&stdin_rec_4875, &stdin_rec_4874, 7, 0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdin_rec_94, stdin_rec_4875);
  INSTR_clo(&stdout_rec_4880, &stdout_rec_4879, 8, 0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdout_rec_98, stdout_rec_4880);
  INSTR_clo(&stderr_rec_4885, &stderr_rec_4884, 9, 0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stderr_rec_102, stderr_rec_4885);
  INSTR_struct(&tt_c1_4886, 1, 0);
  INSTR_call(&tmp_4887, stdin_rec_94, tt_c1_4886);
  INSTR_mov(&stdin_t_106, tmp_4887);
  INSTR_struct(&tt_c1_4888, 1, 0);
  INSTR_call(&tmp_4889, stdout_rec_98, tt_c1_4888);
  INSTR_mov(&stdout_t_107, tmp_4889);
  INSTR_struct(&tt_c1_4890, 1, 0);
  INSTR_call(&tmp_4891, stderr_rec_102, tt_c1_4890);
  INSTR_mov(&stderr_t_108, tmp_4891);
  INSTR_clo(&readline_4899, &readline_4898, 13, 0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&readline_109, readline_4899);
  INSTR_clo(&close_in_4904, &close_in_4903, 14, 0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_in_114, close_in_4904);
  INSTR_clo(&printline_4917, &printline_4916, 15, 0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printline_117, printline_4917);
  INSTR_clo(&close_out_4922, &close_out_4921, 16, 0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_out_122, close_out_4922);
  INSTR_clo(&printerr_4935, &printerr_4934, 17, 0, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printerr_125, printerr_4935);
  INSTR_clo(&close_err_4940, &close_err_4939, 18, 0, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_err_130, close_err_4940);
  INSTR_clo(&maxn_4960, &maxn_4959, 19, 0, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&maxn_133, maxn_4960);
  INSTR_struct(&zero_c4_4961, 4, 0);
  INSTR_struct(&succ_c5_4962, 5, 1, zero_c4_4961);
  INSTR_call(&tmp_4963, maxn_133, succ_c5_4962);
  INSTR_struct(&zero_c4_4964, 4, 0);
  INSTR_struct(&succ_c5_4965, 5, 1, zero_c4_4964);
  INSTR_struct(&succ_c5_4966, 5, 1, succ_c5_4965);
  INSTR_call(&tmp_4967, tmp_4963, succ_c5_4966);
  INSTR_mov(&foo_140, tmp_4967);
  INSTR_clo(&clo_4990, &_4989, 21, 0, foo_140, maxn_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_open(&fork_res_4996, &fork_proc_4997, 0, 14, 20, foo_140, maxn_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_call(&tmp_4998, clo_4990, fork_res_4996);
  INSTR_mov(&_141, tmp_4998);
  return 0;
}
