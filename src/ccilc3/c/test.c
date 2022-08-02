#include "runtime.h"

CLC_ptr _4206(CLC_ptr _4205, CLC_env env)
{
    return _4205;
}

CLC_ptr _4214(CLC_ptr _4210, CLC_env env)
{
  CLC_ptr succ_c5_4213; CLC_ptr tmp_4211; CLC_ptr tmp_4212;
  INSTR_call(&tmp_4211, env[3], env[2]);
  INSTR_call(&tmp_4212, tmp_4211, _4210);
  INSTR_struct(&succ_c5_4213, 5, 1, tmp_4212); return succ_c5_4213;
}

CLC_ptr addn_4216(CLC_ptr _4202, CLC_env env)
{
  CLC_ptr _4208; CLC_ptr case_4203; CLC_ptr clo_4207; CLC_ptr clo_4215;
  switch(((CLC_node)_4202)->tag){
    case 4:
      INSTR_clo(&clo_4207, &_4206, 4, 0, _4202, env[0], env[1]);
      INSTR_mov(&case_4203, clo_4207);
      break;
    case 5:
      INSTR_mov(&_4208, ((CLC_node)_4202)->data[0]);
      INSTR_clo(&clo_4215, &_4214, 5, 0, _4202, _4208, env[0], env[1]);
      INSTR_mov(&case_4203, clo_4215);
      break;}
  return case_4203;
}

CLC_ptr _4224(CLC_ptr _4222, CLC_env env)
{
  CLC_ptr zero_c4_4223; INSTR_struct(&zero_c4_4223, 4, 0);
  return zero_c4_4223;
}

CLC_ptr _4234(CLC_ptr _4228, CLC_env env)
{
  CLC_ptr _4231; CLC_ptr case_4229; CLC_ptr succ_c5_4230; CLC_ptr tmp_4232;
  CLC_ptr tmp_4233;
  switch(((CLC_node)_4228)->tag){
    case 4:
      INSTR_struct(&succ_c5_4230, 5, 1, env[2]);
      INSTR_mov(&case_4229, succ_c5_4230);
      break;
    case 5:
      INSTR_mov(&_4231, ((CLC_node)_4228)->data[0]);
      INSTR_call(&tmp_4232, env[3], env[2]);
      INSTR_call(&tmp_4233, tmp_4232, _4231);
      INSTR_mov(&case_4229, tmp_4233);
      break;}
  return case_4229;
}

CLC_ptr subn_4236(CLC_ptr _4219, CLC_env env)
{
  CLC_ptr _4226; CLC_ptr case_4220; CLC_ptr clo_4225; CLC_ptr clo_4235;
  switch(((CLC_node)_4219)->tag){
    case 4:
      INSTR_clo(&clo_4225, &_4224, 5, 0, _4219, env[0], env[1], env[2]);
      INSTR_mov(&case_4220, clo_4225);
      break;
    case 5:
      INSTR_mov(&_4226, ((CLC_node)_4219)->data[0]);
      INSTR_clo(&clo_4235, &_4234, 6, 0, _4219, _4226, env[0], env[1], env[2]);
      INSTR_mov(&case_4220, clo_4235);
      break;}
  return case_4220;
}

CLC_ptr _4243(CLC_ptr _4242, CLC_env env)
{
    return _4242;
}

CLC_ptr _4252(CLC_ptr _4248, CLC_env env)
{
  CLC_ptr String_c18_4251; CLC_ptr tmp_4249; CLC_ptr tmp_4250;
  INSTR_call(&tmp_4249, env[4], env[3]);
  INSTR_call(&tmp_4250, tmp_4249, _4248);
  INSTR_struct(&String_c18_4251, 18, 2, env[2], tmp_4250);
  return String_c18_4251;
}

CLC_ptr cat_4254(CLC_ptr _4239, CLC_env env)
{
  CLC_ptr _4245; CLC_ptr _4246; CLC_ptr case_4240; CLC_ptr clo_4244;
  CLC_ptr clo_4253;
  switch(((CLC_node)_4239)->tag){
    case 17:
      INSTR_clo(&clo_4244, &_4243, 6, 0, _4239, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_4240, clo_4244);
      break;
    case 18:
      INSTR_mov(&_4245, ((CLC_node)_4239)->data[0]);
      INSTR_mov(&_4246, ((CLC_node)_4239)->data[1]);
      INSTR_clo(&clo_4253, &_4252, 8, 0, _4239, _4245, _4246, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_4240, clo_4253);
      break;}
  return case_4240;
}

CLC_ptr strlen_4264(CLC_ptr _4257, CLC_env env)
{
  CLC_ptr _4260; CLC_ptr _4261; CLC_ptr case_4258; CLC_ptr succ_c5_4263;
  CLC_ptr tmp_4262; CLC_ptr zero_c4_4259;
  switch(((CLC_node)_4257)->tag){
    case 17:
      INSTR_struct(&zero_c4_4259, 4, 0);
      INSTR_mov(&case_4258, zero_c4_4259);
      break;
    case 18:
      INSTR_mov(&_4260, ((CLC_node)_4257)->data[0]);
      INSTR_mov(&_4261, ((CLC_node)_4257)->data[1]);
      INSTR_call(&tmp_4262, env[0], _4261);
      INSTR_struct(&succ_c5_4263, 5, 1, tmp_4262);
      INSTR_mov(&case_4258, succ_c5_4263);
      break;}
  return case_4258;
}

CLC_ptr _4270(CLC_ptr _4269, CLC_env env)
{
    return 0;
}

CLC_ptr lt_4272(CLC_ptr _4267, CLC_env env)
{
  CLC_ptr clo_4271;
  INSTR_clo(&clo_4271, &_4270, 8, 0, _4267, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_4271;
}

CLC_ptr stdin_rec_4277(CLC_ptr _4275, CLC_env env)
{
  CLC_ptr case_4276;
  switch(((CLC_node)_4275)->tag){
    case 1: INSTR_mov(&case_4276, 0);
            break;}
  return case_4276;
}

CLC_ptr stdout_rec_4282(CLC_ptr _4280, CLC_env env)
{
  CLC_ptr case_4281;
  switch(((CLC_node)_4280)->tag){
    case 1: INSTR_mov(&case_4281, 0);
            break;}
  return case_4281;
}

CLC_ptr stderr_rec_4287(CLC_ptr _4285, CLC_env env)
{
  CLC_ptr case_4286;
  switch(((CLC_node)_4285)->tag){
    case 1: INSTR_mov(&case_4286, 0);
            break;}
  return case_4286;
}

CLC_ptr readline_4301(CLC_ptr _4296, CLC_env env)
{
  CLC_ptr recv_struct_4300; CLC_ptr send_clo_4297; CLC_ptr tmp_4299;
  CLC_ptr true_c2_4298;
  INSTR_send(&send_clo_4297, _4296);
  INSTR_struct(&true_c2_4298, 2, 0);
  INSTR_call(&tmp_4299, send_clo_4297, true_c2_4298);
  INSTR_recv(&recv_struct_4300, tmp_4299, 13); return recv_struct_4300;
}

CLC_ptr close_in_4309(CLC_ptr _4304, CLC_env env)
{
  CLC_ptr false_c3_4307; CLC_ptr send_clo_4306; CLC_ptr tmp_4308;
  CLC_ptr unit_struct_4305;
  INSTR_send(&send_clo_4306, _4304);
  INSTR_struct(&false_c3_4307, 3, 0);
  INSTR_call(&tmp_4308, send_clo_4306, false_c3_4307);
  INSTR_struct(&unit_struct_4305, 1, 0); return unit_struct_4305;
}

CLC_ptr _4320(CLC_ptr _4314, CLC_env env)
{
  CLC_ptr send_clo_4315; CLC_ptr send_clo_4318; CLC_ptr tmp_4317;
  CLC_ptr tmp_4319; CLC_ptr true_c2_4316;
  INSTR_send(&send_clo_4315, env[1]);
  INSTR_struct(&true_c2_4316, 2, 0);
  INSTR_call(&tmp_4317, send_clo_4315, true_c2_4316);
  INSTR_send(&send_clo_4318, tmp_4317);
  INSTR_call(&tmp_4319, send_clo_4318, _4314); return tmp_4319;
}

CLC_ptr printline_4322(CLC_ptr _4312, CLC_env env)
{
  CLC_ptr clo_4321;
  INSTR_clo(&clo_4321, &_4320, 17, 0, _4312, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_4321;
}

CLC_ptr close_out_4330(CLC_ptr _4325, CLC_env env)
{
  CLC_ptr false_c3_4328; CLC_ptr send_clo_4327; CLC_ptr tmp_4329;
  CLC_ptr unit_struct_4326;
  INSTR_send(&send_clo_4327, _4325);
  INSTR_struct(&false_c3_4328, 3, 0);
  INSTR_call(&tmp_4329, send_clo_4327, false_c3_4328);
  INSTR_struct(&unit_struct_4326, 1, 0); return unit_struct_4326;
}

CLC_ptr _4341(CLC_ptr _4335, CLC_env env)
{
  CLC_ptr send_clo_4336; CLC_ptr send_clo_4339; CLC_ptr tmp_4338;
  CLC_ptr tmp_4340; CLC_ptr true_c2_4337;
  INSTR_send(&send_clo_4336, env[1]);
  INSTR_struct(&true_c2_4337, 2, 0);
  INSTR_call(&tmp_4338, send_clo_4336, true_c2_4337);
  INSTR_send(&send_clo_4339, tmp_4338);
  INSTR_call(&tmp_4340, send_clo_4339, _4335); return tmp_4340;
}

CLC_ptr printerr_4343(CLC_ptr _4333, CLC_env env)
{
  CLC_ptr clo_4342;
  INSTR_clo(&clo_4342, &_4341, 19, 0, _4333, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16]);
  return clo_4342;
}

CLC_ptr close_err_4351(CLC_ptr _4346, CLC_env env)
{
  CLC_ptr false_c3_4349; CLC_ptr send_clo_4348; CLC_ptr tmp_4350;
  CLC_ptr unit_struct_4347;
  INSTR_send(&send_clo_4348, _4346);
  INSTR_struct(&false_c3_4349, 3, 0);
  INSTR_call(&tmp_4350, send_clo_4348, false_c3_4349);
  INSTR_struct(&unit_struct_4347, 1, 0); return unit_struct_4347;
}

CLC_ptr _4367(CLC_ptr _4365, CLC_env env)
{
  CLC_ptr case_4366;
  switch(((CLC_node)_4365)->tag){
    case 1: INSTR_mov(&case_4366, env[27]);
            break;}
  return case_4366;
}

CLC_ptr _4371(CLC_ptr _4362, CLC_env env)
{
  CLC_ptr case_4363; CLC_ptr clo_4368; CLC_ptr tmp_4369; CLC_ptr tmp_4370;
  switch(((CLC_node)_4362)->tag){
    case 1:
      INSTR_clo(&clo_4368, &_4367, 28, 0, _4362, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25]);
      INSTR_call(&tmp_4369, env[12], env[4]);
      INSTR_call(&tmp_4370, clo_4368, tmp_4369);
      INSTR_mov(&case_4363, tmp_4370);
      break;}
  return case_4363;
}

CLC_ptr _4375(CLC_ptr _4354, CLC_env env)
{
  CLC_ptr _4357; CLC_ptr case_4355; CLC_ptr clo_4372; CLC_ptr stdout_4358;
  CLC_ptr tmp_4359; CLC_ptr tmp_4360; CLC_ptr tmp_4373; CLC_ptr tmp_4374;
  CLC_ptr x_4356;
  switch(((CLC_node)_4354)->tag){
    case 13:
      INSTR_mov(&x_4356, ((CLC_node)_4354)->data[0]);
      INSTR_mov(&_4357, ((CLC_node)_4354)->data[1]);
      INSTR_call(&tmp_4359, env[6], env[1]);
      INSTR_call(&tmp_4360, tmp_4359, x_4356);
      INSTR_mov(&stdout_4358, tmp_4360);
      INSTR_clo(&clo_4372, &_4371, 26, 0, stdout_4358, _4354, x_4356, _4357, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20]);
      INSTR_call(&tmp_4373, env[5], stdout_4358);
      INSTR_call(&tmp_4374, clo_4372, tmp_4373);
      INSTR_mov(&case_4355, tmp_4374);
      break;}
  return case_4355;
}

int main()
{
  CLC_ptr _135; CLC_ptr addn_3; CLC_ptr addn_4217; CLC_ptr cat_67;
  CLC_ptr cat_4255; CLC_ptr clo_4376; CLC_ptr close_err_130;
  CLC_ptr close_err_4352; CLC_ptr close_in_114; CLC_ptr close_in_4310;
  CLC_ptr close_out_122; CLC_ptr close_out_4331; CLC_ptr lt_84;
  CLC_ptr lt_4273; CLC_ptr printerr_125; CLC_ptr printerr_4344;
  CLC_ptr printline_117; CLC_ptr printline_4323; CLC_ptr readline_109;
  CLC_ptr readline_4302; CLC_ptr stderr_rec_102; CLC_ptr stderr_rec_4288;
  CLC_ptr stderr_t_108; CLC_ptr stdin_133; CLC_ptr stdin_rec_94;
  CLC_ptr stdin_rec_4278; CLC_ptr stdin_t_106; CLC_ptr stdout_134;
  CLC_ptr stdout_rec_98; CLC_ptr stdout_rec_4283; CLC_ptr stdout_t_107;
  CLC_ptr strlen_74; CLC_ptr strlen_4265; CLC_ptr subn_9; CLC_ptr subn_4237;
  CLC_ptr tmp_4290; CLC_ptr tmp_4292; CLC_ptr tmp_4294; CLC_ptr tmp_4377;
  CLC_ptr tmp_4378; CLC_ptr tt_c1_4289; CLC_ptr tt_c1_4291;
  CLC_ptr tt_c1_4293;
  INSTR_clo(&addn_4217, &addn_4216, 2, 0, 0);
  INSTR_mov(&addn_3, addn_4217);
  INSTR_clo(&subn_4237, &subn_4236, 3, 0, addn_3, 0);
  INSTR_mov(&subn_9, subn_4237);
  INSTR_clo(&cat_4255, &cat_4254, 4, 0, subn_9, addn_3, 0);
  INSTR_mov(&cat_67, cat_4255);
  INSTR_clo(&strlen_4265, &strlen_4264, 5, 0, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&strlen_74, strlen_4265);
  INSTR_clo(&lt_4273, &lt_4272, 6, 0, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&lt_84, lt_4273);
  INSTR_clo(&stdin_rec_4278, &stdin_rec_4277, 7, 0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdin_rec_94, stdin_rec_4278);
  INSTR_clo(&stdout_rec_4283, &stdout_rec_4282, 8, 0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdout_rec_98, stdout_rec_4283);
  INSTR_clo(&stderr_rec_4288, &stderr_rec_4287, 9, 0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stderr_rec_102, stderr_rec_4288);
  INSTR_struct(&tt_c1_4289, 1, 0);
  INSTR_call(&tmp_4290, stdin_rec_94, tt_c1_4289);
  INSTR_mov(&stdin_t_106, tmp_4290);
  INSTR_struct(&tt_c1_4291, 1, 0);
  INSTR_call(&tmp_4292, stdout_rec_98, tt_c1_4291);
  INSTR_mov(&stdout_t_107, tmp_4292);
  INSTR_struct(&tt_c1_4293, 1, 0);
  INSTR_call(&tmp_4294, stderr_rec_102, tt_c1_4293);
  INSTR_mov(&stderr_t_108, tmp_4294);
  INSTR_clo(&readline_4302, &readline_4301, 13, 0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&readline_109, readline_4302);
  INSTR_clo(&close_in_4310, &close_in_4309, 14, 0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_in_114, close_in_4310);
  INSTR_clo(&printline_4323, &printline_4322, 15, 0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printline_117, printline_4323);
  INSTR_clo(&close_out_4331, &close_out_4330, 16, 0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_out_122, close_out_4331);
  INSTR_clo(&printerr_4344, &printerr_4343, 17, 0, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printerr_125, printerr_4344);
  INSTR_clo(&close_err_4352, &close_err_4351, 18, 0, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_err_130, close_err_4352);
  INSTR_trg(&stdin_133, &PROC_stdin);
  INSTR_trg(&stdout_134, &PROC_stdout);
  INSTR_clo(&clo_4376, &_4375, 21, 0, stdout_134, stdin_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_call(&tmp_4377, readline_109, stdin_133);
  INSTR_call(&tmp_4378, clo_4376, tmp_4377);
  INSTR_mov(&_135, tmp_4378); return 0;
}
