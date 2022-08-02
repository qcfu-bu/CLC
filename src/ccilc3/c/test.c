#include "runtime.h"

CLC_ptr _200;
CLC_ptr addn_3;
CLC_ptr addn_25949;
CLC_ptr bind_158;
CLC_ptr bind_26153;
CLC_ptr cat_67;
CLC_ptr cat_25987;
CLC_ptr clo_26412;
CLC_ptr close_err_130;
CLC_ptr close_err_26084;
CLC_ptr close_in_114;
CLC_ptr close_in_26042;
CLC_ptr close_out_122;
CLC_ptr close_out_26063;
CLC_ptr div2_exn_p_169;
CLC_ptr div2_exn_p_26176;
CLC_ptr exn_143;
CLC_ptr exn_26092;
CLC_ptr exn_p_133;
CLC_ptr exn_p_26088;
CLC_ptr lt_84;
CLC_ptr lt_26005;
CLC_ptr out_199;
CLC_ptr printerr_125;
CLC_ptr printerr_26076;
CLC_ptr printline_117;
CLC_ptr printline_26055;
CLC_ptr readline_109;
CLC_ptr readline_26034;
CLC_ptr ret_147;
CLC_ptr ret_26105;
CLC_ptr stderr_rec_102;
CLC_ptr stderr_rec_26020;
CLC_ptr stderr_t_108;
CLC_ptr stdin_rec_94;
CLC_ptr stdin_rec_26010;
CLC_ptr stdin_t_106;
CLC_ptr stdout_rec_98;
CLC_ptr stdout_rec_26015;
CLC_ptr stdout_t_107;
CLC_ptr string_of_nat_196;
CLC_ptr string_of_nat_26380;
CLC_ptr strlen_74;
CLC_ptr strlen_25997;
CLC_ptr subn_9;
CLC_ptr subn_25969;
CLC_ptr succ_c5_26416;
CLC_ptr succ_c5_26417;
CLC_ptr succ_c5_26418;
CLC_ptr succ_c5_26419;
CLC_ptr succ_c5_26420;
CLC_ptr succ_c5_26421;
CLC_ptr succ_c5_26422;
CLC_ptr succ_c5_26423;
CLC_ptr succ_c5_26424;
CLC_ptr succ_c5_26425;
CLC_ptr succ_c5_26426;
CLC_ptr succ_c5_26427;
CLC_ptr succ_c5_26428;
CLC_ptr succ_c5_26429;
CLC_ptr throw_153;
CLC_ptr throw_26125;
CLC_ptr tmp_26022;
CLC_ptr tmp_26024;
CLC_ptr tmp_26026;
CLC_ptr tmp_26413;
CLC_ptr tmp_26414;
CLC_ptr tmp_26430;
CLC_ptr tmp_26431;
CLC_ptr tmp_26433;
CLC_ptr tmp_26434;
CLC_ptr try_exn_174;
CLC_ptr try_exn_26256;
CLC_ptr tt_c1_26021;
CLC_ptr tt_c1_26023;
CLC_ptr tt_c1_26025;
CLC_ptr zero_c4_26415;
CLC_ptr zero_c4_26432;

CLC_ptr _25938(CLC_ptr _25937, CLC_env env)
{
    return _25937;
}

CLC_ptr _25946(CLC_ptr _25942, CLC_env env)
{
  CLC_ptr succ_c5_25945; CLC_ptr tmp_25943; CLC_ptr tmp_25944;
  INSTR_call(&tmp_25943, env[3], env[2]);
  INSTR_call(&tmp_25944, tmp_25943, _25942);
  INSTR_struct(&succ_c5_25945, 5, 1, tmp_25944); return succ_c5_25945;
}

CLC_ptr addn_25948(CLC_ptr _25934, CLC_env env)
{
  CLC_ptr _25940; CLC_ptr case_25935; CLC_ptr clo_25939; CLC_ptr clo_25947;
  switch(((CLC_node)_25934)->tag){
    case 4:
      INSTR_clo(&clo_25939, &_25938, 4, 0, _25934, env[0], env[1]);
      INSTR_mov(&case_25935, clo_25939);
      break;
    case 5:
      INSTR_mov(&_25940, ((CLC_node)_25934)->data[0]);
      INSTR_clo(&clo_25947, &_25946, 5, 0, _25934, _25940, env[0], env[1]);
      INSTR_mov(&case_25935, clo_25947);
      break;}
  return case_25935;
}

CLC_ptr _25956(CLC_ptr _25954, CLC_env env)
{
  CLC_ptr zero_c4_25955; INSTR_struct(&zero_c4_25955, 4, 0);
  return zero_c4_25955;
}

CLC_ptr _25966(CLC_ptr _25960, CLC_env env)
{
  CLC_ptr _25963; CLC_ptr case_25961; CLC_ptr succ_c5_25962;
  CLC_ptr tmp_25964; CLC_ptr tmp_25965;
  switch(((CLC_node)_25960)->tag){
    case 4:
      INSTR_struct(&succ_c5_25962, 5, 1, env[2]);
      INSTR_mov(&case_25961, succ_c5_25962);
      break;
    case 5:
      INSTR_mov(&_25963, ((CLC_node)_25960)->data[0]);
      INSTR_call(&tmp_25964, env[3], env[2]);
      INSTR_call(&tmp_25965, tmp_25964, _25963);
      INSTR_mov(&case_25961, tmp_25965);
      break;}
  return case_25961;
}

CLC_ptr subn_25968(CLC_ptr _25951, CLC_env env)
{
  CLC_ptr _25958; CLC_ptr case_25952; CLC_ptr clo_25957; CLC_ptr clo_25967;
  switch(((CLC_node)_25951)->tag){
    case 4:
      INSTR_clo(&clo_25957, &_25956, 5, 0, _25951, env[0], env[1], env[2]);
      INSTR_mov(&case_25952, clo_25957);
      break;
    case 5:
      INSTR_mov(&_25958, ((CLC_node)_25951)->data[0]);
      INSTR_clo(&clo_25967, &_25966, 6, 0, _25951, _25958, env[0], env[1], env[2]);
      INSTR_mov(&case_25952, clo_25967);
      break;}
  return case_25952;
}

CLC_ptr _25975(CLC_ptr _25974, CLC_env env)
{
    return _25974;
}

CLC_ptr _25984(CLC_ptr _25980, CLC_env env)
{
  CLC_ptr String_c18_25983; CLC_ptr tmp_25981; CLC_ptr tmp_25982;
  INSTR_call(&tmp_25981, env[4], env[3]);
  INSTR_call(&tmp_25982, tmp_25981, _25980);
  INSTR_struct(&String_c18_25983, 18, 2, env[2], tmp_25982);
  return String_c18_25983;
}

CLC_ptr cat_25986(CLC_ptr _25971, CLC_env env)
{
  CLC_ptr _25977; CLC_ptr _25978; CLC_ptr case_25972; CLC_ptr clo_25976;
  CLC_ptr clo_25985;
  switch(((CLC_node)_25971)->tag){
    case 17:
      INSTR_clo(&clo_25976, &_25975, 6, 0, _25971, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_25972, clo_25976);
      break;
    case 18:
      INSTR_mov(&_25977, ((CLC_node)_25971)->data[0]);
      INSTR_mov(&_25978, ((CLC_node)_25971)->data[1]);
      INSTR_clo(&clo_25985, &_25984, 8, 0, _25971, _25977, _25978, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_25972, clo_25985);
      break;}
  return case_25972;
}

CLC_ptr strlen_25996(CLC_ptr _25989, CLC_env env)
{
  CLC_ptr _25992; CLC_ptr _25993; CLC_ptr case_25990; CLC_ptr succ_c5_25995;
  CLC_ptr tmp_25994; CLC_ptr zero_c4_25991;
  switch(((CLC_node)_25989)->tag){
    case 17:
      INSTR_struct(&zero_c4_25991, 4, 0);
      INSTR_mov(&case_25990, zero_c4_25991);
      break;
    case 18:
      INSTR_mov(&_25992, ((CLC_node)_25989)->data[0]);
      INSTR_mov(&_25993, ((CLC_node)_25989)->data[1]);
      INSTR_call(&tmp_25994, env[0], _25993);
      INSTR_struct(&succ_c5_25995, 5, 1, tmp_25994);
      INSTR_mov(&case_25990, succ_c5_25995);
      break;}
  return case_25990;
}

CLC_ptr _26002(CLC_ptr _26001, CLC_env env)
{
    return 0;
}

CLC_ptr lt_26004(CLC_ptr _25999, CLC_env env)
{
  CLC_ptr clo_26003;
  INSTR_clo(&clo_26003, &_26002, 8, 0, _25999, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_26003;
}

CLC_ptr stdin_rec_26009(CLC_ptr _26007, CLC_env env)
{
  CLC_ptr case_26008;
  switch(((CLC_node)_26007)->tag){
    case 1: INSTR_mov(&case_26008, 0);
            break;}
  return case_26008;
}

CLC_ptr stdout_rec_26014(CLC_ptr _26012, CLC_env env)
{
  CLC_ptr case_26013;
  switch(((CLC_node)_26012)->tag){
    case 1: INSTR_mov(&case_26013, 0);
            break;}
  return case_26013;
}

CLC_ptr stderr_rec_26019(CLC_ptr _26017, CLC_env env)
{
  CLC_ptr case_26018;
  switch(((CLC_node)_26017)->tag){
    case 1: INSTR_mov(&case_26018, 0);
            break;}
  return case_26018;
}

CLC_ptr readline_26033(CLC_ptr _26028, CLC_env env)
{
  CLC_ptr recv_struct_26032; CLC_ptr send_clo_26029; CLC_ptr tmp_26031;
  CLC_ptr true_c2_26030;
  INSTR_send(&send_clo_26029, _26028);
  INSTR_struct(&true_c2_26030, 2, 0);
  INSTR_call(&tmp_26031, send_clo_26029, true_c2_26030);
  INSTR_recv(&recv_struct_26032, tmp_26031, 13); return recv_struct_26032;
}

CLC_ptr close_in_26041(CLC_ptr _26036, CLC_env env)
{
  CLC_ptr false_c3_26039; CLC_ptr send_clo_26038; CLC_ptr tmp_26040;
  CLC_ptr unit_struct_26037;
  INSTR_send(&send_clo_26038, _26036);
  INSTR_struct(&false_c3_26039, 3, 0);
  INSTR_call(&tmp_26040, send_clo_26038, false_c3_26039);
  INSTR_struct(&unit_struct_26037, 1, 0); return unit_struct_26037;
}

CLC_ptr _26052(CLC_ptr _26046, CLC_env env)
{
  CLC_ptr send_clo_26047; CLC_ptr send_clo_26050; CLC_ptr tmp_26049;
  CLC_ptr tmp_26051; CLC_ptr true_c2_26048;
  INSTR_send(&send_clo_26047, env[1]);
  INSTR_struct(&true_c2_26048, 2, 0);
  INSTR_call(&tmp_26049, send_clo_26047, true_c2_26048);
  INSTR_send(&send_clo_26050, tmp_26049);
  INSTR_call(&tmp_26051, send_clo_26050, _26046); return tmp_26051;
}

CLC_ptr printline_26054(CLC_ptr _26044, CLC_env env)
{
  CLC_ptr clo_26053;
  INSTR_clo(&clo_26053, &_26052, 17, 0, _26044, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_26053;
}

CLC_ptr close_out_26062(CLC_ptr _26057, CLC_env env)
{
  CLC_ptr false_c3_26060; CLC_ptr send_clo_26059; CLC_ptr tmp_26061;
  CLC_ptr unit_struct_26058;
  INSTR_send(&send_clo_26059, _26057);
  INSTR_struct(&false_c3_26060, 3, 0);
  INSTR_call(&tmp_26061, send_clo_26059, false_c3_26060);
  INSTR_struct(&unit_struct_26058, 1, 0); return unit_struct_26058;
}

CLC_ptr _26073(CLC_ptr _26067, CLC_env env)
{
  CLC_ptr send_clo_26068; CLC_ptr send_clo_26071; CLC_ptr tmp_26070;
  CLC_ptr tmp_26072; CLC_ptr true_c2_26069;
  INSTR_send(&send_clo_26068, env[1]);
  INSTR_struct(&true_c2_26069, 2, 0);
  INSTR_call(&tmp_26070, send_clo_26068, true_c2_26069);
  INSTR_send(&send_clo_26071, tmp_26070);
  INSTR_call(&tmp_26072, send_clo_26071, _26067); return tmp_26072;
}

CLC_ptr printerr_26075(CLC_ptr _26065, CLC_env env)
{
  CLC_ptr clo_26074;
  INSTR_clo(&clo_26074, &_26073, 19, 0, _26065, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16]);
  return clo_26074;
}

CLC_ptr close_err_26083(CLC_ptr _26078, CLC_env env)
{
  CLC_ptr false_c3_26081; CLC_ptr send_clo_26080; CLC_ptr tmp_26082;
  CLC_ptr unit_struct_26079;
  INSTR_send(&send_clo_26080, _26078);
  INSTR_struct(&false_c3_26081, 3, 0);
  INSTR_call(&tmp_26082, send_clo_26080, false_c3_26081);
  INSTR_struct(&unit_struct_26079, 1, 0); return unit_struct_26079;
}

CLC_ptr exn_p_26087(CLC_ptr _26086, CLC_env env)
{
    return 0;
}

CLC_ptr exn_26091(CLC_ptr _26090, CLC_env env)
{
    return 0;
}

CLC_ptr _26100(CLC_ptr _26098, CLC_env env)
{
  CLC_ptr Ok_c23_26099; INSTR_struct(&Ok_c23_26099, 23, 2, env[1], _26098);
  return Ok_c23_26099;
}

CLC_ptr _26102(CLC_ptr _26096, CLC_env env)
{
  CLC_ptr clo_26101;
  INSTR_clo(&clo_26101, &_26100, 25, 0, _26096, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22]);
  return clo_26101;
}

CLC_ptr ret_26104(CLC_ptr A_26094, CLC_env env)
{
  CLC_ptr clo_26103;
  INSTR_clo(&clo_26103, &_26102, 23, 0, A_26094, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20]);
  return clo_26103;
}

CLC_ptr _26118(CLC_ptr _26115, CLC_env env)
{
  CLC_ptr Error_c22_26117; CLC_ptr case_26116;
  switch(((CLC_node)_26115)->tag){
    case 1:
      INSTR_struct(&Error_c22_26117, 22, 0);
      INSTR_mov(&case_26116, Error_c22_26117);
      break;}
  return case_26116;
}

CLC_ptr _26122(CLC_ptr _26109, CLC_env env)
{
  CLC_ptr ch_26110; CLC_ptr clo_26119; CLC_ptr false_c3_26112;
  CLC_ptr send_clo_26111; CLC_ptr tmp_26113; CLC_ptr tmp_26121;
  CLC_ptr unit_struct_26120;
  INSTR_send(&send_clo_26111, _26109);
  INSTR_struct(&false_c3_26112, 3, 0);
  INSTR_call(&tmp_26113, send_clo_26111, false_c3_26112);
  INSTR_mov(&ch_26110, tmp_26113);
  INSTR_clo(&clo_26119, &_26118, 27, 0, ch_26110, _26109, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23]);
  INSTR_struct(&unit_struct_26120, 1, 0);
  INSTR_call(&tmp_26121, clo_26119, unit_struct_26120); return tmp_26121;
}

CLC_ptr throw_26124(CLC_ptr A_26107, CLC_env env)
{
  CLC_ptr clo_26123;
  INSTR_clo(&clo_26123, &_26122, 24, 0, A_26107, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21]);
  return clo_26123;
}

CLC_ptr _26142(CLC_ptr _26135, CLC_env env)
{
  CLC_ptr _26138; CLC_ptr _26139; CLC_ptr Error_c22_26137;
  CLC_ptr case_26136; CLC_ptr tmp_26140; CLC_ptr tmp_26141;
  switch(((CLC_node)_26135)->tag){
    case 22:
      INSTR_struct(&Error_c22_26137, 22, 0);
      INSTR_mov(&case_26136, Error_c22_26137);
      break;
    case 23:
      INSTR_mov(&_26138, ((CLC_node)_26135)->data[0]);
      INSTR_mov(&_26139, ((CLC_node)_26135)->data[1]);
      INSTR_call(&tmp_26140, env[3], _26138);
      INSTR_call(&tmp_26141, tmp_26140, _26139);
      INSTR_mov(&case_26136, tmp_26141);
      break;}
  return case_26136;
}

CLC_ptr _26146(CLC_ptr _26133, CLC_env env)
{
  CLC_ptr clo_26143; CLC_ptr tmp_26144; CLC_ptr tmp_26145;
  INSTR_clo(&clo_26143, &_26142, 31, 0, _26133, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28]);
  INSTR_call(&tmp_26144, env[3], _26133);
  INSTR_call(&tmp_26145, clo_26143, tmp_26144); return tmp_26145;
}

CLC_ptr _26148(CLC_ptr _26131, CLC_env env)
{
  CLC_ptr clo_26147;
  INSTR_clo(&clo_26147, &_26146, 29, 0, _26131, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26]);
  return clo_26147;
}

CLC_ptr _26150(CLC_ptr _26129, CLC_env env)
{
  CLC_ptr clo_26149;
  INSTR_clo(&clo_26149, &_26148, 27, 0, _26129, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24]);
  return clo_26149;
}

CLC_ptr bind_26152(CLC_ptr A_26127, CLC_env env)
{
  CLC_ptr clo_26151;
  INSTR_clo(&clo_26151, &_26150, 25, 0, A_26127, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22]);
  return clo_26151;
}

CLC_ptr _26172(CLC_ptr _26168, CLC_env env)
{
  CLC_ptr succ_c5_26170; CLC_ptr tmp_26169; CLC_ptr tmp_26171;
  INSTR_call(&tmp_26169, env[7], 0);
  INSTR_struct(&succ_c5_26170, 5, 1, _26168);
  INSTR_call(&tmp_26171, tmp_26169, succ_c5_26170); return tmp_26171;
}

CLC_ptr div2_exn_p_26175(CLC_ptr _26155, CLC_env env)
{
  CLC_ptr _26160; CLC_ptr _26163; CLC_ptr _26173; CLC_ptr case_26156;
  CLC_ptr case_26161; CLC_ptr tmp_26157; CLC_ptr tmp_26159;
  CLC_ptr tmp_26162; CLC_ptr tmp_26164; CLC_ptr tmp_26165; CLC_ptr tmp_26166;
  CLC_ptr tmp_26174; CLC_ptr zero_c4_26158;
  switch(((CLC_node)_26155)->tag){
    case 4:
      INSTR_call(&tmp_26157, env[3], 0);
      INSTR_struct(&zero_c4_26158, 4, 0);
      INSTR_call(&tmp_26159, tmp_26157, zero_c4_26158);
      INSTR_mov(&case_26156, tmp_26159);
      break;
    case 5:
      INSTR_mov(&_26160, ((CLC_node)_26155)->data[0]);
      switch(((CLC_node)_26160)->tag){
        case 4:
          INSTR_call(&tmp_26162, env[2], 0);
          INSTR_mov(&case_26161, tmp_26162);
          break;
        case 5:
          INSTR_mov(&_26163, ((CLC_node)_26160)->data[0]);
          INSTR_call(&tmp_26164, env[1], 0);
          INSTR_call(&tmp_26165, env[0], _26163);
          INSTR_call(&tmp_26166, tmp_26164, tmp_26165);
          INSTR_clo(&_26173, &_26172, 28, 0, _26155, _26160, _26163, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23]);
          INSTR_call(&tmp_26174, tmp_26166, _26173);
          INSTR_mov(&case_26161, tmp_26174);
          break;}
      INSTR_mov(&case_26156, case_26161);
      break;}
  return case_26156;
}

CLC_ptr _26205(CLC_ptr _26202, CLC_env env)
{
  CLC_ptr case_26203; CLC_ptr sig_intro_c13_26204;
  switch(((CLC_node)_26202)->tag){
    case 1:
      INSTR_struct(&sig_intro_c13_26204, 13, 2, env[2], env[11]);
      INSTR_mov(&case_26203, sig_intro_c13_26204);
      break;}
  return case_26203;
}

CLC_ptr _26209(CLC_ptr _26197, CLC_env env)
{
  CLC_ptr _26200; CLC_ptr case_26198; CLC_ptr clo_26206; CLC_ptr tmp_26208;
  CLC_ptr unit_struct_26207; CLC_ptr x_26199;
  switch(((CLC_node)_26197)->tag){
    case 13:
      INSTR_mov(&x_26199, ((CLC_node)_26197)->data[0]);
      INSTR_mov(&_26200, ((CLC_node)_26197)->data[1]);
      INSTR_clo(&clo_26206, &_26205, 45, 0, _26197, x_26199, _26200, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30], env[31], env[32], env[33], env[34], env[35], env[36], env[37], env[38], env[39], env[40]);
      INSTR_close(&unit_struct_26207, _26200, 1);
      INSTR_call(&tmp_26208, clo_26206, unit_struct_26207);
      INSTR_mov(&case_26198, tmp_26208);
      break;}
  return case_26198;
}

CLC_ptr _26217(CLC_ptr _26214, CLC_env env)
{
  CLC_ptr case_26215; CLC_ptr sig_intro_c13_26216;
  switch(((CLC_node)_26214)->tag){
    case 1:
      INSTR_struct(&sig_intro_c13_26216, 13, 2, env[9], env[7]);
      INSTR_mov(&case_26215, sig_intro_c13_26216);
      break;}
  return case_26215;
}

CLC_ptr _26221(CLC_ptr _26191, CLC_env env)
{
  CLC_ptr _26194; CLC_ptr case_26192; CLC_ptr case_26195; CLC_ptr clo_26210;
  CLC_ptr clo_26218; CLC_ptr recv_struct_26211; CLC_ptr tmp_26212;
  CLC_ptr tmp_26220; CLC_ptr unit_struct_26219; CLC_ptr x_26193;
  switch(((CLC_node)_26191)->tag){
    case 13:
      INSTR_mov(&x_26193, ((CLC_node)_26191)->data[0]);
      INSTR_mov(&_26194, ((CLC_node)_26191)->data[1]);
      switch(((CLC_node)x_26193)->tag){
        case 2:
          INSTR_clo(&clo_26210, &_26209, 41, 0, _26191, x_26193, _26194, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30], env[31], env[32], env[33], env[34], env[35], env[36]);
          INSTR_recv(&recv_struct_26211, _26194, 13);
          INSTR_call(&tmp_26212, clo_26210, recv_struct_26211);
          INSTR_mov(&case_26195, tmp_26212);
          break;
        case 3:
          INSTR_clo(&clo_26218, &_26217, 41, 0, _26191, x_26193, _26194, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30], env[31], env[32], env[33], env[34], env[35], env[36]);
          INSTR_close(&unit_struct_26219, _26194, 1);
          INSTR_call(&tmp_26220, clo_26218, unit_struct_26219);
          INSTR_mov(&case_26195, tmp_26220);
          break;}
      INSTR_mov(&case_26192, case_26195);
      break;}
  return case_26192;
}

CLC_ptr _26225(CLC_ptr _26186, CLC_env env)
{
  CLC_ptr _26188; CLC_ptr _26189; CLC_ptr case_26187; CLC_ptr clo_26222;
  CLC_ptr recv_struct_26223; CLC_ptr tmp_26224;
  switch(((CLC_node)_26186)->tag){
    case 14:
      INSTR_mov(&_26188, ((CLC_node)_26186)->data[0]);
      INSTR_mov(&_26189, ((CLC_node)_26186)->data[1]);
      INSTR_clo(&clo_26222, &_26221, 37, 0, _26186, _26188, _26189, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30], env[31], env[32]);
      INSTR_recv(&recv_struct_26223, _26188, 13);
      INSTR_call(&tmp_26224, clo_26222, recv_struct_26223);
      INSTR_mov(&case_26187, tmp_26224);
      break;}
  return case_26187;
}

CLC_ptr _26242(CLC_ptr _26229, CLC_env env)
{
  CLC_ptr _26232; CLC_ptr _26233; CLC_ptr case_26230; CLC_ptr ch_26234;
  CLC_ptr ch_26238; CLC_ptr send_clo_26235; CLC_ptr send_clo_26239;
  CLC_ptr tmp_26237; CLC_ptr tmp_26240; CLC_ptr true_c2_26236;
  CLC_ptr tt_c1_26231; CLC_ptr unit_struct_26241;
  switch(((CLC_node)_26229)->tag){
    case 22:
      INSTR_struct(&tt_c1_26231, 1, 0);
      INSTR_mov(&case_26230, tt_c1_26231);
      break;
    case 23:
      INSTR_mov(&_26232, ((CLC_node)_26229)->data[0]);
      INSTR_mov(&_26233, ((CLC_node)_26229)->data[1]);
      INSTR_send(&send_clo_26235, _26233);
      INSTR_struct(&true_c2_26236, 2, 0);
      INSTR_call(&tmp_26237, send_clo_26235, true_c2_26236);
      INSTR_mov(&ch_26234, tmp_26237);
      INSTR_send(&send_clo_26239, ch_26234);
      INSTR_call(&tmp_26240, send_clo_26239, _26232);
      INSTR_mov(&ch_26238, tmp_26240);
      INSTR_struct(&unit_struct_26241, 1, 0);
      INSTR_mov(&case_26230, unit_struct_26241);
      break;}
  return case_26230;
}

CLC_ptr fork_proc_26247(CLC_env env)
{
  CLC_ptr clo_26243; CLC_ptr tmp_26244; CLC_ptr tmp_26245;
  INSTR_clo(&clo_26243, &_26242, 34, 0, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30], env[31], env[32]);
  INSTR_call(&tmp_26244, env[3], env[0]);
  INSTR_call(&tmp_26245, clo_26243, tmp_26244); return tmp_26245;
}

CLC_ptr _26249(CLC_ptr _26184, CLC_env env)
{
  CLC_ptr clo_26226; CLC_ptr fork_res_26246; CLC_ptr tmp_26248;
  INSTR_clo(&clo_26226, &_26225, 33, 0, _26184, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30]);
  INSTR_open(&fork_res_26246, &fork_proc_26247, env[3], 14, 32, _26184, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30]);
  INSTR_call(&tmp_26248, clo_26226, fork_res_26246); return tmp_26248;
}

CLC_ptr _26251(CLC_ptr _26182, CLC_env env)
{
  CLC_ptr clo_26250;
  INSTR_clo(&clo_26250, &_26249, 31, 0, _26182, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27], env[28]);
  return clo_26250;
}

CLC_ptr _26253(CLC_ptr _26180, CLC_env env)
{
  CLC_ptr clo_26252;
  INSTR_clo(&clo_26252, &_26251, 29, 0, _26180, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26]);
  return clo_26252;
}

CLC_ptr try_exn_26255(CLC_ptr A_26178, CLC_env env)
{
  CLC_ptr clo_26254;
  INSTR_clo(&clo_26254, &_26253, 27, 0, A_26178, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24]);
  return clo_26254;
}

CLC_ptr string_of_nat_26379(CLC_ptr _26258, CLC_env env)
{
  CLC_ptr _26301; CLC_ptr Ascii_c16_26268; CLC_ptr Ascii_c16_26277;
  CLC_ptr Ascii_c16_26286; CLC_ptr Ascii_c16_26295; CLC_ptr Ascii_c16_26310;
  CLC_ptr Ascii_c16_26319; CLC_ptr Ascii_c16_26328; CLC_ptr Ascii_c16_26337;
  CLC_ptr Ascii_c16_26346; CLC_ptr Ascii_c16_26355; CLC_ptr Ascii_c16_26375;
  CLC_ptr EmptyString_c17_26296; CLC_ptr EmptyString_c17_26356;
  CLC_ptr EmptyString_c17_26376; CLC_ptr String_c18_26297;
  CLC_ptr String_c18_26298; CLC_ptr String_c18_26299;
  CLC_ptr String_c18_26300; CLC_ptr String_c18_26357;
  CLC_ptr String_c18_26358; CLC_ptr String_c18_26359;
  CLC_ptr String_c18_26360; CLC_ptr String_c18_26361;
  CLC_ptr String_c18_26362; CLC_ptr String_c18_26377; CLC_ptr case_26259;
  CLC_ptr false_c3_26260; CLC_ptr false_c3_26265; CLC_ptr false_c3_26267;
  CLC_ptr false_c3_26269; CLC_ptr false_c3_26272; CLC_ptr false_c3_26273;
  CLC_ptr false_c3_26275; CLC_ptr false_c3_26278; CLC_ptr false_c3_26282;
  CLC_ptr false_c3_26283; CLC_ptr false_c3_26285; CLC_ptr false_c3_26287;
  CLC_ptr false_c3_26290; CLC_ptr false_c3_26302; CLC_ptr false_c3_26306;
  CLC_ptr false_c3_26307; CLC_ptr false_c3_26311; CLC_ptr false_c3_26315;
  CLC_ptr false_c3_26317; CLC_ptr false_c3_26320; CLC_ptr false_c3_26323;
  CLC_ptr false_c3_26324; CLC_ptr false_c3_26325; CLC_ptr false_c3_26329;
  CLC_ptr false_c3_26332; CLC_ptr false_c3_26333; CLC_ptr false_c3_26334;
  CLC_ptr false_c3_26338; CLC_ptr false_c3_26339; CLC_ptr false_c3_26341;
  CLC_ptr false_c3_26342; CLC_ptr false_c3_26343; CLC_ptr false_c3_26344;
  CLC_ptr false_c3_26345; CLC_ptr false_c3_26347; CLC_ptr false_c3_26348;
  CLC_ptr false_c3_26350; CLC_ptr false_c3_26352; CLC_ptr false_c3_26353;
  CLC_ptr false_c3_26354; CLC_ptr false_c3_26367; CLC_ptr false_c3_26368;
  CLC_ptr false_c3_26370; CLC_ptr false_c3_26372; CLC_ptr false_c3_26373;
  CLC_ptr tmp_26363; CLC_ptr tmp_26364; CLC_ptr tmp_26365; CLC_ptr tmp_26366;
  CLC_ptr tmp_26378; CLC_ptr true_c2_26261; CLC_ptr true_c2_26262;
  CLC_ptr true_c2_26263; CLC_ptr true_c2_26264; CLC_ptr true_c2_26266;
  CLC_ptr true_c2_26270; CLC_ptr true_c2_26271; CLC_ptr true_c2_26274;
  CLC_ptr true_c2_26276; CLC_ptr true_c2_26279; CLC_ptr true_c2_26280;
  CLC_ptr true_c2_26281; CLC_ptr true_c2_26284; CLC_ptr true_c2_26288;
  CLC_ptr true_c2_26289; CLC_ptr true_c2_26291; CLC_ptr true_c2_26292;
  CLC_ptr true_c2_26293; CLC_ptr true_c2_26294; CLC_ptr true_c2_26303;
  CLC_ptr true_c2_26304; CLC_ptr true_c2_26305; CLC_ptr true_c2_26308;
  CLC_ptr true_c2_26309; CLC_ptr true_c2_26312; CLC_ptr true_c2_26313;
  CLC_ptr true_c2_26314; CLC_ptr true_c2_26316; CLC_ptr true_c2_26318;
  CLC_ptr true_c2_26321; CLC_ptr true_c2_26322; CLC_ptr true_c2_26326;
  CLC_ptr true_c2_26327; CLC_ptr true_c2_26330; CLC_ptr true_c2_26331;
  CLC_ptr true_c2_26335; CLC_ptr true_c2_26336; CLC_ptr true_c2_26340;
  CLC_ptr true_c2_26349; CLC_ptr true_c2_26351; CLC_ptr true_c2_26369;
  CLC_ptr true_c2_26371; CLC_ptr true_c2_26374;
  switch(((CLC_node)_26258)->tag){
    case 4:
      INSTR_struct(&false_c3_26260, 3, 0);
      INSTR_struct(&true_c2_26261, 2, 0);
      INSTR_struct(&true_c2_26262, 2, 0);
      INSTR_struct(&true_c2_26263, 2, 0);
      INSTR_struct(&true_c2_26264, 2, 0);
      INSTR_struct(&false_c3_26265, 3, 0);
      INSTR_struct(&true_c2_26266, 2, 0);
      INSTR_struct(&false_c3_26267, 3, 0);
      INSTR_struct(&Ascii_c16_26268, 16, 8, false_c3_26260, true_c2_26261, true_c2_26262, true_c2_26263, true_c2_26264, false_c3_26265, true_c2_26266, false_c3_26267);
      INSTR_struct(&false_c3_26269, 3, 0);
      INSTR_struct(&true_c2_26270, 2, 0);
      INSTR_struct(&true_c2_26271, 2, 0);
      INSTR_struct(&false_c3_26272, 3, 0);
      INSTR_struct(&false_c3_26273, 3, 0);
      INSTR_struct(&true_c2_26274, 2, 0);
      INSTR_struct(&false_c3_26275, 3, 0);
      INSTR_struct(&true_c2_26276, 2, 0);
      INSTR_struct(&Ascii_c16_26277, 16, 8, false_c3_26269, true_c2_26270, true_c2_26271, false_c3_26272, false_c3_26273, true_c2_26274, false_c3_26275, true_c2_26276);
      INSTR_struct(&false_c3_26278, 3, 0);
      INSTR_struct(&true_c2_26279, 2, 0);
      INSTR_struct(&true_c2_26280, 2, 0);
      INSTR_struct(&true_c2_26281, 2, 0);
      INSTR_struct(&false_c3_26282, 3, 0);
      INSTR_struct(&false_c3_26283, 3, 0);
      INSTR_struct(&true_c2_26284, 2, 0);
      INSTR_struct(&false_c3_26285, 3, 0);
      INSTR_struct(&Ascii_c16_26286, 16, 8, false_c3_26278, true_c2_26279, true_c2_26280, true_c2_26281, false_c3_26282, false_c3_26283, true_c2_26284, false_c3_26285);
      INSTR_struct(&false_c3_26287, 3, 0);
      INSTR_struct(&true_c2_26288, 2, 0);
      INSTR_struct(&true_c2_26289, 2, 0);
      INSTR_struct(&false_c3_26290, 3, 0);
      INSTR_struct(&true_c2_26291, 2, 0);
      INSTR_struct(&true_c2_26292, 2, 0);
      INSTR_struct(&true_c2_26293, 2, 0);
      INSTR_struct(&true_c2_26294, 2, 0);
      INSTR_struct(&Ascii_c16_26295, 16, 8, false_c3_26287, true_c2_26288, true_c2_26289, false_c3_26290, true_c2_26291, true_c2_26292, true_c2_26293, true_c2_26294);
      INSTR_struct(&EmptyString_c17_26296, 17, 0);
      INSTR_struct(&String_c18_26297, 18, 2, Ascii_c16_26295, EmptyString_c17_26296);
      INSTR_struct(&String_c18_26298, 18, 2, Ascii_c16_26286, String_c18_26297);
      INSTR_struct(&String_c18_26299, 18, 2, Ascii_c16_26277, String_c18_26298);
      INSTR_struct(&String_c18_26300, 18, 2, Ascii_c16_26268, String_c18_26299);
      INSTR_mov(&case_26259, String_c18_26300);
      break;
    case 5:
      INSTR_mov(&_26301, ((CLC_node)_26258)->data[0]);
      INSTR_struct(&false_c3_26302, 3, 0);
      INSTR_struct(&true_c2_26303, 2, 0);
      INSTR_struct(&true_c2_26304, 2, 0);
      INSTR_struct(&true_c2_26305, 2, 0);
      INSTR_struct(&false_c3_26306, 3, 0);
      INSTR_struct(&false_c3_26307, 3, 0);
      INSTR_struct(&true_c2_26308, 2, 0);
      INSTR_struct(&true_c2_26309, 2, 0);
      INSTR_struct(&Ascii_c16_26310, 16, 8, false_c3_26302, true_c2_26303, true_c2_26304, true_c2_26305, false_c3_26306, false_c3_26307, true_c2_26308, true_c2_26309);
      INSTR_struct(&false_c3_26311, 3, 0);
      INSTR_struct(&true_c2_26312, 2, 0);
      INSTR_struct(&true_c2_26313, 2, 0);
      INSTR_struct(&true_c2_26314, 2, 0);
      INSTR_struct(&false_c3_26315, 3, 0);
      INSTR_struct(&true_c2_26316, 2, 0);
      INSTR_struct(&false_c3_26317, 3, 0);
      INSTR_struct(&true_c2_26318, 2, 0);
      INSTR_struct(&Ascii_c16_26319, 16, 8, false_c3_26311, true_c2_26312, true_c2_26313, true_c2_26314, false_c3_26315, true_c2_26316, false_c3_26317, true_c2_26318);
      INSTR_struct(&false_c3_26320, 3, 0);
      INSTR_struct(&true_c2_26321, 2, 0);
      INSTR_struct(&true_c2_26322, 2, 0);
      INSTR_struct(&false_c3_26323, 3, 0);
      INSTR_struct(&false_c3_26324, 3, 0);
      INSTR_struct(&false_c3_26325, 3, 0);
      INSTR_struct(&true_c2_26326, 2, 0);
      INSTR_struct(&true_c2_26327, 2, 0);
      INSTR_struct(&Ascii_c16_26328, 16, 8, false_c3_26320, true_c2_26321, true_c2_26322, false_c3_26323, false_c3_26324, false_c3_26325, true_c2_26326, true_c2_26327);
      INSTR_struct(&false_c3_26329, 3, 0);
      INSTR_struct(&true_c2_26330, 2, 0);
      INSTR_struct(&true_c2_26331, 2, 0);
      INSTR_struct(&false_c3_26332, 3, 0);
      INSTR_struct(&false_c3_26333, 3, 0);
      INSTR_struct(&false_c3_26334, 3, 0);
      INSTR_struct(&true_c2_26335, 2, 0);
      INSTR_struct(&true_c2_26336, 2, 0);
      INSTR_struct(&Ascii_c16_26337, 16, 8, false_c3_26329, true_c2_26330, true_c2_26331, false_c3_26332, false_c3_26333, false_c3_26334, true_c2_26335, true_c2_26336);
      INSTR_struct(&false_c3_26338, 3, 0);
      INSTR_struct(&false_c3_26339, 3, 0);
      INSTR_struct(&true_c2_26340, 2, 0);
      INSTR_struct(&false_c3_26341, 3, 0);
      INSTR_struct(&false_c3_26342, 3, 0);
      INSTR_struct(&false_c3_26343, 3, 0);
      INSTR_struct(&false_c3_26344, 3, 0);
      INSTR_struct(&false_c3_26345, 3, 0);
      INSTR_struct(&Ascii_c16_26346, 16, 8, false_c3_26338, false_c3_26339, true_c2_26340, false_c3_26341, false_c3_26342, false_c3_26343, false_c3_26344, false_c3_26345);
      INSTR_struct(&false_c3_26347, 3, 0);
      INSTR_struct(&false_c3_26348, 3, 0);
      INSTR_struct(&true_c2_26349, 2, 0);
      INSTR_struct(&false_c3_26350, 3, 0);
      INSTR_struct(&true_c2_26351, 2, 0);
      INSTR_struct(&false_c3_26352, 3, 0);
      INSTR_struct(&false_c3_26353, 3, 0);
      INSTR_struct(&false_c3_26354, 3, 0);
      INSTR_struct(&Ascii_c16_26355, 16, 8, false_c3_26347, false_c3_26348, true_c2_26349, false_c3_26350, true_c2_26351, false_c3_26352, false_c3_26353, false_c3_26354);
      INSTR_struct(&EmptyString_c17_26356, 17, 0);
      INSTR_struct(&String_c18_26357, 18, 2, Ascii_c16_26355, EmptyString_c17_26356);
      INSTR_struct(&String_c18_26358, 18, 2, Ascii_c16_26346, String_c18_26357);
      INSTR_struct(&String_c18_26359, 18, 2, Ascii_c16_26337, String_c18_26358);
      INSTR_struct(&String_c18_26360, 18, 2, Ascii_c16_26328, String_c18_26359);
      INSTR_struct(&String_c18_26361, 18, 2, Ascii_c16_26319, String_c18_26360);
      INSTR_struct(&String_c18_26362, 18, 2, Ascii_c16_26310, String_c18_26361);
      INSTR_call(&tmp_26363, env[22], String_c18_26362);
      INSTR_call(&tmp_26364, env[0], _26301);
      INSTR_call(&tmp_26365, tmp_26363, tmp_26364);
      INSTR_call(&tmp_26366, env[22], tmp_26365);
      INSTR_struct(&false_c3_26367, 3, 0);
      INSTR_struct(&false_c3_26368, 3, 0);
      INSTR_struct(&true_c2_26369, 2, 0);
      INSTR_struct(&false_c3_26370, 3, 0);
      INSTR_struct(&true_c2_26371, 2, 0);
      INSTR_struct(&false_c3_26372, 3, 0);
      INSTR_struct(&false_c3_26373, 3, 0);
      INSTR_struct(&true_c2_26374, 2, 0);
      INSTR_struct(&Ascii_c16_26375, 16, 8, false_c3_26367, false_c3_26368, true_c2_26369, false_c3_26370, true_c2_26371, false_c3_26372, false_c3_26373, true_c2_26374);
      INSTR_struct(&EmptyString_c17_26376, 17, 0);
      INSTR_struct(&String_c18_26377, 18, 2, Ascii_c16_26375, EmptyString_c17_26376);
      INSTR_call(&tmp_26378, tmp_26366, String_c18_26377);
      INSTR_mov(&case_26259, tmp_26378);
      break;}
  return case_26259;
}

CLC_ptr _26407(CLC_ptr _26405, CLC_env env)
{
  CLC_ptr case_26406;
  switch(((CLC_node)_26405)->tag){
    case 1: INSTR_mov(&case_26406, env[5]);
            break;}
  return case_26406;
}

CLC_ptr _26411(CLC_ptr _26382, CLC_env env)
{
  CLC_ptr _26385; CLC_ptr Ascii_c16_26399; CLC_ptr EmptyString_c17_26400;
  CLC_ptr String_c18_26401; CLC_ptr case_26383; CLC_ptr clo_26408;
  CLC_ptr false_c3_26391; CLC_ptr false_c3_26392; CLC_ptr false_c3_26393;
  CLC_ptr false_c3_26394; CLC_ptr false_c3_26396; CLC_ptr false_c3_26398;
  CLC_ptr out_26388; CLC_ptr s_26386; CLC_ptr tmp_26387; CLC_ptr tmp_26389;
  CLC_ptr tmp_26390; CLC_ptr tmp_26402; CLC_ptr tmp_26403; CLC_ptr tmp_26409;
  CLC_ptr tmp_26410; CLC_ptr true_c2_26395; CLC_ptr true_c2_26397;
  CLC_ptr x_26384;
  switch(((CLC_node)_26382)->tag){
    case 13:
      INSTR_mov(&x_26384, ((CLC_node)_26382)->data[0]);
      INSTR_mov(&_26385, ((CLC_node)_26382)->data[1]);
      INSTR_call(&tmp_26387, env[2], x_26384);
      INSTR_mov(&s_26386, tmp_26387);
      INSTR_call(&tmp_26389, env[13], env[1]);
      INSTR_call(&tmp_26390, env[24], s_26386);
      INSTR_struct(&false_c3_26391, 3, 0);
      INSTR_struct(&false_c3_26392, 3, 0);
      INSTR_struct(&false_c3_26393, 3, 0);
      INSTR_struct(&false_c3_26394, 3, 0);
      INSTR_struct(&true_c2_26395, 2, 0);
      INSTR_struct(&false_c3_26396, 3, 0);
      INSTR_struct(&true_c2_26397, 2, 0);
      INSTR_struct(&false_c3_26398, 3, 0);
      INSTR_struct(&Ascii_c16_26399, 16, 8, false_c3_26391, false_c3_26392, false_c3_26393, false_c3_26394, true_c2_26395, false_c3_26396, true_c2_26397, false_c3_26398);
      INSTR_struct(&EmptyString_c17_26400, 17, 0);
      INSTR_struct(&String_c18_26401, 18, 2, Ascii_c16_26399, EmptyString_c17_26400);
      INSTR_call(&tmp_26402, tmp_26390, String_c18_26401);
      INSTR_call(&tmp_26403, tmp_26389, tmp_26402);
      INSTR_mov(&out_26388, tmp_26403);
      INSTR_clo(&clo_26408, &_26407, 34, 0, out_26388, s_26386, _26382, x_26384, _26385, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23], env[24], env[25], env[26], env[27]);
      INSTR_call(&tmp_26409, env[12], out_26388);
      INSTR_call(&tmp_26410, clo_26408, tmp_26409);
      INSTR_mov(&case_26383, tmp_26410);
      break;}
  return case_26383;
}

int main()
{
  INSTR_clo(&addn_25949, &addn_25948, 2, 0, 0);
  INSTR_mov(&addn_3, addn_25949);
  INSTR_clo(&subn_25969, &subn_25968, 3, 0, addn_3, 0);
  INSTR_mov(&subn_9, subn_25969);
  INSTR_clo(&cat_25987, &cat_25986, 4, 0, subn_9, addn_3, 0);
  INSTR_mov(&cat_67, cat_25987);
  INSTR_clo(&strlen_25997, &strlen_25996, 5, 0, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&strlen_74, strlen_25997);
  INSTR_clo(&lt_26005, &lt_26004, 6, 0, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&lt_84, lt_26005);
  INSTR_clo(&stdin_rec_26010, &stdin_rec_26009, 7, 0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdin_rec_94, stdin_rec_26010);
  INSTR_clo(&stdout_rec_26015, &stdout_rec_26014, 8, 0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdout_rec_98, stdout_rec_26015);
  INSTR_clo(&stderr_rec_26020, &stderr_rec_26019, 9, 0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stderr_rec_102, stderr_rec_26020);
  INSTR_struct(&tt_c1_26021, 1, 0);
  INSTR_call(&tmp_26022, stdin_rec_94, tt_c1_26021);
  INSTR_mov(&stdin_t_106, tmp_26022);
  INSTR_struct(&tt_c1_26023, 1, 0);
  INSTR_call(&tmp_26024, stdout_rec_98, tt_c1_26023);
  INSTR_mov(&stdout_t_107, tmp_26024);
  INSTR_struct(&tt_c1_26025, 1, 0);
  INSTR_call(&tmp_26026, stderr_rec_102, tt_c1_26025);
  INSTR_mov(&stderr_t_108, tmp_26026);
  INSTR_clo(&readline_26034, &readline_26033, 13, 0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&readline_109, readline_26034);
  INSTR_clo(&close_in_26042, &close_in_26041, 14, 0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_in_114, close_in_26042);
  INSTR_clo(&printline_26055, &printline_26054, 15, 0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printline_117, printline_26055);
  INSTR_clo(&close_out_26063, &close_out_26062, 16, 0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_out_122, close_out_26063);
  INSTR_clo(&printerr_26076, &printerr_26075, 17, 0, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printerr_125, printerr_26076);
  INSTR_clo(&close_err_26084, &close_err_26083, 18, 0, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_err_130, close_err_26084);
  INSTR_clo(&exn_p_26088, &exn_p_26087, 19, 0, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&exn_p_133, exn_p_26088);
  INSTR_clo(&exn_26092, &exn_26091, 20, 0, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&exn_143, exn_26092);
  INSTR_clo(&ret_26105, &ret_26104, 21, 0, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&ret_147, ret_26105);
  INSTR_clo(&throw_26125, &throw_26124, 22, 0, ret_147, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&throw_153, throw_26125);
  INSTR_clo(&bind_26153, &bind_26152, 23, 0, throw_153, ret_147, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&bind_158, bind_26153);
  INSTR_clo(&div2_exn_p_26176, &div2_exn_p_26175, 24, 0, bind_158, throw_153, ret_147, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&div2_exn_p_169, div2_exn_p_26176);
  INSTR_clo(&try_exn_26256, &try_exn_26255, 25, 0, div2_exn_p_169, bind_158, throw_153, ret_147, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&try_exn_174, try_exn_26256);
  INSTR_clo(&string_of_nat_26380, &string_of_nat_26379, 26, 0, try_exn_174, div2_exn_p_169, bind_158, throw_153, ret_147, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&string_of_nat_196, string_of_nat_26380);
  INSTR_trg(&out_199, &PROC_stdout);
  INSTR_clo(&clo_26412, &_26411, 28, 0, out_199, string_of_nat_196, try_exn_174, div2_exn_p_169, bind_158, throw_153, ret_147, exn_143, exn_p_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_call(&tmp_26413, try_exn_174, 0);
  INSTR_call(&tmp_26414, tmp_26413, 0);
  INSTR_struct(&zero_c4_26415, 4, 0);
  INSTR_struct(&succ_c5_26416, 5, 1, zero_c4_26415);
  INSTR_struct(&succ_c5_26417, 5, 1, succ_c5_26416);
  INSTR_struct(&succ_c5_26418, 5, 1, succ_c5_26417);
  INSTR_struct(&succ_c5_26419, 5, 1, succ_c5_26418);
  INSTR_struct(&succ_c5_26420, 5, 1, succ_c5_26419);
  INSTR_struct(&succ_c5_26421, 5, 1, succ_c5_26420);
  INSTR_struct(&succ_c5_26422, 5, 1, succ_c5_26421);
  INSTR_struct(&succ_c5_26423, 5, 1, succ_c5_26422);
  INSTR_struct(&succ_c5_26424, 5, 1, succ_c5_26423);
  INSTR_struct(&succ_c5_26425, 5, 1, succ_c5_26424);
  INSTR_struct(&succ_c5_26426, 5, 1, succ_c5_26425);
  INSTR_struct(&succ_c5_26427, 5, 1, succ_c5_26426);
  INSTR_struct(&succ_c5_26428, 5, 1, succ_c5_26427);
  INSTR_struct(&succ_c5_26429, 5, 1, succ_c5_26428);
  INSTR_call(&tmp_26430, div2_exn_p_169, succ_c5_26429);
  INSTR_call(&tmp_26431, tmp_26414, tmp_26430);
  INSTR_struct(&zero_c4_26432, 4, 0);
  INSTR_call(&tmp_26433, tmp_26431, zero_c4_26432);
  INSTR_call(&tmp_26434, clo_26412, tmp_26433);
  INSTR_mov(&_200, tmp_26434); return 0;
}
