#include "runtime.h"

clc_ptr lam_29774(clc_ptr _29773, clc_env env)
{
  
  
  return _29773;
}

clc_ptr lam_29782(clc_ptr _29778, clc_env env)
{
  clc_ptr succ_c5_29781; clc_ptr tmp_29779; clc_ptr tmp_29780;
  instr_call(&tmp_29779, env[3], env[2]);
  instr_call(&tmp_29780, tmp_29779, _29778);
  instr_struct(&succ_c5_29781, 5, 1,
    tmp_29780);
  return succ_c5_29781;
}

clc_ptr addn_29784(clc_ptr _29770, clc_env env)
{
  clc_ptr _29776; clc_ptr case_29771; clc_ptr clo_29775; clc_ptr clo_29783;
  switch(((clc_node)_29770)->tag){
    case 4:
      instr_clo(&clo_29775, &lam_29774, 4, 0, _29770, env[0], env[1]);
      instr_mov(&case_29771, clo_29775);
      break;
    case 5:
      instr_mov(&_29776, ((clc_node)_29770)->data[0]);
      instr_clo(&clo_29783, &lam_29782, 5,
        0, _29770, _29776, env[0], env[1]);
      instr_mov(&case_29771, clo_29783);
      break;}
  return case_29771;
}

clc_ptr lam_29792(clc_ptr _29790, clc_env env)
{
  clc_ptr zero_c4_29791;
  instr_struct(&zero_c4_29791, 4, 0);
  return zero_c4_29791;
}

clc_ptr lam_29802(clc_ptr _29796, clc_env env)
{
  clc_ptr _29799; clc_ptr case_29797; clc_ptr succ_c5_29798;
  clc_ptr tmp_29800; clc_ptr tmp_29801;
  switch(((clc_node)_29796)->tag){
    case 4:
      instr_struct(&succ_c5_29798, 5, 1,
        env[2]);
      instr_mov(&case_29797, succ_c5_29798);
      break;
    case 5:
      instr_mov(&_29799, ((clc_node)_29796)->data[0]);
      instr_call(&tmp_29800, env[3], env[2]);
      instr_call(&tmp_29801, tmp_29800, _29799);
      instr_mov(&case_29797, tmp_29801);
      break;}
  return case_29797;
}

clc_ptr subn_29804(clc_ptr _29787, clc_env env)
{
  clc_ptr _29794; clc_ptr case_29788; clc_ptr clo_29793; clc_ptr clo_29803;
  switch(((clc_node)_29787)->tag){
    case 4:
      instr_clo(&clo_29793, &lam_29792, 5,
        0, _29787, env[0], env[1], env[2]);
      instr_mov(&case_29788, clo_29793);
      break;
    case 5:
      instr_mov(&_29794, ((clc_node)_29787)->data[0]);
      instr_clo(&clo_29803, &lam_29802, 6,
        0, _29787, _29794, env[0], env[1], env[2]);
      instr_mov(&case_29788, clo_29803);
      break;}
  return case_29788;
}

clc_ptr lam_29811(clc_ptr _29810, clc_env env)
{
  
  
  return _29810;
}

clc_ptr lam_29820(clc_ptr _29816, clc_env env)
{
  clc_ptr String_c18_29819; clc_ptr tmp_29817; clc_ptr tmp_29818;
  instr_call(&tmp_29817, env[4], env[3]);
  instr_call(&tmp_29818, tmp_29817, _29816);
  instr_struct(&String_c18_29819, 18, 2,
    env[2], tmp_29818);
  return String_c18_29819;
}

clc_ptr cat_29822(clc_ptr _29807, clc_env env)
{
  clc_ptr _29813; clc_ptr _29814; clc_ptr case_29808; clc_ptr clo_29812;
  clc_ptr clo_29821;
  switch(((clc_node)_29807)->tag){
    case 17:
      instr_clo(&clo_29812, &lam_29811, 6,
        0, _29807, env[0], env[1], env[2], env[3]);
      instr_mov(&case_29808, clo_29812);
      break;
    case 18:
      instr_mov(&_29813, ((clc_node)_29807)->data[0]);
      instr_mov(&_29814, ((clc_node)_29807)->data[1]);
      instr_clo(&clo_29821, &lam_29820, 8,
        0, _29807, _29813, _29814, env[0], env[1], env[2], env[3]);
      instr_mov(&case_29808, clo_29821);
      break;}
  return case_29808;
}

clc_ptr strlen_29832(clc_ptr _29825, clc_env env)
{
  clc_ptr _29828; clc_ptr _29829; clc_ptr case_29826; clc_ptr succ_c5_29831;
  clc_ptr tmp_29830; clc_ptr zero_c4_29827;
  switch(((clc_node)_29825)->tag){
    case 17:
      instr_struct(&zero_c4_29827, 4, 0);
      instr_mov(&case_29826, zero_c4_29827);
      break;
    case 18:
      instr_mov(&_29828, ((clc_node)_29825)->data[0]);
      instr_mov(&_29829, ((clc_node)_29825)->data[1]);
      instr_call(&tmp_29830, env[0], _29829);
      instr_struct(&succ_c5_29831, 5, 1,
        tmp_29830);
      instr_mov(&case_29826, succ_c5_29831);
      break;}
  return case_29826;
}

clc_ptr lam_29838(clc_ptr _29837, clc_env env)
{
  
  
  return 0;
}

clc_ptr lt_29840(clc_ptr _29835, clc_env env)
{
  clc_ptr clo_29839;
  instr_clo(&clo_29839, &lam_29838, 8,
    0, _29835, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_29839;
}

clc_ptr stdin_rec_29845(clc_ptr _29843, clc_env env)
{
  clc_ptr case_29844;
  switch(((clc_node)_29843)->tag){
    case 1: instr_mov(&case_29844, 0);
            break;}
  return case_29844;
}

clc_ptr stdout_rec_29850(clc_ptr _29848, clc_env env)
{
  clc_ptr case_29849;
  switch(((clc_node)_29848)->tag){
    case 1: instr_mov(&case_29849, 0);
            break;}
  return case_29849;
}

clc_ptr stderr_rec_29855(clc_ptr _29853, clc_env env)
{
  clc_ptr case_29854;
  switch(((clc_node)_29853)->tag){
    case 1: instr_mov(&case_29854, 0);
            break;}
  return case_29854;
}

clc_ptr readline_29869(clc_ptr _29864, clc_env env)
{
  clc_ptr recv_struct_29868; clc_ptr send_clo_29865; clc_ptr tmp_29867;
  clc_ptr true_c2_29866;
  instr_send(&send_clo_29865, _29864);
  instr_struct(&true_c2_29866, 2, 0);
  instr_call(&tmp_29867, send_clo_29865, true_c2_29866);
  instr_recv(&recv_struct_29868, tmp_29867, 13);
  return recv_struct_29868;
}

clc_ptr close_in_29877(clc_ptr _29872, clc_env env)
{
  clc_ptr false_c3_29875; clc_ptr send_clo_29874; clc_ptr tmp_29876;
  clc_ptr unit_struct_29873;
  instr_send(&send_clo_29874, _29872);
  instr_struct(&false_c3_29875, 3, 0);
  instr_call(&tmp_29876, send_clo_29874, false_c3_29875);
  instr_struct(&unit_struct_29873, 1, 0);
  return unit_struct_29873;
}

clc_ptr lam_29888(clc_ptr _29882, clc_env env)
{
  clc_ptr send_clo_29883; clc_ptr send_clo_29886; clc_ptr tmp_29885;
  clc_ptr tmp_29887; clc_ptr true_c2_29884;
  instr_send(&send_clo_29883, env[1]);
  instr_struct(&true_c2_29884, 2, 0);
  instr_call(&tmp_29885, send_clo_29883, true_c2_29884);
  instr_send(&send_clo_29886, tmp_29885);
  instr_call(&tmp_29887, send_clo_29886, _29882);
  return tmp_29887;
}

clc_ptr printline_29890(clc_ptr _29880, clc_env env)
{
  clc_ptr clo_29889;
  instr_clo(&clo_29889, &lam_29888, 17,
    0, _29880, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_29889;
}

clc_ptr close_out_29898(clc_ptr _29893, clc_env env)
{
  clc_ptr false_c3_29896; clc_ptr send_clo_29895; clc_ptr tmp_29897;
  clc_ptr unit_struct_29894;
  instr_send(&send_clo_29895, _29893);
  instr_struct(&false_c3_29896, 3, 0);
  instr_call(&tmp_29897, send_clo_29895, false_c3_29896);
  instr_struct(&unit_struct_29894, 1, 0);
  return unit_struct_29894;
}

clc_ptr lam_29909(clc_ptr _29903, clc_env env)
{
  clc_ptr send_clo_29904; clc_ptr send_clo_29907; clc_ptr tmp_29906;
  clc_ptr tmp_29908; clc_ptr true_c2_29905;
  instr_send(&send_clo_29904, env[1]);
  instr_struct(&true_c2_29905, 2, 0);
  instr_call(&tmp_29906, send_clo_29904, true_c2_29905);
  instr_send(&send_clo_29907, tmp_29906);
  instr_call(&tmp_29908, send_clo_29907, _29903);
  return tmp_29908;
}

clc_ptr printerr_29911(clc_ptr _29901, clc_env env)
{
  clc_ptr clo_29910;
  instr_clo(&clo_29910, &lam_29909, 19,
    0, _29901, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16]);
  return clo_29910;
}

clc_ptr close_err_29919(clc_ptr _29914, clc_env env)
{
  clc_ptr false_c3_29917; clc_ptr send_clo_29916; clc_ptr tmp_29918;
  clc_ptr unit_struct_29915;
  instr_send(&send_clo_29916, _29914);
  instr_struct(&false_c3_29917, 3, 0);
  instr_call(&tmp_29918, send_clo_29916, false_c3_29917);
  instr_struct(&unit_struct_29915, 1, 0);
  return unit_struct_29915;
}

clc_ptr ref_t_29923(clc_ptr _29922, clc_env env)
{
  
  
  return 0;
}

clc_ptr lam_29950(clc_ptr _29943, clc_env env)
{
  clc_ptr _29946; clc_ptr case_29944; clc_ptr tmp_29947; clc_ptr tmp_29948;
  clc_ptr tmp_29949; clc_ptr x_29945;
  switch(((clc_node)_29943)->tag){
    case 13:
      instr_mov(&x_29945, ((clc_node)_29943)->data[0]);
      instr_mov(&_29946, ((clc_node)_29943)->data[1]);
      instr_call(&tmp_29947, env[10], env[9]);
      instr_call(&tmp_29948, tmp_29947, x_29945);
      instr_call(&tmp_29949, tmp_29948, _29946);
      instr_mov(&case_29944, tmp_29949);
      break;}
  return case_29944;
}

clc_ptr lam_29955(clc_ptr _29932, clc_env env)
{
  clc_ptr _29935; clc_ptr case_29933; clc_ptr case_29936; clc_ptr clo_29951;
  clc_ptr recv_struct_29952; clc_ptr send_clo_29939; clc_ptr tmp_29937;
  clc_ptr tmp_29938; clc_ptr tmp_29940; clc_ptr tmp_29941; clc_ptr tmp_29953;
  clc_ptr unit_struct_29954; clc_ptr x_29934;
  switch(((clc_node)_29932)->tag){
    case 13:
      instr_mov(&x_29934, ((clc_node)_29932)->data[0]);
      instr_mov(&_29935, ((clc_node)_29932)->data[1]);
      switch(((clc_node)x_29934)->tag){
        case 22:
          instr_call(&tmp_29937, env[6], env[5]);
          instr_call(&tmp_29938, tmp_29937, env[3]);
          instr_send(&send_clo_29939, _29935);
          instr_call(&tmp_29940, send_clo_29939, env[3]);
          instr_call(&tmp_29941, tmp_29938, tmp_29940);
          instr_mov(&case_29936, tmp_29941);
          break;
        case 23:
          instr_clo(&clo_29951, &lam_29950, 30,
            0, _29932, x_29934, _29935, env[0], env[1], env[2], env[3],
            env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11],
            env[12], env[13], env[14], env[15], env[16], env[17], env[18],
            env[19], env[20], env[21], env[22], env[23], env[24], env[25]);
          instr_recv(&recv_struct_29952, _29935, 13);
          instr_call(&tmp_29953, clo_29951, recv_struct_29952);
          instr_mov(&case_29936, tmp_29953);
          break;
        case 24:
          instr_struct(&unit_struct_29954, 1, 0);
          instr_mov(&case_29936, unit_struct_29954);
          break;}
      instr_mov(&case_29933, case_29936);
      break;}
  return case_29933;
}

clc_ptr lam_29959(clc_ptr _29930, clc_env env)
{
  clc_ptr clo_29956; clc_ptr recv_struct_29957; clc_ptr tmp_29958;
  instr_clo(&clo_29956, &lam_29955, 26,
    0, _29930, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23]);
  instr_recv(&recv_struct_29957, _29930, 13);
  instr_call(&tmp_29958, clo_29956, recv_struct_29957);
  return tmp_29958;
}

clc_ptr lam_29961(clc_ptr _29928, clc_env env)
{
  clc_ptr clo_29960;
  instr_clo(&clo_29960, &lam_29959, 24,
    0, _29928, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21]);
  return clo_29960;
}

clc_ptr ref_handler_29963(clc_ptr A_29926, clc_env env)
{
  clc_ptr clo_29962;
  instr_clo(&clo_29962, &lam_29961, 22,
    0, A_29926, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19]);
  return clo_29962;
}

clc_ptr fork_proc_29976(clc_env env)
{
  clc_ptr tmp_29972; clc_ptr tmp_29973; clc_ptr tmp_29974;
  instr_call(&tmp_29972, env[7], env[5]);
  instr_call(&tmp_29973, tmp_29972, env[3]);
  instr_call(&tmp_29974, tmp_29973, env[0]);
  return tmp_29974;
}

clc_ptr lam_29977(clc_ptr _29970, clc_env env)
{
  clc_ptr fork_res_29975;
  instr_open(&fork_res_29975, &fork_proc_29976, _29970, 26,
    _29970, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7],
    env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15],
    env[16], env[17], env[18], env[19], env[20], env[21], env[22], env[23],
    env[24]);
  return fork_res_29975;
}

clc_ptr lam_29979(clc_ptr _29968, clc_env env)
{
  clc_ptr clo_29978;
  instr_clo(&clo_29978, &lam_29977, 25,
    0, _29968, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22]);
  return clo_29978;
}

clc_ptr mk_ref_29981(clc_ptr A_29966, clc_env env)
{
  clc_ptr clo_29980;
  instr_clo(&clo_29980, &lam_29979, 23,
    0, A_29966, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20]);
  return clo_29980;
}

clc_ptr lam_29994(clc_ptr _29988, clc_env env)
{
  clc_ptr SET_c23_29990; clc_ptr send_clo_29989; clc_ptr send_clo_29992;
  clc_ptr tmp_29991; clc_ptr tmp_29993;
  instr_send(&send_clo_29989, _29988);
  instr_struct(&SET_c23_29990, 23, 0);
  instr_call(&tmp_29991, send_clo_29989, SET_c23_29990);
  instr_send(&send_clo_29992, tmp_29991);
  instr_call(&tmp_29993, send_clo_29992, env[1]);
  return tmp_29993;
}

clc_ptr lam_29996(clc_ptr _29986, clc_env env)
{
  clc_ptr clo_29995;
  instr_clo(&clo_29995, &lam_29994, 26,
    0, _29986, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23]);
  return clo_29995;
}

clc_ptr set_ref_29998(clc_ptr A_29984, clc_env env)
{
  clc_ptr clo_29997;
  instr_clo(&clo_29997, &lam_29996, 24,
    0, A_29984, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21]);
  return clo_29997;
}

clc_ptr lam_30008(clc_ptr _30003, clc_env env)
{
  clc_ptr GET_c22_30005; clc_ptr recv_struct_30007; clc_ptr send_clo_30004;
  clc_ptr tmp_30006;
  instr_send(&send_clo_30004, _30003);
  instr_struct(&GET_c22_30005, 22, 0);
  instr_call(&tmp_30006, send_clo_30004, GET_c22_30005);
  instr_recv(&recv_struct_30007, tmp_30006, 13);
  return recv_struct_30007;
}

clc_ptr get_ref_30010(clc_ptr A_30001, clc_env env)
{
  clc_ptr clo_30009;
  instr_clo(&clo_30009, &lam_30008, 25,
    0, A_30001, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22]);
  return clo_30009;
}

clc_ptr lam_30020(clc_ptr _30015, clc_env env)
{
  clc_ptr FREE_c24_30018; clc_ptr send_clo_30017; clc_ptr tmp_30019;
  clc_ptr unit_struct_30016;
  instr_send(&send_clo_30017, _30015);
  instr_struct(&FREE_c24_30018, 24, 0);
  instr_call(&tmp_30019, send_clo_30017, FREE_c24_30018);
  instr_close(&unit_struct_30016, tmp_30019);
  return unit_struct_30016;
}

clc_ptr free_ref_30022(clc_ptr A_30013, clc_env env)
{
  clc_ptr clo_30021;
  instr_clo(&clo_30021, &lam_30020, 26,
    0, A_30013, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23]);
  return clo_30021;
}

clc_ptr lam_30075(clc_ptr _30073, clc_env env)
{
  clc_ptr case_30074;
  switch(((clc_node)_30073)->tag){
    case 1: instr_mov(&case_30074, env[21]);
            break;}
  return case_30074;
}

clc_ptr lam_30080(clc_ptr _30070, clc_env env)
{
  clc_ptr case_30071; clc_ptr clo_30076; clc_ptr tmp_30077;
  clc_ptr tmp_30078; clc_ptr tmp_30079;
  switch(((clc_node)_30070)->tag){
    case 1:
      instr_clo(&clo_30076, &lam_30075, 49,
        0, _30070, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
        env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
        env[15], env[16], env[17], env[18], env[19], env[20], env[21],
        env[22], env[23], env[24], env[25], env[26], env[27], env[28],
        env[29], env[30], env[31], env[32], env[33], env[34], env[35],
        env[36], env[37], env[38], env[39], env[40], env[41], env[42],
        env[43], env[44], env[45], env[46]);
      instr_call(&tmp_30077, env[23], 0);
      instr_call(&tmp_30078, tmp_30077, env[4]);
      instr_call(&tmp_30079, clo_30076, tmp_30078);
      instr_mov(&case_30071, tmp_30079);
      break;}
  return case_30071;
}

clc_ptr lam_30084(clc_ptr _30047, clc_env env)
{
  clc_ptr _30050; clc_ptr Ascii_c16_30064; clc_ptr EmptyString_c17_30065;
  clc_ptr String_c18_30066; clc_ptr case_30048; clc_ptr clo_30081;
  clc_ptr false_c3_30056; clc_ptr false_c3_30057; clc_ptr false_c3_30058;
  clc_ptr false_c3_30059; clc_ptr false_c3_30061; clc_ptr false_c3_30063;
  clc_ptr stdout_30051; clc_ptr tmp_30052; clc_ptr tmp_30053;
  clc_ptr tmp_30054; clc_ptr tmp_30055; clc_ptr tmp_30067; clc_ptr tmp_30068;
  clc_ptr tmp_30082; clc_ptr tmp_30083; clc_ptr true_c2_30060;
  clc_ptr true_c2_30062; clc_ptr x_30049;
  switch(((clc_node)_30047)->tag){
    case 13:
      instr_mov(&x_30049, ((clc_node)_30047)->data[0]);
      instr_mov(&_30050, ((clc_node)_30047)->data[1]);
      instr_call(&tmp_30052, env[27], env[17]);
      instr_call(&tmp_30053, env[38], env[9]);
      instr_call(&tmp_30054, tmp_30053, x_30049);
      instr_call(&tmp_30055, env[38], tmp_30054);
      instr_struct(&false_c3_30056, 3, 0);
      instr_struct(&false_c3_30057, 3, 0);
      instr_struct(&false_c3_30058, 3, 0);
      instr_struct(&false_c3_30059, 3, 0);
      instr_struct(&true_c2_30060, 2, 0);
      instr_struct(&false_c3_30061, 3, 0);
      instr_struct(&true_c2_30062, 2, 0);
      instr_struct(&false_c3_30063, 3, 0);
      instr_struct(&Ascii_c16_30064, 16, 8,
        false_c3_30056, false_c3_30057, false_c3_30058, false_c3_30059,
        true_c2_30060, false_c3_30061, true_c2_30062, false_c3_30063);
      instr_struct(&EmptyString_c17_30065, 17, 0);
      instr_struct(&String_c18_30066, 18, 2,
        Ascii_c16_30064, EmptyString_c17_30065);
      instr_call(&tmp_30067, tmp_30055, String_c18_30066);
      instr_call(&tmp_30068, tmp_30052, tmp_30067);
      instr_mov(&stdout_30051, tmp_30068);
      instr_clo(&clo_30081, &lam_30080, 47,
        0, stdout_30051, _30047, x_30049, _30050, env[0], env[1], env[2],
        env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10],
        env[11], env[12], env[13], env[14], env[15], env[16], env[17],
        env[18], env[19], env[20], env[21], env[22], env[23], env[24],
        env[25], env[26], env[27], env[28], env[29], env[30], env[31],
        env[32], env[33], env[34], env[35], env[36], env[37], env[38],
        env[39], env[40], env[41]);
      instr_call(&tmp_30082, env[26], stdout_30051);
      instr_call(&tmp_30083, clo_30081, tmp_30082);
      instr_mov(&case_30048, tmp_30083);
      break;}
  return case_30048;
}

clc_ptr lam_30089(clc_ptr _30040, clc_env env)
{
  clc_ptr case_30041; clc_ptr clo_30085; clc_ptr ref_30042;
  clc_ptr tmp_30043; clc_ptr tmp_30044; clc_ptr tmp_30045; clc_ptr tmp_30086;
  clc_ptr tmp_30087; clc_ptr tmp_30088;
  switch(((clc_node)_30040)->tag){
    case 1:
      instr_call(&tmp_30043, env[17], 0);
      instr_call(&tmp_30044, tmp_30043, env[2]);
      instr_call(&tmp_30045, tmp_30044, env[7]);
      instr_mov(&ref_30042, tmp_30045);
      instr_clo(&clo_30085, &lam_30084, 42,
        0, ref_30042, _30040, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29], env[30], env[31], env[32], env[33], env[34],
        env[35], env[36], env[37], env[38]);
      instr_call(&tmp_30086, env[16], 0);
      instr_call(&tmp_30087, tmp_30086, ref_30042);
      instr_call(&tmp_30088, clo_30085, tmp_30087);
      instr_mov(&case_30041, tmp_30088);
      break;}
  return case_30041;
}

clc_ptr lam_30093(clc_ptr _30035, clc_env env)
{
  clc_ptr _30038; clc_ptr case_30036; clc_ptr clo_30090; clc_ptr tmp_30091;
  clc_ptr tmp_30092; clc_ptr x_30037;
  switch(((clc_node)_30035)->tag){
    case 13:
      instr_mov(&x_30037, ((clc_node)_30035)->data[0]);
      instr_mov(&_30038, ((clc_node)_30035)->data[1]);
      instr_clo(&clo_30090, &lam_30089, 39,
        0, _30035, x_30037, _30038, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26],
        env[27], env[28], env[29], env[30], env[31], env[32], env[33],
        env[34]);
      instr_call(&tmp_30091, env[21], _30038);
      instr_call(&tmp_30092, clo_30090, tmp_30091);
      instr_mov(&case_30036, tmp_30092);
      break;}
  return case_30036;
}

clc_ptr lam_30097(clc_ptr _30030, clc_env env)
{
  clc_ptr _30033; clc_ptr case_30031; clc_ptr clo_30094; clc_ptr tmp_30095;
  clc_ptr tmp_30096; clc_ptr x_30032;
  switch(((clc_node)_30030)->tag){
    case 13:
      instr_mov(&x_30032, ((clc_node)_30030)->data[0]);
      instr_mov(&_30033, ((clc_node)_30030)->data[1]);
      instr_clo(&clo_30094, &lam_30093, 35,
        0, _30030, x_30032, _30033, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26],
        env[27], env[28], env[29], env[30]);
      instr_call(&tmp_30095, env[18], env[5]);
      instr_call(&tmp_30096, clo_30094, tmp_30095);
      instr_mov(&case_30031, tmp_30096);
      break;}
  return case_30031;
}

clc_ptr lam_30102(clc_ptr _30025, clc_env env)
{
  clc_ptr _30027; clc_ptr _30028; clc_ptr case_30026; clc_ptr clo_30098;
  clc_ptr tmp_30099; clc_ptr tmp_30100; clc_ptr tmp_30101;
  switch(((clc_node)_30025)->tag){
    case 14:
      instr_mov(&_30027, ((clc_node)_30025)->data[0]);
      instr_mov(&_30028, ((clc_node)_30025)->data[1]);
      instr_clo(&clo_30098, &lam_30097, 31,
        0, _30025, _30027, _30028, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26]);
      instr_call(&tmp_30099, env[4], 0);
      instr_call(&tmp_30100, tmp_30099, _30027);
      instr_call(&tmp_30101, clo_30098, tmp_30100);
      instr_mov(&case_30026, tmp_30101);
      break;}
  return case_30026;
}

int main()
{
  clc_ptr Ascii_c16_30113; clc_ptr Ascii_c16_30122; clc_ptr Ascii_c16_30131;
  clc_ptr Ascii_c16_30140; clc_ptr Ascii_c16_30149; clc_ptr Ascii_c16_30158;
  clc_ptr EmptyString_c17_30159; clc_ptr String_c18_30160;
  clc_ptr String_c18_30161; clc_ptr String_c18_30162;
  clc_ptr String_c18_30163; clc_ptr String_c18_30164;
  clc_ptr String_c18_30165; clc_ptr addn_3; clc_ptr addn_29785;
  clc_ptr cat_67; clc_ptr cat_29823; clc_ptr clo_30103;
  clc_ptr close_err_130; clc_ptr close_err_29920; clc_ptr close_in_114;
  clc_ptr close_in_29878; clc_ptr close_out_122; clc_ptr close_out_29899;
  clc_ptr false_c3_30105; clc_ptr false_c3_30108; clc_ptr false_c3_30110;
  clc_ptr false_c3_30111; clc_ptr false_c3_30112; clc_ptr false_c3_30114;
  clc_ptr false_c3_30117; clc_ptr false_c3_30118; clc_ptr false_c3_30120;
  clc_ptr false_c3_30123; clc_ptr false_c3_30126; clc_ptr false_c3_30129;
  clc_ptr false_c3_30130; clc_ptr false_c3_30132; clc_ptr false_c3_30135;
  clc_ptr false_c3_30138; clc_ptr false_c3_30139; clc_ptr false_c3_30141;
  clc_ptr false_c3_30144; clc_ptr false_c3_30150; clc_ptr false_c3_30151;
  clc_ptr false_c3_30153; clc_ptr false_c3_30154; clc_ptr false_c3_30155;
  clc_ptr false_c3_30156; clc_ptr false_c3_30157; clc_ptr free_ref_173;
  clc_ptr free_ref_30023; clc_ptr get_ref_166; clc_ptr get_ref_30011;
  clc_ptr lt_84; clc_ptr lt_29841; clc_ptr main_180; clc_ptr mk_ref_151;
  clc_ptr mk_ref_29982; clc_ptr printerr_125; clc_ptr printerr_29912;
  clc_ptr printline_117; clc_ptr printline_29891; clc_ptr readline_109;
  clc_ptr readline_29870; clc_ptr ref_handler_139; clc_ptr ref_handler_29964;
  clc_ptr ref_t_133; clc_ptr ref_t_29924; clc_ptr set_ref_159;
  clc_ptr set_ref_29999; clc_ptr stderr_rec_102; clc_ptr stderr_rec_29856;
  clc_ptr stderr_t_108; clc_ptr stdin_179; clc_ptr stdin_rec_94;
  clc_ptr stdin_rec_29846; clc_ptr stdin_t_106; clc_ptr stdout_178;
  clc_ptr stdout_rec_98; clc_ptr stdout_rec_29851; clc_ptr stdout_t_107;
  clc_ptr strlen_74; clc_ptr strlen_29833; clc_ptr subn_9;
  clc_ptr subn_29805; clc_ptr tmp_29858; clc_ptr tmp_29860;
  clc_ptr tmp_29862; clc_ptr tmp_30104; clc_ptr tmp_30166; clc_ptr tmp_30167;
  clc_ptr tmp_30168; clc_ptr true_c2_30106; clc_ptr true_c2_30107;
  clc_ptr true_c2_30109; clc_ptr true_c2_30115; clc_ptr true_c2_30116;
  clc_ptr true_c2_30119; clc_ptr true_c2_30121; clc_ptr true_c2_30124;
  clc_ptr true_c2_30125; clc_ptr true_c2_30127; clc_ptr true_c2_30128;
  clc_ptr true_c2_30133; clc_ptr true_c2_30134; clc_ptr true_c2_30136;
  clc_ptr true_c2_30137; clc_ptr true_c2_30142; clc_ptr true_c2_30143;
  clc_ptr true_c2_30145; clc_ptr true_c2_30146; clc_ptr true_c2_30147;
  clc_ptr true_c2_30148; clc_ptr true_c2_30152; clc_ptr tt_c1_29857;
  clc_ptr tt_c1_29859; clc_ptr tt_c1_29861;
  instr_clo(&addn_29785, &addn_29784, 2, 0, 0);
  instr_mov(&addn_3, addn_29785);
  instr_clo(&subn_29805, &subn_29804, 3, 0, addn_3, 0);
  instr_mov(&subn_9, subn_29805);
  instr_clo(&cat_29823, &cat_29822, 4, 0, subn_9, addn_3, 0);
  instr_mov(&cat_67, cat_29823);
  instr_clo(&strlen_29833, &strlen_29832, 5, 0, cat_67, subn_9, addn_3, 0);
  instr_mov(&strlen_74, strlen_29833);
  instr_clo(&lt_29841, &lt_29840, 6,
    0, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&lt_84, lt_29841);
  instr_clo(&stdin_rec_29846, &stdin_rec_29845, 7,
    0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdin_rec_94, stdin_rec_29846);
  instr_clo(&stdout_rec_29851, &stdout_rec_29850, 8,
    0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdout_rec_98, stdout_rec_29851);
  instr_clo(&stderr_rec_29856, &stderr_rec_29855, 9,
    0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3,
    0);
  instr_mov(&stderr_rec_102, stderr_rec_29856);
  instr_struct(&tt_c1_29857, 1, 0);
  instr_call(&tmp_29858, stdin_rec_94, tt_c1_29857);
  instr_mov(&stdin_t_106, tmp_29858);
  instr_struct(&tt_c1_29859, 1, 0);
  instr_call(&tmp_29860, stdout_rec_98, tt_c1_29859);
  instr_mov(&stdout_t_107, tmp_29860);
  instr_struct(&tt_c1_29861, 1, 0);
  instr_call(&tmp_29862, stderr_rec_102, tt_c1_29861);
  instr_mov(&stderr_t_108, tmp_29862);
  instr_clo(&readline_29870, &readline_29869, 13,
    0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&readline_109, readline_29870);
  instr_clo(&close_in_29878, &close_in_29877, 14,
    0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_in_114, close_in_29878);
  instr_clo(&printline_29891, &printline_29890, 15,
    0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&printline_117, printline_29891);
  instr_clo(&close_out_29899, &close_out_29898, 16,
    0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_out_122, close_out_29899);
  instr_clo(&printerr_29912, &printerr_29911, 17,
    0, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&printerr_125, printerr_29912);
  instr_clo(&close_err_29920, &close_err_29919, 18,
    0, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_err_130, close_err_29920);
  instr_clo(&ref_t_29924, &ref_t_29923, 19,
    0, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&ref_t_133, ref_t_29924);
  instr_clo(&ref_handler_29964, &ref_handler_29963, 20,
    0, ref_t_133, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&ref_handler_139, ref_handler_29964);
  instr_clo(&mk_ref_29982, &mk_ref_29981, 21,
    0, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&mk_ref_151, mk_ref_29982);
  instr_clo(&set_ref_29999, &set_ref_29998, 22,
    0, mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&set_ref_159, set_ref_29999);
  instr_clo(&get_ref_30011, &get_ref_30010, 23,
    0, set_ref_159, mk_ref_151, ref_handler_139, ref_t_133, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&get_ref_166, get_ref_30011);
  instr_clo(&free_ref_30023, &free_ref_30022, 24,
    0, get_ref_166, set_ref_159, mk_ref_151, ref_handler_139, ref_t_133,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&free_ref_173, free_ref_30023);
  instr_trg(&stdout_178, &proc_stdout);
  instr_trg(&stdin_179, &proc_stdin);
  instr_clo(&clo_30103, &lam_30102, 27,
    0, stdin_179, stdout_178, free_ref_173, get_ref_166, set_ref_159,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_call(&tmp_30104, mk_ref_151, 0);
  instr_struct(&false_c3_30105, 3, 0);
  instr_struct(&true_c2_30106, 2, 0);
  instr_struct(&true_c2_30107, 2, 0);
  instr_struct(&false_c3_30108, 3, 0);
  instr_struct(&true_c2_30109, 2, 0);
  instr_struct(&false_c3_30110, 3, 0);
  instr_struct(&false_c3_30111, 3, 0);
  instr_struct(&false_c3_30112, 3, 0);
  instr_struct(&Ascii_c16_30113, 16, 8,
    false_c3_30105, true_c2_30106, true_c2_30107, false_c3_30108,
    true_c2_30109, false_c3_30110, false_c3_30111, false_c3_30112);
  instr_struct(&false_c3_30114, 3, 0);
  instr_struct(&true_c2_30115, 2, 0);
  instr_struct(&true_c2_30116, 2, 0);
  instr_struct(&false_c3_30117, 3, 0);
  instr_struct(&false_c3_30118, 3, 0);
  instr_struct(&true_c2_30119, 2, 0);
  instr_struct(&false_c3_30120, 3, 0);
  instr_struct(&true_c2_30121, 2, 0);
  instr_struct(&Ascii_c16_30122, 16, 8,
    false_c3_30114, true_c2_30115, true_c2_30116, false_c3_30117,
    false_c3_30118, true_c2_30119, false_c3_30120, true_c2_30121);
  instr_struct(&false_c3_30123, 3, 0);
  instr_struct(&true_c2_30124, 2, 0);
  instr_struct(&true_c2_30125, 2, 0);
  instr_struct(&false_c3_30126, 3, 0);
  instr_struct(&true_c2_30127, 2, 0);
  instr_struct(&true_c2_30128, 2, 0);
  instr_struct(&false_c3_30129, 3, 0);
  instr_struct(&false_c3_30130, 3, 0);
  instr_struct(&Ascii_c16_30131, 16, 8,
    false_c3_30123, true_c2_30124, true_c2_30125, false_c3_30126,
    true_c2_30127, true_c2_30128, false_c3_30129, false_c3_30130);
  instr_struct(&false_c3_30132, 3, 0);
  instr_struct(&true_c2_30133, 2, 0);
  instr_struct(&true_c2_30134, 2, 0);
  instr_struct(&false_c3_30135, 3, 0);
  instr_struct(&true_c2_30136, 2, 0);
  instr_struct(&true_c2_30137, 2, 0);
  instr_struct(&false_c3_30138, 3, 0);
  instr_struct(&false_c3_30139, 3, 0);
  instr_struct(&Ascii_c16_30140, 16, 8,
    false_c3_30132, true_c2_30133, true_c2_30134, false_c3_30135,
    true_c2_30136, true_c2_30137, false_c3_30138, false_c3_30139);
  instr_struct(&false_c3_30141, 3, 0);
  instr_struct(&true_c2_30142, 2, 0);
  instr_struct(&true_c2_30143, 2, 0);
  instr_struct(&false_c3_30144, 3, 0);
  instr_struct(&true_c2_30145, 2, 0);
  instr_struct(&true_c2_30146, 2, 0);
  instr_struct(&true_c2_30147, 2, 0);
  instr_struct(&true_c2_30148, 2, 0);
  instr_struct(&Ascii_c16_30149, 16, 8,
    false_c3_30141, true_c2_30142, true_c2_30143, false_c3_30144,
    true_c2_30145, true_c2_30146, true_c2_30147, true_c2_30148);
  instr_struct(&false_c3_30150, 3, 0);
  instr_struct(&false_c3_30151, 3, 0);
  instr_struct(&true_c2_30152, 2, 0);
  instr_struct(&false_c3_30153, 3, 0);
  instr_struct(&false_c3_30154, 3, 0);
  instr_struct(&false_c3_30155, 3, 0);
  instr_struct(&false_c3_30156, 3, 0);
  instr_struct(&false_c3_30157, 3, 0);
  instr_struct(&Ascii_c16_30158, 16, 8,
    false_c3_30150, false_c3_30151, true_c2_30152, false_c3_30153,
    false_c3_30154, false_c3_30155, false_c3_30156, false_c3_30157);
  instr_struct(&EmptyString_c17_30159, 17, 0);
  instr_struct(&String_c18_30160, 18, 2,
    Ascii_c16_30158, EmptyString_c17_30159);
  instr_struct(&String_c18_30161, 18, 2,
    Ascii_c16_30149, String_c18_30160);
  instr_struct(&String_c18_30162, 18, 2,
    Ascii_c16_30140, String_c18_30161);
  instr_struct(&String_c18_30163, 18, 2,
    Ascii_c16_30131, String_c18_30162);
  instr_struct(&String_c18_30164, 18, 2,
    Ascii_c16_30122, String_c18_30163);
  instr_struct(&String_c18_30165, 18, 2,
    Ascii_c16_30113, String_c18_30164);
  instr_call(&tmp_30166, tmp_30104, String_c18_30165);
  instr_call(&tmp_30167, tmp_30166, 0);
  instr_call(&tmp_30168, clo_30103, tmp_30167);
  instr_mov(&main_180, tmp_30168);
  return 0;
}
