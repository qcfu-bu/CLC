#include "runtime.h"

clc_ptr lam_29771(clc_ptr _29770, clc_env env)
{
  
  
  return _29770;
}

clc_ptr lam_29779(clc_ptr _29775, clc_env env)
{
  clc_ptr succ_c5_29778; clc_ptr tmp_29776; clc_ptr tmp_29777;
  instr_call(&tmp_29776, env[3], env[2]);
  instr_call(&tmp_29777, tmp_29776, _29775);
  instr_struct(&succ_c5_29778, 5, 1,
    tmp_29777);
  return succ_c5_29778;
}

clc_ptr addn_29781(clc_ptr _29767, clc_env env)
{
  clc_ptr _29773; clc_ptr case_29768; clc_ptr clo_29772; clc_ptr clo_29780;
  switch(((clc_node)_29767)->tag){
    case 4:
      instr_clo(&clo_29772, &lam_29771, 2, env, 1, _29767);
      instr_mov(&case_29768, clo_29772);
      break;
    case 5:
      instr_mov(&_29773, ((clc_node)_29767)->data[0]);
      instr_clo(&clo_29780, &lam_29779, 2, env, 2, _29767, _29773);
      instr_mov(&case_29768, clo_29780);
      break;}
  return case_29768;
}

clc_ptr lam_29789(clc_ptr _29787, clc_env env)
{
  clc_ptr zero_c4_29788;
  instr_struct(&zero_c4_29788, 4, 0);
  return zero_c4_29788;
}

clc_ptr lam_29799(clc_ptr _29793, clc_env env)
{
  clc_ptr _29796; clc_ptr case_29794; clc_ptr succ_c5_29795;
  clc_ptr tmp_29797; clc_ptr tmp_29798;
  switch(((clc_node)_29793)->tag){
    case 4:
      instr_struct(&succ_c5_29795, 5, 1,
        env[2]);
      instr_mov(&case_29794, succ_c5_29795);
      break;
    case 5:
      instr_mov(&_29796, ((clc_node)_29793)->data[0]);
      instr_call(&tmp_29797, env[3], env[2]);
      instr_call(&tmp_29798, tmp_29797, _29796);
      instr_mov(&case_29794, tmp_29798);
      break;}
  return case_29794;
}

clc_ptr subn_29801(clc_ptr _29784, clc_env env)
{
  clc_ptr _29791; clc_ptr case_29785; clc_ptr clo_29790; clc_ptr clo_29800;
  switch(((clc_node)_29784)->tag){
    case 4:
      instr_clo(&clo_29790, &lam_29789, 3, env, 1, _29784);
      instr_mov(&case_29785, clo_29790);
      break;
    case 5:
      instr_mov(&_29791, ((clc_node)_29784)->data[0]);
      instr_clo(&clo_29800, &lam_29799, 3, env, 2, _29784, _29791);
      instr_mov(&case_29785, clo_29800);
      break;}
  return case_29785;
}

clc_ptr lam_29808(clc_ptr _29807, clc_env env)
{
  
  
  return _29807;
}

clc_ptr lam_29817(clc_ptr _29813, clc_env env)
{
  clc_ptr String_c18_29816; clc_ptr tmp_29814; clc_ptr tmp_29815;
  instr_call(&tmp_29814, env[4], env[3]);
  instr_call(&tmp_29815, tmp_29814, _29813);
  instr_struct(&String_c18_29816, 18, 2,
    env[2], tmp_29815);
  return String_c18_29816;
}

clc_ptr cat_29819(clc_ptr _29804, clc_env env)
{
  clc_ptr _29810; clc_ptr _29811; clc_ptr case_29805; clc_ptr clo_29809;
  clc_ptr clo_29818;
  switch(((clc_node)_29804)->tag){
    case 17:
      instr_clo(&clo_29809, &lam_29808, 4, env, 1, _29804);
      instr_mov(&case_29805, clo_29809);
      break;
    case 18:
      instr_mov(&_29810, ((clc_node)_29804)->data[0]);
      instr_mov(&_29811, ((clc_node)_29804)->data[1]);
      instr_clo(&clo_29818, &lam_29817, 4, env, 3, _29804, _29810, _29811);
      instr_mov(&case_29805, clo_29818);
      break;}
  return case_29805;
}

clc_ptr strlen_29829(clc_ptr _29822, clc_env env)
{
  clc_ptr _29825; clc_ptr _29826; clc_ptr case_29823; clc_ptr succ_c5_29828;
  clc_ptr tmp_29827; clc_ptr zero_c4_29824;
  switch(((clc_node)_29822)->tag){
    case 17:
      instr_struct(&zero_c4_29824, 4, 0);
      instr_mov(&case_29823, zero_c4_29824);
      break;
    case 18:
      instr_mov(&_29825, ((clc_node)_29822)->data[0]);
      instr_mov(&_29826, ((clc_node)_29822)->data[1]);
      instr_call(&tmp_29827, env[0], _29826);
      instr_struct(&succ_c5_29828, 5, 1,
        tmp_29827);
      instr_mov(&case_29823, succ_c5_29828);
      break;}
  return case_29823;
}

clc_ptr lam_29835(clc_ptr _29834, clc_env env)
{
  
  
  return 0;
}

clc_ptr lt_29837(clc_ptr _29832, clc_env env)
{
  clc_ptr clo_29836;
  instr_clo(&clo_29836, &lam_29835, 6, env, 1, _29832);
  return clo_29836;
}

clc_ptr stdin_rec_29842(clc_ptr _29840, clc_env env)
{
  clc_ptr case_29841;
  switch(((clc_node)_29840)->tag){
    case 1: instr_mov(&case_29841, 0);
            break;}
  return case_29841;
}

clc_ptr stdout_rec_29847(clc_ptr _29845, clc_env env)
{
  clc_ptr case_29846;
  switch(((clc_node)_29845)->tag){
    case 1: instr_mov(&case_29846, 0);
            break;}
  return case_29846;
}

clc_ptr stderr_rec_29852(clc_ptr _29850, clc_env env)
{
  clc_ptr case_29851;
  switch(((clc_node)_29850)->tag){
    case 1: instr_mov(&case_29851, 0);
            break;}
  return case_29851;
}

clc_ptr readline_29866(clc_ptr _29861, clc_env env)
{
  clc_ptr recv_struct_29865; clc_ptr send_clo_29862; clc_ptr tmp_29864;
  clc_ptr true_c2_29863;
  instr_send(&send_clo_29862, _29861);
  instr_struct(&true_c2_29863, 2, 0);
  instr_call(&tmp_29864, send_clo_29862, true_c2_29863);
  instr_recv(&recv_struct_29865, tmp_29864, 13);
  return recv_struct_29865;
}

clc_ptr close_in_29874(clc_ptr _29869, clc_env env)
{
  clc_ptr false_c3_29872; clc_ptr send_clo_29871; clc_ptr tmp_29873;
  clc_ptr unit_struct_29870;
  instr_send(&send_clo_29871, _29869);
  instr_struct(&false_c3_29872, 3, 0);
  instr_call(&tmp_29873, send_clo_29871, false_c3_29872);
  instr_struct(&unit_struct_29870, 1, 0);
  return unit_struct_29870;
}

clc_ptr lam_29885(clc_ptr _29879, clc_env env)
{
  clc_ptr send_clo_29880; clc_ptr send_clo_29883; clc_ptr tmp_29882;
  clc_ptr tmp_29884; clc_ptr true_c2_29881;
  instr_send(&send_clo_29880, env[1]);
  instr_struct(&true_c2_29881, 2, 0);
  instr_call(&tmp_29882, send_clo_29880, true_c2_29881);
  instr_send(&send_clo_29883, tmp_29882);
  instr_call(&tmp_29884, send_clo_29883, _29879);
  return tmp_29884;
}

clc_ptr printline_29887(clc_ptr _29877, clc_env env)
{
  clc_ptr clo_29886;
  instr_clo(&clo_29886, &lam_29885, 15, env, 1, _29877);
  return clo_29886;
}

clc_ptr close_out_29895(clc_ptr _29890, clc_env env)
{
  clc_ptr false_c3_29893; clc_ptr send_clo_29892; clc_ptr tmp_29894;
  clc_ptr unit_struct_29891;
  instr_send(&send_clo_29892, _29890);
  instr_struct(&false_c3_29893, 3, 0);
  instr_call(&tmp_29894, send_clo_29892, false_c3_29893);
  instr_struct(&unit_struct_29891, 1, 0);
  return unit_struct_29891;
}

clc_ptr lam_29906(clc_ptr _29900, clc_env env)
{
  clc_ptr send_clo_29901; clc_ptr send_clo_29904; clc_ptr tmp_29903;
  clc_ptr tmp_29905; clc_ptr true_c2_29902;
  instr_send(&send_clo_29901, env[1]);
  instr_struct(&true_c2_29902, 2, 0);
  instr_call(&tmp_29903, send_clo_29901, true_c2_29902);
  instr_send(&send_clo_29904, tmp_29903);
  instr_call(&tmp_29905, send_clo_29904, _29900);
  return tmp_29905;
}

clc_ptr printerr_29908(clc_ptr _29898, clc_env env)
{
  clc_ptr clo_29907;
  instr_clo(&clo_29907, &lam_29906, 17, env, 1, _29898);
  return clo_29907;
}

clc_ptr close_err_29916(clc_ptr _29911, clc_env env)
{
  clc_ptr false_c3_29914; clc_ptr send_clo_29913; clc_ptr tmp_29915;
  clc_ptr unit_struct_29912;
  instr_send(&send_clo_29913, _29911);
  instr_struct(&false_c3_29914, 3, 0);
  instr_call(&tmp_29915, send_clo_29913, false_c3_29914);
  instr_struct(&unit_struct_29912, 1, 0);
  return unit_struct_29912;
}

clc_ptr ref_t_29920(clc_ptr _29919, clc_env env)
{
  
  
  return 0;
}

clc_ptr lam_29947(clc_ptr _29940, clc_env env)
{
  clc_ptr _29943; clc_ptr case_29941; clc_ptr tmp_29944; clc_ptr tmp_29945;
  clc_ptr tmp_29946; clc_ptr x_29942;
  switch(((clc_node)_29940)->tag){
    case 13:
      instr_mov(&x_29942, ((clc_node)_29940)->data[0]);
      instr_mov(&_29943, ((clc_node)_29940)->data[1]);
      instr_call(&tmp_29944, env[10], env[9]);
      instr_call(&tmp_29945, tmp_29944, x_29942);
      instr_call(&tmp_29946, tmp_29945, _29943);
      instr_mov(&case_29941, tmp_29946);
      break;}
  return case_29941;
}

clc_ptr lam_29952(clc_ptr _29929, clc_env env)
{
  clc_ptr _29932; clc_ptr case_29930; clc_ptr case_29933; clc_ptr clo_29948;
  clc_ptr recv_struct_29949; clc_ptr send_clo_29936; clc_ptr tmp_29934;
  clc_ptr tmp_29935; clc_ptr tmp_29937; clc_ptr tmp_29938; clc_ptr tmp_29950;
  clc_ptr unit_struct_29951; clc_ptr x_29931;
  switch(((clc_node)_29929)->tag){
    case 13:
      instr_mov(&x_29931, ((clc_node)_29929)->data[0]);
      instr_mov(&_29932, ((clc_node)_29929)->data[1]);
      switch(((clc_node)x_29931)->tag){
        case 22:
          instr_call(&tmp_29934, env[6], env[5]);
          instr_call(&tmp_29935, tmp_29934, env[3]);
          instr_send(&send_clo_29936, _29932);
          instr_call(&tmp_29937, send_clo_29936, env[3]);
          instr_call(&tmp_29938, tmp_29935, tmp_29937);
          instr_mov(&case_29933, tmp_29938);
          break;
        case 23:
          instr_clo(&clo_29948, &lam_29947, 26, env, 3,
            _29929, x_29931, _29932);
          instr_recv(&recv_struct_29949, _29932, 13);
          instr_call(&tmp_29950, clo_29948, recv_struct_29949);
          instr_mov(&case_29933, tmp_29950);
          break;
        case 24:
          instr_struct(&unit_struct_29951, 1, 0);
          instr_mov(&case_29933, unit_struct_29951);
          break;}
      instr_mov(&case_29930, case_29933);
      break;}
  return case_29930;
}

clc_ptr lam_29956(clc_ptr _29927, clc_env env)
{
  clc_ptr clo_29953; clc_ptr recv_struct_29954; clc_ptr tmp_29955;
  instr_clo(&clo_29953, &lam_29952, 24, env, 1, _29927);
  instr_recv(&recv_struct_29954, _29927, 13);
  instr_call(&tmp_29955, clo_29953, recv_struct_29954);
  return tmp_29955;
}

clc_ptr lam_29958(clc_ptr _29925, clc_env env)
{
  clc_ptr clo_29957;
  instr_clo(&clo_29957, &lam_29956, 22, env, 1, _29925);
  return clo_29957;
}

clc_ptr ref_handler_29960(clc_ptr A_29923, clc_env env)
{
  clc_ptr clo_29959;
  instr_clo(&clo_29959, &lam_29958, 20, env, 1, A_29923);
  return clo_29959;
}

clc_ptr fork_proc_29973(clc_env env)
{
  clc_ptr tmp_29969; clc_ptr tmp_29970; clc_ptr tmp_29971;
  instr_call(&tmp_29969, env[7], env[5]);
  instr_call(&tmp_29970, tmp_29969, env[3]);
  instr_call(&tmp_29971, tmp_29970, env[0]);
  return tmp_29971;
}

clc_ptr lam_29974(clc_ptr _29967, clc_env env)
{
  clc_ptr fork_res_29972;
  instr_open(&fork_res_29972, &fork_proc_29973, _29967, 25, env, 1,
    _29967);
  return fork_res_29972;
}

clc_ptr lam_29976(clc_ptr _29965, clc_env env)
{
  clc_ptr clo_29975;
  instr_clo(&clo_29975, &lam_29974, 23, env, 1, _29965);
  return clo_29975;
}

clc_ptr mk_ref_29978(clc_ptr A_29963, clc_env env)
{
  clc_ptr clo_29977;
  instr_clo(&clo_29977, &lam_29976, 21, env, 1, A_29963);
  return clo_29977;
}

clc_ptr lam_29991(clc_ptr _29985, clc_env env)
{
  clc_ptr SET_c23_29987; clc_ptr send_clo_29986; clc_ptr send_clo_29989;
  clc_ptr tmp_29988; clc_ptr tmp_29990;
  instr_send(&send_clo_29986, _29985);
  instr_struct(&SET_c23_29987, 23, 0);
  instr_call(&tmp_29988, send_clo_29986, SET_c23_29987);
  instr_send(&send_clo_29989, tmp_29988);
  instr_call(&tmp_29990, send_clo_29989, env[1]);
  return tmp_29990;
}

clc_ptr lam_29993(clc_ptr _29983, clc_env env)
{
  clc_ptr clo_29992;
  instr_clo(&clo_29992, &lam_29991, 24, env, 1, _29983);
  return clo_29992;
}

clc_ptr set_ref_29995(clc_ptr A_29981, clc_env env)
{
  clc_ptr clo_29994;
  instr_clo(&clo_29994, &lam_29993, 22, env, 1, A_29981);
  return clo_29994;
}

clc_ptr lam_30005(clc_ptr _30000, clc_env env)
{
  clc_ptr GET_c22_30002; clc_ptr recv_struct_30004; clc_ptr send_clo_30001;
  clc_ptr tmp_30003;
  instr_send(&send_clo_30001, _30000);
  instr_struct(&GET_c22_30002, 22, 0);
  instr_call(&tmp_30003, send_clo_30001, GET_c22_30002);
  instr_recv(&recv_struct_30004, tmp_30003, 13);
  return recv_struct_30004;
}

clc_ptr get_ref_30007(clc_ptr A_29998, clc_env env)
{
  clc_ptr clo_30006;
  instr_clo(&clo_30006, &lam_30005, 23, env, 1, A_29998);
  return clo_30006;
}

clc_ptr lam_30017(clc_ptr _30012, clc_env env)
{
  clc_ptr FREE_c24_30015; clc_ptr send_clo_30014; clc_ptr tmp_30016;
  clc_ptr unit_struct_30013;
  instr_send(&send_clo_30014, _30012);
  instr_struct(&FREE_c24_30015, 24, 0);
  instr_call(&tmp_30016, send_clo_30014, FREE_c24_30015);
  instr_close(&unit_struct_30013, tmp_30016);
  return unit_struct_30013;
}

clc_ptr free_ref_30019(clc_ptr A_30010, clc_env env)
{
  clc_ptr clo_30018;
  instr_clo(&clo_30018, &lam_30017, 24, env, 1, A_30010);
  return clo_30018;
}

clc_ptr lam_30072(clc_ptr _30070, clc_env env)
{
  clc_ptr case_30071;
  switch(((clc_node)_30070)->tag){
    case 1: instr_mov(&case_30071, env[21]);
            break;}
  return case_30071;
}

clc_ptr lam_30077(clc_ptr _30067, clc_env env)
{
  clc_ptr case_30068; clc_ptr clo_30073; clc_ptr tmp_30074;
  clc_ptr tmp_30075; clc_ptr tmp_30076;
  switch(((clc_node)_30067)->tag){
    case 1:
      instr_clo(&clo_30073, &lam_30072, 47, env, 1, _30067);
      instr_call(&tmp_30074, env[23], 0);
      instr_call(&tmp_30075, tmp_30074, env[4]);
      instr_call(&tmp_30076, clo_30073, tmp_30075);
      instr_mov(&case_30068, tmp_30076);
      break;}
  return case_30068;
}

clc_ptr lam_30081(clc_ptr _30044, clc_env env)
{
  clc_ptr _30047; clc_ptr Ascii_c16_30061; clc_ptr EmptyString_c17_30062;
  clc_ptr String_c18_30063; clc_ptr case_30045; clc_ptr clo_30078;
  clc_ptr false_c3_30053; clc_ptr false_c3_30054; clc_ptr false_c3_30055;
  clc_ptr false_c3_30056; clc_ptr false_c3_30058; clc_ptr false_c3_30060;
  clc_ptr stdout_30048; clc_ptr tmp_30049; clc_ptr tmp_30050;
  clc_ptr tmp_30051; clc_ptr tmp_30052; clc_ptr tmp_30064; clc_ptr tmp_30065;
  clc_ptr tmp_30079; clc_ptr tmp_30080; clc_ptr true_c2_30057;
  clc_ptr true_c2_30059; clc_ptr x_30046;
  switch(((clc_node)_30044)->tag){
    case 13:
      instr_mov(&x_30046, ((clc_node)_30044)->data[0]);
      instr_mov(&_30047, ((clc_node)_30044)->data[1]);
      instr_call(&tmp_30049, env[27], env[17]);
      instr_call(&tmp_30050, env[38], env[9]);
      instr_call(&tmp_30051, tmp_30050, x_30046);
      instr_call(&tmp_30052, env[38], tmp_30051);
      instr_struct(&false_c3_30053, 3, 0);
      instr_struct(&false_c3_30054, 3, 0);
      instr_struct(&false_c3_30055, 3, 0);
      instr_struct(&false_c3_30056, 3, 0);
      instr_struct(&true_c2_30057, 2, 0);
      instr_struct(&false_c3_30058, 3, 0);
      instr_struct(&true_c2_30059, 2, 0);
      instr_struct(&false_c3_30060, 3, 0);
      instr_struct(&Ascii_c16_30061, 16, 8,
        false_c3_30053, false_c3_30054, false_c3_30055, false_c3_30056,
        true_c2_30057, false_c3_30058, true_c2_30059, false_c3_30060);
      instr_struct(&EmptyString_c17_30062, 17, 0);
      instr_struct(&String_c18_30063, 18, 2,
        Ascii_c16_30061, EmptyString_c17_30062);
      instr_call(&tmp_30064, tmp_30052, String_c18_30063);
      instr_call(&tmp_30065, tmp_30049, tmp_30064);
      instr_mov(&stdout_30048, tmp_30065);
      instr_clo(&clo_30078, &lam_30077, 42, env, 4,
        stdout_30048, _30044, x_30046, _30047);
      instr_call(&tmp_30079, env[26], stdout_30048);
      instr_call(&tmp_30080, clo_30078, tmp_30079);
      instr_mov(&case_30045, tmp_30080);
      break;}
  return case_30045;
}

clc_ptr lam_30086(clc_ptr _30037, clc_env env)
{
  clc_ptr case_30038; clc_ptr clo_30082; clc_ptr ref_30039;
  clc_ptr tmp_30040; clc_ptr tmp_30041; clc_ptr tmp_30042; clc_ptr tmp_30083;
  clc_ptr tmp_30084; clc_ptr tmp_30085;
  switch(((clc_node)_30037)->tag){
    case 1:
      instr_call(&tmp_30040, env[17], 0);
      instr_call(&tmp_30041, tmp_30040, env[2]);
      instr_call(&tmp_30042, tmp_30041, env[7]);
      instr_mov(&ref_30039, tmp_30042);
      instr_clo(&clo_30082, &lam_30081, 39, env, 2, ref_30039, _30037);
      instr_call(&tmp_30083, env[16], 0);
      instr_call(&tmp_30084, tmp_30083, ref_30039);
      instr_call(&tmp_30085, clo_30082, tmp_30084);
      instr_mov(&case_30038, tmp_30085);
      break;}
  return case_30038;
}

clc_ptr lam_30090(clc_ptr _30032, clc_env env)
{
  clc_ptr _30035; clc_ptr case_30033; clc_ptr clo_30087; clc_ptr tmp_30088;
  clc_ptr tmp_30089; clc_ptr x_30034;
  switch(((clc_node)_30032)->tag){
    case 13:
      instr_mov(&x_30034, ((clc_node)_30032)->data[0]);
      instr_mov(&_30035, ((clc_node)_30032)->data[1]);
      instr_clo(&clo_30087, &lam_30086, 35, env, 3, _30032, x_30034, _30035);
      instr_call(&tmp_30088, env[21], _30035);
      instr_call(&tmp_30089, clo_30087, tmp_30088);
      instr_mov(&case_30033, tmp_30089);
      break;}
  return case_30033;
}

clc_ptr lam_30094(clc_ptr _30027, clc_env env)
{
  clc_ptr _30030; clc_ptr case_30028; clc_ptr clo_30091; clc_ptr tmp_30092;
  clc_ptr tmp_30093; clc_ptr x_30029;
  switch(((clc_node)_30027)->tag){
    case 13:
      instr_mov(&x_30029, ((clc_node)_30027)->data[0]);
      instr_mov(&_30030, ((clc_node)_30027)->data[1]);
      instr_clo(&clo_30091, &lam_30090, 31, env, 3, _30027, x_30029, _30030);
      instr_call(&tmp_30092, env[18], env[5]);
      instr_call(&tmp_30093, clo_30091, tmp_30092);
      instr_mov(&case_30028, tmp_30093);
      break;}
  return case_30028;
}

clc_ptr lam_30099(clc_ptr _30022, clc_env env)
{
  clc_ptr _30024; clc_ptr _30025; clc_ptr case_30023; clc_ptr clo_30095;
  clc_ptr tmp_30096; clc_ptr tmp_30097; clc_ptr tmp_30098;
  switch(((clc_node)_30022)->tag){
    case 14:
      instr_mov(&_30024, ((clc_node)_30022)->data[0]);
      instr_mov(&_30025, ((clc_node)_30022)->data[1]);
      instr_clo(&clo_30095, &lam_30094, 27, env, 3, _30022, _30024, _30025);
      instr_call(&tmp_30096, env[4], 0);
      instr_call(&tmp_30097, tmp_30096, _30024);
      instr_call(&tmp_30098, clo_30095, tmp_30097);
      instr_mov(&case_30023, tmp_30098);
      break;}
  return case_30023;
}

int main()
{
  clc_ptr Ascii_c16_30110; clc_ptr Ascii_c16_30119; clc_ptr Ascii_c16_30128;
  clc_ptr Ascii_c16_30137; clc_ptr Ascii_c16_30146; clc_ptr Ascii_c16_30155;
  clc_ptr EmptyString_c17_30156; clc_ptr String_c18_30157;
  clc_ptr String_c18_30158; clc_ptr String_c18_30159;
  clc_ptr String_c18_30160; clc_ptr String_c18_30161;
  clc_ptr String_c18_30162; clc_ptr addn_3; clc_ptr addn_29782;
  clc_ptr cat_67; clc_ptr cat_29820; clc_ptr clo_30100;
  clc_ptr close_err_130; clc_ptr close_err_29917; clc_ptr close_in_114;
  clc_ptr close_in_29875; clc_ptr close_out_122; clc_ptr close_out_29896;
  clc_ptr false_c3_30102; clc_ptr false_c3_30105; clc_ptr false_c3_30107;
  clc_ptr false_c3_30108; clc_ptr false_c3_30109; clc_ptr false_c3_30111;
  clc_ptr false_c3_30114; clc_ptr false_c3_30115; clc_ptr false_c3_30117;
  clc_ptr false_c3_30120; clc_ptr false_c3_30123; clc_ptr false_c3_30126;
  clc_ptr false_c3_30127; clc_ptr false_c3_30129; clc_ptr false_c3_30132;
  clc_ptr false_c3_30135; clc_ptr false_c3_30136; clc_ptr false_c3_30138;
  clc_ptr false_c3_30141; clc_ptr false_c3_30147; clc_ptr false_c3_30148;
  clc_ptr false_c3_30150; clc_ptr false_c3_30151; clc_ptr false_c3_30152;
  clc_ptr false_c3_30153; clc_ptr false_c3_30154; clc_ptr free_ref_173;
  clc_ptr free_ref_30020; clc_ptr get_ref_166; clc_ptr get_ref_30008;
  clc_ptr lt_84; clc_ptr lt_29838; clc_ptr main_180; clc_ptr mk_ref_151;
  clc_ptr mk_ref_29979; clc_ptr printerr_125; clc_ptr printerr_29909;
  clc_ptr printline_117; clc_ptr printline_29888; clc_ptr readline_109;
  clc_ptr readline_29867; clc_ptr ref_handler_139; clc_ptr ref_handler_29961;
  clc_ptr ref_t_133; clc_ptr ref_t_29921; clc_ptr set_ref_159;
  clc_ptr set_ref_29996; clc_ptr stderr_rec_102; clc_ptr stderr_rec_29853;
  clc_ptr stderr_t_108; clc_ptr stdin_179; clc_ptr stdin_rec_94;
  clc_ptr stdin_rec_29843; clc_ptr stdin_t_106; clc_ptr stdout_178;
  clc_ptr stdout_rec_98; clc_ptr stdout_rec_29848; clc_ptr stdout_t_107;
  clc_ptr strlen_74; clc_ptr strlen_29830; clc_ptr subn_9;
  clc_ptr subn_29802; clc_ptr tmp_29855; clc_ptr tmp_29857;
  clc_ptr tmp_29859; clc_ptr tmp_30101; clc_ptr tmp_30163; clc_ptr tmp_30164;
  clc_ptr tmp_30165; clc_ptr true_c2_30103; clc_ptr true_c2_30104;
  clc_ptr true_c2_30106; clc_ptr true_c2_30112; clc_ptr true_c2_30113;
  clc_ptr true_c2_30116; clc_ptr true_c2_30118; clc_ptr true_c2_30121;
  clc_ptr true_c2_30122; clc_ptr true_c2_30124; clc_ptr true_c2_30125;
  clc_ptr true_c2_30130; clc_ptr true_c2_30131; clc_ptr true_c2_30133;
  clc_ptr true_c2_30134; clc_ptr true_c2_30139; clc_ptr true_c2_30140;
  clc_ptr true_c2_30142; clc_ptr true_c2_30143; clc_ptr true_c2_30144;
  clc_ptr true_c2_30145; clc_ptr true_c2_30149; clc_ptr tt_c1_29854;
  clc_ptr tt_c1_29856; clc_ptr tt_c1_29858;
  clc_env env = 0;
  instr_init();
  instr_clo(&addn_29782, &addn_29781, 0, env, 1, 0);
  instr_mov(&addn_3, addn_29782);
  instr_clo(&subn_29802, &subn_29801, 0, env, 2, addn_3, 0);
  instr_mov(&subn_9, subn_29802);
  instr_clo(&cat_29820, &cat_29819, 0, env, 3, subn_9, addn_3, 0);
  instr_mov(&cat_67, cat_29820);
  instr_clo(&strlen_29830, &strlen_29829, 0, env, 4,
    cat_67, subn_9, addn_3, 0);
  instr_mov(&strlen_74, strlen_29830);
  instr_clo(&lt_29838, &lt_29837, 0, env, 5,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&lt_84, lt_29838);
  instr_clo(&stdin_rec_29843, &stdin_rec_29842, 0, env, 6,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdin_rec_94, stdin_rec_29843);
  instr_clo(&stdout_rec_29848, &stdout_rec_29847, 0, env, 7,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdout_rec_98, stdout_rec_29848);
  instr_clo(&stderr_rec_29853, &stderr_rec_29852, 0, env, 8,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stderr_rec_102, stderr_rec_29853);
  instr_struct(&tt_c1_29854, 1, 0);
  instr_call(&tmp_29855, stdin_rec_94, tt_c1_29854);
  instr_mov(&stdin_t_106, tmp_29855);
  instr_struct(&tt_c1_29856, 1, 0);
  instr_call(&tmp_29857, stdout_rec_98, tt_c1_29856);
  instr_mov(&stdout_t_107, tmp_29857);
  instr_struct(&tt_c1_29858, 1, 0);
  instr_call(&tmp_29859, stderr_rec_102, tt_c1_29858);
  instr_mov(&stderr_t_108, tmp_29859);
  instr_clo(&readline_29867, &readline_29866, 0, env, 12,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&readline_109, readline_29867);
  instr_clo(&close_in_29875, &close_in_29874, 0, env, 13,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_in_114, close_in_29875);
  instr_clo(&printline_29888, &printline_29887, 0, env, 14,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&printline_117, printline_29888);
  instr_clo(&close_out_29896, &close_out_29895, 0, env, 15,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_out_122, close_out_29896);
  instr_clo(&printerr_29909, &printerr_29908, 0, env, 16,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&printerr_125, printerr_29909);
  instr_clo(&close_err_29917, &close_err_29916, 0, env, 17,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_err_130, close_err_29917);
  instr_clo(&ref_t_29921, &ref_t_29920, 0, env, 18,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&ref_t_133, ref_t_29921);
  instr_clo(&ref_handler_29961, &ref_handler_29960, 0, env, 19,
    ref_t_133, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&ref_handler_139, ref_handler_29961);
  instr_clo(&mk_ref_29979, &mk_ref_29978, 0, env, 20,
    ref_handler_139, ref_t_133, close_err_130, printerr_125, close_out_122,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&mk_ref_151, mk_ref_29979);
  instr_clo(&set_ref_29996, &set_ref_29995, 0, env, 21,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&set_ref_159, set_ref_29996);
  instr_clo(&get_ref_30008, &get_ref_30007, 0, env, 22,
    set_ref_159, mk_ref_151, ref_handler_139, ref_t_133, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&get_ref_166, get_ref_30008);
  instr_clo(&free_ref_30020, &free_ref_30019, 0, env, 23,
    get_ref_166, set_ref_159, mk_ref_151, ref_handler_139, ref_t_133,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&free_ref_173, free_ref_30020);
  instr_trg(&stdout_178, &proc_stdout);
  instr_trg(&stdin_179, &proc_stdin);
  instr_clo(&clo_30100, &lam_30099, 0, env, 26,
    stdin_179, stdout_178, free_ref_173, get_ref_166, set_ref_159,
    mk_ref_151, ref_handler_139, ref_t_133, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_call(&tmp_30101, mk_ref_151, 0);
  instr_struct(&false_c3_30102, 3, 0);
  instr_struct(&true_c2_30103, 2, 0);
  instr_struct(&true_c2_30104, 2, 0);
  instr_struct(&false_c3_30105, 3, 0);
  instr_struct(&true_c2_30106, 2, 0);
  instr_struct(&false_c3_30107, 3, 0);
  instr_struct(&false_c3_30108, 3, 0);
  instr_struct(&false_c3_30109, 3, 0);
  instr_struct(&Ascii_c16_30110, 16, 8,
    false_c3_30102, true_c2_30103, true_c2_30104, false_c3_30105,
    true_c2_30106, false_c3_30107, false_c3_30108, false_c3_30109);
  instr_struct(&false_c3_30111, 3, 0);
  instr_struct(&true_c2_30112, 2, 0);
  instr_struct(&true_c2_30113, 2, 0);
  instr_struct(&false_c3_30114, 3, 0);
  instr_struct(&false_c3_30115, 3, 0);
  instr_struct(&true_c2_30116, 2, 0);
  instr_struct(&false_c3_30117, 3, 0);
  instr_struct(&true_c2_30118, 2, 0);
  instr_struct(&Ascii_c16_30119, 16, 8,
    false_c3_30111, true_c2_30112, true_c2_30113, false_c3_30114,
    false_c3_30115, true_c2_30116, false_c3_30117, true_c2_30118);
  instr_struct(&false_c3_30120, 3, 0);
  instr_struct(&true_c2_30121, 2, 0);
  instr_struct(&true_c2_30122, 2, 0);
  instr_struct(&false_c3_30123, 3, 0);
  instr_struct(&true_c2_30124, 2, 0);
  instr_struct(&true_c2_30125, 2, 0);
  instr_struct(&false_c3_30126, 3, 0);
  instr_struct(&false_c3_30127, 3, 0);
  instr_struct(&Ascii_c16_30128, 16, 8,
    false_c3_30120, true_c2_30121, true_c2_30122, false_c3_30123,
    true_c2_30124, true_c2_30125, false_c3_30126, false_c3_30127);
  instr_struct(&false_c3_30129, 3, 0);
  instr_struct(&true_c2_30130, 2, 0);
  instr_struct(&true_c2_30131, 2, 0);
  instr_struct(&false_c3_30132, 3, 0);
  instr_struct(&true_c2_30133, 2, 0);
  instr_struct(&true_c2_30134, 2, 0);
  instr_struct(&false_c3_30135, 3, 0);
  instr_struct(&false_c3_30136, 3, 0);
  instr_struct(&Ascii_c16_30137, 16, 8,
    false_c3_30129, true_c2_30130, true_c2_30131, false_c3_30132,
    true_c2_30133, true_c2_30134, false_c3_30135, false_c3_30136);
  instr_struct(&false_c3_30138, 3, 0);
  instr_struct(&true_c2_30139, 2, 0);
  instr_struct(&true_c2_30140, 2, 0);
  instr_struct(&false_c3_30141, 3, 0);
  instr_struct(&true_c2_30142, 2, 0);
  instr_struct(&true_c2_30143, 2, 0);
  instr_struct(&true_c2_30144, 2, 0);
  instr_struct(&true_c2_30145, 2, 0);
  instr_struct(&Ascii_c16_30146, 16, 8,
    false_c3_30138, true_c2_30139, true_c2_30140, false_c3_30141,
    true_c2_30142, true_c2_30143, true_c2_30144, true_c2_30145);
  instr_struct(&false_c3_30147, 3, 0);
  instr_struct(&false_c3_30148, 3, 0);
  instr_struct(&true_c2_30149, 2, 0);
  instr_struct(&false_c3_30150, 3, 0);
  instr_struct(&false_c3_30151, 3, 0);
  instr_struct(&false_c3_30152, 3, 0);
  instr_struct(&false_c3_30153, 3, 0);
  instr_struct(&false_c3_30154, 3, 0);
  instr_struct(&Ascii_c16_30155, 16, 8,
    false_c3_30147, false_c3_30148, true_c2_30149, false_c3_30150,
    false_c3_30151, false_c3_30152, false_c3_30153, false_c3_30154);
  instr_struct(&EmptyString_c17_30156, 17, 0);
  instr_struct(&String_c18_30157, 18, 2,
    Ascii_c16_30155, EmptyString_c17_30156);
  instr_struct(&String_c18_30158, 18, 2,
    Ascii_c16_30146, String_c18_30157);
  instr_struct(&String_c18_30159, 18, 2,
    Ascii_c16_30137, String_c18_30158);
  instr_struct(&String_c18_30160, 18, 2,
    Ascii_c16_30128, String_c18_30159);
  instr_struct(&String_c18_30161, 18, 2,
    Ascii_c16_30119, String_c18_30160);
  instr_struct(&String_c18_30162, 18, 2,
    Ascii_c16_30110, String_c18_30161);
  instr_call(&tmp_30163, tmp_30101, String_c18_30162);
  instr_call(&tmp_30164, tmp_30163, 0);
  instr_call(&tmp_30165, clo_30100, tmp_30164);
  instr_mov(&main_180, tmp_30165);
  return 0;
}
