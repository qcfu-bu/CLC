#include "runtime.h"

clc_ptr lam_69913(clc_ptr _69912, clc_env env)
{
  
  
  return _69912;
}

clc_ptr lam_69921(clc_ptr _69917, clc_env env)
{
  clc_ptr succ_c5_69920; clc_ptr tmp_69918; clc_ptr tmp_69919;
  instr_call(&tmp_69918, env[3], env[2]);
  instr_call(&tmp_69919, tmp_69918, _69917);
  instr_struct(&succ_c5_69920, 5, 1,
    tmp_69919);
  return succ_c5_69920;
}

clc_ptr addn_69923(clc_ptr _69909, clc_env env)
{
  clc_ptr _69915; clc_ptr case_69910; clc_ptr clo_69914; clc_ptr clo_69922;
  switch(((clc_node)_69909)->tag){
    case 4:
      instr_clo(&clo_69914, &lam_69913, 4, 0, _69909, env[0], env[1]);
      instr_mov(&case_69910, clo_69914);
      break;
    case 5:
      instr_mov(&_69915, ((clc_node)_69909)->data[0]);
      instr_clo(&clo_69922, &lam_69921, 5,
        0, _69909, _69915, env[0], env[1]);
      instr_mov(&case_69910, clo_69922);
      break;}
  return case_69910;
}

clc_ptr lam_69931(clc_ptr _69929, clc_env env)
{
  clc_ptr zero_c4_69930;
  instr_struct(&zero_c4_69930, 4, 0);
  return zero_c4_69930;
}

clc_ptr lam_69941(clc_ptr _69935, clc_env env)
{
  clc_ptr _69938; clc_ptr case_69936; clc_ptr succ_c5_69937;
  clc_ptr tmp_69939; clc_ptr tmp_69940;
  switch(((clc_node)_69935)->tag){
    case 4:
      instr_struct(&succ_c5_69937, 5, 1,
        env[2]);
      instr_mov(&case_69936, succ_c5_69937);
      break;
    case 5:
      instr_mov(&_69938, ((clc_node)_69935)->data[0]);
      instr_call(&tmp_69939, env[3], env[2]);
      instr_call(&tmp_69940, tmp_69939, _69938);
      instr_mov(&case_69936, tmp_69940);
      break;}
  return case_69936;
}

clc_ptr subn_69943(clc_ptr _69926, clc_env env)
{
  clc_ptr _69933; clc_ptr case_69927; clc_ptr clo_69932; clc_ptr clo_69942;
  switch(((clc_node)_69926)->tag){
    case 4:
      instr_clo(&clo_69932, &lam_69931, 5,
        0, _69926, env[0], env[1], env[2]);
      instr_mov(&case_69927, clo_69932);
      break;
    case 5:
      instr_mov(&_69933, ((clc_node)_69926)->data[0]);
      instr_clo(&clo_69942, &lam_69941, 6,
        0, _69926, _69933, env[0], env[1], env[2]);
      instr_mov(&case_69927, clo_69942);
      break;}
  return case_69927;
}

clc_ptr lam_69950(clc_ptr _69949, clc_env env)
{
  
  
  return _69949;
}

clc_ptr lam_69959(clc_ptr _69955, clc_env env)
{
  clc_ptr String_c18_69958; clc_ptr tmp_69956; clc_ptr tmp_69957;
  instr_call(&tmp_69956, env[4], env[3]);
  instr_call(&tmp_69957, tmp_69956, _69955);
  instr_struct(&String_c18_69958, 18, 2,
    env[2], tmp_69957);
  return String_c18_69958;
}

clc_ptr cat_69961(clc_ptr _69946, clc_env env)
{
  clc_ptr _69952; clc_ptr _69953; clc_ptr case_69947; clc_ptr clo_69951;
  clc_ptr clo_69960;
  switch(((clc_node)_69946)->tag){
    case 17:
      instr_clo(&clo_69951, &lam_69950, 6,
        0, _69946, env[0], env[1], env[2], env[3]);
      instr_mov(&case_69947, clo_69951);
      break;
    case 18:
      instr_mov(&_69952, ((clc_node)_69946)->data[0]);
      instr_mov(&_69953, ((clc_node)_69946)->data[1]);
      instr_clo(&clo_69960, &lam_69959, 8,
        0, _69946, _69952, _69953, env[0], env[1], env[2], env[3]);
      instr_mov(&case_69947, clo_69960);
      break;}
  return case_69947;
}

clc_ptr strlen_69971(clc_ptr _69964, clc_env env)
{
  clc_ptr _69967; clc_ptr _69968; clc_ptr case_69965; clc_ptr succ_c5_69970;
  clc_ptr tmp_69969; clc_ptr zero_c4_69966;
  switch(((clc_node)_69964)->tag){
    case 17:
      instr_struct(&zero_c4_69966, 4, 0);
      instr_mov(&case_69965, zero_c4_69966);
      break;
    case 18:
      instr_mov(&_69967, ((clc_node)_69964)->data[0]);
      instr_mov(&_69968, ((clc_node)_69964)->data[1]);
      instr_call(&tmp_69969, env[0], _69968);
      instr_struct(&succ_c5_69970, 5, 1,
        tmp_69969);
      instr_mov(&case_69965, succ_c5_69970);
      break;}
  return case_69965;
}

clc_ptr lam_69977(clc_ptr _69976, clc_env env)
{
  
  
  return 0;
}

clc_ptr lt_69979(clc_ptr _69974, clc_env env)
{
  clc_ptr clo_69978;
  instr_clo(&clo_69978, &lam_69977, 8,
    0, _69974, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_69978;
}

clc_ptr stdin_rec_69984(clc_ptr _69982, clc_env env)
{
  clc_ptr case_69983;
  switch(((clc_node)_69982)->tag){
    case 1: instr_mov(&case_69983, 0);
            break;}
  return case_69983;
}

clc_ptr stdout_rec_69989(clc_ptr _69987, clc_env env)
{
  clc_ptr case_69988;
  switch(((clc_node)_69987)->tag){
    case 1: instr_mov(&case_69988, 0);
            break;}
  return case_69988;
}

clc_ptr stderr_rec_69994(clc_ptr _69992, clc_env env)
{
  clc_ptr case_69993;
  switch(((clc_node)_69992)->tag){
    case 1: instr_mov(&case_69993, 0);
            break;}
  return case_69993;
}

clc_ptr readline_70008(clc_ptr _70003, clc_env env)
{
  clc_ptr recv_struct_70007; clc_ptr send_clo_70004; clc_ptr tmp_70006;
  clc_ptr true_c2_70005;
  instr_send(&send_clo_70004, _70003);
  instr_struct(&true_c2_70005, 2, 0);
  instr_call(&tmp_70006, send_clo_70004, true_c2_70005);
  instr_recv(&recv_struct_70007, tmp_70006, 13);
  return recv_struct_70007;
}

clc_ptr close_in_70016(clc_ptr _70011, clc_env env)
{
  clc_ptr false_c3_70014; clc_ptr send_clo_70013; clc_ptr tmp_70015;
  clc_ptr unit_struct_70012;
  instr_send(&send_clo_70013, _70011);
  instr_struct(&false_c3_70014, 3, 0);
  instr_call(&tmp_70015, send_clo_70013, false_c3_70014);
  instr_struct(&unit_struct_70012, 1, 0);
  return unit_struct_70012;
}

clc_ptr lam_70027(clc_ptr _70021, clc_env env)
{
  clc_ptr send_clo_70022; clc_ptr send_clo_70025; clc_ptr tmp_70024;
  clc_ptr tmp_70026; clc_ptr true_c2_70023;
  instr_send(&send_clo_70022, env[1]);
  instr_struct(&true_c2_70023, 2, 0);
  instr_call(&tmp_70024, send_clo_70022, true_c2_70023);
  instr_send(&send_clo_70025, tmp_70024);
  instr_call(&tmp_70026, send_clo_70025, _70021);
  return tmp_70026;
}

clc_ptr printline_70029(clc_ptr _70019, clc_env env)
{
  clc_ptr clo_70028;
  instr_clo(&clo_70028, &lam_70027, 17,
    0, _70019, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_70028;
}

clc_ptr close_out_70037(clc_ptr _70032, clc_env env)
{
  clc_ptr false_c3_70035; clc_ptr send_clo_70034; clc_ptr tmp_70036;
  clc_ptr unit_struct_70033;
  instr_send(&send_clo_70034, _70032);
  instr_struct(&false_c3_70035, 3, 0);
  instr_call(&tmp_70036, send_clo_70034, false_c3_70035);
  instr_struct(&unit_struct_70033, 1, 0);
  return unit_struct_70033;
}

clc_ptr lam_70048(clc_ptr _70042, clc_env env)
{
  clc_ptr send_clo_70043; clc_ptr send_clo_70046; clc_ptr tmp_70045;
  clc_ptr tmp_70047; clc_ptr true_c2_70044;
  instr_send(&send_clo_70043, env[1]);
  instr_struct(&true_c2_70044, 2, 0);
  instr_call(&tmp_70045, send_clo_70043, true_c2_70044);
  instr_send(&send_clo_70046, tmp_70045);
  instr_call(&tmp_70047, send_clo_70046, _70042);
  return tmp_70047;
}

clc_ptr printerr_70050(clc_ptr _70040, clc_env env)
{
  clc_ptr clo_70049;
  instr_clo(&clo_70049, &lam_70048, 19,
    0, _70040, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16]);
  return clo_70049;
}

clc_ptr close_err_70058(clc_ptr _70053, clc_env env)
{
  clc_ptr false_c3_70056; clc_ptr send_clo_70055; clc_ptr tmp_70057;
  clc_ptr unit_struct_70054;
  instr_send(&send_clo_70055, _70053);
  instr_struct(&false_c3_70056, 3, 0);
  instr_call(&tmp_70057, send_clo_70055, false_c3_70056);
  instr_struct(&unit_struct_70054, 1, 0);
  return unit_struct_70054;
}

clc_ptr lam_70065(clc_ptr _70063, clc_env env)
{
  clc_ptr DocCons_c23_70064;
  instr_struct(&DocCons_c23_70064, 23, 2,
    env[1], _70063);
  return DocCons_c23_70064;
}

clc_ptr dcons_70067(clc_ptr _70061, clc_env env)
{
  clc_ptr clo_70066;
  instr_clo(&clo_70066, &lam_70065, 21,
    0, _70061, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18]);
  return clo_70066;
}

clc_ptr text_70073(clc_ptr _70071, clc_env env)
{
  clc_ptr DocText_c24_70072;
  instr_struct(&DocText_c24_70072, 24, 1,
    _70071);
  return DocText_c24_70072;
}

clc_ptr lam_70080(clc_ptr _70078, clc_env env)
{
  clc_ptr DocNest_c25_70079;
  instr_struct(&DocNest_c25_70079, 25, 2,
    env[1], _70078);
  return DocNest_c25_70079;
}

clc_ptr nest_70082(clc_ptr _70076, clc_env env)
{
  clc_ptr clo_70081;
  instr_clo(&clo_70081, &lam_70080, 24,
    0, _70076, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21]);
  return clo_70081;
}

clc_ptr breakWith_70099(clc_ptr _70097, clc_env env)
{
  clc_ptr DocBreak_c26_70098;
  instr_struct(&DocBreak_c26_70098, 26, 1,
    _70097);
  return DocBreak_c26_70098;
}

clc_ptr group_70104(clc_ptr _70102, clc_env env)
{
  clc_ptr DocGroup_c27_70103;
  instr_struct(&DocGroup_c27_70103, 27, 1,
    _70102);
  return DocGroup_c27_70103;
}

clc_ptr loop_70137(clc_ptr _70119, clc_env env)
{
  clc_ptr _70122; clc_ptr Ascii_c16_70131; clc_ptr EmptyString_c17_70121;
  clc_ptr EmptyString_c17_70132; clc_ptr String_c18_70133;
  clc_ptr case_70120; clc_ptr false_c3_70123; clc_ptr false_c3_70124;
  clc_ptr false_c3_70126; clc_ptr false_c3_70127; clc_ptr false_c3_70128;
  clc_ptr false_c3_70129; clc_ptr false_c3_70130; clc_ptr tmp_70134;
  clc_ptr tmp_70135; clc_ptr tmp_70136; clc_ptr true_c2_70125;
  switch(((clc_node)_70119)->tag){
    case 4:
      instr_struct(&EmptyString_c17_70121, 17, 0);
      instr_mov(&case_70120, EmptyString_c17_70121);
      break;
    case 5:
      instr_mov(&_70122, ((clc_node)_70119)->data[0]);
      instr_struct(&false_c3_70123, 3, 0);
      instr_struct(&false_c3_70124, 3, 0);
      instr_struct(&true_c2_70125, 2, 0);
      instr_struct(&false_c3_70126, 3, 0);
      instr_struct(&false_c3_70127, 3, 0);
      instr_struct(&false_c3_70128, 3, 0);
      instr_struct(&false_c3_70129, 3, 0);
      instr_struct(&false_c3_70130, 3, 0);
      instr_struct(&Ascii_c16_70131, 16, 8,
        false_c3_70123, false_c3_70124, true_c2_70125, false_c3_70126,
        false_c3_70127, false_c3_70128, false_c3_70129, false_c3_70130);
      instr_struct(&EmptyString_c17_70132, 17, 0);
      instr_struct(&String_c18_70133, 18, 2,
        Ascii_c16_70131, EmptyString_c17_70132);
      instr_call(&tmp_70134, env[26], String_c18_70133);
      instr_call(&tmp_70135, env[0], _70122);
      instr_call(&tmp_70136, tmp_70134, tmp_70135);
      instr_mov(&case_70120, tmp_70136);
      break;}
  return case_70120;
}

clc_ptr sdocToString_70156(clc_ptr _70107, clc_env env)
{
  clc_ptr _70110; clc_ptr _70111; clc_ptr _70115; clc_ptr _70116;
  clc_ptr Ascii_c16_70147; clc_ptr EmptyString_c17_70109;
  clc_ptr EmptyString_c17_70148; clc_ptr String_c18_70149;
  clc_ptr case_70108; clc_ptr false_c3_70139; clc_ptr false_c3_70140;
  clc_ptr false_c3_70141; clc_ptr false_c3_70142; clc_ptr false_c3_70144;
  clc_ptr false_c3_70146; clc_ptr loop_70117; clc_ptr loop_70138;
  clc_ptr tmp_70112; clc_ptr tmp_70113; clc_ptr tmp_70114; clc_ptr tmp_70150;
  clc_ptr tmp_70151; clc_ptr tmp_70152; clc_ptr tmp_70153; clc_ptr tmp_70154;
  clc_ptr tmp_70155; clc_ptr true_c2_70143; clc_ptr true_c2_70145;
  switch(((clc_node)_70107)->tag){
    case 28:
      instr_struct(&EmptyString_c17_70109, 17, 0);
      instr_mov(&case_70108, EmptyString_c17_70109);
      break;
    case 29:
      instr_mov(&_70110, ((clc_node)_70107)->data[0]);
      instr_mov(&_70111, ((clc_node)_70107)->data[1]);
      instr_call(&tmp_70112, env[22], _70110);
      instr_call(&tmp_70113, env[0], _70111);
      instr_call(&tmp_70114, tmp_70112, tmp_70113);
      instr_mov(&case_70108, tmp_70114);
      break;
    case 30:
      instr_mov(&_70115, ((clc_node)_70107)->data[0]);
      instr_mov(&_70116, ((clc_node)_70107)->data[1]);
      instr_clo(&loop_70138, &loop_70137, 30,
        0, _70107, _70115, _70116, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25]);
      instr_mov(&loop_70117, loop_70138);
      instr_struct(&false_c3_70139, 3, 0);
      instr_struct(&false_c3_70140, 3, 0);
      instr_struct(&false_c3_70141, 3, 0);
      instr_struct(&false_c3_70142, 3, 0);
      instr_struct(&true_c2_70143, 2, 0);
      instr_struct(&false_c3_70144, 3, 0);
      instr_struct(&true_c2_70145, 2, 0);
      instr_struct(&false_c3_70146, 3, 0);
      instr_struct(&Ascii_c16_70147, 16, 8,
        false_c3_70139, false_c3_70140, false_c3_70141, false_c3_70142,
        true_c2_70143, false_c3_70144, true_c2_70145, false_c3_70146);
      instr_struct(&EmptyString_c17_70148, 17, 0);
      instr_struct(&String_c18_70149, 18, 2,
        Ascii_c16_70147, EmptyString_c17_70148);
      instr_call(&tmp_70150, env[22], String_c18_70149);
      instr_call(&tmp_70151, loop_70117, _70115);
      instr_call(&tmp_70152, tmp_70150, tmp_70151);
      instr_call(&tmp_70153, env[22], tmp_70152);
      instr_call(&tmp_70154, env[0], _70116);
      instr_call(&tmp_70155, tmp_70153, tmp_70154);
      instr_mov(&case_70108, tmp_70155);
      break;}
  return case_70108;
}

clc_ptr lam_70164(clc_ptr _70162, clc_env env)
{
  clc_ptr false_c3_70163;
  instr_struct(&false_c3_70163, 3, 0);
  return false_c3_70163;
}

clc_ptr lam_70228(clc_ptr _70168, clc_env env)
{
  clc_ptr _70171; clc_ptr _70172; clc_ptr _70175; clc_ptr _70178;
  clc_ptr _70183; clc_ptr _70184; clc_ptr _70194; clc_ptr _70201;
  clc_ptr _70202; clc_ptr _70211; clc_ptr _70220; clc_ptr Flat_c31_70223;
  clc_ptr case_70169; clc_ptr case_70173; clc_ptr case_70176;
  clc_ptr case_70179; clc_ptr case_70212; clc_ptr cons_c9_70191;
  clc_ptr cons_c9_70192; clc_ptr cons_c9_70209; clc_ptr cons_c9_70226;
  clc_ptr ex_intro_c12_70187; clc_ptr ex_intro_c12_70188;
  clc_ptr ex_intro_c12_70189; clc_ptr ex_intro_c12_70190;
  clc_ptr ex_intro_c12_70207; clc_ptr ex_intro_c12_70208;
  clc_ptr ex_intro_c12_70224; clc_ptr ex_intro_c12_70225;
  clc_ptr succ_c5_70180; clc_ptr succ_c5_70185; clc_ptr succ_c5_70195;
  clc_ptr succ_c5_70203; clc_ptr succ_c5_70213; clc_ptr succ_c5_70221;
  clc_ptr tmp_70181; clc_ptr tmp_70182; clc_ptr tmp_70186; clc_ptr tmp_70193;
  clc_ptr tmp_70196; clc_ptr tmp_70197; clc_ptr tmp_70198; clc_ptr tmp_70199;
  clc_ptr tmp_70200; clc_ptr tmp_70204; clc_ptr tmp_70205; clc_ptr tmp_70206;
  clc_ptr tmp_70210; clc_ptr tmp_70214; clc_ptr tmp_70215; clc_ptr tmp_70216;
  clc_ptr tmp_70217; clc_ptr tmp_70218; clc_ptr tmp_70222; clc_ptr tmp_70227;
  clc_ptr true_c2_70170; clc_ptr true_c2_70219; clc_ptr x_70174;
  clc_ptr x_70177;
  switch(((clc_node)_70168)->tag){
    case 8:
      instr_struct(&true_c2_70170, 2, 0);
      instr_mov(&case_70169, true_c2_70170);
      break;
    case 9:
      instr_mov(&_70171, ((clc_node)_70168)->data[0]);
      instr_mov(&_70172, ((clc_node)_70168)->data[1]);
      switch(((clc_node)_70171)->tag){
        case 12:
          instr_mov(&x_70174, ((clc_node)_70171)->data[0]);
          instr_mov(&_70175, ((clc_node)_70171)->data[1]);
          switch(((clc_node)x_70174)->tag){
            case 12:
              instr_mov(&x_70177, ((clc_node)x_70174)->data[0]);
              instr_mov(&_70178, ((clc_node)x_70174)->data[1]);
              switch(((clc_node)_70175)->tag){
                case 22:
                  instr_struct(&succ_c5_70180, 5, 1,
                    env[2]);
                  instr_call(&tmp_70181, env[3], succ_c5_70180);
                  instr_call(&tmp_70182, tmp_70181, _70172);
                  instr_mov(&case_70179, tmp_70182);
                  break;
                case 23:
                  instr_mov(&_70183, ((clc_node)_70175)->data[0]);
                  instr_mov(&_70184, ((clc_node)_70175)->data[1]);
                  instr_struct(&succ_c5_70185, 5, 1,
                    env[2]);
                  instr_call(&tmp_70186, env[3], succ_c5_70185);
                  instr_struct(&ex_intro_c12_70187, 12, 2,
                    x_70177, _70178);
                  instr_struct(&ex_intro_c12_70188, 12, 2,
                    ex_intro_c12_70187, _70183);
                  instr_struct(&ex_intro_c12_70189, 12, 2,
                    x_70177, _70178);
                  instr_struct(&ex_intro_c12_70190, 12, 2,
                    ex_intro_c12_70189, _70184);
                  instr_struct(&cons_c9_70191, 9, 2,
                    ex_intro_c12_70190, _70172);
                  instr_struct(&cons_c9_70192, 9, 2,
                    ex_intro_c12_70188, cons_c9_70191);
                  instr_call(&tmp_70193, tmp_70186, cons_c9_70192);
                  instr_mov(&case_70179, tmp_70193);
                  break;
                case 24:
                  instr_mov(&_70194, ((clc_node)_70175)->data[0]);
                  instr_struct(&succ_c5_70195, 5, 1,
                    env[2]);
                  instr_call(&tmp_70196, env[27], succ_c5_70195);
                  instr_call(&tmp_70197, env[25], _70194);
                  instr_call(&tmp_70198, tmp_70196, tmp_70197);
                  instr_call(&tmp_70199, env[3], tmp_70198);
                  instr_call(&tmp_70200, tmp_70199, _70172);
                  instr_mov(&case_70179, tmp_70200);
                  break;
                case 25:
                  instr_mov(&_70201, ((clc_node)_70175)->data[0]);
                  instr_mov(&_70202, ((clc_node)_70175)->data[1]);
                  instr_struct(&succ_c5_70203, 5, 1,
                    env[2]);
                  instr_call(&tmp_70204, env[3], succ_c5_70203);
                  instr_call(&tmp_70205, env[28], x_70177);
                  instr_call(&tmp_70206, tmp_70205, _70201);
                  instr_struct(&ex_intro_c12_70207, 12, 2,
                    tmp_70206, _70178);
                  instr_struct(&ex_intro_c12_70208, 12, 2,
                    ex_intro_c12_70207, _70202);
                  instr_struct(&cons_c9_70209, 9, 2,
                    ex_intro_c12_70208, _70172);
                  instr_call(&tmp_70210, tmp_70204, cons_c9_70209);
                  instr_mov(&case_70179, tmp_70210);
                  break;
                case 26:
                  instr_mov(&_70211, ((clc_node)_70175)->data[0]);
                  switch(((clc_node)_70178)->tag){
                    case 31:
                      instr_struct(&succ_c5_70213, 5, 1,
                        env[2]);
                      instr_call(&tmp_70214, env[27], succ_c5_70213);
                      instr_call(&tmp_70215, env[25], _70211);
                      instr_call(&tmp_70216, tmp_70214, tmp_70215);
                      instr_call(&tmp_70217, env[3], tmp_70216);
                      instr_call(&tmp_70218, tmp_70217, _70172);
                      instr_mov(&case_70212, tmp_70218);
                      break;
                    case 32:
                      instr_struct(&true_c2_70219, 2, 0);
                      instr_mov(&case_70212, true_c2_70219);
                      break;}
                  instr_mov(&case_70179, case_70212);
                  break;
                case 27:
                  instr_mov(&_70220, ((clc_node)_70175)->data[0]);
                  instr_struct(&succ_c5_70221, 5, 1,
                    env[2]);
                  instr_call(&tmp_70222, env[3], succ_c5_70221);
                  instr_struct(&Flat_c31_70223, 31, 0);
                  instr_struct(&ex_intro_c12_70224, 12, 2,
                    x_70177, Flat_c31_70223);
                  instr_struct(&ex_intro_c12_70225, 12, 2,
                    ex_intro_c12_70224, _70220);
                  instr_struct(&cons_c9_70226, 9, 2,
                    ex_intro_c12_70225, _70172);
                  instr_call(&tmp_70227, tmp_70222, cons_c9_70226);
                  instr_mov(&case_70179, tmp_70227);
                  break;}
              instr_mov(&case_70176, case_70179);
              break;}
          instr_mov(&case_70173, case_70176);
          break;}
      instr_mov(&case_70169, case_70173);
      break;}
  return case_70169;
}

clc_ptr fits_70230(clc_ptr _70159, clc_env env)
{
  clc_ptr _70166; clc_ptr case_70160; clc_ptr clo_70165; clc_ptr clo_70229;
  switch(((clc_node)_70159)->tag){
    case 4:
      instr_clo(&clo_70165, &lam_70164, 29,
        0, _70159, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
        env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
        env[15], env[16], env[17], env[18], env[19], env[20], env[21],
        env[22], env[23], env[24], env[25], env[26]);
      instr_mov(&case_70160, clo_70165);
      break;
    case 5:
      instr_mov(&_70166, ((clc_node)_70159)->data[0]);
      instr_clo(&clo_70229, &lam_70228, 30,
        0, _70159, _70166, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26]);
      instr_mov(&case_70160, clo_70229);
      break;}
  return case_70160;
}

clc_ptr lam_70318(clc_ptr _70237, clc_env env)
{
  clc_ptr _70240; clc_ptr _70241; clc_ptr _70244; clc_ptr _70247;
  clc_ptr _70252; clc_ptr _70253; clc_ptr _70263; clc_ptr _70271;
  clc_ptr _70272; clc_ptr _70281; clc_ptr _70294; clc_ptr Break_c32_70313;
  clc_ptr Flat_c31_70298; clc_ptr Flat_c31_70306; clc_ptr SLine_c30_70293;
  clc_ptr SNil_c28_70239; clc_ptr SText_c29_70270; clc_ptr SText_c29_70289;
  clc_ptr case_70238; clc_ptr case_70242; clc_ptr case_70245;
  clc_ptr case_70248; clc_ptr case_70282; clc_ptr case_70303;
  clc_ptr cons_c9_70260; clc_ptr cons_c9_70261; clc_ptr cons_c9_70279;
  clc_ptr cons_c9_70301; clc_ptr cons_c9_70309; clc_ptr cons_c9_70316;
  clc_ptr ex_intro_c12_70256; clc_ptr ex_intro_c12_70257;
  clc_ptr ex_intro_c12_70258; clc_ptr ex_intro_c12_70259;
  clc_ptr ex_intro_c12_70277; clc_ptr ex_intro_c12_70278;
  clc_ptr ex_intro_c12_70299; clc_ptr ex_intro_c12_70300;
  clc_ptr ex_intro_c12_70307; clc_ptr ex_intro_c12_70308;
  clc_ptr ex_intro_c12_70314; clc_ptr ex_intro_c12_70315; clc_ptr tmp_70249;
  clc_ptr tmp_70250; clc_ptr tmp_70251; clc_ptr tmp_70254; clc_ptr tmp_70255;
  clc_ptr tmp_70262; clc_ptr tmp_70264; clc_ptr tmp_70265; clc_ptr tmp_70266;
  clc_ptr tmp_70267; clc_ptr tmp_70268; clc_ptr tmp_70269; clc_ptr tmp_70273;
  clc_ptr tmp_70274; clc_ptr tmp_70275; clc_ptr tmp_70276; clc_ptr tmp_70280;
  clc_ptr tmp_70283; clc_ptr tmp_70284; clc_ptr tmp_70285; clc_ptr tmp_70286;
  clc_ptr tmp_70287; clc_ptr tmp_70288; clc_ptr tmp_70290; clc_ptr tmp_70291;
  clc_ptr tmp_70292; clc_ptr tmp_70295; clc_ptr tmp_70296; clc_ptr tmp_70297;
  clc_ptr tmp_70302; clc_ptr tmp_70304; clc_ptr tmp_70305; clc_ptr tmp_70310;
  clc_ptr tmp_70311; clc_ptr tmp_70312; clc_ptr tmp_70317; clc_ptr x_70243;
  clc_ptr x_70246;
  switch(((clc_node)_70237)->tag){
    case 8:
      instr_struct(&SNil_c28_70239, 28, 0);
      instr_mov(&case_70238, SNil_c28_70239);
      break;
    case 9:
      instr_mov(&_70240, ((clc_node)_70237)->data[0]);
      instr_mov(&_70241, ((clc_node)_70237)->data[1]);
      switch(((clc_node)_70240)->tag){
        case 12:
          instr_mov(&x_70243, ((clc_node)_70240)->data[0]);
          instr_mov(&_70244, ((clc_node)_70240)->data[1]);
          switch(((clc_node)x_70243)->tag){
            case 12:
              instr_mov(&x_70246, ((clc_node)x_70243)->data[0]);
              instr_mov(&_70247, ((clc_node)x_70243)->data[1]);
              switch(((clc_node)_70244)->tag){
                case 22:
                  instr_call(&tmp_70249, env[4], env[3]);
                  instr_call(&tmp_70250, tmp_70249, env[1]);
                  instr_call(&tmp_70251, tmp_70250, _70241);
                  instr_mov(&case_70248, tmp_70251);
                  break;
                case 23:
                  instr_mov(&_70252, ((clc_node)_70244)->data[0]);
                  instr_mov(&_70253, ((clc_node)_70244)->data[1]);
                  instr_call(&tmp_70254, env[4], env[3]);
                  instr_call(&tmp_70255, tmp_70254, env[1]);
                  instr_struct(&ex_intro_c12_70256, 12, 2,
                    x_70246, _70247);
                  instr_struct(&ex_intro_c12_70257, 12, 2,
                    ex_intro_c12_70256, _70252);
                  instr_struct(&ex_intro_c12_70258, 12, 2,
                    x_70246, _70247);
                  instr_struct(&ex_intro_c12_70259, 12, 2,
                    ex_intro_c12_70258, _70253);
                  instr_struct(&cons_c9_70260, 9, 2,
                    ex_intro_c12_70259, _70241);
                  instr_struct(&cons_c9_70261, 9, 2,
                    ex_intro_c12_70257, cons_c9_70260);
                  instr_call(&tmp_70262, tmp_70255, cons_c9_70261);
                  instr_mov(&case_70248, tmp_70262);
                  break;
                case 24:
                  instr_mov(&_70263, ((clc_node)_70244)->data[0]);
                  instr_call(&tmp_70264, env[4], env[3]);
                  instr_call(&tmp_70265, env[30], env[1]);
                  instr_call(&tmp_70266, env[27], _70263);
                  instr_call(&tmp_70267, tmp_70265, tmp_70266);
                  instr_call(&tmp_70268, tmp_70264, tmp_70267);
                  instr_call(&tmp_70269, tmp_70268, _70241);
                  instr_struct(&SText_c29_70270, 29, 2,
                    _70263, tmp_70269);
                  instr_mov(&case_70248, SText_c29_70270);
                  break;
                case 25:
                  instr_mov(&_70271, ((clc_node)_70244)->data[0]);
                  instr_mov(&_70272, ((clc_node)_70244)->data[1]);
                  instr_call(&tmp_70273, env[4], env[3]);
                  instr_call(&tmp_70274, tmp_70273, env[1]);
                  instr_call(&tmp_70275, env[30], x_70246);
                  instr_call(&tmp_70276, tmp_70275, _70271);
                  instr_struct(&ex_intro_c12_70277, 12, 2,
                    tmp_70276, _70247);
                  instr_struct(&ex_intro_c12_70278, 12, 2,
                    ex_intro_c12_70277, _70272);
                  instr_struct(&cons_c9_70279, 9, 2,
                    ex_intro_c12_70278, _70241);
                  instr_call(&tmp_70280, tmp_70274, cons_c9_70279);
                  instr_mov(&case_70248, tmp_70280);
                  break;
                case 26:
                  instr_mov(&_70281, ((clc_node)_70244)->data[0]);
                  switch(((clc_node)_70247)->tag){
                    case 31:
                      instr_call(&tmp_70283, env[4], env[3]);
                      instr_call(&tmp_70284, env[30], env[1]);
                      instr_call(&tmp_70285, env[27], _70281);
                      instr_call(&tmp_70286, tmp_70284, tmp_70285);
                      instr_call(&tmp_70287, tmp_70283, tmp_70286);
                      instr_call(&tmp_70288, tmp_70287, _70241);
                      instr_struct(&SText_c29_70289, 29, 2,
                        _70281, tmp_70288);
                      instr_mov(&case_70282, SText_c29_70289);
                      break;
                    case 32:
                      instr_call(&tmp_70290, env[4], env[3]);
                      instr_call(&tmp_70291, tmp_70290, x_70246);
                      instr_call(&tmp_70292, tmp_70291, _70241);
                      instr_struct(&SLine_c30_70293, 30, 2,
                        x_70246, tmp_70292);
                      instr_mov(&case_70282, SLine_c30_70293);
                      break;}
                  instr_mov(&case_70248, case_70282);
                  break;
                case 27:
                  instr_mov(&_70294, ((clc_node)_70244)->data[0]);
                  instr_call(&tmp_70295, env[29], env[3]);
                  instr_call(&tmp_70296, tmp_70295, env[1]);
                  instr_call(&tmp_70297, env[5], tmp_70296);
                  instr_struct(&Flat_c31_70298, 31, 0);
                  instr_struct(&ex_intro_c12_70299, 12, 2,
                    x_70246, Flat_c31_70298);
                  instr_struct(&ex_intro_c12_70300, 12, 2,
                    ex_intro_c12_70299, _70294);
                  instr_struct(&cons_c9_70301, 9, 2,
                    ex_intro_c12_70300, _70241);
                  instr_call(&tmp_70302, tmp_70297, cons_c9_70301);
                  switch(((clc_node)tmp_70302)->tag){
                    case 2:
                      instr_call(&tmp_70304, env[4], env[3]);
                      instr_call(&tmp_70305, tmp_70304, env[1]);
                      instr_struct(&Flat_c31_70306, 31, 0);
                      instr_struct(&ex_intro_c12_70307, 12, 2,
                        x_70246, Flat_c31_70306);
                      instr_struct(&ex_intro_c12_70308, 12, 2,
                        ex_intro_c12_70307, _70294);
                      instr_struct(&cons_c9_70309, 9, 2,
                        ex_intro_c12_70308, _70241);
                      instr_call(&tmp_70310, tmp_70305, cons_c9_70309);
                      instr_mov(&case_70303, tmp_70310);
                      break;
                    case 3:
                      instr_call(&tmp_70311, env[4], env[3]);
                      instr_call(&tmp_70312, tmp_70311, env[1]);
                      instr_struct(&Break_c32_70313, 32, 0);
                      instr_struct(&ex_intro_c12_70314, 12, 2,
                        x_70246, Break_c32_70313);
                      instr_struct(&ex_intro_c12_70315, 12, 2,
                        ex_intro_c12_70314, _70294);
                      instr_struct(&cons_c9_70316, 9, 2,
                        ex_intro_c12_70315, _70241);
                      instr_call(&tmp_70317, tmp_70312, cons_c9_70316);
                      instr_mov(&case_70303, tmp_70317);
                      break;}
                  instr_mov(&case_70248, case_70303);
                  break;}
              instr_mov(&case_70245, case_70248);
              break;}
          instr_mov(&case_70242, case_70245);
          break;}
      instr_mov(&case_70238, case_70242);
      break;}
  return case_70238;
}

clc_ptr lam_70320(clc_ptr _70235, clc_env env)
{
  clc_ptr clo_70319;
  instr_clo(&clo_70319, &lam_70318, 32,
    0, _70235, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29]);
  return clo_70319;
}

clc_ptr format_70322(clc_ptr _70233, clc_env env)
{
  clc_ptr clo_70321;
  instr_clo(&clo_70321, &lam_70320, 30,
    0, _70233, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27]);
  return clo_70321;
}

clc_ptr lam_70355(clc_ptr _70327, clc_env env)
{
  clc_ptr Ascii_c16_70351; clc_ptr EmptyString_c17_70352;
  clc_ptr Flat_c31_70334; clc_ptr String_c18_70353; clc_ptr cons_c9_70339;
  clc_ptr ex_intro_c12_70335; clc_ptr ex_intro_c12_70337;
  clc_ptr false_c3_70343; clc_ptr false_c3_70344; clc_ptr false_c3_70345;
  clc_ptr false_c3_70346; clc_ptr false_c3_70348; clc_ptr false_c3_70350;
  clc_ptr nil_c8_70338; clc_ptr sd_70328; clc_ptr succ_c5_70329;
  clc_ptr tmp_70330; clc_ptr tmp_70332; clc_ptr tmp_70336; clc_ptr tmp_70340;
  clc_ptr tmp_70341; clc_ptr tmp_70342; clc_ptr tmp_70354;
  clc_ptr true_c2_70347; clc_ptr true_c2_70349; clc_ptr zero_c4_70331;
  clc_ptr zero_c4_70333;
  instr_struct(&succ_c5_70329, 5, 1,
    env[1]);
  instr_call(&tmp_70330, env[3], succ_c5_70329);
  instr_struct(&zero_c4_70331, 4, 0);
  instr_call(&tmp_70332, tmp_70330, zero_c4_70331);
  instr_struct(&zero_c4_70333, 4, 0);
  instr_struct(&Flat_c31_70334, 31, 0);
  instr_struct(&ex_intro_c12_70335, 12, 2,
    zero_c4_70333, Flat_c31_70334);
  instr_call(&tmp_70336, env[6], _70327);
  instr_struct(&ex_intro_c12_70337, 12, 2,
    ex_intro_c12_70335, tmp_70336);
  instr_struct(&nil_c8_70338, 8, 0);
  instr_struct(&cons_c9_70339, 9, 2,
    ex_intro_c12_70337, nil_c8_70338);
  instr_call(&tmp_70340, tmp_70332, cons_c9_70339);
  instr_mov(&sd_70328, tmp_70340);
  instr_call(&tmp_70341, env[5], sd_70328);
  instr_call(&tmp_70342, env[27], tmp_70341);
  instr_struct(&false_c3_70343, 3, 0);
  instr_struct(&false_c3_70344, 3, 0);
  instr_struct(&false_c3_70345, 3, 0);
  instr_struct(&false_c3_70346, 3, 0);
  instr_struct(&true_c2_70347, 2, 0);
  instr_struct(&false_c3_70348, 3, 0);
  instr_struct(&true_c2_70349, 2, 0);
  instr_struct(&false_c3_70350, 3, 0);
  instr_struct(&Ascii_c16_70351, 16, 8,
    false_c3_70343, false_c3_70344, false_c3_70345, false_c3_70346,
    true_c2_70347, false_c3_70348, true_c2_70349, false_c3_70350);
  instr_struct(&EmptyString_c17_70352, 17, 0);
  instr_struct(&String_c18_70353, 18, 2,
    Ascii_c16_70351, EmptyString_c17_70352);
  instr_call(&tmp_70354, tmp_70342, String_c18_70353);
  return tmp_70354;
}

clc_ptr pretty_70357(clc_ptr _70325, clc_env env)
{
  clc_ptr clo_70356;
  instr_clo(&clo_70356, &lam_70355, 31,
    0, _70325, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28]);
  return clo_70356;
}

clc_ptr lam_70364(clc_ptr _70363, clc_env env)
{
  
  
  return _70363;
}

clc_ptr lam_70409(clc_ptr _70369, clc_env env)
{
  clc_ptr _70372; clc_ptr _70373; clc_ptr _70380; clc_ptr _70387;
  clc_ptr _70388; clc_ptr _70395; clc_ptr _70402; clc_ptr DocBreak_c26_70400;
  clc_ptr DocCons_c23_70371; clc_ptr DocCons_c23_70374;
  clc_ptr DocCons_c23_70378; clc_ptr DocCons_c23_70381;
  clc_ptr DocCons_c23_70389; clc_ptr DocCons_c23_70396;
  clc_ptr DocCons_c23_70403; clc_ptr DocGroup_c27_70407;
  clc_ptr DocNest_c25_70393; clc_ptr DocText_c24_70385; clc_ptr case_70370;
  clc_ptr tmp_70375; clc_ptr tmp_70376; clc_ptr tmp_70377; clc_ptr tmp_70379;
  clc_ptr tmp_70382; clc_ptr tmp_70383; clc_ptr tmp_70384; clc_ptr tmp_70386;
  clc_ptr tmp_70390; clc_ptr tmp_70391; clc_ptr tmp_70392; clc_ptr tmp_70394;
  clc_ptr tmp_70397; clc_ptr tmp_70398; clc_ptr tmp_70399; clc_ptr tmp_70401;
  clc_ptr tmp_70404; clc_ptr tmp_70405; clc_ptr tmp_70406; clc_ptr tmp_70408;
  switch(((clc_node)_70369)->tag){
    case 22:
      instr_struct(&DocCons_c23_70371, 23, 2,
        env[2], env[3]);
      instr_mov(&case_70370, DocCons_c23_70371);
      break;
    case 23:
      instr_mov(&_70372, ((clc_node)_70369)->data[0]);
      instr_mov(&_70373, ((clc_node)_70369)->data[1]);
      instr_struct(&DocCons_c23_70374, 23, 2,
        env[2], env[3]);
      instr_call(&tmp_70375, env[15], DocCons_c23_70374);
      instr_call(&tmp_70376, tmp_70375, env[11]);
      instr_call(&tmp_70377, env[15], tmp_70376);
      instr_struct(&DocCons_c23_70378, 23, 2,
        _70372, _70373);
      instr_call(&tmp_70379, tmp_70377, DocCons_c23_70378);
      instr_mov(&case_70370, tmp_70379);
      break;
    case 24:
      instr_mov(&_70380, ((clc_node)_70369)->data[0]);
      instr_struct(&DocCons_c23_70381, 23, 2,
        env[2], env[3]);
      instr_call(&tmp_70382, env[15], DocCons_c23_70381);
      instr_call(&tmp_70383, tmp_70382, env[11]);
      instr_call(&tmp_70384, env[15], tmp_70383);
      instr_struct(&DocText_c24_70385, 24, 1,
        _70380);
      instr_call(&tmp_70386, tmp_70384, DocText_c24_70385);
      instr_mov(&case_70370, tmp_70386);
      break;
    case 25:
      instr_mov(&_70387, ((clc_node)_70369)->data[0]);
      instr_mov(&_70388, ((clc_node)_70369)->data[1]);
      instr_struct(&DocCons_c23_70389, 23, 2,
        env[2], env[3]);
      instr_call(&tmp_70390, env[15], DocCons_c23_70389);
      instr_call(&tmp_70391, tmp_70390, env[11]);
      instr_call(&tmp_70392, env[15], tmp_70391);
      instr_struct(&DocNest_c25_70393, 25, 2,
        _70387, _70388);
      instr_call(&tmp_70394, tmp_70392, DocNest_c25_70393);
      instr_mov(&case_70370, tmp_70394);
      break;
    case 26:
      instr_mov(&_70395, ((clc_node)_70369)->data[0]);
      instr_struct(&DocCons_c23_70396, 23, 2,
        env[2], env[3]);
      instr_call(&tmp_70397, env[15], DocCons_c23_70396);
      instr_call(&tmp_70398, tmp_70397, env[11]);
      instr_call(&tmp_70399, env[15], tmp_70398);
      instr_struct(&DocBreak_c26_70400, 26, 1,
        _70395);
      instr_call(&tmp_70401, tmp_70399, DocBreak_c26_70400);
      instr_mov(&case_70370, tmp_70401);
      break;
    case 27:
      instr_mov(&_70402, ((clc_node)_70369)->data[0]);
      instr_struct(&DocCons_c23_70403, 23, 2,
        env[2], env[3]);
      instr_call(&tmp_70404, env[15], DocCons_c23_70403);
      instr_call(&tmp_70405, tmp_70404, env[11]);
      instr_call(&tmp_70406, env[15], tmp_70405);
      instr_struct(&DocGroup_c27_70407, 27, 1,
        _70402);
      instr_call(&tmp_70408, tmp_70406, DocGroup_c27_70407);
      instr_mov(&case_70370, tmp_70408);
      break;}
  return case_70370;
}

clc_ptr lam_70453(clc_ptr _70413, clc_env env)
{
  clc_ptr _70416; clc_ptr _70417; clc_ptr _70424; clc_ptr _70431;
  clc_ptr _70432; clc_ptr _70439; clc_ptr _70446; clc_ptr DocBreak_c26_70444;
  clc_ptr DocCons_c23_70422; clc_ptr DocGroup_c27_70451;
  clc_ptr DocNest_c25_70437; clc_ptr DocText_c24_70415;
  clc_ptr DocText_c24_70418; clc_ptr DocText_c24_70425;
  clc_ptr DocText_c24_70429; clc_ptr DocText_c24_70433;
  clc_ptr DocText_c24_70440; clc_ptr DocText_c24_70447; clc_ptr case_70414;
  clc_ptr tmp_70419; clc_ptr tmp_70420; clc_ptr tmp_70421; clc_ptr tmp_70423;
  clc_ptr tmp_70426; clc_ptr tmp_70427; clc_ptr tmp_70428; clc_ptr tmp_70430;
  clc_ptr tmp_70434; clc_ptr tmp_70435; clc_ptr tmp_70436; clc_ptr tmp_70438;
  clc_ptr tmp_70441; clc_ptr tmp_70442; clc_ptr tmp_70443; clc_ptr tmp_70445;
  clc_ptr tmp_70448; clc_ptr tmp_70449; clc_ptr tmp_70450; clc_ptr tmp_70452;
  switch(((clc_node)_70413)->tag){
    case 22:
      instr_struct(&DocText_c24_70415, 24, 1,
        env[2]);
      instr_mov(&case_70414, DocText_c24_70415);
      break;
    case 23:
      instr_mov(&_70416, ((clc_node)_70413)->data[0]);
      instr_mov(&_70417, ((clc_node)_70413)->data[1]);
      instr_struct(&DocText_c24_70418, 24, 1,
        env[2]);
      instr_call(&tmp_70419, env[14], DocText_c24_70418);
      instr_call(&tmp_70420, tmp_70419, env[10]);
      instr_call(&tmp_70421, env[14], tmp_70420);
      instr_struct(&DocCons_c23_70422, 23, 2,
        _70416, _70417);
      instr_call(&tmp_70423, tmp_70421, DocCons_c23_70422);
      instr_mov(&case_70414, tmp_70423);
      break;
    case 24:
      instr_mov(&_70424, ((clc_node)_70413)->data[0]);
      instr_struct(&DocText_c24_70425, 24, 1,
        env[2]);
      instr_call(&tmp_70426, env[14], DocText_c24_70425);
      instr_call(&tmp_70427, tmp_70426, env[10]);
      instr_call(&tmp_70428, env[14], tmp_70427);
      instr_struct(&DocText_c24_70429, 24, 1,
        _70424);
      instr_call(&tmp_70430, tmp_70428, DocText_c24_70429);
      instr_mov(&case_70414, tmp_70430);
      break;
    case 25:
      instr_mov(&_70431, ((clc_node)_70413)->data[0]);
      instr_mov(&_70432, ((clc_node)_70413)->data[1]);
      instr_struct(&DocText_c24_70433, 24, 1,
        env[2]);
      instr_call(&tmp_70434, env[14], DocText_c24_70433);
      instr_call(&tmp_70435, tmp_70434, env[10]);
      instr_call(&tmp_70436, env[14], tmp_70435);
      instr_struct(&DocNest_c25_70437, 25, 2,
        _70431, _70432);
      instr_call(&tmp_70438, tmp_70436, DocNest_c25_70437);
      instr_mov(&case_70414, tmp_70438);
      break;
    case 26:
      instr_mov(&_70439, ((clc_node)_70413)->data[0]);
      instr_struct(&DocText_c24_70440, 24, 1,
        env[2]);
      instr_call(&tmp_70441, env[14], DocText_c24_70440);
      instr_call(&tmp_70442, tmp_70441, env[10]);
      instr_call(&tmp_70443, env[14], tmp_70442);
      instr_struct(&DocBreak_c26_70444, 26, 1,
        _70439);
      instr_call(&tmp_70445, tmp_70443, DocBreak_c26_70444);
      instr_mov(&case_70414, tmp_70445);
      break;
    case 27:
      instr_mov(&_70446, ((clc_node)_70413)->data[0]);
      instr_struct(&DocText_c24_70447, 24, 1,
        env[2]);
      instr_call(&tmp_70448, env[14], DocText_c24_70447);
      instr_call(&tmp_70449, tmp_70448, env[10]);
      instr_call(&tmp_70450, env[14], tmp_70449);
      instr_struct(&DocGroup_c27_70451, 27, 1,
        _70446);
      instr_call(&tmp_70452, tmp_70450, DocGroup_c27_70451);
      instr_mov(&case_70414, tmp_70452);
      break;}
  return case_70414;
}

clc_ptr lam_70498(clc_ptr _70458, clc_env env)
{
  clc_ptr _70461; clc_ptr _70462; clc_ptr _70469; clc_ptr _70476;
  clc_ptr _70477; clc_ptr _70484; clc_ptr _70491; clc_ptr DocBreak_c26_70489;
  clc_ptr DocCons_c23_70467; clc_ptr DocGroup_c27_70496;
  clc_ptr DocNest_c25_70460; clc_ptr DocNest_c25_70463;
  clc_ptr DocNest_c25_70470; clc_ptr DocNest_c25_70478;
  clc_ptr DocNest_c25_70482; clc_ptr DocNest_c25_70485;
  clc_ptr DocNest_c25_70492; clc_ptr DocText_c24_70474; clc_ptr case_70459;
  clc_ptr tmp_70464; clc_ptr tmp_70465; clc_ptr tmp_70466; clc_ptr tmp_70468;
  clc_ptr tmp_70471; clc_ptr tmp_70472; clc_ptr tmp_70473; clc_ptr tmp_70475;
  clc_ptr tmp_70479; clc_ptr tmp_70480; clc_ptr tmp_70481; clc_ptr tmp_70483;
  clc_ptr tmp_70486; clc_ptr tmp_70487; clc_ptr tmp_70488; clc_ptr tmp_70490;
  clc_ptr tmp_70493; clc_ptr tmp_70494; clc_ptr tmp_70495; clc_ptr tmp_70497;
  switch(((clc_node)_70458)->tag){
    case 22:
      instr_struct(&DocNest_c25_70460, 25, 2,
        env[2], env[3]);
      instr_mov(&case_70459, DocNest_c25_70460);
      break;
    case 23:
      instr_mov(&_70461, ((clc_node)_70458)->data[0]);
      instr_mov(&_70462, ((clc_node)_70458)->data[1]);
      instr_struct(&DocNest_c25_70463, 25, 2,
        env[2], env[3]);
      instr_call(&tmp_70464, env[15], DocNest_c25_70463);
      instr_call(&tmp_70465, tmp_70464, env[11]);
      instr_call(&tmp_70466, env[15], tmp_70465);
      instr_struct(&DocCons_c23_70467, 23, 2,
        _70461, _70462);
      instr_call(&tmp_70468, tmp_70466, DocCons_c23_70467);
      instr_mov(&case_70459, tmp_70468);
      break;
    case 24:
      instr_mov(&_70469, ((clc_node)_70458)->data[0]);
      instr_struct(&DocNest_c25_70470, 25, 2,
        env[2], env[3]);
      instr_call(&tmp_70471, env[15], DocNest_c25_70470);
      instr_call(&tmp_70472, tmp_70471, env[11]);
      instr_call(&tmp_70473, env[15], tmp_70472);
      instr_struct(&DocText_c24_70474, 24, 1,
        _70469);
      instr_call(&tmp_70475, tmp_70473, DocText_c24_70474);
      instr_mov(&case_70459, tmp_70475);
      break;
    case 25:
      instr_mov(&_70476, ((clc_node)_70458)->data[0]);
      instr_mov(&_70477, ((clc_node)_70458)->data[1]);
      instr_struct(&DocNest_c25_70478, 25, 2,
        env[2], env[3]);
      instr_call(&tmp_70479, env[15], DocNest_c25_70478);
      instr_call(&tmp_70480, tmp_70479, env[11]);
      instr_call(&tmp_70481, env[15], tmp_70480);
      instr_struct(&DocNest_c25_70482, 25, 2,
        _70476, _70477);
      instr_call(&tmp_70483, tmp_70481, DocNest_c25_70482);
      instr_mov(&case_70459, tmp_70483);
      break;
    case 26:
      instr_mov(&_70484, ((clc_node)_70458)->data[0]);
      instr_struct(&DocNest_c25_70485, 25, 2,
        env[2], env[3]);
      instr_call(&tmp_70486, env[15], DocNest_c25_70485);
      instr_call(&tmp_70487, tmp_70486, env[11]);
      instr_call(&tmp_70488, env[15], tmp_70487);
      instr_struct(&DocBreak_c26_70489, 26, 1,
        _70484);
      instr_call(&tmp_70490, tmp_70488, DocBreak_c26_70489);
      instr_mov(&case_70459, tmp_70490);
      break;
    case 27:
      instr_mov(&_70491, ((clc_node)_70458)->data[0]);
      instr_struct(&DocNest_c25_70492, 25, 2,
        env[2], env[3]);
      instr_call(&tmp_70493, env[15], DocNest_c25_70492);
      instr_call(&tmp_70494, tmp_70493, env[11]);
      instr_call(&tmp_70495, env[15], tmp_70494);
      instr_struct(&DocGroup_c27_70496, 27, 1,
        _70491);
      instr_call(&tmp_70497, tmp_70495, DocGroup_c27_70496);
      instr_mov(&case_70459, tmp_70497);
      break;}
  return case_70459;
}

clc_ptr lam_70542(clc_ptr _70502, clc_env env)
{
  clc_ptr _70505; clc_ptr _70506; clc_ptr _70513; clc_ptr _70520;
  clc_ptr _70521; clc_ptr _70528; clc_ptr _70535; clc_ptr DocBreak_c26_70504;
  clc_ptr DocBreak_c26_70507; clc_ptr DocBreak_c26_70514;
  clc_ptr DocBreak_c26_70522; clc_ptr DocBreak_c26_70529;
  clc_ptr DocBreak_c26_70533; clc_ptr DocBreak_c26_70536;
  clc_ptr DocCons_c23_70511; clc_ptr DocGroup_c27_70540;
  clc_ptr DocNest_c25_70526; clc_ptr DocText_c24_70518; clc_ptr case_70503;
  clc_ptr tmp_70508; clc_ptr tmp_70509; clc_ptr tmp_70510; clc_ptr tmp_70512;
  clc_ptr tmp_70515; clc_ptr tmp_70516; clc_ptr tmp_70517; clc_ptr tmp_70519;
  clc_ptr tmp_70523; clc_ptr tmp_70524; clc_ptr tmp_70525; clc_ptr tmp_70527;
  clc_ptr tmp_70530; clc_ptr tmp_70531; clc_ptr tmp_70532; clc_ptr tmp_70534;
  clc_ptr tmp_70537; clc_ptr tmp_70538; clc_ptr tmp_70539; clc_ptr tmp_70541;
  switch(((clc_node)_70502)->tag){
    case 22:
      instr_struct(&DocBreak_c26_70504, 26, 1,
        env[2]);
      instr_mov(&case_70503, DocBreak_c26_70504);
      break;
    case 23:
      instr_mov(&_70505, ((clc_node)_70502)->data[0]);
      instr_mov(&_70506, ((clc_node)_70502)->data[1]);
      instr_struct(&DocBreak_c26_70507, 26, 1,
        env[2]);
      instr_call(&tmp_70508, env[14], DocBreak_c26_70507);
      instr_call(&tmp_70509, tmp_70508, env[10]);
      instr_call(&tmp_70510, env[14], tmp_70509);
      instr_struct(&DocCons_c23_70511, 23, 2,
        _70505, _70506);
      instr_call(&tmp_70512, tmp_70510, DocCons_c23_70511);
      instr_mov(&case_70503, tmp_70512);
      break;
    case 24:
      instr_mov(&_70513, ((clc_node)_70502)->data[0]);
      instr_struct(&DocBreak_c26_70514, 26, 1,
        env[2]);
      instr_call(&tmp_70515, env[14], DocBreak_c26_70514);
      instr_call(&tmp_70516, tmp_70515, env[10]);
      instr_call(&tmp_70517, env[14], tmp_70516);
      instr_struct(&DocText_c24_70518, 24, 1,
        _70513);
      instr_call(&tmp_70519, tmp_70517, DocText_c24_70518);
      instr_mov(&case_70503, tmp_70519);
      break;
    case 25:
      instr_mov(&_70520, ((clc_node)_70502)->data[0]);
      instr_mov(&_70521, ((clc_node)_70502)->data[1]);
      instr_struct(&DocBreak_c26_70522, 26, 1,
        env[2]);
      instr_call(&tmp_70523, env[14], DocBreak_c26_70522);
      instr_call(&tmp_70524, tmp_70523, env[10]);
      instr_call(&tmp_70525, env[14], tmp_70524);
      instr_struct(&DocNest_c25_70526, 25, 2,
        _70520, _70521);
      instr_call(&tmp_70527, tmp_70525, DocNest_c25_70526);
      instr_mov(&case_70503, tmp_70527);
      break;
    case 26:
      instr_mov(&_70528, ((clc_node)_70502)->data[0]);
      instr_struct(&DocBreak_c26_70529, 26, 1,
        env[2]);
      instr_call(&tmp_70530, env[14], DocBreak_c26_70529);
      instr_call(&tmp_70531, tmp_70530, env[10]);
      instr_call(&tmp_70532, env[14], tmp_70531);
      instr_struct(&DocBreak_c26_70533, 26, 1,
        _70528);
      instr_call(&tmp_70534, tmp_70532, DocBreak_c26_70533);
      instr_mov(&case_70503, tmp_70534);
      break;
    case 27:
      instr_mov(&_70535, ((clc_node)_70502)->data[0]);
      instr_struct(&DocBreak_c26_70536, 26, 1,
        env[2]);
      instr_call(&tmp_70537, env[14], DocBreak_c26_70536);
      instr_call(&tmp_70538, tmp_70537, env[10]);
      instr_call(&tmp_70539, env[14], tmp_70538);
      instr_struct(&DocGroup_c27_70540, 27, 1,
        _70535);
      instr_call(&tmp_70541, tmp_70539, DocGroup_c27_70540);
      instr_mov(&case_70503, tmp_70541);
      break;}
  return case_70503;
}

clc_ptr lam_70586(clc_ptr _70546, clc_env env)
{
  clc_ptr _70549; clc_ptr _70550; clc_ptr _70557; clc_ptr _70564;
  clc_ptr _70565; clc_ptr _70572; clc_ptr _70579; clc_ptr DocBreak_c26_70577;
  clc_ptr DocCons_c23_70555; clc_ptr DocGroup_c27_70548;
  clc_ptr DocGroup_c27_70551; clc_ptr DocGroup_c27_70558;
  clc_ptr DocGroup_c27_70566; clc_ptr DocGroup_c27_70573;
  clc_ptr DocGroup_c27_70580; clc_ptr DocGroup_c27_70584;
  clc_ptr DocNest_c25_70570; clc_ptr DocText_c24_70562; clc_ptr case_70547;
  clc_ptr tmp_70552; clc_ptr tmp_70553; clc_ptr tmp_70554; clc_ptr tmp_70556;
  clc_ptr tmp_70559; clc_ptr tmp_70560; clc_ptr tmp_70561; clc_ptr tmp_70563;
  clc_ptr tmp_70567; clc_ptr tmp_70568; clc_ptr tmp_70569; clc_ptr tmp_70571;
  clc_ptr tmp_70574; clc_ptr tmp_70575; clc_ptr tmp_70576; clc_ptr tmp_70578;
  clc_ptr tmp_70581; clc_ptr tmp_70582; clc_ptr tmp_70583; clc_ptr tmp_70585;
  switch(((clc_node)_70546)->tag){
    case 22:
      instr_struct(&DocGroup_c27_70548, 27, 1,
        env[2]);
      instr_mov(&case_70547, DocGroup_c27_70548);
      break;
    case 23:
      instr_mov(&_70549, ((clc_node)_70546)->data[0]);
      instr_mov(&_70550, ((clc_node)_70546)->data[1]);
      instr_struct(&DocGroup_c27_70551, 27, 1,
        env[2]);
      instr_call(&tmp_70552, env[14], DocGroup_c27_70551);
      instr_call(&tmp_70553, tmp_70552, env[10]);
      instr_call(&tmp_70554, env[14], tmp_70553);
      instr_struct(&DocCons_c23_70555, 23, 2,
        _70549, _70550);
      instr_call(&tmp_70556, tmp_70554, DocCons_c23_70555);
      instr_mov(&case_70547, tmp_70556);
      break;
    case 24:
      instr_mov(&_70557, ((clc_node)_70546)->data[0]);
      instr_struct(&DocGroup_c27_70558, 27, 1,
        env[2]);
      instr_call(&tmp_70559, env[14], DocGroup_c27_70558);
      instr_call(&tmp_70560, tmp_70559, env[10]);
      instr_call(&tmp_70561, env[14], tmp_70560);
      instr_struct(&DocText_c24_70562, 24, 1,
        _70557);
      instr_call(&tmp_70563, tmp_70561, DocText_c24_70562);
      instr_mov(&case_70547, tmp_70563);
      break;
    case 25:
      instr_mov(&_70564, ((clc_node)_70546)->data[0]);
      instr_mov(&_70565, ((clc_node)_70546)->data[1]);
      instr_struct(&DocGroup_c27_70566, 27, 1,
        env[2]);
      instr_call(&tmp_70567, env[14], DocGroup_c27_70566);
      instr_call(&tmp_70568, tmp_70567, env[10]);
      instr_call(&tmp_70569, env[14], tmp_70568);
      instr_struct(&DocNest_c25_70570, 25, 2,
        _70564, _70565);
      instr_call(&tmp_70571, tmp_70569, DocNest_c25_70570);
      instr_mov(&case_70547, tmp_70571);
      break;
    case 26:
      instr_mov(&_70572, ((clc_node)_70546)->data[0]);
      instr_struct(&DocGroup_c27_70573, 27, 1,
        env[2]);
      instr_call(&tmp_70574, env[14], DocGroup_c27_70573);
      instr_call(&tmp_70575, tmp_70574, env[10]);
      instr_call(&tmp_70576, env[14], tmp_70575);
      instr_struct(&DocBreak_c26_70577, 26, 1,
        _70572);
      instr_call(&tmp_70578, tmp_70576, DocBreak_c26_70577);
      instr_mov(&case_70547, tmp_70578);
      break;
    case 27:
      instr_mov(&_70579, ((clc_node)_70546)->data[0]);
      instr_struct(&DocGroup_c27_70580, 27, 1,
        env[2]);
      instr_call(&tmp_70581, env[14], DocGroup_c27_70580);
      instr_call(&tmp_70582, tmp_70581, env[10]);
      instr_call(&tmp_70583, env[14], tmp_70582);
      instr_struct(&DocGroup_c27_70584, 27, 1,
        _70579);
      instr_call(&tmp_70585, tmp_70583, DocGroup_c27_70584);
      instr_mov(&case_70547, tmp_70585);
      break;}
  return case_70547;
}

clc_ptr join_70588(clc_ptr _70360, clc_env env)
{
  clc_ptr _70366; clc_ptr _70367; clc_ptr _70411; clc_ptr _70455;
  clc_ptr _70456; clc_ptr _70500; clc_ptr _70544; clc_ptr case_70361;
  clc_ptr clo_70365; clc_ptr clo_70410; clc_ptr clo_70454; clc_ptr clo_70499;
  clc_ptr clo_70543; clc_ptr clo_70587;
  switch(((clc_node)_70360)->tag){
    case 22:
      instr_clo(&clo_70365, &lam_70364, 32,
        0, _70360, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
        env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
        env[15], env[16], env[17], env[18], env[19], env[20], env[21],
        env[22], env[23], env[24], env[25], env[26], env[27], env[28],
        env[29]);
      instr_mov(&case_70361, clo_70365);
      break;
    case 23:
      instr_mov(&_70366, ((clc_node)_70360)->data[0]);
      instr_mov(&_70367, ((clc_node)_70360)->data[1]);
      instr_clo(&clo_70410, &lam_70409, 34,
        0, _70360, _70366, _70367, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26],
        env[27], env[28], env[29]);
      instr_mov(&case_70361, clo_70410);
      break;
    case 24:
      instr_mov(&_70411, ((clc_node)_70360)->data[0]);
      instr_clo(&clo_70454, &lam_70453, 33,
        0, _70360, _70411, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29]);
      instr_mov(&case_70361, clo_70454);
      break;
    case 25:
      instr_mov(&_70455, ((clc_node)_70360)->data[0]);
      instr_mov(&_70456, ((clc_node)_70360)->data[1]);
      instr_clo(&clo_70499, &lam_70498, 34,
        0, _70360, _70455, _70456, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26],
        env[27], env[28], env[29]);
      instr_mov(&case_70361, clo_70499);
      break;
    case 26:
      instr_mov(&_70500, ((clc_node)_70360)->data[0]);
      instr_clo(&clo_70543, &lam_70542, 33,
        0, _70360, _70500, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29]);
      instr_mov(&case_70361, clo_70543);
      break;
    case 27:
      instr_mov(&_70544, ((clc_node)_70360)->data[0]);
      instr_clo(&clo_70587, &lam_70586, 33,
        0, _70360, _70544, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29]);
      instr_mov(&case_70361, clo_70587);
      break;}
  return case_70361;
}

clc_ptr lam_70610(clc_ptr _70595, clc_env env)
{
  clc_ptr succ_c5_70597; clc_ptr succ_c5_70598; clc_ptr tmp_70599;
  clc_ptr tmp_70600; clc_ptr tmp_70601; clc_ptr tmp_70602; clc_ptr tmp_70603;
  clc_ptr tmp_70604; clc_ptr tmp_70605; clc_ptr tmp_70606; clc_ptr tmp_70607;
  clc_ptr tmp_70608; clc_ptr tmp_70609; clc_ptr zero_c4_70596;
  instr_struct(&zero_c4_70596, 4, 0);
  instr_struct(&succ_c5_70597, 5, 1,
    zero_c4_70596);
  instr_struct(&succ_c5_70598, 5, 1,
    succ_c5_70597);
  instr_call(&tmp_70599, env[13], succ_c5_70598);
  instr_call(&tmp_70600, env[14], env[3]);
  instr_call(&tmp_70601, env[5], tmp_70600);
  instr_call(&tmp_70602, env[14], env[1]);
  instr_call(&tmp_70603, tmp_70601, tmp_70602);
  instr_call(&tmp_70604, env[10], tmp_70603);
  instr_call(&tmp_70605, env[5], tmp_70604);
  instr_call(&tmp_70606, env[14], _70595);
  instr_call(&tmp_70607, tmp_70605, tmp_70606);
  instr_call(&tmp_70608, tmp_70599, tmp_70607);
  instr_call(&tmp_70609, env[10], tmp_70608);
  return tmp_70609;
}

clc_ptr lam_70612(clc_ptr _70593, clc_env env)
{
  clc_ptr clo_70611;
  instr_clo(&clo_70611, &lam_70610, 35,
    0, _70593, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30],
    env[31], env[32]);
  return clo_70611;
}

clc_ptr binop_70614(clc_ptr _70591, clc_env env)
{
  clc_ptr clo_70613;
  instr_clo(&clo_70613, &lam_70612, 33,
    0, _70591, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30]);
  return clo_70613;
}

clc_ptr lam_70885(clc_ptr _70749, clc_env env)
{
  clc_ptr Ascii_c16_70762; clc_ptr Ascii_c16_70771; clc_ptr Ascii_c16_70793;
  clc_ptr Ascii_c16_70802; clc_ptr Ascii_c16_70811; clc_ptr Ascii_c16_70820;
  clc_ptr Ascii_c16_70844; clc_ptr Ascii_c16_70853; clc_ptr Ascii_c16_70862;
  clc_ptr Ascii_c16_70871; clc_ptr EmptyString_c17_70772;
  clc_ptr EmptyString_c17_70821; clc_ptr EmptyString_c17_70872;
  clc_ptr String_c18_70773; clc_ptr String_c18_70774;
  clc_ptr String_c18_70822; clc_ptr String_c18_70823;
  clc_ptr String_c18_70824; clc_ptr String_c18_70825;
  clc_ptr String_c18_70873; clc_ptr String_c18_70874;
  clc_ptr String_c18_70875; clc_ptr String_c18_70876; clc_ptr false_c3_70754;
  clc_ptr false_c3_70757; clc_ptr false_c3_70759; clc_ptr false_c3_70760;
  clc_ptr false_c3_70763; clc_ptr false_c3_70766; clc_ptr false_c3_70767;
  clc_ptr false_c3_70770; clc_ptr false_c3_70785; clc_ptr false_c3_70789;
  clc_ptr false_c3_70791; clc_ptr false_c3_70792; clc_ptr false_c3_70794;
  clc_ptr false_c3_70797; clc_ptr false_c3_70799; clc_ptr false_c3_70800;
  clc_ptr false_c3_70801; clc_ptr false_c3_70803; clc_ptr false_c3_70806;
  clc_ptr false_c3_70807; clc_ptr false_c3_70809; clc_ptr false_c3_70812;
  clc_ptr false_c3_70815; clc_ptr false_c3_70819; clc_ptr false_c3_70836;
  clc_ptr false_c3_70839; clc_ptr false_c3_70840; clc_ptr false_c3_70842;
  clc_ptr false_c3_70845; clc_ptr false_c3_70848; clc_ptr false_c3_70851;
  clc_ptr false_c3_70852; clc_ptr false_c3_70854; clc_ptr false_c3_70858;
  clc_ptr false_c3_70859; clc_ptr false_c3_70863; clc_ptr false_c3_70866;
  clc_ptr false_c3_70867; clc_ptr false_c3_70869; clc_ptr succ_c5_70751;
  clc_ptr succ_c5_70752; clc_ptr succ_c5_70782; clc_ptr succ_c5_70783;
  clc_ptr succ_c5_70833; clc_ptr succ_c5_70834; clc_ptr tmp_70753;
  clc_ptr tmp_70775; clc_ptr tmp_70776; clc_ptr tmp_70777; clc_ptr tmp_70778;
  clc_ptr tmp_70779; clc_ptr tmp_70780; clc_ptr tmp_70784; clc_ptr tmp_70826;
  clc_ptr tmp_70827; clc_ptr tmp_70828; clc_ptr tmp_70829; clc_ptr tmp_70830;
  clc_ptr tmp_70831; clc_ptr tmp_70835; clc_ptr tmp_70877; clc_ptr tmp_70878;
  clc_ptr tmp_70879; clc_ptr tmp_70880; clc_ptr tmp_70881; clc_ptr tmp_70882;
  clc_ptr tmp_70883; clc_ptr tmp_70884; clc_ptr true_c2_70755;
  clc_ptr true_c2_70756; clc_ptr true_c2_70758; clc_ptr true_c2_70761;
  clc_ptr true_c2_70764; clc_ptr true_c2_70765; clc_ptr true_c2_70768;
  clc_ptr true_c2_70769; clc_ptr true_c2_70786; clc_ptr true_c2_70787;
  clc_ptr true_c2_70788; clc_ptr true_c2_70790; clc_ptr true_c2_70795;
  clc_ptr true_c2_70796; clc_ptr true_c2_70798; clc_ptr true_c2_70804;
  clc_ptr true_c2_70805; clc_ptr true_c2_70808; clc_ptr true_c2_70810;
  clc_ptr true_c2_70813; clc_ptr true_c2_70814; clc_ptr true_c2_70816;
  clc_ptr true_c2_70817; clc_ptr true_c2_70818; clc_ptr true_c2_70837;
  clc_ptr true_c2_70838; clc_ptr true_c2_70841; clc_ptr true_c2_70843;
  clc_ptr true_c2_70846; clc_ptr true_c2_70847; clc_ptr true_c2_70849;
  clc_ptr true_c2_70850; clc_ptr true_c2_70855; clc_ptr true_c2_70856;
  clc_ptr true_c2_70857; clc_ptr true_c2_70860; clc_ptr true_c2_70861;
  clc_ptr true_c2_70864; clc_ptr true_c2_70865; clc_ptr true_c2_70868;
  clc_ptr true_c2_70870; clc_ptr zero_c4_70750; clc_ptr zero_c4_70781;
  clc_ptr zero_c4_70832;
  instr_struct(&zero_c4_70750, 4, 0);
  instr_struct(&succ_c5_70751, 5, 1,
    zero_c4_70750);
  instr_struct(&succ_c5_70752, 5, 1,
    succ_c5_70751);
  instr_call(&tmp_70753, env[17], succ_c5_70752);
  instr_struct(&false_c3_70754, 3, 0);
  instr_struct(&true_c2_70755, 2, 0);
  instr_struct(&true_c2_70756, 2, 0);
  instr_struct(&false_c3_70757, 3, 0);
  instr_struct(&true_c2_70758, 2, 0);
  instr_struct(&false_c3_70759, 3, 0);
  instr_struct(&false_c3_70760, 3, 0);
  instr_struct(&true_c2_70761, 2, 0);
  instr_struct(&Ascii_c16_70762, 16, 8,
    false_c3_70754, true_c2_70755, true_c2_70756, false_c3_70757,
    true_c2_70758, false_c3_70759, false_c3_70760, true_c2_70761);
  instr_struct(&false_c3_70763, 3, 0);
  instr_struct(&true_c2_70764, 2, 0);
  instr_struct(&true_c2_70765, 2, 0);
  instr_struct(&false_c3_70766, 3, 0);
  instr_struct(&false_c3_70767, 3, 0);
  instr_struct(&true_c2_70768, 2, 0);
  instr_struct(&true_c2_70769, 2, 0);
  instr_struct(&false_c3_70770, 3, 0);
  instr_struct(&Ascii_c16_70771, 16, 8,
    false_c3_70763, true_c2_70764, true_c2_70765, false_c3_70766,
    false_c3_70767, true_c2_70768, true_c2_70769, false_c3_70770);
  instr_struct(&EmptyString_c17_70772, 17, 0);
  instr_struct(&String_c18_70773, 18, 2,
    Ascii_c16_70771, EmptyString_c17_70772);
  instr_struct(&String_c18_70774, 18, 2,
    Ascii_c16_70762, String_c18_70773);
  instr_call(&tmp_70775, env[18], String_c18_70774);
  instr_call(&tmp_70776, env[9], tmp_70775);
  instr_call(&tmp_70777, tmp_70776, env[3]);
  instr_call(&tmp_70778, tmp_70753, tmp_70777);
  instr_call(&tmp_70779, env[14], tmp_70778);
  instr_call(&tmp_70780, env[9], tmp_70779);
  instr_struct(&zero_c4_70781, 4, 0);
  instr_struct(&succ_c5_70782, 5, 1,
    zero_c4_70781);
  instr_struct(&succ_c5_70783, 5, 1,
    succ_c5_70782);
  instr_call(&tmp_70784, env[17], succ_c5_70783);
  instr_struct(&false_c3_70785, 3, 0);
  instr_struct(&true_c2_70786, 2, 0);
  instr_struct(&true_c2_70787, 2, 0);
  instr_struct(&true_c2_70788, 2, 0);
  instr_struct(&false_c3_70789, 3, 0);
  instr_struct(&true_c2_70790, 2, 0);
  instr_struct(&false_c3_70791, 3, 0);
  instr_struct(&false_c3_70792, 3, 0);
  instr_struct(&Ascii_c16_70793, 16, 8,
    false_c3_70785, true_c2_70786, true_c2_70787, true_c2_70788,
    false_c3_70789, true_c2_70790, false_c3_70791, false_c3_70792);
  instr_struct(&false_c3_70794, 3, 0);
  instr_struct(&true_c2_70795, 2, 0);
  instr_struct(&true_c2_70796, 2, 0);
  instr_struct(&false_c3_70797, 3, 0);
  instr_struct(&true_c2_70798, 2, 0);
  instr_struct(&false_c3_70799, 3, 0);
  instr_struct(&false_c3_70800, 3, 0);
  instr_struct(&false_c3_70801, 3, 0);
  instr_struct(&Ascii_c16_70802, 16, 8,
    false_c3_70794, true_c2_70795, true_c2_70796, false_c3_70797,
    true_c2_70798, false_c3_70799, false_c3_70800, false_c3_70801);
  instr_struct(&false_c3_70803, 3, 0);
  instr_struct(&true_c2_70804, 2, 0);
  instr_struct(&true_c2_70805, 2, 0);
  instr_struct(&false_c3_70806, 3, 0);
  instr_struct(&false_c3_70807, 3, 0);
  instr_struct(&true_c2_70808, 2, 0);
  instr_struct(&false_c3_70809, 3, 0);
  instr_struct(&true_c2_70810, 2, 0);
  instr_struct(&Ascii_c16_70811, 16, 8,
    false_c3_70803, true_c2_70804, true_c2_70805, false_c3_70806,
    false_c3_70807, true_c2_70808, false_c3_70809, true_c2_70810);
  instr_struct(&false_c3_70812, 3, 0);
  instr_struct(&true_c2_70813, 2, 0);
  instr_struct(&true_c2_70814, 2, 0);
  instr_struct(&false_c3_70815, 3, 0);
  instr_struct(&true_c2_70816, 2, 0);
  instr_struct(&true_c2_70817, 2, 0);
  instr_struct(&true_c2_70818, 2, 0);
  instr_struct(&false_c3_70819, 3, 0);
  instr_struct(&Ascii_c16_70820, 16, 8,
    false_c3_70812, true_c2_70813, true_c2_70814, false_c3_70815,
    true_c2_70816, true_c2_70817, true_c2_70818, false_c3_70819);
  instr_struct(&EmptyString_c17_70821, 17, 0);
  instr_struct(&String_c18_70822, 18, 2,
    Ascii_c16_70820, EmptyString_c17_70821);
  instr_struct(&String_c18_70823, 18, 2,
    Ascii_c16_70811, String_c18_70822);
  instr_struct(&String_c18_70824, 18, 2,
    Ascii_c16_70802, String_c18_70823);
  instr_struct(&String_c18_70825, 18, 2,
    Ascii_c16_70793, String_c18_70824);
  instr_call(&tmp_70826, env[18], String_c18_70825);
  instr_call(&tmp_70827, env[9], tmp_70826);
  instr_call(&tmp_70828, tmp_70827, env[1]);
  instr_call(&tmp_70829, tmp_70784, tmp_70828);
  instr_call(&tmp_70830, env[14], tmp_70829);
  instr_call(&tmp_70831, env[9], tmp_70830);
  instr_struct(&zero_c4_70832, 4, 0);
  instr_struct(&succ_c5_70833, 5, 1,
    zero_c4_70832);
  instr_struct(&succ_c5_70834, 5, 1,
    succ_c5_70833);
  instr_call(&tmp_70835, env[17], succ_c5_70834);
  instr_struct(&false_c3_70836, 3, 0);
  instr_struct(&true_c2_70837, 2, 0);
  instr_struct(&true_c2_70838, 2, 0);
  instr_struct(&false_c3_70839, 3, 0);
  instr_struct(&false_c3_70840, 3, 0);
  instr_struct(&true_c2_70841, 2, 0);
  instr_struct(&false_c3_70842, 3, 0);
  instr_struct(&true_c2_70843, 2, 0);
  instr_struct(&Ascii_c16_70844, 16, 8,
    false_c3_70836, true_c2_70837, true_c2_70838, false_c3_70839,
    false_c3_70840, true_c2_70841, false_c3_70842, true_c2_70843);
  instr_struct(&false_c3_70845, 3, 0);
  instr_struct(&true_c2_70846, 2, 0);
  instr_struct(&true_c2_70847, 2, 0);
  instr_struct(&false_c3_70848, 3, 0);
  instr_struct(&true_c2_70849, 2, 0);
  instr_struct(&true_c2_70850, 2, 0);
  instr_struct(&false_c3_70851, 3, 0);
  instr_struct(&false_c3_70852, 3, 0);
  instr_struct(&Ascii_c16_70853, 16, 8,
    false_c3_70845, true_c2_70846, true_c2_70847, false_c3_70848,
    true_c2_70849, true_c2_70850, false_c3_70851, false_c3_70852);
  instr_struct(&false_c3_70854, 3, 0);
  instr_struct(&true_c2_70855, 2, 0);
  instr_struct(&true_c2_70856, 2, 0);
  instr_struct(&true_c2_70857, 2, 0);
  instr_struct(&false_c3_70858, 3, 0);
  instr_struct(&false_c3_70859, 3, 0);
  instr_struct(&true_c2_70860, 2, 0);
  instr_struct(&true_c2_70861, 2, 0);
  instr_struct(&Ascii_c16_70862, 16, 8,
    false_c3_70854, true_c2_70855, true_c2_70856, true_c2_70857,
    false_c3_70858, false_c3_70859, true_c2_70860, true_c2_70861);
  instr_struct(&false_c3_70863, 3, 0);
  instr_struct(&true_c2_70864, 2, 0);
  instr_struct(&true_c2_70865, 2, 0);
  instr_struct(&false_c3_70866, 3, 0);
  instr_struct(&false_c3_70867, 3, 0);
  instr_struct(&true_c2_70868, 2, 0);
  instr_struct(&false_c3_70869, 3, 0);
  instr_struct(&true_c2_70870, 2, 0);
  instr_struct(&Ascii_c16_70871, 16, 8,
    false_c3_70863, true_c2_70864, true_c2_70865, false_c3_70866,
    false_c3_70867, true_c2_70868, false_c3_70869, true_c2_70870);
  instr_struct(&EmptyString_c17_70872, 17, 0);
  instr_struct(&String_c18_70873, 18, 2,
    Ascii_c16_70871, EmptyString_c17_70872);
  instr_struct(&String_c18_70874, 18, 2,
    Ascii_c16_70862, String_c18_70873);
  instr_struct(&String_c18_70875, 18, 2,
    Ascii_c16_70853, String_c18_70874);
  instr_struct(&String_c18_70876, 18, 2,
    Ascii_c16_70844, String_c18_70875);
  instr_call(&tmp_70877, env[18], String_c18_70876);
  instr_call(&tmp_70878, env[9], tmp_70877);
  instr_call(&tmp_70879, tmp_70878, _70749);
  instr_call(&tmp_70880, tmp_70835, tmp_70879);
  instr_call(&tmp_70881, env[14], tmp_70880);
  instr_call(&tmp_70882, tmp_70831, tmp_70881);
  instr_call(&tmp_70883, tmp_70780, tmp_70882);
  instr_call(&tmp_70884, env[14], tmp_70883);
  return tmp_70884;
}

clc_ptr lam_70887(clc_ptr _70747, clc_env env)
{
  clc_ptr clo_70886;
  instr_clo(&clo_70886, &lam_70885, 39,
    0, _70747, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30],
    env[31], env[32], env[33], env[34], env[35], env[36]);
  return clo_70886;
}

clc_ptr ifthen_70889(clc_ptr _70745, clc_env env)
{
  clc_ptr clo_70888;
  instr_clo(&clo_70888, &lam_70887, 37,
    0, _70745, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30],
    env[31], env[32], env[33], env[34]);
  return clo_70888;
}

clc_ptr lam_70913(clc_ptr _70911, clc_env env)
{
  clc_ptr case_70912;
  switch(((clc_node)_70911)->tag){
    case 1: instr_mov(&case_70912, env[38]);
            break;}
  return case_70912;
}

int main()
{
  clc_ptr _301; clc_ptr Ascii_c16_70092; clc_ptr Ascii_c16_70624;
  clc_ptr Ascii_c16_70636; clc_ptr Ascii_c16_70645; clc_ptr Ascii_c16_70658;
  clc_ptr Ascii_c16_70670; clc_ptr Ascii_c16_70682; clc_ptr Ascii_c16_70691;
  clc_ptr Ascii_c16_70704; clc_ptr Ascii_c16_70716; clc_ptr Ascii_c16_70728;
  clc_ptr Ascii_c16_70740; clc_ptr DocBreak_c26_70095;
  clc_ptr DocNil_c22_70069; clc_ptr EmptyString_c17_70093;
  clc_ptr EmptyString_c17_70625; clc_ptr EmptyString_c17_70646;
  clc_ptr EmptyString_c17_70659; clc_ptr EmptyString_c17_70671;
  clc_ptr EmptyString_c17_70692; clc_ptr EmptyString_c17_70705;
  clc_ptr EmptyString_c17_70717; clc_ptr EmptyString_c17_70729;
  clc_ptr EmptyString_c17_70741; clc_ptr String_c18_70094;
  clc_ptr String_c18_70626; clc_ptr String_c18_70647;
  clc_ptr String_c18_70648; clc_ptr String_c18_70660;
  clc_ptr String_c18_70672; clc_ptr String_c18_70693;
  clc_ptr String_c18_70694; clc_ptr String_c18_70706;
  clc_ptr String_c18_70718; clc_ptr String_c18_70730;
  clc_ptr String_c18_70742; clc_ptr addn_3; clc_ptr addn_69924;
  clc_ptr binop_282; clc_ptr binop_70615; clc_ptr break_154;
  clc_ptr breakWith_155; clc_ptr breakWith_70100; clc_ptr cat_67;
  clc_ptr cat_69962; clc_ptr clo_70914; clc_ptr close_err_130;
  clc_ptr close_err_70059; clc_ptr close_in_114; clc_ptr close_in_70017;
  clc_ptr close_out_122; clc_ptr close_out_70038; clc_ptr cond_289;
  clc_ptr dcons_140; clc_ptr dcons_70068; clc_ptr doc_299; clc_ptr empty_145;
  clc_ptr expr1_290; clc_ptr expr2_291; clc_ptr false_c3_70084;
  clc_ptr false_c3_70085; clc_ptr false_c3_70087; clc_ptr false_c3_70088;
  clc_ptr false_c3_70089; clc_ptr false_c3_70090; clc_ptr false_c3_70091;
  clc_ptr false_c3_70616; clc_ptr false_c3_70619; clc_ptr false_c3_70620;
  clc_ptr false_c3_70621; clc_ptr false_c3_70622; clc_ptr false_c3_70628;
  clc_ptr false_c3_70629; clc_ptr false_c3_70634; clc_ptr false_c3_70637;
  clc_ptr false_c3_70638; clc_ptr false_c3_70643; clc_ptr false_c3_70650;
  clc_ptr false_c3_70653; clc_ptr false_c3_70654; clc_ptr false_c3_70655;
  clc_ptr false_c3_70657; clc_ptr false_c3_70662; clc_ptr false_c3_70665;
  clc_ptr false_c3_70666; clc_ptr false_c3_70667; clc_ptr false_c3_70668;
  clc_ptr false_c3_70674; clc_ptr false_c3_70675; clc_ptr false_c3_70680;
  clc_ptr false_c3_70681; clc_ptr false_c3_70683; clc_ptr false_c3_70684;
  clc_ptr false_c3_70689; clc_ptr false_c3_70690; clc_ptr false_c3_70696;
  clc_ptr false_c3_70699; clc_ptr false_c3_70700; clc_ptr false_c3_70701;
  clc_ptr false_c3_70703; clc_ptr false_c3_70708; clc_ptr false_c3_70711;
  clc_ptr false_c3_70712; clc_ptr false_c3_70713; clc_ptr false_c3_70714;
  clc_ptr false_c3_70720; clc_ptr false_c3_70721; clc_ptr false_c3_70723;
  clc_ptr false_c3_70725; clc_ptr false_c3_70732; clc_ptr false_c3_70735;
  clc_ptr false_c3_70736; clc_ptr false_c3_70737; clc_ptr false_c3_70739;
  clc_ptr fits_175; clc_ptr fits_70231; clc_ptr format_218;
  clc_ptr format_70323; clc_ptr group_158; clc_ptr group_70105;
  clc_ptr ifthen_292; clc_ptr ifthen_70890; clc_ptr join_275;
  clc_ptr join_70589; clc_ptr lt_84; clc_ptr lt_69980; clc_ptr nest_149;
  clc_ptr nest_70083; clc_ptr pretty_269; clc_ptr pretty_70358;
  clc_ptr printerr_125; clc_ptr printerr_70051; clc_ptr printline_117;
  clc_ptr printline_70030; clc_ptr readline_109; clc_ptr readline_70009;
  clc_ptr sdocToString_165; clc_ptr sdocToString_70157;
  clc_ptr stderr_rec_102; clc_ptr stderr_rec_69995; clc_ptr stderr_t_108;
  clc_ptr stdin_rec_94; clc_ptr stdin_rec_69985; clc_ptr stdin_t_106;
  clc_ptr stdout_300; clc_ptr stdout_70894; clc_ptr stdout_rec_98;
  clc_ptr stdout_rec_69990; clc_ptr stdout_t_107; clc_ptr strlen_74;
  clc_ptr strlen_69972; clc_ptr subn_9; clc_ptr subn_69944;
  clc_ptr succ_c5_70897; clc_ptr succ_c5_70898; clc_ptr succ_c5_70899;
  clc_ptr succ_c5_70900; clc_ptr succ_c5_70901; clc_ptr succ_c5_70902;
  clc_ptr succ_c5_70903; clc_ptr succ_c5_70904; clc_ptr succ_c5_70905;
  clc_ptr succ_c5_70906; clc_ptr text_146; clc_ptr text_70074;
  clc_ptr tmp_69997; clc_ptr tmp_69999; clc_ptr tmp_70001; clc_ptr tmp_70627;
  clc_ptr tmp_70649; clc_ptr tmp_70661; clc_ptr tmp_70673; clc_ptr tmp_70695;
  clc_ptr tmp_70707; clc_ptr tmp_70719; clc_ptr tmp_70731; clc_ptr tmp_70743;
  clc_ptr tmp_70891; clc_ptr tmp_70892; clc_ptr tmp_70893; clc_ptr tmp_70895;
  clc_ptr tmp_70907; clc_ptr tmp_70908; clc_ptr tmp_70909; clc_ptr tmp_70915;
  clc_ptr tmp_70916; clc_ptr true_c2_70086; clc_ptr true_c2_70617;
  clc_ptr true_c2_70618; clc_ptr true_c2_70623; clc_ptr true_c2_70630;
  clc_ptr true_c2_70631; clc_ptr true_c2_70632; clc_ptr true_c2_70633;
  clc_ptr true_c2_70635; clc_ptr true_c2_70639; clc_ptr true_c2_70640;
  clc_ptr true_c2_70641; clc_ptr true_c2_70642; clc_ptr true_c2_70644;
  clc_ptr true_c2_70651; clc_ptr true_c2_70652; clc_ptr true_c2_70656;
  clc_ptr true_c2_70663; clc_ptr true_c2_70664; clc_ptr true_c2_70669;
  clc_ptr true_c2_70676; clc_ptr true_c2_70677; clc_ptr true_c2_70678;
  clc_ptr true_c2_70679; clc_ptr true_c2_70685; clc_ptr true_c2_70686;
  clc_ptr true_c2_70687; clc_ptr true_c2_70688; clc_ptr true_c2_70697;
  clc_ptr true_c2_70698; clc_ptr true_c2_70702; clc_ptr true_c2_70709;
  clc_ptr true_c2_70710; clc_ptr true_c2_70715; clc_ptr true_c2_70722;
  clc_ptr true_c2_70724; clc_ptr true_c2_70726; clc_ptr true_c2_70727;
  clc_ptr true_c2_70733; clc_ptr true_c2_70734; clc_ptr true_c2_70738;
  clc_ptr tt_c1_69996; clc_ptr tt_c1_69998; clc_ptr tt_c1_70000;
  clc_ptr zero_c4_70896;
  instr_init();
  instr_clo(&addn_69924, &addn_69923, 2, 0, 0);
  instr_mov(&addn_3, addn_69924);
  instr_clo(&subn_69944, &subn_69943, 3, 0, addn_3, 0);
  instr_mov(&subn_9, subn_69944);
  instr_clo(&cat_69962, &cat_69961, 4, 0, subn_9, addn_3, 0);
  instr_mov(&cat_67, cat_69962);
  instr_clo(&strlen_69972, &strlen_69971, 5, 0, cat_67, subn_9, addn_3, 0);
  instr_mov(&strlen_74, strlen_69972);
  instr_clo(&lt_69980, &lt_69979, 6,
    0, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&lt_84, lt_69980);
  instr_clo(&stdin_rec_69985, &stdin_rec_69984, 7,
    0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdin_rec_94, stdin_rec_69985);
  instr_clo(&stdout_rec_69990, &stdout_rec_69989, 8,
    0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdout_rec_98, stdout_rec_69990);
  instr_clo(&stderr_rec_69995, &stderr_rec_69994, 9,
    0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3,
    0);
  instr_mov(&stderr_rec_102, stderr_rec_69995);
  instr_struct(&tt_c1_69996, 1, 0);
  instr_call(&tmp_69997, stdin_rec_94, tt_c1_69996);
  instr_mov(&stdin_t_106, tmp_69997);
  instr_struct(&tt_c1_69998, 1, 0);
  instr_call(&tmp_69999, stdout_rec_98, tt_c1_69998);
  instr_mov(&stdout_t_107, tmp_69999);
  instr_struct(&tt_c1_70000, 1, 0);
  instr_call(&tmp_70001, stderr_rec_102, tt_c1_70000);
  instr_mov(&stderr_t_108, tmp_70001);
  instr_clo(&readline_70009, &readline_70008, 13,
    0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&readline_109, readline_70009);
  instr_clo(&close_in_70017, &close_in_70016, 14,
    0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_in_114, close_in_70017);
  instr_clo(&printline_70030, &printline_70029, 15,
    0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&printline_117, printline_70030);
  instr_clo(&close_out_70038, &close_out_70037, 16,
    0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_out_122, close_out_70038);
  instr_clo(&printerr_70051, &printerr_70050, 17,
    0, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&printerr_125, printerr_70051);
  instr_clo(&close_err_70059, &close_err_70058, 18,
    0, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_err_130, close_err_70059);
  instr_clo(&dcons_70068, &dcons_70067, 19,
    0, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&dcons_140, dcons_70068);
  instr_struct(&DocNil_c22_70069, 22, 0);
  instr_mov(&empty_145, DocNil_c22_70069);
  instr_clo(&text_70074, &text_70073, 21,
    0, empty_145, dcons_140, close_err_130, printerr_125, close_out_122,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&text_146, text_70074);
  instr_clo(&nest_70083, &nest_70082, 22,
    0, text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&nest_149, nest_70083);
  instr_struct(&false_c3_70084, 3, 0);
  instr_struct(&false_c3_70085, 3, 0);
  instr_struct(&true_c2_70086, 2, 0);
  instr_struct(&false_c3_70087, 3, 0);
  instr_struct(&false_c3_70088, 3, 0);
  instr_struct(&false_c3_70089, 3, 0);
  instr_struct(&false_c3_70090, 3, 0);
  instr_struct(&false_c3_70091, 3, 0);
  instr_struct(&Ascii_c16_70092, 16, 8,
    false_c3_70084, false_c3_70085, true_c2_70086, false_c3_70087,
    false_c3_70088, false_c3_70089, false_c3_70090, false_c3_70091);
  instr_struct(&EmptyString_c17_70093, 17, 0);
  instr_struct(&String_c18_70094, 18, 2,
    Ascii_c16_70092, EmptyString_c17_70093);
  instr_struct(&DocBreak_c26_70095, 26, 1,
    String_c18_70094);
  instr_mov(&break_154, DocBreak_c26_70095);
  instr_clo(&breakWith_70100, &breakWith_70099, 24,
    0, break_154, nest_149, text_146, empty_145, dcons_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&breakWith_155, breakWith_70100);
  instr_clo(&group_70105, &group_70104, 25,
    0, breakWith_155, break_154, nest_149, text_146, empty_145, dcons_140,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&group_158, group_70105);
  instr_clo(&sdocToString_70157, &sdocToString_70156, 26,
    0, group_158, breakWith_155, break_154, nest_149, text_146, empty_145,
    dcons_140, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&sdocToString_165, sdocToString_70157);
  instr_clo(&fits_70231, &fits_70230, 27,
    0, sdocToString_165, group_158, breakWith_155, break_154, nest_149,
    text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&fits_175, fits_70231);
  instr_clo(&format_70323, &format_70322, 28,
    0, fits_175, sdocToString_165, group_158, breakWith_155, break_154,
    nest_149, text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&format_218, format_70323);
  instr_clo(&pretty_70358, &pretty_70357, 29,
    0, format_218, fits_175, sdocToString_165, group_158, breakWith_155,
    break_154, nest_149, text_146, empty_145, dcons_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&pretty_269, pretty_70358);
  instr_clo(&join_70589, &join_70588, 30,
    0, pretty_269, format_218, fits_175, sdocToString_165, group_158,
    breakWith_155, break_154, nest_149, text_146, empty_145, dcons_140,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&join_275, join_70589);
  instr_clo(&binop_70615, &binop_70614, 31,
    0, join_275, pretty_269, format_218, fits_175, sdocToString_165,
    group_158, breakWith_155, break_154, nest_149, text_146, empty_145,
    dcons_140, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&binop_282, binop_70615);
  instr_struct(&false_c3_70616, 3, 0);
  instr_struct(&true_c2_70617, 2, 0);
  instr_struct(&true_c2_70618, 2, 0);
  instr_struct(&false_c3_70619, 3, 0);
  instr_struct(&false_c3_70620, 3, 0);
  instr_struct(&false_c3_70621, 3, 0);
  instr_struct(&false_c3_70622, 3, 0);
  instr_struct(&true_c2_70623, 2, 0);
  instr_struct(&Ascii_c16_70624, 16, 8,
    false_c3_70616, true_c2_70617, true_c2_70618, false_c3_70619,
    false_c3_70620, false_c3_70621, false_c3_70622, true_c2_70623);
  instr_struct(&EmptyString_c17_70625, 17, 0);
  instr_struct(&String_c18_70626, 18, 2,
    Ascii_c16_70624, EmptyString_c17_70625);
  instr_call(&tmp_70627, binop_282, String_c18_70626);
  instr_struct(&false_c3_70628, 3, 0);
  instr_struct(&false_c3_70629, 3, 0);
  instr_struct(&true_c2_70630, 2, 0);
  instr_struct(&true_c2_70631, 2, 0);
  instr_struct(&true_c2_70632, 2, 0);
  instr_struct(&true_c2_70633, 2, 0);
  instr_struct(&false_c3_70634, 3, 0);
  instr_struct(&true_c2_70635, 2, 0);
  instr_struct(&Ascii_c16_70636, 16, 8,
    false_c3_70628, false_c3_70629, true_c2_70630, true_c2_70631,
    true_c2_70632, true_c2_70633, false_c3_70634, true_c2_70635);
  instr_struct(&false_c3_70637, 3, 0);
  instr_struct(&false_c3_70638, 3, 0);
  instr_struct(&true_c2_70639, 2, 0);
  instr_struct(&true_c2_70640, 2, 0);
  instr_struct(&true_c2_70641, 2, 0);
  instr_struct(&true_c2_70642, 2, 0);
  instr_struct(&false_c3_70643, 3, 0);
  instr_struct(&true_c2_70644, 2, 0);
  instr_struct(&Ascii_c16_70645, 16, 8,
    false_c3_70637, false_c3_70638, true_c2_70639, true_c2_70640,
    true_c2_70641, true_c2_70642, false_c3_70643, true_c2_70644);
  instr_struct(&EmptyString_c17_70646, 17, 0);
  instr_struct(&String_c18_70647, 18, 2,
    Ascii_c16_70645, EmptyString_c17_70646);
  instr_struct(&String_c18_70648, 18, 2,
    Ascii_c16_70636, String_c18_70647);
  instr_call(&tmp_70649, tmp_70627, String_c18_70648);
  instr_struct(&false_c3_70650, 3, 0);
  instr_struct(&true_c2_70651, 2, 0);
  instr_struct(&true_c2_70652, 2, 0);
  instr_struct(&false_c3_70653, 3, 0);
  instr_struct(&false_c3_70654, 3, 0);
  instr_struct(&false_c3_70655, 3, 0);
  instr_struct(&true_c2_70656, 2, 0);
  instr_struct(&false_c3_70657, 3, 0);
  instr_struct(&Ascii_c16_70658, 16, 8,
    false_c3_70650, true_c2_70651, true_c2_70652, false_c3_70653,
    false_c3_70654, false_c3_70655, true_c2_70656, false_c3_70657);
  instr_struct(&EmptyString_c17_70659, 17, 0);
  instr_struct(&String_c18_70660, 18, 2,
    Ascii_c16_70658, EmptyString_c17_70659);
  instr_call(&tmp_70661, tmp_70649, String_c18_70660);
  instr_mov(&cond_289, tmp_70661);
  instr_struct(&false_c3_70662, 3, 0);
  instr_struct(&true_c2_70663, 2, 0);
  instr_struct(&true_c2_70664, 2, 0);
  instr_struct(&false_c3_70665, 3, 0);
  instr_struct(&false_c3_70666, 3, 0);
  instr_struct(&false_c3_70667, 3, 0);
  instr_struct(&false_c3_70668, 3, 0);
  instr_struct(&true_c2_70669, 2, 0);
  instr_struct(&Ascii_c16_70670, 16, 8,
    false_c3_70662, true_c2_70663, true_c2_70664, false_c3_70665,
    false_c3_70666, false_c3_70667, false_c3_70668, true_c2_70669);
  instr_struct(&EmptyString_c17_70671, 17, 0);
  instr_struct(&String_c18_70672, 18, 2,
    Ascii_c16_70670, EmptyString_c17_70671);
  instr_call(&tmp_70673, binop_282, String_c18_70672);
  instr_struct(&false_c3_70674, 3, 0);
  instr_struct(&false_c3_70675, 3, 0);
  instr_struct(&true_c2_70676, 2, 0);
  instr_struct(&true_c2_70677, 2, 0);
  instr_struct(&true_c2_70678, 2, 0);
  instr_struct(&true_c2_70679, 2, 0);
  instr_struct(&false_c3_70680, 3, 0);
  instr_struct(&false_c3_70681, 3, 0);
  instr_struct(&Ascii_c16_70682, 16, 8,
    false_c3_70674, false_c3_70675, true_c2_70676, true_c2_70677,
    true_c2_70678, true_c2_70679, false_c3_70680, false_c3_70681);
  instr_struct(&false_c3_70683, 3, 0);
  instr_struct(&false_c3_70684, 3, 0);
  instr_struct(&true_c2_70685, 2, 0);
  instr_struct(&true_c2_70686, 2, 0);
  instr_struct(&true_c2_70687, 2, 0);
  instr_struct(&true_c2_70688, 2, 0);
  instr_struct(&false_c3_70689, 3, 0);
  instr_struct(&false_c3_70690, 3, 0);
  instr_struct(&Ascii_c16_70691, 16, 8,
    false_c3_70683, false_c3_70684, true_c2_70685, true_c2_70686,
    true_c2_70687, true_c2_70688, false_c3_70689, false_c3_70690);
  instr_struct(&EmptyString_c17_70692, 17, 0);
  instr_struct(&String_c18_70693, 18, 2,
    Ascii_c16_70691, EmptyString_c17_70692);
  instr_struct(&String_c18_70694, 18, 2,
    Ascii_c16_70682, String_c18_70693);
  instr_call(&tmp_70695, tmp_70673, String_c18_70694);
  instr_struct(&false_c3_70696, 3, 0);
  instr_struct(&true_c2_70697, 2, 0);
  instr_struct(&true_c2_70698, 2, 0);
  instr_struct(&false_c3_70699, 3, 0);
  instr_struct(&false_c3_70700, 3, 0);
  instr_struct(&false_c3_70701, 3, 0);
  instr_struct(&true_c2_70702, 2, 0);
  instr_struct(&false_c3_70703, 3, 0);
  instr_struct(&Ascii_c16_70704, 16, 8,
    false_c3_70696, true_c2_70697, true_c2_70698, false_c3_70699,
    false_c3_70700, false_c3_70701, true_c2_70702, false_c3_70703);
  instr_struct(&EmptyString_c17_70705, 17, 0);
  instr_struct(&String_c18_70706, 18, 2,
    Ascii_c16_70704, EmptyString_c17_70705);
  instr_call(&tmp_70707, tmp_70695, String_c18_70706);
  instr_mov(&expr1_290, tmp_70707);
  instr_struct(&false_c3_70708, 3, 0);
  instr_struct(&true_c2_70709, 2, 0);
  instr_struct(&true_c2_70710, 2, 0);
  instr_struct(&false_c3_70711, 3, 0);
  instr_struct(&false_c3_70712, 3, 0);
  instr_struct(&false_c3_70713, 3, 0);
  instr_struct(&false_c3_70714, 3, 0);
  instr_struct(&true_c2_70715, 2, 0);
  instr_struct(&Ascii_c16_70716, 16, 8,
    false_c3_70708, true_c2_70709, true_c2_70710, false_c3_70711,
    false_c3_70712, false_c3_70713, false_c3_70714, true_c2_70715);
  instr_struct(&EmptyString_c17_70717, 17, 0);
  instr_struct(&String_c18_70718, 18, 2,
    Ascii_c16_70716, EmptyString_c17_70717);
  instr_call(&tmp_70719, binop_282, String_c18_70718);
  instr_struct(&false_c3_70720, 3, 0);
  instr_struct(&false_c3_70721, 3, 0);
  instr_struct(&true_c2_70722, 2, 0);
  instr_struct(&false_c3_70723, 3, 0);
  instr_struct(&true_c2_70724, 2, 0);
  instr_struct(&false_c3_70725, 3, 0);
  instr_struct(&true_c2_70726, 2, 0);
  instr_struct(&true_c2_70727, 2, 0);
  instr_struct(&Ascii_c16_70728, 16, 8,
    false_c3_70720, false_c3_70721, true_c2_70722, false_c3_70723,
    true_c2_70724, false_c3_70725, true_c2_70726, true_c2_70727);
  instr_struct(&EmptyString_c17_70729, 17, 0);
  instr_struct(&String_c18_70730, 18, 2,
    Ascii_c16_70728, EmptyString_c17_70729);
  instr_call(&tmp_70731, tmp_70719, String_c18_70730);
  instr_struct(&false_c3_70732, 3, 0);
  instr_struct(&true_c2_70733, 2, 0);
  instr_struct(&true_c2_70734, 2, 0);
  instr_struct(&false_c3_70735, 3, 0);
  instr_struct(&false_c3_70736, 3, 0);
  instr_struct(&false_c3_70737, 3, 0);
  instr_struct(&true_c2_70738, 2, 0);
  instr_struct(&false_c3_70739, 3, 0);
  instr_struct(&Ascii_c16_70740, 16, 8,
    false_c3_70732, true_c2_70733, true_c2_70734, false_c3_70735,
    false_c3_70736, false_c3_70737, true_c2_70738, false_c3_70739);
  instr_struct(&EmptyString_c17_70741, 17, 0);
  instr_struct(&String_c18_70742, 18, 2,
    Ascii_c16_70740, EmptyString_c17_70741);
  instr_call(&tmp_70743, tmp_70731, String_c18_70742);
  instr_mov(&expr2_291, tmp_70743);
  instr_clo(&ifthen_70890, &ifthen_70889, 35,
    0, expr2_291, expr1_290, cond_289, binop_282, join_275, pretty_269,
    format_218, fits_175, sdocToString_165, group_158, breakWith_155,
    break_154, nest_149, text_146, empty_145, dcons_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&ifthen_292, ifthen_70890);
  instr_call(&tmp_70891, ifthen_292, cond_289);
  instr_call(&tmp_70892, tmp_70891, expr1_290);
  instr_call(&tmp_70893, tmp_70892, expr2_291);
  instr_mov(&doc_299, tmp_70893);
  instr_trg(&stdout_300, &proc_stdout);
  instr_call(&tmp_70895, printline_117, stdout_300);
  instr_struct(&zero_c4_70896, 4, 0);
  instr_struct(&succ_c5_70897, 5, 1,
    zero_c4_70896);
  instr_struct(&succ_c5_70898, 5, 1,
    succ_c5_70897);
  instr_struct(&succ_c5_70899, 5, 1,
    succ_c5_70898);
  instr_struct(&succ_c5_70900, 5, 1,
    succ_c5_70899);
  instr_struct(&succ_c5_70901, 5, 1,
    succ_c5_70900);
  instr_struct(&succ_c5_70902, 5, 1,
    succ_c5_70901);
  instr_struct(&succ_c5_70903, 5, 1,
    succ_c5_70902);
  instr_struct(&succ_c5_70904, 5, 1,
    succ_c5_70903);
  instr_struct(&succ_c5_70905, 5, 1,
    succ_c5_70904);
  instr_struct(&succ_c5_70906, 5, 1,
    succ_c5_70905);
  instr_call(&tmp_70907, pretty_269, succ_c5_70906);
  instr_call(&tmp_70908, tmp_70907, doc_299);
  instr_call(&tmp_70909, tmp_70895, tmp_70908);
  instr_mov(&stdout_70894, tmp_70909);
  instr_clo(&clo_70914, &lam_70913, 39,
    0, stdout_70894, stdout_300, doc_299, ifthen_292, expr2_291, expr1_290,
    cond_289, binop_282, join_275, pretty_269, format_218, fits_175,
    sdocToString_165, group_158, breakWith_155, break_154, nest_149,
    text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_call(&tmp_70915, close_out_122, stdout_70894);
  instr_call(&tmp_70916, clo_70914, tmp_70915);
  instr_mov(&_301, tmp_70916);
  return 0;
}
