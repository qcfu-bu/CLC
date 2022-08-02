#include "runtime.h"

CLC_ptr lam_69913(CLC_ptr _69912, CLC_env env)
{
  
  
  return _69912;
}

CLC_ptr lam_69921(CLC_ptr _69917, CLC_env env)
{
  CLC_ptr succ_c5_69920; CLC_ptr tmp_69918; CLC_ptr tmp_69919;
  INSTR_call(&tmp_69918, env[3], env[2]);
  INSTR_call(&tmp_69919, tmp_69918, _69917);
  INSTR_struct(&succ_c5_69920, 5, 1,
    tmp_69919);
  return succ_c5_69920;
}

CLC_ptr addn_69923(CLC_ptr _69909, CLC_env env)
{
  CLC_ptr _69915; CLC_ptr case_69910; CLC_ptr clo_69914; CLC_ptr clo_69922;
  switch(((CLC_node)_69909)->tag){
    case 4:
      INSTR_clo(&clo_69914, &lam_69913, 4, 0, _69909, env[0], env[1]);
      INSTR_mov(&case_69910, clo_69914);
      break;
    case 5:
      INSTR_mov(&_69915, ((CLC_node)_69909)->data[0]);
      INSTR_clo(&clo_69922, &lam_69921, 5,
        0, _69909, _69915, env[0], env[1]);
      INSTR_mov(&case_69910, clo_69922);
      break;}
  return case_69910;
}

CLC_ptr lam_69931(CLC_ptr _69929, CLC_env env)
{
  CLC_ptr zero_c4_69930;
  INSTR_struct(&zero_c4_69930, 4, 0);
  return zero_c4_69930;
}

CLC_ptr lam_69941(CLC_ptr _69935, CLC_env env)
{
  CLC_ptr _69938; CLC_ptr case_69936; CLC_ptr succ_c5_69937;
  CLC_ptr tmp_69939; CLC_ptr tmp_69940;
  switch(((CLC_node)_69935)->tag){
    case 4:
      INSTR_struct(&succ_c5_69937, 5, 1,
        env[2]);
      INSTR_mov(&case_69936, succ_c5_69937);
      break;
    case 5:
      INSTR_mov(&_69938, ((CLC_node)_69935)->data[0]);
      INSTR_call(&tmp_69939, env[3], env[2]);
      INSTR_call(&tmp_69940, tmp_69939, _69938);
      INSTR_mov(&case_69936, tmp_69940);
      break;}
  return case_69936;
}

CLC_ptr subn_69943(CLC_ptr _69926, CLC_env env)
{
  CLC_ptr _69933; CLC_ptr case_69927; CLC_ptr clo_69932; CLC_ptr clo_69942;
  switch(((CLC_node)_69926)->tag){
    case 4:
      INSTR_clo(&clo_69932, &lam_69931, 5,
        0, _69926, env[0], env[1], env[2]);
      INSTR_mov(&case_69927, clo_69932);
      break;
    case 5:
      INSTR_mov(&_69933, ((CLC_node)_69926)->data[0]);
      INSTR_clo(&clo_69942, &lam_69941, 6,
        0, _69926, _69933, env[0], env[1], env[2]);
      INSTR_mov(&case_69927, clo_69942);
      break;}
  return case_69927;
}

CLC_ptr lam_69950(CLC_ptr _69949, CLC_env env)
{
  
  
  return _69949;
}

CLC_ptr lam_69959(CLC_ptr _69955, CLC_env env)
{
  CLC_ptr String_c18_69958; CLC_ptr tmp_69956; CLC_ptr tmp_69957;
  INSTR_call(&tmp_69956, env[4], env[3]);
  INSTR_call(&tmp_69957, tmp_69956, _69955);
  INSTR_struct(&String_c18_69958, 18, 2,
    env[2], tmp_69957);
  return String_c18_69958;
}

CLC_ptr cat_69961(CLC_ptr _69946, CLC_env env)
{
  CLC_ptr _69952; CLC_ptr _69953; CLC_ptr case_69947; CLC_ptr clo_69951;
  CLC_ptr clo_69960;
  switch(((CLC_node)_69946)->tag){
    case 17:
      INSTR_clo(&clo_69951, &lam_69950, 6,
        0, _69946, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_69947, clo_69951);
      break;
    case 18:
      INSTR_mov(&_69952, ((CLC_node)_69946)->data[0]);
      INSTR_mov(&_69953, ((CLC_node)_69946)->data[1]);
      INSTR_clo(&clo_69960, &lam_69959, 8,
        0, _69946, _69952, _69953, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_69947, clo_69960);
      break;}
  return case_69947;
}

CLC_ptr strlen_69971(CLC_ptr _69964, CLC_env env)
{
  CLC_ptr _69967; CLC_ptr _69968; CLC_ptr case_69965; CLC_ptr succ_c5_69970;
  CLC_ptr tmp_69969; CLC_ptr zero_c4_69966;
  switch(((CLC_node)_69964)->tag){
    case 17:
      INSTR_struct(&zero_c4_69966, 4, 0);
      INSTR_mov(&case_69965, zero_c4_69966);
      break;
    case 18:
      INSTR_mov(&_69967, ((CLC_node)_69964)->data[0]);
      INSTR_mov(&_69968, ((CLC_node)_69964)->data[1]);
      INSTR_call(&tmp_69969, env[0], _69968);
      INSTR_struct(&succ_c5_69970, 5, 1,
        tmp_69969);
      INSTR_mov(&case_69965, succ_c5_69970);
      break;}
  return case_69965;
}

CLC_ptr lam_69977(CLC_ptr _69976, CLC_env env)
{
  
  
  return 0;
}

CLC_ptr lt_69979(CLC_ptr _69974, CLC_env env)
{
  CLC_ptr clo_69978;
  INSTR_clo(&clo_69978, &lam_69977, 8,
    0, _69974, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_69978;
}

CLC_ptr stdin_rec_69984(CLC_ptr _69982, CLC_env env)
{
  CLC_ptr case_69983;
  switch(((CLC_node)_69982)->tag){
    case 1: INSTR_mov(&case_69983, 0);
            break;}
  return case_69983;
}

CLC_ptr stdout_rec_69989(CLC_ptr _69987, CLC_env env)
{
  CLC_ptr case_69988;
  switch(((CLC_node)_69987)->tag){
    case 1: INSTR_mov(&case_69988, 0);
            break;}
  return case_69988;
}

CLC_ptr stderr_rec_69994(CLC_ptr _69992, CLC_env env)
{
  CLC_ptr case_69993;
  switch(((CLC_node)_69992)->tag){
    case 1: INSTR_mov(&case_69993, 0);
            break;}
  return case_69993;
}

CLC_ptr readline_70008(CLC_ptr _70003, CLC_env env)
{
  CLC_ptr recv_struct_70007; CLC_ptr send_clo_70004; CLC_ptr tmp_70006;
  CLC_ptr true_c2_70005;
  INSTR_send(&send_clo_70004, _70003);
  INSTR_struct(&true_c2_70005, 2, 0);
  INSTR_call(&tmp_70006, send_clo_70004, true_c2_70005);
  INSTR_recv(&recv_struct_70007, tmp_70006, 13);
  return recv_struct_70007;
}

CLC_ptr close_in_70016(CLC_ptr _70011, CLC_env env)
{
  CLC_ptr false_c3_70014; CLC_ptr send_clo_70013; CLC_ptr tmp_70015;
  CLC_ptr unit_struct_70012;
  INSTR_send(&send_clo_70013, _70011);
  INSTR_struct(&false_c3_70014, 3, 0);
  INSTR_call(&tmp_70015, send_clo_70013, false_c3_70014);
  INSTR_struct(&unit_struct_70012, 1, 0);
  return unit_struct_70012;
}

CLC_ptr lam_70027(CLC_ptr _70021, CLC_env env)
{
  CLC_ptr send_clo_70022; CLC_ptr send_clo_70025; CLC_ptr tmp_70024;
  CLC_ptr tmp_70026; CLC_ptr true_c2_70023;
  INSTR_send(&send_clo_70022, env[1]);
  INSTR_struct(&true_c2_70023, 2, 0);
  INSTR_call(&tmp_70024, send_clo_70022, true_c2_70023);
  INSTR_send(&send_clo_70025, tmp_70024);
  INSTR_call(&tmp_70026, send_clo_70025, _70021);
  return tmp_70026;
}

CLC_ptr printline_70029(CLC_ptr _70019, CLC_env env)
{
  CLC_ptr clo_70028;
  INSTR_clo(&clo_70028, &lam_70027, 17,
    0, _70019, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_70028;
}

CLC_ptr close_out_70037(CLC_ptr _70032, CLC_env env)
{
  CLC_ptr false_c3_70035; CLC_ptr send_clo_70034; CLC_ptr tmp_70036;
  CLC_ptr unit_struct_70033;
  INSTR_send(&send_clo_70034, _70032);
  INSTR_struct(&false_c3_70035, 3, 0);
  INSTR_call(&tmp_70036, send_clo_70034, false_c3_70035);
  INSTR_struct(&unit_struct_70033, 1, 0);
  return unit_struct_70033;
}

CLC_ptr lam_70048(CLC_ptr _70042, CLC_env env)
{
  CLC_ptr send_clo_70043; CLC_ptr send_clo_70046; CLC_ptr tmp_70045;
  CLC_ptr tmp_70047; CLC_ptr true_c2_70044;
  INSTR_send(&send_clo_70043, env[1]);
  INSTR_struct(&true_c2_70044, 2, 0);
  INSTR_call(&tmp_70045, send_clo_70043, true_c2_70044);
  INSTR_send(&send_clo_70046, tmp_70045);
  INSTR_call(&tmp_70047, send_clo_70046, _70042);
  return tmp_70047;
}

CLC_ptr printerr_70050(CLC_ptr _70040, CLC_env env)
{
  CLC_ptr clo_70049;
  INSTR_clo(&clo_70049, &lam_70048, 19,
    0, _70040, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16]);
  return clo_70049;
}

CLC_ptr close_err_70058(CLC_ptr _70053, CLC_env env)
{
  CLC_ptr false_c3_70056; CLC_ptr send_clo_70055; CLC_ptr tmp_70057;
  CLC_ptr unit_struct_70054;
  INSTR_send(&send_clo_70055, _70053);
  INSTR_struct(&false_c3_70056, 3, 0);
  INSTR_call(&tmp_70057, send_clo_70055, false_c3_70056);
  INSTR_struct(&unit_struct_70054, 1, 0);
  return unit_struct_70054;
}

CLC_ptr lam_70065(CLC_ptr _70063, CLC_env env)
{
  CLC_ptr DocCons_c23_70064;
  INSTR_struct(&DocCons_c23_70064, 23, 2,
    env[1], _70063);
  return DocCons_c23_70064;
}

CLC_ptr dcons_70067(CLC_ptr _70061, CLC_env env)
{
  CLC_ptr clo_70066;
  INSTR_clo(&clo_70066, &lam_70065, 21,
    0, _70061, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18]);
  return clo_70066;
}

CLC_ptr text_70073(CLC_ptr _70071, CLC_env env)
{
  CLC_ptr DocText_c24_70072;
  INSTR_struct(&DocText_c24_70072, 24, 1,
    _70071);
  return DocText_c24_70072;
}

CLC_ptr lam_70080(CLC_ptr _70078, CLC_env env)
{
  CLC_ptr DocNest_c25_70079;
  INSTR_struct(&DocNest_c25_70079, 25, 2,
    env[1], _70078);
  return DocNest_c25_70079;
}

CLC_ptr nest_70082(CLC_ptr _70076, CLC_env env)
{
  CLC_ptr clo_70081;
  INSTR_clo(&clo_70081, &lam_70080, 24,
    0, _70076, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21]);
  return clo_70081;
}

CLC_ptr breakWith_70099(CLC_ptr _70097, CLC_env env)
{
  CLC_ptr DocBreak_c26_70098;
  INSTR_struct(&DocBreak_c26_70098, 26, 1,
    _70097);
  return DocBreak_c26_70098;
}

CLC_ptr group_70104(CLC_ptr _70102, CLC_env env)
{
  CLC_ptr DocGroup_c27_70103;
  INSTR_struct(&DocGroup_c27_70103, 27, 1,
    _70102);
  return DocGroup_c27_70103;
}

CLC_ptr loop_70137(CLC_ptr _70119, CLC_env env)
{
  CLC_ptr _70122; CLC_ptr Ascii_c16_70131; CLC_ptr EmptyString_c17_70121;
  CLC_ptr EmptyString_c17_70132; CLC_ptr String_c18_70133;
  CLC_ptr case_70120; CLC_ptr false_c3_70123; CLC_ptr false_c3_70124;
  CLC_ptr false_c3_70126; CLC_ptr false_c3_70127; CLC_ptr false_c3_70128;
  CLC_ptr false_c3_70129; CLC_ptr false_c3_70130; CLC_ptr tmp_70134;
  CLC_ptr tmp_70135; CLC_ptr tmp_70136; CLC_ptr true_c2_70125;
  switch(((CLC_node)_70119)->tag){
    case 4:
      INSTR_struct(&EmptyString_c17_70121, 17, 0);
      INSTR_mov(&case_70120, EmptyString_c17_70121);
      break;
    case 5:
      INSTR_mov(&_70122, ((CLC_node)_70119)->data[0]);
      INSTR_struct(&false_c3_70123, 3, 0);
      INSTR_struct(&false_c3_70124, 3, 0);
      INSTR_struct(&true_c2_70125, 2, 0);
      INSTR_struct(&false_c3_70126, 3, 0);
      INSTR_struct(&false_c3_70127, 3, 0);
      INSTR_struct(&false_c3_70128, 3, 0);
      INSTR_struct(&false_c3_70129, 3, 0);
      INSTR_struct(&false_c3_70130, 3, 0);
      INSTR_struct(&Ascii_c16_70131, 16, 8,
        false_c3_70123, false_c3_70124, true_c2_70125, false_c3_70126,
        false_c3_70127, false_c3_70128, false_c3_70129, false_c3_70130);
      INSTR_struct(&EmptyString_c17_70132, 17, 0);
      INSTR_struct(&String_c18_70133, 18, 2,
        Ascii_c16_70131, EmptyString_c17_70132);
      INSTR_call(&tmp_70134, env[26], String_c18_70133);
      INSTR_call(&tmp_70135, env[0], _70122);
      INSTR_call(&tmp_70136, tmp_70134, tmp_70135);
      INSTR_mov(&case_70120, tmp_70136);
      break;}
  return case_70120;
}

CLC_ptr sdocToString_70156(CLC_ptr _70107, CLC_env env)
{
  CLC_ptr _70110; CLC_ptr _70111; CLC_ptr _70115; CLC_ptr _70116;
  CLC_ptr Ascii_c16_70147; CLC_ptr EmptyString_c17_70109;
  CLC_ptr EmptyString_c17_70148; CLC_ptr String_c18_70149;
  CLC_ptr case_70108; CLC_ptr false_c3_70139; CLC_ptr false_c3_70140;
  CLC_ptr false_c3_70141; CLC_ptr false_c3_70142; CLC_ptr false_c3_70144;
  CLC_ptr false_c3_70146; CLC_ptr loop_70117; CLC_ptr loop_70138;
  CLC_ptr tmp_70112; CLC_ptr tmp_70113; CLC_ptr tmp_70114; CLC_ptr tmp_70150;
  CLC_ptr tmp_70151; CLC_ptr tmp_70152; CLC_ptr tmp_70153; CLC_ptr tmp_70154;
  CLC_ptr tmp_70155; CLC_ptr true_c2_70143; CLC_ptr true_c2_70145;
  switch(((CLC_node)_70107)->tag){
    case 28:
      INSTR_struct(&EmptyString_c17_70109, 17, 0);
      INSTR_mov(&case_70108, EmptyString_c17_70109);
      break;
    case 29:
      INSTR_mov(&_70110, ((CLC_node)_70107)->data[0]);
      INSTR_mov(&_70111, ((CLC_node)_70107)->data[1]);
      INSTR_call(&tmp_70112, env[22], _70110);
      INSTR_call(&tmp_70113, env[0], _70111);
      INSTR_call(&tmp_70114, tmp_70112, tmp_70113);
      INSTR_mov(&case_70108, tmp_70114);
      break;
    case 30:
      INSTR_mov(&_70115, ((CLC_node)_70107)->data[0]);
      INSTR_mov(&_70116, ((CLC_node)_70107)->data[1]);
      INSTR_clo(&loop_70138, &loop_70137, 30,
        0, _70107, _70115, _70116, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25]);
      INSTR_mov(&loop_70117, loop_70138);
      INSTR_struct(&false_c3_70139, 3, 0);
      INSTR_struct(&false_c3_70140, 3, 0);
      INSTR_struct(&false_c3_70141, 3, 0);
      INSTR_struct(&false_c3_70142, 3, 0);
      INSTR_struct(&true_c2_70143, 2, 0);
      INSTR_struct(&false_c3_70144, 3, 0);
      INSTR_struct(&true_c2_70145, 2, 0);
      INSTR_struct(&false_c3_70146, 3, 0);
      INSTR_struct(&Ascii_c16_70147, 16, 8,
        false_c3_70139, false_c3_70140, false_c3_70141, false_c3_70142,
        true_c2_70143, false_c3_70144, true_c2_70145, false_c3_70146);
      INSTR_struct(&EmptyString_c17_70148, 17, 0);
      INSTR_struct(&String_c18_70149, 18, 2,
        Ascii_c16_70147, EmptyString_c17_70148);
      INSTR_call(&tmp_70150, env[22], String_c18_70149);
      INSTR_call(&tmp_70151, loop_70117, _70115);
      INSTR_call(&tmp_70152, tmp_70150, tmp_70151);
      INSTR_call(&tmp_70153, env[22], tmp_70152);
      INSTR_call(&tmp_70154, env[0], _70116);
      INSTR_call(&tmp_70155, tmp_70153, tmp_70154);
      INSTR_mov(&case_70108, tmp_70155);
      break;}
  return case_70108;
}

CLC_ptr lam_70164(CLC_ptr _70162, CLC_env env)
{
  CLC_ptr false_c3_70163;
  INSTR_struct(&false_c3_70163, 3, 0);
  return false_c3_70163;
}

CLC_ptr lam_70228(CLC_ptr _70168, CLC_env env)
{
  CLC_ptr _70171; CLC_ptr _70172; CLC_ptr _70175; CLC_ptr _70178;
  CLC_ptr _70183; CLC_ptr _70184; CLC_ptr _70194; CLC_ptr _70201;
  CLC_ptr _70202; CLC_ptr _70211; CLC_ptr _70220; CLC_ptr Flat_c31_70223;
  CLC_ptr case_70169; CLC_ptr case_70173; CLC_ptr case_70176;
  CLC_ptr case_70179; CLC_ptr case_70212; CLC_ptr cons_c9_70191;
  CLC_ptr cons_c9_70192; CLC_ptr cons_c9_70209; CLC_ptr cons_c9_70226;
  CLC_ptr ex_intro_c12_70187; CLC_ptr ex_intro_c12_70188;
  CLC_ptr ex_intro_c12_70189; CLC_ptr ex_intro_c12_70190;
  CLC_ptr ex_intro_c12_70207; CLC_ptr ex_intro_c12_70208;
  CLC_ptr ex_intro_c12_70224; CLC_ptr ex_intro_c12_70225;
  CLC_ptr succ_c5_70180; CLC_ptr succ_c5_70185; CLC_ptr succ_c5_70195;
  CLC_ptr succ_c5_70203; CLC_ptr succ_c5_70213; CLC_ptr succ_c5_70221;
  CLC_ptr tmp_70181; CLC_ptr tmp_70182; CLC_ptr tmp_70186; CLC_ptr tmp_70193;
  CLC_ptr tmp_70196; CLC_ptr tmp_70197; CLC_ptr tmp_70198; CLC_ptr tmp_70199;
  CLC_ptr tmp_70200; CLC_ptr tmp_70204; CLC_ptr tmp_70205; CLC_ptr tmp_70206;
  CLC_ptr tmp_70210; CLC_ptr tmp_70214; CLC_ptr tmp_70215; CLC_ptr tmp_70216;
  CLC_ptr tmp_70217; CLC_ptr tmp_70218; CLC_ptr tmp_70222; CLC_ptr tmp_70227;
  CLC_ptr true_c2_70170; CLC_ptr true_c2_70219; CLC_ptr x_70174;
  CLC_ptr x_70177;
  switch(((CLC_node)_70168)->tag){
    case 8:
      INSTR_struct(&true_c2_70170, 2, 0);
      INSTR_mov(&case_70169, true_c2_70170);
      break;
    case 9:
      INSTR_mov(&_70171, ((CLC_node)_70168)->data[0]);
      INSTR_mov(&_70172, ((CLC_node)_70168)->data[1]);
      switch(((CLC_node)_70171)->tag){
        case 12:
          INSTR_mov(&x_70174, ((CLC_node)_70171)->data[0]);
          INSTR_mov(&_70175, ((CLC_node)_70171)->data[1]);
          switch(((CLC_node)x_70174)->tag){
            case 12:
              INSTR_mov(&x_70177, ((CLC_node)x_70174)->data[0]);
              INSTR_mov(&_70178, ((CLC_node)x_70174)->data[1]);
              switch(((CLC_node)_70175)->tag){
                case 22:
                  INSTR_struct(&succ_c5_70180, 5, 1,
                    env[2]);
                  INSTR_call(&tmp_70181, env[3], succ_c5_70180);
                  INSTR_call(&tmp_70182, tmp_70181, _70172);
                  INSTR_mov(&case_70179, tmp_70182);
                  break;
                case 23:
                  INSTR_mov(&_70183, ((CLC_node)_70175)->data[0]);
                  INSTR_mov(&_70184, ((CLC_node)_70175)->data[1]);
                  INSTR_struct(&succ_c5_70185, 5, 1,
                    env[2]);
                  INSTR_call(&tmp_70186, env[3], succ_c5_70185);
                  INSTR_struct(&ex_intro_c12_70187, 12, 2,
                    x_70177, _70178);
                  INSTR_struct(&ex_intro_c12_70188, 12, 2,
                    ex_intro_c12_70187, _70183);
                  INSTR_struct(&ex_intro_c12_70189, 12, 2,
                    x_70177, _70178);
                  INSTR_struct(&ex_intro_c12_70190, 12, 2,
                    ex_intro_c12_70189, _70184);
                  INSTR_struct(&cons_c9_70191, 9, 2,
                    ex_intro_c12_70190, _70172);
                  INSTR_struct(&cons_c9_70192, 9, 2,
                    ex_intro_c12_70188, cons_c9_70191);
                  INSTR_call(&tmp_70193, tmp_70186, cons_c9_70192);
                  INSTR_mov(&case_70179, tmp_70193);
                  break;
                case 24:
                  INSTR_mov(&_70194, ((CLC_node)_70175)->data[0]);
                  INSTR_struct(&succ_c5_70195, 5, 1,
                    env[2]);
                  INSTR_call(&tmp_70196, env[27], succ_c5_70195);
                  INSTR_call(&tmp_70197, env[25], _70194);
                  INSTR_call(&tmp_70198, tmp_70196, tmp_70197);
                  INSTR_call(&tmp_70199, env[3], tmp_70198);
                  INSTR_call(&tmp_70200, tmp_70199, _70172);
                  INSTR_mov(&case_70179, tmp_70200);
                  break;
                case 25:
                  INSTR_mov(&_70201, ((CLC_node)_70175)->data[0]);
                  INSTR_mov(&_70202, ((CLC_node)_70175)->data[1]);
                  INSTR_struct(&succ_c5_70203, 5, 1,
                    env[2]);
                  INSTR_call(&tmp_70204, env[3], succ_c5_70203);
                  INSTR_call(&tmp_70205, env[28], x_70177);
                  INSTR_call(&tmp_70206, tmp_70205, _70201);
                  INSTR_struct(&ex_intro_c12_70207, 12, 2,
                    tmp_70206, _70178);
                  INSTR_struct(&ex_intro_c12_70208, 12, 2,
                    ex_intro_c12_70207, _70202);
                  INSTR_struct(&cons_c9_70209, 9, 2,
                    ex_intro_c12_70208, _70172);
                  INSTR_call(&tmp_70210, tmp_70204, cons_c9_70209);
                  INSTR_mov(&case_70179, tmp_70210);
                  break;
                case 26:
                  INSTR_mov(&_70211, ((CLC_node)_70175)->data[0]);
                  switch(((CLC_node)_70178)->tag){
                    case 31:
                      INSTR_struct(&succ_c5_70213, 5, 1,
                        env[2]);
                      INSTR_call(&tmp_70214, env[27], succ_c5_70213);
                      INSTR_call(&tmp_70215, env[25], _70211);
                      INSTR_call(&tmp_70216, tmp_70214, tmp_70215);
                      INSTR_call(&tmp_70217, env[3], tmp_70216);
                      INSTR_call(&tmp_70218, tmp_70217, _70172);
                      INSTR_mov(&case_70212, tmp_70218);
                      break;
                    case 32:
                      INSTR_struct(&true_c2_70219, 2, 0);
                      INSTR_mov(&case_70212, true_c2_70219);
                      break;}
                  INSTR_mov(&case_70179, case_70212);
                  break;
                case 27:
                  INSTR_mov(&_70220, ((CLC_node)_70175)->data[0]);
                  INSTR_struct(&succ_c5_70221, 5, 1,
                    env[2]);
                  INSTR_call(&tmp_70222, env[3], succ_c5_70221);
                  INSTR_struct(&Flat_c31_70223, 31, 0);
                  INSTR_struct(&ex_intro_c12_70224, 12, 2,
                    x_70177, Flat_c31_70223);
                  INSTR_struct(&ex_intro_c12_70225, 12, 2,
                    ex_intro_c12_70224, _70220);
                  INSTR_struct(&cons_c9_70226, 9, 2,
                    ex_intro_c12_70225, _70172);
                  INSTR_call(&tmp_70227, tmp_70222, cons_c9_70226);
                  INSTR_mov(&case_70179, tmp_70227);
                  break;}
              INSTR_mov(&case_70176, case_70179);
              break;}
          INSTR_mov(&case_70173, case_70176);
          break;}
      INSTR_mov(&case_70169, case_70173);
      break;}
  return case_70169;
}

CLC_ptr fits_70230(CLC_ptr _70159, CLC_env env)
{
  CLC_ptr _70166; CLC_ptr case_70160; CLC_ptr clo_70165; CLC_ptr clo_70229;
  switch(((CLC_node)_70159)->tag){
    case 4:
      INSTR_clo(&clo_70165, &lam_70164, 29,
        0, _70159, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
        env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
        env[15], env[16], env[17], env[18], env[19], env[20], env[21],
        env[22], env[23], env[24], env[25], env[26]);
      INSTR_mov(&case_70160, clo_70165);
      break;
    case 5:
      INSTR_mov(&_70166, ((CLC_node)_70159)->data[0]);
      INSTR_clo(&clo_70229, &lam_70228, 30,
        0, _70159, _70166, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26]);
      INSTR_mov(&case_70160, clo_70229);
      break;}
  return case_70160;
}

CLC_ptr lam_70318(CLC_ptr _70237, CLC_env env)
{
  CLC_ptr _70240; CLC_ptr _70241; CLC_ptr _70244; CLC_ptr _70247;
  CLC_ptr _70252; CLC_ptr _70253; CLC_ptr _70263; CLC_ptr _70271;
  CLC_ptr _70272; CLC_ptr _70281; CLC_ptr _70294; CLC_ptr Break_c32_70313;
  CLC_ptr Flat_c31_70298; CLC_ptr Flat_c31_70306; CLC_ptr SLine_c30_70293;
  CLC_ptr SNil_c28_70239; CLC_ptr SText_c29_70270; CLC_ptr SText_c29_70289;
  CLC_ptr case_70238; CLC_ptr case_70242; CLC_ptr case_70245;
  CLC_ptr case_70248; CLC_ptr case_70282; CLC_ptr case_70303;
  CLC_ptr cons_c9_70260; CLC_ptr cons_c9_70261; CLC_ptr cons_c9_70279;
  CLC_ptr cons_c9_70301; CLC_ptr cons_c9_70309; CLC_ptr cons_c9_70316;
  CLC_ptr ex_intro_c12_70256; CLC_ptr ex_intro_c12_70257;
  CLC_ptr ex_intro_c12_70258; CLC_ptr ex_intro_c12_70259;
  CLC_ptr ex_intro_c12_70277; CLC_ptr ex_intro_c12_70278;
  CLC_ptr ex_intro_c12_70299; CLC_ptr ex_intro_c12_70300;
  CLC_ptr ex_intro_c12_70307; CLC_ptr ex_intro_c12_70308;
  CLC_ptr ex_intro_c12_70314; CLC_ptr ex_intro_c12_70315; CLC_ptr tmp_70249;
  CLC_ptr tmp_70250; CLC_ptr tmp_70251; CLC_ptr tmp_70254; CLC_ptr tmp_70255;
  CLC_ptr tmp_70262; CLC_ptr tmp_70264; CLC_ptr tmp_70265; CLC_ptr tmp_70266;
  CLC_ptr tmp_70267; CLC_ptr tmp_70268; CLC_ptr tmp_70269; CLC_ptr tmp_70273;
  CLC_ptr tmp_70274; CLC_ptr tmp_70275; CLC_ptr tmp_70276; CLC_ptr tmp_70280;
  CLC_ptr tmp_70283; CLC_ptr tmp_70284; CLC_ptr tmp_70285; CLC_ptr tmp_70286;
  CLC_ptr tmp_70287; CLC_ptr tmp_70288; CLC_ptr tmp_70290; CLC_ptr tmp_70291;
  CLC_ptr tmp_70292; CLC_ptr tmp_70295; CLC_ptr tmp_70296; CLC_ptr tmp_70297;
  CLC_ptr tmp_70302; CLC_ptr tmp_70304; CLC_ptr tmp_70305; CLC_ptr tmp_70310;
  CLC_ptr tmp_70311; CLC_ptr tmp_70312; CLC_ptr tmp_70317; CLC_ptr x_70243;
  CLC_ptr x_70246;
  switch(((CLC_node)_70237)->tag){
    case 8:
      INSTR_struct(&SNil_c28_70239, 28, 0);
      INSTR_mov(&case_70238, SNil_c28_70239);
      break;
    case 9:
      INSTR_mov(&_70240, ((CLC_node)_70237)->data[0]);
      INSTR_mov(&_70241, ((CLC_node)_70237)->data[1]);
      switch(((CLC_node)_70240)->tag){
        case 12:
          INSTR_mov(&x_70243, ((CLC_node)_70240)->data[0]);
          INSTR_mov(&_70244, ((CLC_node)_70240)->data[1]);
          switch(((CLC_node)x_70243)->tag){
            case 12:
              INSTR_mov(&x_70246, ((CLC_node)x_70243)->data[0]);
              INSTR_mov(&_70247, ((CLC_node)x_70243)->data[1]);
              switch(((CLC_node)_70244)->tag){
                case 22:
                  INSTR_call(&tmp_70249, env[4], env[3]);
                  INSTR_call(&tmp_70250, tmp_70249, env[1]);
                  INSTR_call(&tmp_70251, tmp_70250, _70241);
                  INSTR_mov(&case_70248, tmp_70251);
                  break;
                case 23:
                  INSTR_mov(&_70252, ((CLC_node)_70244)->data[0]);
                  INSTR_mov(&_70253, ((CLC_node)_70244)->data[1]);
                  INSTR_call(&tmp_70254, env[4], env[3]);
                  INSTR_call(&tmp_70255, tmp_70254, env[1]);
                  INSTR_struct(&ex_intro_c12_70256, 12, 2,
                    x_70246, _70247);
                  INSTR_struct(&ex_intro_c12_70257, 12, 2,
                    ex_intro_c12_70256, _70252);
                  INSTR_struct(&ex_intro_c12_70258, 12, 2,
                    x_70246, _70247);
                  INSTR_struct(&ex_intro_c12_70259, 12, 2,
                    ex_intro_c12_70258, _70253);
                  INSTR_struct(&cons_c9_70260, 9, 2,
                    ex_intro_c12_70259, _70241);
                  INSTR_struct(&cons_c9_70261, 9, 2,
                    ex_intro_c12_70257, cons_c9_70260);
                  INSTR_call(&tmp_70262, tmp_70255, cons_c9_70261);
                  INSTR_mov(&case_70248, tmp_70262);
                  break;
                case 24:
                  INSTR_mov(&_70263, ((CLC_node)_70244)->data[0]);
                  INSTR_call(&tmp_70264, env[4], env[3]);
                  INSTR_call(&tmp_70265, env[30], env[1]);
                  INSTR_call(&tmp_70266, env[27], _70263);
                  INSTR_call(&tmp_70267, tmp_70265, tmp_70266);
                  INSTR_call(&tmp_70268, tmp_70264, tmp_70267);
                  INSTR_call(&tmp_70269, tmp_70268, _70241);
                  INSTR_struct(&SText_c29_70270, 29, 2,
                    _70263, tmp_70269);
                  INSTR_mov(&case_70248, SText_c29_70270);
                  break;
                case 25:
                  INSTR_mov(&_70271, ((CLC_node)_70244)->data[0]);
                  INSTR_mov(&_70272, ((CLC_node)_70244)->data[1]);
                  INSTR_call(&tmp_70273, env[4], env[3]);
                  INSTR_call(&tmp_70274, tmp_70273, env[1]);
                  INSTR_call(&tmp_70275, env[30], x_70246);
                  INSTR_call(&tmp_70276, tmp_70275, _70271);
                  INSTR_struct(&ex_intro_c12_70277, 12, 2,
                    tmp_70276, _70247);
                  INSTR_struct(&ex_intro_c12_70278, 12, 2,
                    ex_intro_c12_70277, _70272);
                  INSTR_struct(&cons_c9_70279, 9, 2,
                    ex_intro_c12_70278, _70241);
                  INSTR_call(&tmp_70280, tmp_70274, cons_c9_70279);
                  INSTR_mov(&case_70248, tmp_70280);
                  break;
                case 26:
                  INSTR_mov(&_70281, ((CLC_node)_70244)->data[0]);
                  switch(((CLC_node)_70247)->tag){
                    case 31:
                      INSTR_call(&tmp_70283, env[4], env[3]);
                      INSTR_call(&tmp_70284, env[30], env[1]);
                      INSTR_call(&tmp_70285, env[27], _70281);
                      INSTR_call(&tmp_70286, tmp_70284, tmp_70285);
                      INSTR_call(&tmp_70287, tmp_70283, tmp_70286);
                      INSTR_call(&tmp_70288, tmp_70287, _70241);
                      INSTR_struct(&SText_c29_70289, 29, 2,
                        _70281, tmp_70288);
                      INSTR_mov(&case_70282, SText_c29_70289);
                      break;
                    case 32:
                      INSTR_call(&tmp_70290, env[4], env[3]);
                      INSTR_call(&tmp_70291, tmp_70290, x_70246);
                      INSTR_call(&tmp_70292, tmp_70291, _70241);
                      INSTR_struct(&SLine_c30_70293, 30, 2,
                        x_70246, tmp_70292);
                      INSTR_mov(&case_70282, SLine_c30_70293);
                      break;}
                  INSTR_mov(&case_70248, case_70282);
                  break;
                case 27:
                  INSTR_mov(&_70294, ((CLC_node)_70244)->data[0]);
                  INSTR_call(&tmp_70295, env[29], env[3]);
                  INSTR_call(&tmp_70296, tmp_70295, env[1]);
                  INSTR_call(&tmp_70297, env[5], tmp_70296);
                  INSTR_struct(&Flat_c31_70298, 31, 0);
                  INSTR_struct(&ex_intro_c12_70299, 12, 2,
                    x_70246, Flat_c31_70298);
                  INSTR_struct(&ex_intro_c12_70300, 12, 2,
                    ex_intro_c12_70299, _70294);
                  INSTR_struct(&cons_c9_70301, 9, 2,
                    ex_intro_c12_70300, _70241);
                  INSTR_call(&tmp_70302, tmp_70297, cons_c9_70301);
                  switch(((CLC_node)tmp_70302)->tag){
                    case 2:
                      INSTR_call(&tmp_70304, env[4], env[3]);
                      INSTR_call(&tmp_70305, tmp_70304, env[1]);
                      INSTR_struct(&Flat_c31_70306, 31, 0);
                      INSTR_struct(&ex_intro_c12_70307, 12, 2,
                        x_70246, Flat_c31_70306);
                      INSTR_struct(&ex_intro_c12_70308, 12, 2,
                        ex_intro_c12_70307, _70294);
                      INSTR_struct(&cons_c9_70309, 9, 2,
                        ex_intro_c12_70308, _70241);
                      INSTR_call(&tmp_70310, tmp_70305, cons_c9_70309);
                      INSTR_mov(&case_70303, tmp_70310);
                      break;
                    case 3:
                      INSTR_call(&tmp_70311, env[4], env[3]);
                      INSTR_call(&tmp_70312, tmp_70311, env[1]);
                      INSTR_struct(&Break_c32_70313, 32, 0);
                      INSTR_struct(&ex_intro_c12_70314, 12, 2,
                        x_70246, Break_c32_70313);
                      INSTR_struct(&ex_intro_c12_70315, 12, 2,
                        ex_intro_c12_70314, _70294);
                      INSTR_struct(&cons_c9_70316, 9, 2,
                        ex_intro_c12_70315, _70241);
                      INSTR_call(&tmp_70317, tmp_70312, cons_c9_70316);
                      INSTR_mov(&case_70303, tmp_70317);
                      break;}
                  INSTR_mov(&case_70248, case_70303);
                  break;}
              INSTR_mov(&case_70245, case_70248);
              break;}
          INSTR_mov(&case_70242, case_70245);
          break;}
      INSTR_mov(&case_70238, case_70242);
      break;}
  return case_70238;
}

CLC_ptr lam_70320(CLC_ptr _70235, CLC_env env)
{
  CLC_ptr clo_70319;
  INSTR_clo(&clo_70319, &lam_70318, 32,
    0, _70235, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29]);
  return clo_70319;
}

CLC_ptr format_70322(CLC_ptr _70233, CLC_env env)
{
  CLC_ptr clo_70321;
  INSTR_clo(&clo_70321, &lam_70320, 30,
    0, _70233, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27]);
  return clo_70321;
}

CLC_ptr lam_70355(CLC_ptr _70327, CLC_env env)
{
  CLC_ptr Ascii_c16_70351; CLC_ptr EmptyString_c17_70352;
  CLC_ptr Flat_c31_70334; CLC_ptr String_c18_70353; CLC_ptr cons_c9_70339;
  CLC_ptr ex_intro_c12_70335; CLC_ptr ex_intro_c12_70337;
  CLC_ptr false_c3_70343; CLC_ptr false_c3_70344; CLC_ptr false_c3_70345;
  CLC_ptr false_c3_70346; CLC_ptr false_c3_70348; CLC_ptr false_c3_70350;
  CLC_ptr nil_c8_70338; CLC_ptr sd_70328; CLC_ptr succ_c5_70329;
  CLC_ptr tmp_70330; CLC_ptr tmp_70332; CLC_ptr tmp_70336; CLC_ptr tmp_70340;
  CLC_ptr tmp_70341; CLC_ptr tmp_70342; CLC_ptr tmp_70354;
  CLC_ptr true_c2_70347; CLC_ptr true_c2_70349; CLC_ptr zero_c4_70331;
  CLC_ptr zero_c4_70333;
  INSTR_struct(&succ_c5_70329, 5, 1,
    env[1]);
  INSTR_call(&tmp_70330, env[3], succ_c5_70329);
  INSTR_struct(&zero_c4_70331, 4, 0);
  INSTR_call(&tmp_70332, tmp_70330, zero_c4_70331);
  INSTR_struct(&zero_c4_70333, 4, 0);
  INSTR_struct(&Flat_c31_70334, 31, 0);
  INSTR_struct(&ex_intro_c12_70335, 12, 2,
    zero_c4_70333, Flat_c31_70334);
  INSTR_call(&tmp_70336, env[6], _70327);
  INSTR_struct(&ex_intro_c12_70337, 12, 2,
    ex_intro_c12_70335, tmp_70336);
  INSTR_struct(&nil_c8_70338, 8, 0);
  INSTR_struct(&cons_c9_70339, 9, 2,
    ex_intro_c12_70337, nil_c8_70338);
  INSTR_call(&tmp_70340, tmp_70332, cons_c9_70339);
  INSTR_mov(&sd_70328, tmp_70340);
  INSTR_call(&tmp_70341, env[5], sd_70328);
  INSTR_call(&tmp_70342, env[27], tmp_70341);
  INSTR_struct(&false_c3_70343, 3, 0);
  INSTR_struct(&false_c3_70344, 3, 0);
  INSTR_struct(&false_c3_70345, 3, 0);
  INSTR_struct(&false_c3_70346, 3, 0);
  INSTR_struct(&true_c2_70347, 2, 0);
  INSTR_struct(&false_c3_70348, 3, 0);
  INSTR_struct(&true_c2_70349, 2, 0);
  INSTR_struct(&false_c3_70350, 3, 0);
  INSTR_struct(&Ascii_c16_70351, 16, 8,
    false_c3_70343, false_c3_70344, false_c3_70345, false_c3_70346,
    true_c2_70347, false_c3_70348, true_c2_70349, false_c3_70350);
  INSTR_struct(&EmptyString_c17_70352, 17, 0);
  INSTR_struct(&String_c18_70353, 18, 2,
    Ascii_c16_70351, EmptyString_c17_70352);
  INSTR_call(&tmp_70354, tmp_70342, String_c18_70353);
  return tmp_70354;
}

CLC_ptr pretty_70357(CLC_ptr _70325, CLC_env env)
{
  CLC_ptr clo_70356;
  INSTR_clo(&clo_70356, &lam_70355, 31,
    0, _70325, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28]);
  return clo_70356;
}

CLC_ptr lam_70364(CLC_ptr _70363, CLC_env env)
{
  
  
  return _70363;
}

CLC_ptr lam_70409(CLC_ptr _70369, CLC_env env)
{
  CLC_ptr _70372; CLC_ptr _70373; CLC_ptr _70380; CLC_ptr _70387;
  CLC_ptr _70388; CLC_ptr _70395; CLC_ptr _70402; CLC_ptr DocBreak_c26_70400;
  CLC_ptr DocCons_c23_70371; CLC_ptr DocCons_c23_70374;
  CLC_ptr DocCons_c23_70378; CLC_ptr DocCons_c23_70381;
  CLC_ptr DocCons_c23_70389; CLC_ptr DocCons_c23_70396;
  CLC_ptr DocCons_c23_70403; CLC_ptr DocGroup_c27_70407;
  CLC_ptr DocNest_c25_70393; CLC_ptr DocText_c24_70385; CLC_ptr case_70370;
  CLC_ptr tmp_70375; CLC_ptr tmp_70376; CLC_ptr tmp_70377; CLC_ptr tmp_70379;
  CLC_ptr tmp_70382; CLC_ptr tmp_70383; CLC_ptr tmp_70384; CLC_ptr tmp_70386;
  CLC_ptr tmp_70390; CLC_ptr tmp_70391; CLC_ptr tmp_70392; CLC_ptr tmp_70394;
  CLC_ptr tmp_70397; CLC_ptr tmp_70398; CLC_ptr tmp_70399; CLC_ptr tmp_70401;
  CLC_ptr tmp_70404; CLC_ptr tmp_70405; CLC_ptr tmp_70406; CLC_ptr tmp_70408;
  switch(((CLC_node)_70369)->tag){
    case 22:
      INSTR_struct(&DocCons_c23_70371, 23, 2,
        env[2], env[3]);
      INSTR_mov(&case_70370, DocCons_c23_70371);
      break;
    case 23:
      INSTR_mov(&_70372, ((CLC_node)_70369)->data[0]);
      INSTR_mov(&_70373, ((CLC_node)_70369)->data[1]);
      INSTR_struct(&DocCons_c23_70374, 23, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70375, env[15], DocCons_c23_70374);
      INSTR_call(&tmp_70376, tmp_70375, env[11]);
      INSTR_call(&tmp_70377, env[15], tmp_70376);
      INSTR_struct(&DocCons_c23_70378, 23, 2,
        _70372, _70373);
      INSTR_call(&tmp_70379, tmp_70377, DocCons_c23_70378);
      INSTR_mov(&case_70370, tmp_70379);
      break;
    case 24:
      INSTR_mov(&_70380, ((CLC_node)_70369)->data[0]);
      INSTR_struct(&DocCons_c23_70381, 23, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70382, env[15], DocCons_c23_70381);
      INSTR_call(&tmp_70383, tmp_70382, env[11]);
      INSTR_call(&tmp_70384, env[15], tmp_70383);
      INSTR_struct(&DocText_c24_70385, 24, 1,
        _70380);
      INSTR_call(&tmp_70386, tmp_70384, DocText_c24_70385);
      INSTR_mov(&case_70370, tmp_70386);
      break;
    case 25:
      INSTR_mov(&_70387, ((CLC_node)_70369)->data[0]);
      INSTR_mov(&_70388, ((CLC_node)_70369)->data[1]);
      INSTR_struct(&DocCons_c23_70389, 23, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70390, env[15], DocCons_c23_70389);
      INSTR_call(&tmp_70391, tmp_70390, env[11]);
      INSTR_call(&tmp_70392, env[15], tmp_70391);
      INSTR_struct(&DocNest_c25_70393, 25, 2,
        _70387, _70388);
      INSTR_call(&tmp_70394, tmp_70392, DocNest_c25_70393);
      INSTR_mov(&case_70370, tmp_70394);
      break;
    case 26:
      INSTR_mov(&_70395, ((CLC_node)_70369)->data[0]);
      INSTR_struct(&DocCons_c23_70396, 23, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70397, env[15], DocCons_c23_70396);
      INSTR_call(&tmp_70398, tmp_70397, env[11]);
      INSTR_call(&tmp_70399, env[15], tmp_70398);
      INSTR_struct(&DocBreak_c26_70400, 26, 1,
        _70395);
      INSTR_call(&tmp_70401, tmp_70399, DocBreak_c26_70400);
      INSTR_mov(&case_70370, tmp_70401);
      break;
    case 27:
      INSTR_mov(&_70402, ((CLC_node)_70369)->data[0]);
      INSTR_struct(&DocCons_c23_70403, 23, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70404, env[15], DocCons_c23_70403);
      INSTR_call(&tmp_70405, tmp_70404, env[11]);
      INSTR_call(&tmp_70406, env[15], tmp_70405);
      INSTR_struct(&DocGroup_c27_70407, 27, 1,
        _70402);
      INSTR_call(&tmp_70408, tmp_70406, DocGroup_c27_70407);
      INSTR_mov(&case_70370, tmp_70408);
      break;}
  return case_70370;
}

CLC_ptr lam_70453(CLC_ptr _70413, CLC_env env)
{
  CLC_ptr _70416; CLC_ptr _70417; CLC_ptr _70424; CLC_ptr _70431;
  CLC_ptr _70432; CLC_ptr _70439; CLC_ptr _70446; CLC_ptr DocBreak_c26_70444;
  CLC_ptr DocCons_c23_70422; CLC_ptr DocGroup_c27_70451;
  CLC_ptr DocNest_c25_70437; CLC_ptr DocText_c24_70415;
  CLC_ptr DocText_c24_70418; CLC_ptr DocText_c24_70425;
  CLC_ptr DocText_c24_70429; CLC_ptr DocText_c24_70433;
  CLC_ptr DocText_c24_70440; CLC_ptr DocText_c24_70447; CLC_ptr case_70414;
  CLC_ptr tmp_70419; CLC_ptr tmp_70420; CLC_ptr tmp_70421; CLC_ptr tmp_70423;
  CLC_ptr tmp_70426; CLC_ptr tmp_70427; CLC_ptr tmp_70428; CLC_ptr tmp_70430;
  CLC_ptr tmp_70434; CLC_ptr tmp_70435; CLC_ptr tmp_70436; CLC_ptr tmp_70438;
  CLC_ptr tmp_70441; CLC_ptr tmp_70442; CLC_ptr tmp_70443; CLC_ptr tmp_70445;
  CLC_ptr tmp_70448; CLC_ptr tmp_70449; CLC_ptr tmp_70450; CLC_ptr tmp_70452;
  switch(((CLC_node)_70413)->tag){
    case 22:
      INSTR_struct(&DocText_c24_70415, 24, 1,
        env[2]);
      INSTR_mov(&case_70414, DocText_c24_70415);
      break;
    case 23:
      INSTR_mov(&_70416, ((CLC_node)_70413)->data[0]);
      INSTR_mov(&_70417, ((CLC_node)_70413)->data[1]);
      INSTR_struct(&DocText_c24_70418, 24, 1,
        env[2]);
      INSTR_call(&tmp_70419, env[14], DocText_c24_70418);
      INSTR_call(&tmp_70420, tmp_70419, env[10]);
      INSTR_call(&tmp_70421, env[14], tmp_70420);
      INSTR_struct(&DocCons_c23_70422, 23, 2,
        _70416, _70417);
      INSTR_call(&tmp_70423, tmp_70421, DocCons_c23_70422);
      INSTR_mov(&case_70414, tmp_70423);
      break;
    case 24:
      INSTR_mov(&_70424, ((CLC_node)_70413)->data[0]);
      INSTR_struct(&DocText_c24_70425, 24, 1,
        env[2]);
      INSTR_call(&tmp_70426, env[14], DocText_c24_70425);
      INSTR_call(&tmp_70427, tmp_70426, env[10]);
      INSTR_call(&tmp_70428, env[14], tmp_70427);
      INSTR_struct(&DocText_c24_70429, 24, 1,
        _70424);
      INSTR_call(&tmp_70430, tmp_70428, DocText_c24_70429);
      INSTR_mov(&case_70414, tmp_70430);
      break;
    case 25:
      INSTR_mov(&_70431, ((CLC_node)_70413)->data[0]);
      INSTR_mov(&_70432, ((CLC_node)_70413)->data[1]);
      INSTR_struct(&DocText_c24_70433, 24, 1,
        env[2]);
      INSTR_call(&tmp_70434, env[14], DocText_c24_70433);
      INSTR_call(&tmp_70435, tmp_70434, env[10]);
      INSTR_call(&tmp_70436, env[14], tmp_70435);
      INSTR_struct(&DocNest_c25_70437, 25, 2,
        _70431, _70432);
      INSTR_call(&tmp_70438, tmp_70436, DocNest_c25_70437);
      INSTR_mov(&case_70414, tmp_70438);
      break;
    case 26:
      INSTR_mov(&_70439, ((CLC_node)_70413)->data[0]);
      INSTR_struct(&DocText_c24_70440, 24, 1,
        env[2]);
      INSTR_call(&tmp_70441, env[14], DocText_c24_70440);
      INSTR_call(&tmp_70442, tmp_70441, env[10]);
      INSTR_call(&tmp_70443, env[14], tmp_70442);
      INSTR_struct(&DocBreak_c26_70444, 26, 1,
        _70439);
      INSTR_call(&tmp_70445, tmp_70443, DocBreak_c26_70444);
      INSTR_mov(&case_70414, tmp_70445);
      break;
    case 27:
      INSTR_mov(&_70446, ((CLC_node)_70413)->data[0]);
      INSTR_struct(&DocText_c24_70447, 24, 1,
        env[2]);
      INSTR_call(&tmp_70448, env[14], DocText_c24_70447);
      INSTR_call(&tmp_70449, tmp_70448, env[10]);
      INSTR_call(&tmp_70450, env[14], tmp_70449);
      INSTR_struct(&DocGroup_c27_70451, 27, 1,
        _70446);
      INSTR_call(&tmp_70452, tmp_70450, DocGroup_c27_70451);
      INSTR_mov(&case_70414, tmp_70452);
      break;}
  return case_70414;
}

CLC_ptr lam_70498(CLC_ptr _70458, CLC_env env)
{
  CLC_ptr _70461; CLC_ptr _70462; CLC_ptr _70469; CLC_ptr _70476;
  CLC_ptr _70477; CLC_ptr _70484; CLC_ptr _70491; CLC_ptr DocBreak_c26_70489;
  CLC_ptr DocCons_c23_70467; CLC_ptr DocGroup_c27_70496;
  CLC_ptr DocNest_c25_70460; CLC_ptr DocNest_c25_70463;
  CLC_ptr DocNest_c25_70470; CLC_ptr DocNest_c25_70478;
  CLC_ptr DocNest_c25_70482; CLC_ptr DocNest_c25_70485;
  CLC_ptr DocNest_c25_70492; CLC_ptr DocText_c24_70474; CLC_ptr case_70459;
  CLC_ptr tmp_70464; CLC_ptr tmp_70465; CLC_ptr tmp_70466; CLC_ptr tmp_70468;
  CLC_ptr tmp_70471; CLC_ptr tmp_70472; CLC_ptr tmp_70473; CLC_ptr tmp_70475;
  CLC_ptr tmp_70479; CLC_ptr tmp_70480; CLC_ptr tmp_70481; CLC_ptr tmp_70483;
  CLC_ptr tmp_70486; CLC_ptr tmp_70487; CLC_ptr tmp_70488; CLC_ptr tmp_70490;
  CLC_ptr tmp_70493; CLC_ptr tmp_70494; CLC_ptr tmp_70495; CLC_ptr tmp_70497;
  switch(((CLC_node)_70458)->tag){
    case 22:
      INSTR_struct(&DocNest_c25_70460, 25, 2,
        env[2], env[3]);
      INSTR_mov(&case_70459, DocNest_c25_70460);
      break;
    case 23:
      INSTR_mov(&_70461, ((CLC_node)_70458)->data[0]);
      INSTR_mov(&_70462, ((CLC_node)_70458)->data[1]);
      INSTR_struct(&DocNest_c25_70463, 25, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70464, env[15], DocNest_c25_70463);
      INSTR_call(&tmp_70465, tmp_70464, env[11]);
      INSTR_call(&tmp_70466, env[15], tmp_70465);
      INSTR_struct(&DocCons_c23_70467, 23, 2,
        _70461, _70462);
      INSTR_call(&tmp_70468, tmp_70466, DocCons_c23_70467);
      INSTR_mov(&case_70459, tmp_70468);
      break;
    case 24:
      INSTR_mov(&_70469, ((CLC_node)_70458)->data[0]);
      INSTR_struct(&DocNest_c25_70470, 25, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70471, env[15], DocNest_c25_70470);
      INSTR_call(&tmp_70472, tmp_70471, env[11]);
      INSTR_call(&tmp_70473, env[15], tmp_70472);
      INSTR_struct(&DocText_c24_70474, 24, 1,
        _70469);
      INSTR_call(&tmp_70475, tmp_70473, DocText_c24_70474);
      INSTR_mov(&case_70459, tmp_70475);
      break;
    case 25:
      INSTR_mov(&_70476, ((CLC_node)_70458)->data[0]);
      INSTR_mov(&_70477, ((CLC_node)_70458)->data[1]);
      INSTR_struct(&DocNest_c25_70478, 25, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70479, env[15], DocNest_c25_70478);
      INSTR_call(&tmp_70480, tmp_70479, env[11]);
      INSTR_call(&tmp_70481, env[15], tmp_70480);
      INSTR_struct(&DocNest_c25_70482, 25, 2,
        _70476, _70477);
      INSTR_call(&tmp_70483, tmp_70481, DocNest_c25_70482);
      INSTR_mov(&case_70459, tmp_70483);
      break;
    case 26:
      INSTR_mov(&_70484, ((CLC_node)_70458)->data[0]);
      INSTR_struct(&DocNest_c25_70485, 25, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70486, env[15], DocNest_c25_70485);
      INSTR_call(&tmp_70487, tmp_70486, env[11]);
      INSTR_call(&tmp_70488, env[15], tmp_70487);
      INSTR_struct(&DocBreak_c26_70489, 26, 1,
        _70484);
      INSTR_call(&tmp_70490, tmp_70488, DocBreak_c26_70489);
      INSTR_mov(&case_70459, tmp_70490);
      break;
    case 27:
      INSTR_mov(&_70491, ((CLC_node)_70458)->data[0]);
      INSTR_struct(&DocNest_c25_70492, 25, 2,
        env[2], env[3]);
      INSTR_call(&tmp_70493, env[15], DocNest_c25_70492);
      INSTR_call(&tmp_70494, tmp_70493, env[11]);
      INSTR_call(&tmp_70495, env[15], tmp_70494);
      INSTR_struct(&DocGroup_c27_70496, 27, 1,
        _70491);
      INSTR_call(&tmp_70497, tmp_70495, DocGroup_c27_70496);
      INSTR_mov(&case_70459, tmp_70497);
      break;}
  return case_70459;
}

CLC_ptr lam_70542(CLC_ptr _70502, CLC_env env)
{
  CLC_ptr _70505; CLC_ptr _70506; CLC_ptr _70513; CLC_ptr _70520;
  CLC_ptr _70521; CLC_ptr _70528; CLC_ptr _70535; CLC_ptr DocBreak_c26_70504;
  CLC_ptr DocBreak_c26_70507; CLC_ptr DocBreak_c26_70514;
  CLC_ptr DocBreak_c26_70522; CLC_ptr DocBreak_c26_70529;
  CLC_ptr DocBreak_c26_70533; CLC_ptr DocBreak_c26_70536;
  CLC_ptr DocCons_c23_70511; CLC_ptr DocGroup_c27_70540;
  CLC_ptr DocNest_c25_70526; CLC_ptr DocText_c24_70518; CLC_ptr case_70503;
  CLC_ptr tmp_70508; CLC_ptr tmp_70509; CLC_ptr tmp_70510; CLC_ptr tmp_70512;
  CLC_ptr tmp_70515; CLC_ptr tmp_70516; CLC_ptr tmp_70517; CLC_ptr tmp_70519;
  CLC_ptr tmp_70523; CLC_ptr tmp_70524; CLC_ptr tmp_70525; CLC_ptr tmp_70527;
  CLC_ptr tmp_70530; CLC_ptr tmp_70531; CLC_ptr tmp_70532; CLC_ptr tmp_70534;
  CLC_ptr tmp_70537; CLC_ptr tmp_70538; CLC_ptr tmp_70539; CLC_ptr tmp_70541;
  switch(((CLC_node)_70502)->tag){
    case 22:
      INSTR_struct(&DocBreak_c26_70504, 26, 1,
        env[2]);
      INSTR_mov(&case_70503, DocBreak_c26_70504);
      break;
    case 23:
      INSTR_mov(&_70505, ((CLC_node)_70502)->data[0]);
      INSTR_mov(&_70506, ((CLC_node)_70502)->data[1]);
      INSTR_struct(&DocBreak_c26_70507, 26, 1,
        env[2]);
      INSTR_call(&tmp_70508, env[14], DocBreak_c26_70507);
      INSTR_call(&tmp_70509, tmp_70508, env[10]);
      INSTR_call(&tmp_70510, env[14], tmp_70509);
      INSTR_struct(&DocCons_c23_70511, 23, 2,
        _70505, _70506);
      INSTR_call(&tmp_70512, tmp_70510, DocCons_c23_70511);
      INSTR_mov(&case_70503, tmp_70512);
      break;
    case 24:
      INSTR_mov(&_70513, ((CLC_node)_70502)->data[0]);
      INSTR_struct(&DocBreak_c26_70514, 26, 1,
        env[2]);
      INSTR_call(&tmp_70515, env[14], DocBreak_c26_70514);
      INSTR_call(&tmp_70516, tmp_70515, env[10]);
      INSTR_call(&tmp_70517, env[14], tmp_70516);
      INSTR_struct(&DocText_c24_70518, 24, 1,
        _70513);
      INSTR_call(&tmp_70519, tmp_70517, DocText_c24_70518);
      INSTR_mov(&case_70503, tmp_70519);
      break;
    case 25:
      INSTR_mov(&_70520, ((CLC_node)_70502)->data[0]);
      INSTR_mov(&_70521, ((CLC_node)_70502)->data[1]);
      INSTR_struct(&DocBreak_c26_70522, 26, 1,
        env[2]);
      INSTR_call(&tmp_70523, env[14], DocBreak_c26_70522);
      INSTR_call(&tmp_70524, tmp_70523, env[10]);
      INSTR_call(&tmp_70525, env[14], tmp_70524);
      INSTR_struct(&DocNest_c25_70526, 25, 2,
        _70520, _70521);
      INSTR_call(&tmp_70527, tmp_70525, DocNest_c25_70526);
      INSTR_mov(&case_70503, tmp_70527);
      break;
    case 26:
      INSTR_mov(&_70528, ((CLC_node)_70502)->data[0]);
      INSTR_struct(&DocBreak_c26_70529, 26, 1,
        env[2]);
      INSTR_call(&tmp_70530, env[14], DocBreak_c26_70529);
      INSTR_call(&tmp_70531, tmp_70530, env[10]);
      INSTR_call(&tmp_70532, env[14], tmp_70531);
      INSTR_struct(&DocBreak_c26_70533, 26, 1,
        _70528);
      INSTR_call(&tmp_70534, tmp_70532, DocBreak_c26_70533);
      INSTR_mov(&case_70503, tmp_70534);
      break;
    case 27:
      INSTR_mov(&_70535, ((CLC_node)_70502)->data[0]);
      INSTR_struct(&DocBreak_c26_70536, 26, 1,
        env[2]);
      INSTR_call(&tmp_70537, env[14], DocBreak_c26_70536);
      INSTR_call(&tmp_70538, tmp_70537, env[10]);
      INSTR_call(&tmp_70539, env[14], tmp_70538);
      INSTR_struct(&DocGroup_c27_70540, 27, 1,
        _70535);
      INSTR_call(&tmp_70541, tmp_70539, DocGroup_c27_70540);
      INSTR_mov(&case_70503, tmp_70541);
      break;}
  return case_70503;
}

CLC_ptr lam_70586(CLC_ptr _70546, CLC_env env)
{
  CLC_ptr _70549; CLC_ptr _70550; CLC_ptr _70557; CLC_ptr _70564;
  CLC_ptr _70565; CLC_ptr _70572; CLC_ptr _70579; CLC_ptr DocBreak_c26_70577;
  CLC_ptr DocCons_c23_70555; CLC_ptr DocGroup_c27_70548;
  CLC_ptr DocGroup_c27_70551; CLC_ptr DocGroup_c27_70558;
  CLC_ptr DocGroup_c27_70566; CLC_ptr DocGroup_c27_70573;
  CLC_ptr DocGroup_c27_70580; CLC_ptr DocGroup_c27_70584;
  CLC_ptr DocNest_c25_70570; CLC_ptr DocText_c24_70562; CLC_ptr case_70547;
  CLC_ptr tmp_70552; CLC_ptr tmp_70553; CLC_ptr tmp_70554; CLC_ptr tmp_70556;
  CLC_ptr tmp_70559; CLC_ptr tmp_70560; CLC_ptr tmp_70561; CLC_ptr tmp_70563;
  CLC_ptr tmp_70567; CLC_ptr tmp_70568; CLC_ptr tmp_70569; CLC_ptr tmp_70571;
  CLC_ptr tmp_70574; CLC_ptr tmp_70575; CLC_ptr tmp_70576; CLC_ptr tmp_70578;
  CLC_ptr tmp_70581; CLC_ptr tmp_70582; CLC_ptr tmp_70583; CLC_ptr tmp_70585;
  switch(((CLC_node)_70546)->tag){
    case 22:
      INSTR_struct(&DocGroup_c27_70548, 27, 1,
        env[2]);
      INSTR_mov(&case_70547, DocGroup_c27_70548);
      break;
    case 23:
      INSTR_mov(&_70549, ((CLC_node)_70546)->data[0]);
      INSTR_mov(&_70550, ((CLC_node)_70546)->data[1]);
      INSTR_struct(&DocGroup_c27_70551, 27, 1,
        env[2]);
      INSTR_call(&tmp_70552, env[14], DocGroup_c27_70551);
      INSTR_call(&tmp_70553, tmp_70552, env[10]);
      INSTR_call(&tmp_70554, env[14], tmp_70553);
      INSTR_struct(&DocCons_c23_70555, 23, 2,
        _70549, _70550);
      INSTR_call(&tmp_70556, tmp_70554, DocCons_c23_70555);
      INSTR_mov(&case_70547, tmp_70556);
      break;
    case 24:
      INSTR_mov(&_70557, ((CLC_node)_70546)->data[0]);
      INSTR_struct(&DocGroup_c27_70558, 27, 1,
        env[2]);
      INSTR_call(&tmp_70559, env[14], DocGroup_c27_70558);
      INSTR_call(&tmp_70560, tmp_70559, env[10]);
      INSTR_call(&tmp_70561, env[14], tmp_70560);
      INSTR_struct(&DocText_c24_70562, 24, 1,
        _70557);
      INSTR_call(&tmp_70563, tmp_70561, DocText_c24_70562);
      INSTR_mov(&case_70547, tmp_70563);
      break;
    case 25:
      INSTR_mov(&_70564, ((CLC_node)_70546)->data[0]);
      INSTR_mov(&_70565, ((CLC_node)_70546)->data[1]);
      INSTR_struct(&DocGroup_c27_70566, 27, 1,
        env[2]);
      INSTR_call(&tmp_70567, env[14], DocGroup_c27_70566);
      INSTR_call(&tmp_70568, tmp_70567, env[10]);
      INSTR_call(&tmp_70569, env[14], tmp_70568);
      INSTR_struct(&DocNest_c25_70570, 25, 2,
        _70564, _70565);
      INSTR_call(&tmp_70571, tmp_70569, DocNest_c25_70570);
      INSTR_mov(&case_70547, tmp_70571);
      break;
    case 26:
      INSTR_mov(&_70572, ((CLC_node)_70546)->data[0]);
      INSTR_struct(&DocGroup_c27_70573, 27, 1,
        env[2]);
      INSTR_call(&tmp_70574, env[14], DocGroup_c27_70573);
      INSTR_call(&tmp_70575, tmp_70574, env[10]);
      INSTR_call(&tmp_70576, env[14], tmp_70575);
      INSTR_struct(&DocBreak_c26_70577, 26, 1,
        _70572);
      INSTR_call(&tmp_70578, tmp_70576, DocBreak_c26_70577);
      INSTR_mov(&case_70547, tmp_70578);
      break;
    case 27:
      INSTR_mov(&_70579, ((CLC_node)_70546)->data[0]);
      INSTR_struct(&DocGroup_c27_70580, 27, 1,
        env[2]);
      INSTR_call(&tmp_70581, env[14], DocGroup_c27_70580);
      INSTR_call(&tmp_70582, tmp_70581, env[10]);
      INSTR_call(&tmp_70583, env[14], tmp_70582);
      INSTR_struct(&DocGroup_c27_70584, 27, 1,
        _70579);
      INSTR_call(&tmp_70585, tmp_70583, DocGroup_c27_70584);
      INSTR_mov(&case_70547, tmp_70585);
      break;}
  return case_70547;
}

CLC_ptr join_70588(CLC_ptr _70360, CLC_env env)
{
  CLC_ptr _70366; CLC_ptr _70367; CLC_ptr _70411; CLC_ptr _70455;
  CLC_ptr _70456; CLC_ptr _70500; CLC_ptr _70544; CLC_ptr case_70361;
  CLC_ptr clo_70365; CLC_ptr clo_70410; CLC_ptr clo_70454; CLC_ptr clo_70499;
  CLC_ptr clo_70543; CLC_ptr clo_70587;
  switch(((CLC_node)_70360)->tag){
    case 22:
      INSTR_clo(&clo_70365, &lam_70364, 32,
        0, _70360, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
        env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
        env[15], env[16], env[17], env[18], env[19], env[20], env[21],
        env[22], env[23], env[24], env[25], env[26], env[27], env[28],
        env[29]);
      INSTR_mov(&case_70361, clo_70365);
      break;
    case 23:
      INSTR_mov(&_70366, ((CLC_node)_70360)->data[0]);
      INSTR_mov(&_70367, ((CLC_node)_70360)->data[1]);
      INSTR_clo(&clo_70410, &lam_70409, 34,
        0, _70360, _70366, _70367, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26],
        env[27], env[28], env[29]);
      INSTR_mov(&case_70361, clo_70410);
      break;
    case 24:
      INSTR_mov(&_70411, ((CLC_node)_70360)->data[0]);
      INSTR_clo(&clo_70454, &lam_70453, 33,
        0, _70360, _70411, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29]);
      INSTR_mov(&case_70361, clo_70454);
      break;
    case 25:
      INSTR_mov(&_70455, ((CLC_node)_70360)->data[0]);
      INSTR_mov(&_70456, ((CLC_node)_70360)->data[1]);
      INSTR_clo(&clo_70499, &lam_70498, 34,
        0, _70360, _70455, _70456, env[0], env[1], env[2], env[3], env[4],
        env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12],
        env[13], env[14], env[15], env[16], env[17], env[18], env[19],
        env[20], env[21], env[22], env[23], env[24], env[25], env[26],
        env[27], env[28], env[29]);
      INSTR_mov(&case_70361, clo_70499);
      break;
    case 26:
      INSTR_mov(&_70500, ((CLC_node)_70360)->data[0]);
      INSTR_clo(&clo_70543, &lam_70542, 33,
        0, _70360, _70500, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29]);
      INSTR_mov(&case_70361, clo_70543);
      break;
    case 27:
      INSTR_mov(&_70544, ((CLC_node)_70360)->data[0]);
      INSTR_clo(&clo_70587, &lam_70586, 33,
        0, _70360, _70544, env[0], env[1], env[2], env[3], env[4], env[5],
        env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13],
        env[14], env[15], env[16], env[17], env[18], env[19], env[20],
        env[21], env[22], env[23], env[24], env[25], env[26], env[27],
        env[28], env[29]);
      INSTR_mov(&case_70361, clo_70587);
      break;}
  return case_70361;
}

CLC_ptr lam_70610(CLC_ptr _70595, CLC_env env)
{
  CLC_ptr succ_c5_70597; CLC_ptr succ_c5_70598; CLC_ptr tmp_70599;
  CLC_ptr tmp_70600; CLC_ptr tmp_70601; CLC_ptr tmp_70602; CLC_ptr tmp_70603;
  CLC_ptr tmp_70604; CLC_ptr tmp_70605; CLC_ptr tmp_70606; CLC_ptr tmp_70607;
  CLC_ptr tmp_70608; CLC_ptr tmp_70609; CLC_ptr zero_c4_70596;
  INSTR_struct(&zero_c4_70596, 4, 0);
  INSTR_struct(&succ_c5_70597, 5, 1,
    zero_c4_70596);
  INSTR_struct(&succ_c5_70598, 5, 1,
    succ_c5_70597);
  INSTR_call(&tmp_70599, env[13], succ_c5_70598);
  INSTR_call(&tmp_70600, env[14], env[3]);
  INSTR_call(&tmp_70601, env[5], tmp_70600);
  INSTR_call(&tmp_70602, env[14], env[1]);
  INSTR_call(&tmp_70603, tmp_70601, tmp_70602);
  INSTR_call(&tmp_70604, env[10], tmp_70603);
  INSTR_call(&tmp_70605, env[5], tmp_70604);
  INSTR_call(&tmp_70606, env[14], _70595);
  INSTR_call(&tmp_70607, tmp_70605, tmp_70606);
  INSTR_call(&tmp_70608, tmp_70599, tmp_70607);
  INSTR_call(&tmp_70609, env[10], tmp_70608);
  return tmp_70609;
}

CLC_ptr lam_70612(CLC_ptr _70593, CLC_env env)
{
  CLC_ptr clo_70611;
  INSTR_clo(&clo_70611, &lam_70610, 35,
    0, _70593, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30],
    env[31], env[32]);
  return clo_70611;
}

CLC_ptr binop_70614(CLC_ptr _70591, CLC_env env)
{
  CLC_ptr clo_70613;
  INSTR_clo(&clo_70613, &lam_70612, 33,
    0, _70591, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30]);
  return clo_70613;
}

CLC_ptr lam_70885(CLC_ptr _70749, CLC_env env)
{
  CLC_ptr Ascii_c16_70762; CLC_ptr Ascii_c16_70771; CLC_ptr Ascii_c16_70793;
  CLC_ptr Ascii_c16_70802; CLC_ptr Ascii_c16_70811; CLC_ptr Ascii_c16_70820;
  CLC_ptr Ascii_c16_70844; CLC_ptr Ascii_c16_70853; CLC_ptr Ascii_c16_70862;
  CLC_ptr Ascii_c16_70871; CLC_ptr EmptyString_c17_70772;
  CLC_ptr EmptyString_c17_70821; CLC_ptr EmptyString_c17_70872;
  CLC_ptr String_c18_70773; CLC_ptr String_c18_70774;
  CLC_ptr String_c18_70822; CLC_ptr String_c18_70823;
  CLC_ptr String_c18_70824; CLC_ptr String_c18_70825;
  CLC_ptr String_c18_70873; CLC_ptr String_c18_70874;
  CLC_ptr String_c18_70875; CLC_ptr String_c18_70876; CLC_ptr false_c3_70754;
  CLC_ptr false_c3_70757; CLC_ptr false_c3_70759; CLC_ptr false_c3_70760;
  CLC_ptr false_c3_70763; CLC_ptr false_c3_70766; CLC_ptr false_c3_70767;
  CLC_ptr false_c3_70770; CLC_ptr false_c3_70785; CLC_ptr false_c3_70789;
  CLC_ptr false_c3_70791; CLC_ptr false_c3_70792; CLC_ptr false_c3_70794;
  CLC_ptr false_c3_70797; CLC_ptr false_c3_70799; CLC_ptr false_c3_70800;
  CLC_ptr false_c3_70801; CLC_ptr false_c3_70803; CLC_ptr false_c3_70806;
  CLC_ptr false_c3_70807; CLC_ptr false_c3_70809; CLC_ptr false_c3_70812;
  CLC_ptr false_c3_70815; CLC_ptr false_c3_70819; CLC_ptr false_c3_70836;
  CLC_ptr false_c3_70839; CLC_ptr false_c3_70840; CLC_ptr false_c3_70842;
  CLC_ptr false_c3_70845; CLC_ptr false_c3_70848; CLC_ptr false_c3_70851;
  CLC_ptr false_c3_70852; CLC_ptr false_c3_70854; CLC_ptr false_c3_70858;
  CLC_ptr false_c3_70859; CLC_ptr false_c3_70863; CLC_ptr false_c3_70866;
  CLC_ptr false_c3_70867; CLC_ptr false_c3_70869; CLC_ptr succ_c5_70751;
  CLC_ptr succ_c5_70752; CLC_ptr succ_c5_70782; CLC_ptr succ_c5_70783;
  CLC_ptr succ_c5_70833; CLC_ptr succ_c5_70834; CLC_ptr tmp_70753;
  CLC_ptr tmp_70775; CLC_ptr tmp_70776; CLC_ptr tmp_70777; CLC_ptr tmp_70778;
  CLC_ptr tmp_70779; CLC_ptr tmp_70780; CLC_ptr tmp_70784; CLC_ptr tmp_70826;
  CLC_ptr tmp_70827; CLC_ptr tmp_70828; CLC_ptr tmp_70829; CLC_ptr tmp_70830;
  CLC_ptr tmp_70831; CLC_ptr tmp_70835; CLC_ptr tmp_70877; CLC_ptr tmp_70878;
  CLC_ptr tmp_70879; CLC_ptr tmp_70880; CLC_ptr tmp_70881; CLC_ptr tmp_70882;
  CLC_ptr tmp_70883; CLC_ptr tmp_70884; CLC_ptr true_c2_70755;
  CLC_ptr true_c2_70756; CLC_ptr true_c2_70758; CLC_ptr true_c2_70761;
  CLC_ptr true_c2_70764; CLC_ptr true_c2_70765; CLC_ptr true_c2_70768;
  CLC_ptr true_c2_70769; CLC_ptr true_c2_70786; CLC_ptr true_c2_70787;
  CLC_ptr true_c2_70788; CLC_ptr true_c2_70790; CLC_ptr true_c2_70795;
  CLC_ptr true_c2_70796; CLC_ptr true_c2_70798; CLC_ptr true_c2_70804;
  CLC_ptr true_c2_70805; CLC_ptr true_c2_70808; CLC_ptr true_c2_70810;
  CLC_ptr true_c2_70813; CLC_ptr true_c2_70814; CLC_ptr true_c2_70816;
  CLC_ptr true_c2_70817; CLC_ptr true_c2_70818; CLC_ptr true_c2_70837;
  CLC_ptr true_c2_70838; CLC_ptr true_c2_70841; CLC_ptr true_c2_70843;
  CLC_ptr true_c2_70846; CLC_ptr true_c2_70847; CLC_ptr true_c2_70849;
  CLC_ptr true_c2_70850; CLC_ptr true_c2_70855; CLC_ptr true_c2_70856;
  CLC_ptr true_c2_70857; CLC_ptr true_c2_70860; CLC_ptr true_c2_70861;
  CLC_ptr true_c2_70864; CLC_ptr true_c2_70865; CLC_ptr true_c2_70868;
  CLC_ptr true_c2_70870; CLC_ptr zero_c4_70750; CLC_ptr zero_c4_70781;
  CLC_ptr zero_c4_70832;
  INSTR_struct(&zero_c4_70750, 4, 0);
  INSTR_struct(&succ_c5_70751, 5, 1,
    zero_c4_70750);
  INSTR_struct(&succ_c5_70752, 5, 1,
    succ_c5_70751);
  INSTR_call(&tmp_70753, env[17], succ_c5_70752);
  INSTR_struct(&false_c3_70754, 3, 0);
  INSTR_struct(&true_c2_70755, 2, 0);
  INSTR_struct(&true_c2_70756, 2, 0);
  INSTR_struct(&false_c3_70757, 3, 0);
  INSTR_struct(&true_c2_70758, 2, 0);
  INSTR_struct(&false_c3_70759, 3, 0);
  INSTR_struct(&false_c3_70760, 3, 0);
  INSTR_struct(&true_c2_70761, 2, 0);
  INSTR_struct(&Ascii_c16_70762, 16, 8,
    false_c3_70754, true_c2_70755, true_c2_70756, false_c3_70757,
    true_c2_70758, false_c3_70759, false_c3_70760, true_c2_70761);
  INSTR_struct(&false_c3_70763, 3, 0);
  INSTR_struct(&true_c2_70764, 2, 0);
  INSTR_struct(&true_c2_70765, 2, 0);
  INSTR_struct(&false_c3_70766, 3, 0);
  INSTR_struct(&false_c3_70767, 3, 0);
  INSTR_struct(&true_c2_70768, 2, 0);
  INSTR_struct(&true_c2_70769, 2, 0);
  INSTR_struct(&false_c3_70770, 3, 0);
  INSTR_struct(&Ascii_c16_70771, 16, 8,
    false_c3_70763, true_c2_70764, true_c2_70765, false_c3_70766,
    false_c3_70767, true_c2_70768, true_c2_70769, false_c3_70770);
  INSTR_struct(&EmptyString_c17_70772, 17, 0);
  INSTR_struct(&String_c18_70773, 18, 2,
    Ascii_c16_70771, EmptyString_c17_70772);
  INSTR_struct(&String_c18_70774, 18, 2,
    Ascii_c16_70762, String_c18_70773);
  INSTR_call(&tmp_70775, env[18], String_c18_70774);
  INSTR_call(&tmp_70776, env[9], tmp_70775);
  INSTR_call(&tmp_70777, tmp_70776, env[3]);
  INSTR_call(&tmp_70778, tmp_70753, tmp_70777);
  INSTR_call(&tmp_70779, env[14], tmp_70778);
  INSTR_call(&tmp_70780, env[9], tmp_70779);
  INSTR_struct(&zero_c4_70781, 4, 0);
  INSTR_struct(&succ_c5_70782, 5, 1,
    zero_c4_70781);
  INSTR_struct(&succ_c5_70783, 5, 1,
    succ_c5_70782);
  INSTR_call(&tmp_70784, env[17], succ_c5_70783);
  INSTR_struct(&false_c3_70785, 3, 0);
  INSTR_struct(&true_c2_70786, 2, 0);
  INSTR_struct(&true_c2_70787, 2, 0);
  INSTR_struct(&true_c2_70788, 2, 0);
  INSTR_struct(&false_c3_70789, 3, 0);
  INSTR_struct(&true_c2_70790, 2, 0);
  INSTR_struct(&false_c3_70791, 3, 0);
  INSTR_struct(&false_c3_70792, 3, 0);
  INSTR_struct(&Ascii_c16_70793, 16, 8,
    false_c3_70785, true_c2_70786, true_c2_70787, true_c2_70788,
    false_c3_70789, true_c2_70790, false_c3_70791, false_c3_70792);
  INSTR_struct(&false_c3_70794, 3, 0);
  INSTR_struct(&true_c2_70795, 2, 0);
  INSTR_struct(&true_c2_70796, 2, 0);
  INSTR_struct(&false_c3_70797, 3, 0);
  INSTR_struct(&true_c2_70798, 2, 0);
  INSTR_struct(&false_c3_70799, 3, 0);
  INSTR_struct(&false_c3_70800, 3, 0);
  INSTR_struct(&false_c3_70801, 3, 0);
  INSTR_struct(&Ascii_c16_70802, 16, 8,
    false_c3_70794, true_c2_70795, true_c2_70796, false_c3_70797,
    true_c2_70798, false_c3_70799, false_c3_70800, false_c3_70801);
  INSTR_struct(&false_c3_70803, 3, 0);
  INSTR_struct(&true_c2_70804, 2, 0);
  INSTR_struct(&true_c2_70805, 2, 0);
  INSTR_struct(&false_c3_70806, 3, 0);
  INSTR_struct(&false_c3_70807, 3, 0);
  INSTR_struct(&true_c2_70808, 2, 0);
  INSTR_struct(&false_c3_70809, 3, 0);
  INSTR_struct(&true_c2_70810, 2, 0);
  INSTR_struct(&Ascii_c16_70811, 16, 8,
    false_c3_70803, true_c2_70804, true_c2_70805, false_c3_70806,
    false_c3_70807, true_c2_70808, false_c3_70809, true_c2_70810);
  INSTR_struct(&false_c3_70812, 3, 0);
  INSTR_struct(&true_c2_70813, 2, 0);
  INSTR_struct(&true_c2_70814, 2, 0);
  INSTR_struct(&false_c3_70815, 3, 0);
  INSTR_struct(&true_c2_70816, 2, 0);
  INSTR_struct(&true_c2_70817, 2, 0);
  INSTR_struct(&true_c2_70818, 2, 0);
  INSTR_struct(&false_c3_70819, 3, 0);
  INSTR_struct(&Ascii_c16_70820, 16, 8,
    false_c3_70812, true_c2_70813, true_c2_70814, false_c3_70815,
    true_c2_70816, true_c2_70817, true_c2_70818, false_c3_70819);
  INSTR_struct(&EmptyString_c17_70821, 17, 0);
  INSTR_struct(&String_c18_70822, 18, 2,
    Ascii_c16_70820, EmptyString_c17_70821);
  INSTR_struct(&String_c18_70823, 18, 2,
    Ascii_c16_70811, String_c18_70822);
  INSTR_struct(&String_c18_70824, 18, 2,
    Ascii_c16_70802, String_c18_70823);
  INSTR_struct(&String_c18_70825, 18, 2,
    Ascii_c16_70793, String_c18_70824);
  INSTR_call(&tmp_70826, env[18], String_c18_70825);
  INSTR_call(&tmp_70827, env[9], tmp_70826);
  INSTR_call(&tmp_70828, tmp_70827, env[1]);
  INSTR_call(&tmp_70829, tmp_70784, tmp_70828);
  INSTR_call(&tmp_70830, env[14], tmp_70829);
  INSTR_call(&tmp_70831, env[9], tmp_70830);
  INSTR_struct(&zero_c4_70832, 4, 0);
  INSTR_struct(&succ_c5_70833, 5, 1,
    zero_c4_70832);
  INSTR_struct(&succ_c5_70834, 5, 1,
    succ_c5_70833);
  INSTR_call(&tmp_70835, env[17], succ_c5_70834);
  INSTR_struct(&false_c3_70836, 3, 0);
  INSTR_struct(&true_c2_70837, 2, 0);
  INSTR_struct(&true_c2_70838, 2, 0);
  INSTR_struct(&false_c3_70839, 3, 0);
  INSTR_struct(&false_c3_70840, 3, 0);
  INSTR_struct(&true_c2_70841, 2, 0);
  INSTR_struct(&false_c3_70842, 3, 0);
  INSTR_struct(&true_c2_70843, 2, 0);
  INSTR_struct(&Ascii_c16_70844, 16, 8,
    false_c3_70836, true_c2_70837, true_c2_70838, false_c3_70839,
    false_c3_70840, true_c2_70841, false_c3_70842, true_c2_70843);
  INSTR_struct(&false_c3_70845, 3, 0);
  INSTR_struct(&true_c2_70846, 2, 0);
  INSTR_struct(&true_c2_70847, 2, 0);
  INSTR_struct(&false_c3_70848, 3, 0);
  INSTR_struct(&true_c2_70849, 2, 0);
  INSTR_struct(&true_c2_70850, 2, 0);
  INSTR_struct(&false_c3_70851, 3, 0);
  INSTR_struct(&false_c3_70852, 3, 0);
  INSTR_struct(&Ascii_c16_70853, 16, 8,
    false_c3_70845, true_c2_70846, true_c2_70847, false_c3_70848,
    true_c2_70849, true_c2_70850, false_c3_70851, false_c3_70852);
  INSTR_struct(&false_c3_70854, 3, 0);
  INSTR_struct(&true_c2_70855, 2, 0);
  INSTR_struct(&true_c2_70856, 2, 0);
  INSTR_struct(&true_c2_70857, 2, 0);
  INSTR_struct(&false_c3_70858, 3, 0);
  INSTR_struct(&false_c3_70859, 3, 0);
  INSTR_struct(&true_c2_70860, 2, 0);
  INSTR_struct(&true_c2_70861, 2, 0);
  INSTR_struct(&Ascii_c16_70862, 16, 8,
    false_c3_70854, true_c2_70855, true_c2_70856, true_c2_70857,
    false_c3_70858, false_c3_70859, true_c2_70860, true_c2_70861);
  INSTR_struct(&false_c3_70863, 3, 0);
  INSTR_struct(&true_c2_70864, 2, 0);
  INSTR_struct(&true_c2_70865, 2, 0);
  INSTR_struct(&false_c3_70866, 3, 0);
  INSTR_struct(&false_c3_70867, 3, 0);
  INSTR_struct(&true_c2_70868, 2, 0);
  INSTR_struct(&false_c3_70869, 3, 0);
  INSTR_struct(&true_c2_70870, 2, 0);
  INSTR_struct(&Ascii_c16_70871, 16, 8,
    false_c3_70863, true_c2_70864, true_c2_70865, false_c3_70866,
    false_c3_70867, true_c2_70868, false_c3_70869, true_c2_70870);
  INSTR_struct(&EmptyString_c17_70872, 17, 0);
  INSTR_struct(&String_c18_70873, 18, 2,
    Ascii_c16_70871, EmptyString_c17_70872);
  INSTR_struct(&String_c18_70874, 18, 2,
    Ascii_c16_70862, String_c18_70873);
  INSTR_struct(&String_c18_70875, 18, 2,
    Ascii_c16_70853, String_c18_70874);
  INSTR_struct(&String_c18_70876, 18, 2,
    Ascii_c16_70844, String_c18_70875);
  INSTR_call(&tmp_70877, env[18], String_c18_70876);
  INSTR_call(&tmp_70878, env[9], tmp_70877);
  INSTR_call(&tmp_70879, tmp_70878, _70749);
  INSTR_call(&tmp_70880, tmp_70835, tmp_70879);
  INSTR_call(&tmp_70881, env[14], tmp_70880);
  INSTR_call(&tmp_70882, tmp_70831, tmp_70881);
  INSTR_call(&tmp_70883, tmp_70780, tmp_70882);
  INSTR_call(&tmp_70884, env[14], tmp_70883);
  return tmp_70884;
}

CLC_ptr lam_70887(CLC_ptr _70747, CLC_env env)
{
  CLC_ptr clo_70886;
  INSTR_clo(&clo_70886, &lam_70885, 39,
    0, _70747, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30],
    env[31], env[32], env[33], env[34], env[35], env[36]);
  return clo_70886;
}

CLC_ptr ifthen_70889(CLC_ptr _70745, CLC_env env)
{
  CLC_ptr clo_70888;
  INSTR_clo(&clo_70888, &lam_70887, 37,
    0, _70745, env[0], env[1], env[2], env[3], env[4], env[5], env[6],
    env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14],
    env[15], env[16], env[17], env[18], env[19], env[20], env[21], env[22],
    env[23], env[24], env[25], env[26], env[27], env[28], env[29], env[30],
    env[31], env[32], env[33], env[34]);
  return clo_70888;
}

CLC_ptr lam_70913(CLC_ptr _70911, CLC_env env)
{
  CLC_ptr case_70912;
  switch(((CLC_node)_70911)->tag){
    case 1: INSTR_mov(&case_70912, env[38]);
            break;}
  return case_70912;
}

int main()
{
  CLC_ptr _301; CLC_ptr Ascii_c16_70092; CLC_ptr Ascii_c16_70624;
  CLC_ptr Ascii_c16_70636; CLC_ptr Ascii_c16_70645; CLC_ptr Ascii_c16_70658;
  CLC_ptr Ascii_c16_70670; CLC_ptr Ascii_c16_70682; CLC_ptr Ascii_c16_70691;
  CLC_ptr Ascii_c16_70704; CLC_ptr Ascii_c16_70716; CLC_ptr Ascii_c16_70728;
  CLC_ptr Ascii_c16_70740; CLC_ptr DocBreak_c26_70095;
  CLC_ptr DocNil_c22_70069; CLC_ptr EmptyString_c17_70093;
  CLC_ptr EmptyString_c17_70625; CLC_ptr EmptyString_c17_70646;
  CLC_ptr EmptyString_c17_70659; CLC_ptr EmptyString_c17_70671;
  CLC_ptr EmptyString_c17_70692; CLC_ptr EmptyString_c17_70705;
  CLC_ptr EmptyString_c17_70717; CLC_ptr EmptyString_c17_70729;
  CLC_ptr EmptyString_c17_70741; CLC_ptr String_c18_70094;
  CLC_ptr String_c18_70626; CLC_ptr String_c18_70647;
  CLC_ptr String_c18_70648; CLC_ptr String_c18_70660;
  CLC_ptr String_c18_70672; CLC_ptr String_c18_70693;
  CLC_ptr String_c18_70694; CLC_ptr String_c18_70706;
  CLC_ptr String_c18_70718; CLC_ptr String_c18_70730;
  CLC_ptr String_c18_70742; CLC_ptr addn_3; CLC_ptr addn_69924;
  CLC_ptr binop_282; CLC_ptr binop_70615; CLC_ptr break_154;
  CLC_ptr breakWith_155; CLC_ptr breakWith_70100; CLC_ptr cat_67;
  CLC_ptr cat_69962; CLC_ptr clo_70914; CLC_ptr close_err_130;
  CLC_ptr close_err_70059; CLC_ptr close_in_114; CLC_ptr close_in_70017;
  CLC_ptr close_out_122; CLC_ptr close_out_70038; CLC_ptr cond_289;
  CLC_ptr dcons_140; CLC_ptr dcons_70068; CLC_ptr doc_299; CLC_ptr empty_145;
  CLC_ptr expr1_290; CLC_ptr expr2_291; CLC_ptr false_c3_70084;
  CLC_ptr false_c3_70085; CLC_ptr false_c3_70087; CLC_ptr false_c3_70088;
  CLC_ptr false_c3_70089; CLC_ptr false_c3_70090; CLC_ptr false_c3_70091;
  CLC_ptr false_c3_70616; CLC_ptr false_c3_70619; CLC_ptr false_c3_70620;
  CLC_ptr false_c3_70621; CLC_ptr false_c3_70622; CLC_ptr false_c3_70628;
  CLC_ptr false_c3_70629; CLC_ptr false_c3_70634; CLC_ptr false_c3_70637;
  CLC_ptr false_c3_70638; CLC_ptr false_c3_70643; CLC_ptr false_c3_70650;
  CLC_ptr false_c3_70653; CLC_ptr false_c3_70654; CLC_ptr false_c3_70655;
  CLC_ptr false_c3_70657; CLC_ptr false_c3_70662; CLC_ptr false_c3_70665;
  CLC_ptr false_c3_70666; CLC_ptr false_c3_70667; CLC_ptr false_c3_70668;
  CLC_ptr false_c3_70674; CLC_ptr false_c3_70675; CLC_ptr false_c3_70680;
  CLC_ptr false_c3_70681; CLC_ptr false_c3_70683; CLC_ptr false_c3_70684;
  CLC_ptr false_c3_70689; CLC_ptr false_c3_70690; CLC_ptr false_c3_70696;
  CLC_ptr false_c3_70699; CLC_ptr false_c3_70700; CLC_ptr false_c3_70701;
  CLC_ptr false_c3_70703; CLC_ptr false_c3_70708; CLC_ptr false_c3_70711;
  CLC_ptr false_c3_70712; CLC_ptr false_c3_70713; CLC_ptr false_c3_70714;
  CLC_ptr false_c3_70720; CLC_ptr false_c3_70721; CLC_ptr false_c3_70723;
  CLC_ptr false_c3_70725; CLC_ptr false_c3_70732; CLC_ptr false_c3_70735;
  CLC_ptr false_c3_70736; CLC_ptr false_c3_70737; CLC_ptr false_c3_70739;
  CLC_ptr fits_175; CLC_ptr fits_70231; CLC_ptr format_218;
  CLC_ptr format_70323; CLC_ptr group_158; CLC_ptr group_70105;
  CLC_ptr ifthen_292; CLC_ptr ifthen_70890; CLC_ptr join_275;
  CLC_ptr join_70589; CLC_ptr lt_84; CLC_ptr lt_69980; CLC_ptr nest_149;
  CLC_ptr nest_70083; CLC_ptr pretty_269; CLC_ptr pretty_70358;
  CLC_ptr printerr_125; CLC_ptr printerr_70051; CLC_ptr printline_117;
  CLC_ptr printline_70030; CLC_ptr readline_109; CLC_ptr readline_70009;
  CLC_ptr sdocToString_165; CLC_ptr sdocToString_70157;
  CLC_ptr stderr_rec_102; CLC_ptr stderr_rec_69995; CLC_ptr stderr_t_108;
  CLC_ptr stdin_rec_94; CLC_ptr stdin_rec_69985; CLC_ptr stdin_t_106;
  CLC_ptr stdout_300; CLC_ptr stdout_70894; CLC_ptr stdout_rec_98;
  CLC_ptr stdout_rec_69990; CLC_ptr stdout_t_107; CLC_ptr strlen_74;
  CLC_ptr strlen_69972; CLC_ptr subn_9; CLC_ptr subn_69944;
  CLC_ptr succ_c5_70897; CLC_ptr succ_c5_70898; CLC_ptr succ_c5_70899;
  CLC_ptr succ_c5_70900; CLC_ptr succ_c5_70901; CLC_ptr succ_c5_70902;
  CLC_ptr succ_c5_70903; CLC_ptr succ_c5_70904; CLC_ptr succ_c5_70905;
  CLC_ptr succ_c5_70906; CLC_ptr text_146; CLC_ptr text_70074;
  CLC_ptr tmp_69997; CLC_ptr tmp_69999; CLC_ptr tmp_70001; CLC_ptr tmp_70627;
  CLC_ptr tmp_70649; CLC_ptr tmp_70661; CLC_ptr tmp_70673; CLC_ptr tmp_70695;
  CLC_ptr tmp_70707; CLC_ptr tmp_70719; CLC_ptr tmp_70731; CLC_ptr tmp_70743;
  CLC_ptr tmp_70891; CLC_ptr tmp_70892; CLC_ptr tmp_70893; CLC_ptr tmp_70895;
  CLC_ptr tmp_70907; CLC_ptr tmp_70908; CLC_ptr tmp_70909; CLC_ptr tmp_70915;
  CLC_ptr tmp_70916; CLC_ptr true_c2_70086; CLC_ptr true_c2_70617;
  CLC_ptr true_c2_70618; CLC_ptr true_c2_70623; CLC_ptr true_c2_70630;
  CLC_ptr true_c2_70631; CLC_ptr true_c2_70632; CLC_ptr true_c2_70633;
  CLC_ptr true_c2_70635; CLC_ptr true_c2_70639; CLC_ptr true_c2_70640;
  CLC_ptr true_c2_70641; CLC_ptr true_c2_70642; CLC_ptr true_c2_70644;
  CLC_ptr true_c2_70651; CLC_ptr true_c2_70652; CLC_ptr true_c2_70656;
  CLC_ptr true_c2_70663; CLC_ptr true_c2_70664; CLC_ptr true_c2_70669;
  CLC_ptr true_c2_70676; CLC_ptr true_c2_70677; CLC_ptr true_c2_70678;
  CLC_ptr true_c2_70679; CLC_ptr true_c2_70685; CLC_ptr true_c2_70686;
  CLC_ptr true_c2_70687; CLC_ptr true_c2_70688; CLC_ptr true_c2_70697;
  CLC_ptr true_c2_70698; CLC_ptr true_c2_70702; CLC_ptr true_c2_70709;
  CLC_ptr true_c2_70710; CLC_ptr true_c2_70715; CLC_ptr true_c2_70722;
  CLC_ptr true_c2_70724; CLC_ptr true_c2_70726; CLC_ptr true_c2_70727;
  CLC_ptr true_c2_70733; CLC_ptr true_c2_70734; CLC_ptr true_c2_70738;
  CLC_ptr tt_c1_69996; CLC_ptr tt_c1_69998; CLC_ptr tt_c1_70000;
  CLC_ptr zero_c4_70896;
  INSTR_clo(&addn_69924, &addn_69923, 2, 0, 0);
  INSTR_mov(&addn_3, addn_69924);
  INSTR_clo(&subn_69944, &subn_69943, 3, 0, addn_3, 0);
  INSTR_mov(&subn_9, subn_69944);
  INSTR_clo(&cat_69962, &cat_69961, 4, 0, subn_9, addn_3, 0);
  INSTR_mov(&cat_67, cat_69962);
  INSTR_clo(&strlen_69972, &strlen_69971, 5, 0, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&strlen_74, strlen_69972);
  INSTR_clo(&lt_69980, &lt_69979, 6,
    0, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&lt_84, lt_69980);
  INSTR_clo(&stdin_rec_69985, &stdin_rec_69984, 7,
    0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdin_rec_94, stdin_rec_69985);
  INSTR_clo(&stdout_rec_69990, &stdout_rec_69989, 8,
    0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdout_rec_98, stdout_rec_69990);
  INSTR_clo(&stderr_rec_69995, &stderr_rec_69994, 9,
    0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3,
    0);
  INSTR_mov(&stderr_rec_102, stderr_rec_69995);
  INSTR_struct(&tt_c1_69996, 1, 0);
  INSTR_call(&tmp_69997, stdin_rec_94, tt_c1_69996);
  INSTR_mov(&stdin_t_106, tmp_69997);
  INSTR_struct(&tt_c1_69998, 1, 0);
  INSTR_call(&tmp_69999, stdout_rec_98, tt_c1_69998);
  INSTR_mov(&stdout_t_107, tmp_69999);
  INSTR_struct(&tt_c1_70000, 1, 0);
  INSTR_call(&tmp_70001, stderr_rec_102, tt_c1_70000);
  INSTR_mov(&stderr_t_108, tmp_70001);
  INSTR_clo(&readline_70009, &readline_70008, 13,
    0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&readline_109, readline_70009);
  INSTR_clo(&close_in_70017, &close_in_70016, 14,
    0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_in_114, close_in_70017);
  INSTR_clo(&printline_70030, &printline_70029, 15,
    0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  INSTR_mov(&printline_117, printline_70030);
  INSTR_clo(&close_out_70038, &close_out_70037, 16,
    0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_out_122, close_out_70038);
  INSTR_clo(&printerr_70051, &printerr_70050, 17,
    0, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printerr_125, printerr_70051);
  INSTR_clo(&close_err_70059, &close_err_70058, 18,
    0, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_err_130, close_err_70059);
  INSTR_clo(&dcons_70068, &dcons_70067, 19,
    0, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  INSTR_mov(&dcons_140, dcons_70068);
  INSTR_struct(&DocNil_c22_70069, 22, 0);
  INSTR_mov(&empty_145, DocNil_c22_70069);
  INSTR_clo(&text_70074, &text_70073, 21,
    0, empty_145, dcons_140, close_err_130, printerr_125, close_out_122,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&text_146, text_70074);
  INSTR_clo(&nest_70083, &nest_70082, 22,
    0, text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&nest_149, nest_70083);
  INSTR_struct(&false_c3_70084, 3, 0);
  INSTR_struct(&false_c3_70085, 3, 0);
  INSTR_struct(&true_c2_70086, 2, 0);
  INSTR_struct(&false_c3_70087, 3, 0);
  INSTR_struct(&false_c3_70088, 3, 0);
  INSTR_struct(&false_c3_70089, 3, 0);
  INSTR_struct(&false_c3_70090, 3, 0);
  INSTR_struct(&false_c3_70091, 3, 0);
  INSTR_struct(&Ascii_c16_70092, 16, 8,
    false_c3_70084, false_c3_70085, true_c2_70086, false_c3_70087,
    false_c3_70088, false_c3_70089, false_c3_70090, false_c3_70091);
  INSTR_struct(&EmptyString_c17_70093, 17, 0);
  INSTR_struct(&String_c18_70094, 18, 2,
    Ascii_c16_70092, EmptyString_c17_70093);
  INSTR_struct(&DocBreak_c26_70095, 26, 1,
    String_c18_70094);
  INSTR_mov(&break_154, DocBreak_c26_70095);
  INSTR_clo(&breakWith_70100, &breakWith_70099, 24,
    0, break_154, nest_149, text_146, empty_145, dcons_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&breakWith_155, breakWith_70100);
  INSTR_clo(&group_70105, &group_70104, 25,
    0, breakWith_155, break_154, nest_149, text_146, empty_145, dcons_140,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&group_158, group_70105);
  INSTR_clo(&sdocToString_70157, &sdocToString_70156, 26,
    0, group_158, breakWith_155, break_154, nest_149, text_146, empty_145,
    dcons_140, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  INSTR_mov(&sdocToString_165, sdocToString_70157);
  INSTR_clo(&fits_70231, &fits_70230, 27,
    0, sdocToString_165, group_158, breakWith_155, break_154, nest_149,
    text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&fits_175, fits_70231);
  INSTR_clo(&format_70323, &format_70322, 28,
    0, fits_175, sdocToString_165, group_158, breakWith_155, break_154,
    nest_149, text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&format_218, format_70323);
  INSTR_clo(&pretty_70358, &pretty_70357, 29,
    0, format_218, fits_175, sdocToString_165, group_158, breakWith_155,
    break_154, nest_149, text_146, empty_145, dcons_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&pretty_269, pretty_70358);
  INSTR_clo(&join_70589, &join_70588, 30,
    0, pretty_269, format_218, fits_175, sdocToString_165, group_158,
    breakWith_155, break_154, nest_149, text_146, empty_145, dcons_140,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&join_275, join_70589);
  INSTR_clo(&binop_70615, &binop_70614, 31,
    0, join_275, pretty_269, format_218, fits_175, sdocToString_165,
    group_158, breakWith_155, break_154, nest_149, text_146, empty_145,
    dcons_140, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  INSTR_mov(&binop_282, binop_70615);
  INSTR_struct(&false_c3_70616, 3, 0);
  INSTR_struct(&true_c2_70617, 2, 0);
  INSTR_struct(&true_c2_70618, 2, 0);
  INSTR_struct(&false_c3_70619, 3, 0);
  INSTR_struct(&false_c3_70620, 3, 0);
  INSTR_struct(&false_c3_70621, 3, 0);
  INSTR_struct(&false_c3_70622, 3, 0);
  INSTR_struct(&true_c2_70623, 2, 0);
  INSTR_struct(&Ascii_c16_70624, 16, 8,
    false_c3_70616, true_c2_70617, true_c2_70618, false_c3_70619,
    false_c3_70620, false_c3_70621, false_c3_70622, true_c2_70623);
  INSTR_struct(&EmptyString_c17_70625, 17, 0);
  INSTR_struct(&String_c18_70626, 18, 2,
    Ascii_c16_70624, EmptyString_c17_70625);
  INSTR_call(&tmp_70627, binop_282, String_c18_70626);
  INSTR_struct(&false_c3_70628, 3, 0);
  INSTR_struct(&false_c3_70629, 3, 0);
  INSTR_struct(&true_c2_70630, 2, 0);
  INSTR_struct(&true_c2_70631, 2, 0);
  INSTR_struct(&true_c2_70632, 2, 0);
  INSTR_struct(&true_c2_70633, 2, 0);
  INSTR_struct(&false_c3_70634, 3, 0);
  INSTR_struct(&true_c2_70635, 2, 0);
  INSTR_struct(&Ascii_c16_70636, 16, 8,
    false_c3_70628, false_c3_70629, true_c2_70630, true_c2_70631,
    true_c2_70632, true_c2_70633, false_c3_70634, true_c2_70635);
  INSTR_struct(&false_c3_70637, 3, 0);
  INSTR_struct(&false_c3_70638, 3, 0);
  INSTR_struct(&true_c2_70639, 2, 0);
  INSTR_struct(&true_c2_70640, 2, 0);
  INSTR_struct(&true_c2_70641, 2, 0);
  INSTR_struct(&true_c2_70642, 2, 0);
  INSTR_struct(&false_c3_70643, 3, 0);
  INSTR_struct(&true_c2_70644, 2, 0);
  INSTR_struct(&Ascii_c16_70645, 16, 8,
    false_c3_70637, false_c3_70638, true_c2_70639, true_c2_70640,
    true_c2_70641, true_c2_70642, false_c3_70643, true_c2_70644);
  INSTR_struct(&EmptyString_c17_70646, 17, 0);
  INSTR_struct(&String_c18_70647, 18, 2,
    Ascii_c16_70645, EmptyString_c17_70646);
  INSTR_struct(&String_c18_70648, 18, 2,
    Ascii_c16_70636, String_c18_70647);
  INSTR_call(&tmp_70649, tmp_70627, String_c18_70648);
  INSTR_struct(&false_c3_70650, 3, 0);
  INSTR_struct(&true_c2_70651, 2, 0);
  INSTR_struct(&true_c2_70652, 2, 0);
  INSTR_struct(&false_c3_70653, 3, 0);
  INSTR_struct(&false_c3_70654, 3, 0);
  INSTR_struct(&false_c3_70655, 3, 0);
  INSTR_struct(&true_c2_70656, 2, 0);
  INSTR_struct(&false_c3_70657, 3, 0);
  INSTR_struct(&Ascii_c16_70658, 16, 8,
    false_c3_70650, true_c2_70651, true_c2_70652, false_c3_70653,
    false_c3_70654, false_c3_70655, true_c2_70656, false_c3_70657);
  INSTR_struct(&EmptyString_c17_70659, 17, 0);
  INSTR_struct(&String_c18_70660, 18, 2,
    Ascii_c16_70658, EmptyString_c17_70659);
  INSTR_call(&tmp_70661, tmp_70649, String_c18_70660);
  INSTR_mov(&cond_289, tmp_70661);
  INSTR_struct(&false_c3_70662, 3, 0);
  INSTR_struct(&true_c2_70663, 2, 0);
  INSTR_struct(&true_c2_70664, 2, 0);
  INSTR_struct(&false_c3_70665, 3, 0);
  INSTR_struct(&false_c3_70666, 3, 0);
  INSTR_struct(&false_c3_70667, 3, 0);
  INSTR_struct(&false_c3_70668, 3, 0);
  INSTR_struct(&true_c2_70669, 2, 0);
  INSTR_struct(&Ascii_c16_70670, 16, 8,
    false_c3_70662, true_c2_70663, true_c2_70664, false_c3_70665,
    false_c3_70666, false_c3_70667, false_c3_70668, true_c2_70669);
  INSTR_struct(&EmptyString_c17_70671, 17, 0);
  INSTR_struct(&String_c18_70672, 18, 2,
    Ascii_c16_70670, EmptyString_c17_70671);
  INSTR_call(&tmp_70673, binop_282, String_c18_70672);
  INSTR_struct(&false_c3_70674, 3, 0);
  INSTR_struct(&false_c3_70675, 3, 0);
  INSTR_struct(&true_c2_70676, 2, 0);
  INSTR_struct(&true_c2_70677, 2, 0);
  INSTR_struct(&true_c2_70678, 2, 0);
  INSTR_struct(&true_c2_70679, 2, 0);
  INSTR_struct(&false_c3_70680, 3, 0);
  INSTR_struct(&false_c3_70681, 3, 0);
  INSTR_struct(&Ascii_c16_70682, 16, 8,
    false_c3_70674, false_c3_70675, true_c2_70676, true_c2_70677,
    true_c2_70678, true_c2_70679, false_c3_70680, false_c3_70681);
  INSTR_struct(&false_c3_70683, 3, 0);
  INSTR_struct(&false_c3_70684, 3, 0);
  INSTR_struct(&true_c2_70685, 2, 0);
  INSTR_struct(&true_c2_70686, 2, 0);
  INSTR_struct(&true_c2_70687, 2, 0);
  INSTR_struct(&true_c2_70688, 2, 0);
  INSTR_struct(&false_c3_70689, 3, 0);
  INSTR_struct(&false_c3_70690, 3, 0);
  INSTR_struct(&Ascii_c16_70691, 16, 8,
    false_c3_70683, false_c3_70684, true_c2_70685, true_c2_70686,
    true_c2_70687, true_c2_70688, false_c3_70689, false_c3_70690);
  INSTR_struct(&EmptyString_c17_70692, 17, 0);
  INSTR_struct(&String_c18_70693, 18, 2,
    Ascii_c16_70691, EmptyString_c17_70692);
  INSTR_struct(&String_c18_70694, 18, 2,
    Ascii_c16_70682, String_c18_70693);
  INSTR_call(&tmp_70695, tmp_70673, String_c18_70694);
  INSTR_struct(&false_c3_70696, 3, 0);
  INSTR_struct(&true_c2_70697, 2, 0);
  INSTR_struct(&true_c2_70698, 2, 0);
  INSTR_struct(&false_c3_70699, 3, 0);
  INSTR_struct(&false_c3_70700, 3, 0);
  INSTR_struct(&false_c3_70701, 3, 0);
  INSTR_struct(&true_c2_70702, 2, 0);
  INSTR_struct(&false_c3_70703, 3, 0);
  INSTR_struct(&Ascii_c16_70704, 16, 8,
    false_c3_70696, true_c2_70697, true_c2_70698, false_c3_70699,
    false_c3_70700, false_c3_70701, true_c2_70702, false_c3_70703);
  INSTR_struct(&EmptyString_c17_70705, 17, 0);
  INSTR_struct(&String_c18_70706, 18, 2,
    Ascii_c16_70704, EmptyString_c17_70705);
  INSTR_call(&tmp_70707, tmp_70695, String_c18_70706);
  INSTR_mov(&expr1_290, tmp_70707);
  INSTR_struct(&false_c3_70708, 3, 0);
  INSTR_struct(&true_c2_70709, 2, 0);
  INSTR_struct(&true_c2_70710, 2, 0);
  INSTR_struct(&false_c3_70711, 3, 0);
  INSTR_struct(&false_c3_70712, 3, 0);
  INSTR_struct(&false_c3_70713, 3, 0);
  INSTR_struct(&false_c3_70714, 3, 0);
  INSTR_struct(&true_c2_70715, 2, 0);
  INSTR_struct(&Ascii_c16_70716, 16, 8,
    false_c3_70708, true_c2_70709, true_c2_70710, false_c3_70711,
    false_c3_70712, false_c3_70713, false_c3_70714, true_c2_70715);
  INSTR_struct(&EmptyString_c17_70717, 17, 0);
  INSTR_struct(&String_c18_70718, 18, 2,
    Ascii_c16_70716, EmptyString_c17_70717);
  INSTR_call(&tmp_70719, binop_282, String_c18_70718);
  INSTR_struct(&false_c3_70720, 3, 0);
  INSTR_struct(&false_c3_70721, 3, 0);
  INSTR_struct(&true_c2_70722, 2, 0);
  INSTR_struct(&false_c3_70723, 3, 0);
  INSTR_struct(&true_c2_70724, 2, 0);
  INSTR_struct(&false_c3_70725, 3, 0);
  INSTR_struct(&true_c2_70726, 2, 0);
  INSTR_struct(&true_c2_70727, 2, 0);
  INSTR_struct(&Ascii_c16_70728, 16, 8,
    false_c3_70720, false_c3_70721, true_c2_70722, false_c3_70723,
    true_c2_70724, false_c3_70725, true_c2_70726, true_c2_70727);
  INSTR_struct(&EmptyString_c17_70729, 17, 0);
  INSTR_struct(&String_c18_70730, 18, 2,
    Ascii_c16_70728, EmptyString_c17_70729);
  INSTR_call(&tmp_70731, tmp_70719, String_c18_70730);
  INSTR_struct(&false_c3_70732, 3, 0);
  INSTR_struct(&true_c2_70733, 2, 0);
  INSTR_struct(&true_c2_70734, 2, 0);
  INSTR_struct(&false_c3_70735, 3, 0);
  INSTR_struct(&false_c3_70736, 3, 0);
  INSTR_struct(&false_c3_70737, 3, 0);
  INSTR_struct(&true_c2_70738, 2, 0);
  INSTR_struct(&false_c3_70739, 3, 0);
  INSTR_struct(&Ascii_c16_70740, 16, 8,
    false_c3_70732, true_c2_70733, true_c2_70734, false_c3_70735,
    false_c3_70736, false_c3_70737, true_c2_70738, false_c3_70739);
  INSTR_struct(&EmptyString_c17_70741, 17, 0);
  INSTR_struct(&String_c18_70742, 18, 2,
    Ascii_c16_70740, EmptyString_c17_70741);
  INSTR_call(&tmp_70743, tmp_70731, String_c18_70742);
  INSTR_mov(&expr2_291, tmp_70743);
  INSTR_clo(&ifthen_70890, &ifthen_70889, 35,
    0, expr2_291, expr1_290, cond_289, binop_282, join_275, pretty_269,
    format_218, fits_175, sdocToString_165, group_158, breakWith_155,
    break_154, nest_149, text_146, empty_145, dcons_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&ifthen_292, ifthen_70890);
  INSTR_call(&tmp_70891, ifthen_292, cond_289);
  INSTR_call(&tmp_70892, tmp_70891, expr1_290);
  INSTR_call(&tmp_70893, tmp_70892, expr2_291);
  INSTR_mov(&doc_299, tmp_70893);
  INSTR_trg(&stdout_300, &PROC_stdout);
  INSTR_call(&tmp_70895, printline_117, stdout_300);
  INSTR_struct(&zero_c4_70896, 4, 0);
  INSTR_struct(&succ_c5_70897, 5, 1,
    zero_c4_70896);
  INSTR_struct(&succ_c5_70898, 5, 1,
    succ_c5_70897);
  INSTR_struct(&succ_c5_70899, 5, 1,
    succ_c5_70898);
  INSTR_struct(&succ_c5_70900, 5, 1,
    succ_c5_70899);
  INSTR_struct(&succ_c5_70901, 5, 1,
    succ_c5_70900);
  INSTR_struct(&succ_c5_70902, 5, 1,
    succ_c5_70901);
  INSTR_struct(&succ_c5_70903, 5, 1,
    succ_c5_70902);
  INSTR_struct(&succ_c5_70904, 5, 1,
    succ_c5_70903);
  INSTR_struct(&succ_c5_70905, 5, 1,
    succ_c5_70904);
  INSTR_struct(&succ_c5_70906, 5, 1,
    succ_c5_70905);
  INSTR_call(&tmp_70907, pretty_269, succ_c5_70906);
  INSTR_call(&tmp_70908, tmp_70907, doc_299);
  INSTR_call(&tmp_70909, tmp_70895, tmp_70908);
  INSTR_mov(&stdout_70894, tmp_70909);
  INSTR_clo(&clo_70914, &lam_70913, 39,
    0, stdout_70894, stdout_300, doc_299, ifthen_292, expr2_291, expr1_290,
    cond_289, binop_282, join_275, pretty_269, format_218, fits_175,
    sdocToString_165, group_158, breakWith_155, break_154, nest_149,
    text_146, empty_145, dcons_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_call(&tmp_70915, close_out_122, stdout_70894);
  INSTR_call(&tmp_70916, clo_70914, tmp_70915);
  INSTR_mov(&_301, tmp_70916);
  return 0;
}
