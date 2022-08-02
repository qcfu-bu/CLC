#include "runtime.h"

clc_ptr lam_20107(clc_ptr _20106, clc_env env)
{
  
  
  return _20106;
}

clc_ptr lam_20115(clc_ptr _20111, clc_env env)
{
  clc_ptr succ_c5_20114; clc_ptr tmp_20112; clc_ptr tmp_20113;
  instr_call(&tmp_20112, env[3], env[2]);
  instr_call(&tmp_20113, tmp_20112, _20111);
  instr_struct(&succ_c5_20114, 5, 1,
    tmp_20113);
  return succ_c5_20114;
}

clc_ptr addn_20117(clc_ptr _20103, clc_env env)
{
  clc_ptr _20109; clc_ptr case_20104; clc_ptr clo_20108; clc_ptr clo_20116;
  switch(((clc_node)_20103)->tag){
    case 4:
      instr_clo(&clo_20108, &lam_20107, 2, env, 1, _20103);
      instr_mov(&case_20104, clo_20108);
      break;
    case 5:
      instr_mov(&_20109, ((clc_node)_20103)->data[0]);
      instr_clo(&clo_20116, &lam_20115, 2, env, 2, _20103, _20109);
      instr_mov(&case_20104, clo_20116);
      break;}
  return case_20104;
}

clc_ptr lam_20125(clc_ptr _20123, clc_env env)
{
  clc_ptr zero_c4_20124;
  instr_struct(&zero_c4_20124, 4, 0);
  return zero_c4_20124;
}

clc_ptr lam_20135(clc_ptr _20129, clc_env env)
{
  clc_ptr _20132; clc_ptr case_20130; clc_ptr succ_c5_20131;
  clc_ptr tmp_20133; clc_ptr tmp_20134;
  switch(((clc_node)_20129)->tag){
    case 4:
      instr_struct(&succ_c5_20131, 5, 1,
        env[2]);
      instr_mov(&case_20130, succ_c5_20131);
      break;
    case 5:
      instr_mov(&_20132, ((clc_node)_20129)->data[0]);
      instr_call(&tmp_20133, env[3], env[2]);
      instr_call(&tmp_20134, tmp_20133, _20132);
      instr_mov(&case_20130, tmp_20134);
      break;}
  return case_20130;
}

clc_ptr subn_20137(clc_ptr _20120, clc_env env)
{
  clc_ptr _20127; clc_ptr case_20121; clc_ptr clo_20126; clc_ptr clo_20136;
  switch(((clc_node)_20120)->tag){
    case 4:
      instr_clo(&clo_20126, &lam_20125, 3, env, 1, _20120);
      instr_mov(&case_20121, clo_20126);
      break;
    case 5:
      instr_mov(&_20127, ((clc_node)_20120)->data[0]);
      instr_clo(&clo_20136, &lam_20135, 3, env, 2, _20120, _20127);
      instr_mov(&case_20121, clo_20136);
      break;}
  return case_20121;
}

clc_ptr lam_20144(clc_ptr _20143, clc_env env)
{
  
  
  return _20143;
}

clc_ptr lam_20153(clc_ptr _20149, clc_env env)
{
  clc_ptr String_c18_20152; clc_ptr tmp_20150; clc_ptr tmp_20151;
  instr_call(&tmp_20150, env[4], env[3]);
  instr_call(&tmp_20151, tmp_20150, _20149);
  instr_struct(&String_c18_20152, 18, 2,
    env[2], tmp_20151);
  return String_c18_20152;
}

clc_ptr cat_20155(clc_ptr _20140, clc_env env)
{
  clc_ptr _20146; clc_ptr _20147; clc_ptr case_20141; clc_ptr clo_20145;
  clc_ptr clo_20154;
  switch(((clc_node)_20140)->tag){
    case 17:
      instr_clo(&clo_20145, &lam_20144, 4, env, 1, _20140);
      instr_mov(&case_20141, clo_20145);
      break;
    case 18:
      instr_mov(&_20146, ((clc_node)_20140)->data[0]);
      instr_mov(&_20147, ((clc_node)_20140)->data[1]);
      instr_clo(&clo_20154, &lam_20153, 4, env, 3, _20140, _20146, _20147);
      instr_mov(&case_20141, clo_20154);
      break;}
  return case_20141;
}

clc_ptr strlen_20165(clc_ptr _20158, clc_env env)
{
  clc_ptr _20161; clc_ptr _20162; clc_ptr case_20159; clc_ptr succ_c5_20164;
  clc_ptr tmp_20163; clc_ptr zero_c4_20160;
  switch(((clc_node)_20158)->tag){
    case 17:
      instr_struct(&zero_c4_20160, 4, 0);
      instr_mov(&case_20159, zero_c4_20160);
      break;
    case 18:
      instr_mov(&_20161, ((clc_node)_20158)->data[0]);
      instr_mov(&_20162, ((clc_node)_20158)->data[1]);
      instr_call(&tmp_20163, env[0], _20162);
      instr_struct(&succ_c5_20164, 5, 1,
        tmp_20163);
      instr_mov(&case_20159, succ_c5_20164);
      break;}
  return case_20159;
}

clc_ptr lam_20171(clc_ptr _20170, clc_env env)
{
  
  
  return 0;
}

clc_ptr lt_20173(clc_ptr _20168, clc_env env)
{
  clc_ptr clo_20172;
  instr_clo(&clo_20172, &lam_20171, 6, env, 1, _20168);
  return clo_20172;
}

clc_ptr stdin_rec_20178(clc_ptr _20176, clc_env env)
{
  clc_ptr case_20177;
  switch(((clc_node)_20176)->tag){
    case 1: instr_mov(&case_20177, 0);
            break;}
  return case_20177;
}

clc_ptr stdout_rec_20183(clc_ptr _20181, clc_env env)
{
  clc_ptr case_20182;
  switch(((clc_node)_20181)->tag){
    case 1: instr_mov(&case_20182, 0);
            break;}
  return case_20182;
}

clc_ptr stderr_rec_20188(clc_ptr _20186, clc_env env)
{
  clc_ptr case_20187;
  switch(((clc_node)_20186)->tag){
    case 1: instr_mov(&case_20187, 0);
            break;}
  return case_20187;
}

clc_ptr readline_20202(clc_ptr _20197, clc_env env)
{
  clc_ptr recv_struct_20201; clc_ptr send_clo_20198; clc_ptr tmp_20200;
  clc_ptr true_c2_20199;
  instr_send(&send_clo_20198, _20197);
  instr_struct(&true_c2_20199, 2, 0);
  instr_call(&tmp_20200, send_clo_20198, true_c2_20199);
  instr_free_clo(send_clo_20198);
  instr_recv(&recv_struct_20201, tmp_20200, 13);
  return recv_struct_20201;
}

clc_ptr close_in_20210(clc_ptr _20205, clc_env env)
{
  clc_ptr false_c3_20208; clc_ptr send_clo_20207; clc_ptr tmp_20209;
  clc_ptr unit_struct_20206;
  instr_send(&send_clo_20207, _20205);
  instr_struct(&false_c3_20208, 3, 0);
  instr_call(&tmp_20209, send_clo_20207, false_c3_20208);
  instr_free_clo(send_clo_20207);
  instr_struct(&unit_struct_20206, 1, 0);
  return unit_struct_20206;
}

clc_ptr lam_20221(clc_ptr _20215, clc_env env)
{
  clc_ptr send_clo_20216; clc_ptr send_clo_20219; clc_ptr tmp_20218;
  clc_ptr tmp_20220; clc_ptr true_c2_20217;
  instr_send(&send_clo_20216, env[1]);
  instr_struct(&true_c2_20217, 2, 0);
  instr_call(&tmp_20218, send_clo_20216, true_c2_20217);
  instr_free_clo(send_clo_20216);
  instr_send(&send_clo_20219, tmp_20218);
  instr_call(&tmp_20220, send_clo_20219, _20215);
  instr_free_clo(send_clo_20219);
  return tmp_20220;
}

clc_ptr printline_20223(clc_ptr _20213, clc_env env)
{
  clc_ptr clo_20222;
  instr_clo(&clo_20222, &lam_20221, 15, env, 1, _20213);
  return clo_20222;
}

clc_ptr close_out_20231(clc_ptr _20226, clc_env env)
{
  clc_ptr false_c3_20229; clc_ptr send_clo_20228; clc_ptr tmp_20230;
  clc_ptr unit_struct_20227;
  instr_send(&send_clo_20228, _20226);
  instr_struct(&false_c3_20229, 3, 0);
  instr_call(&tmp_20230, send_clo_20228, false_c3_20229);
  instr_free_clo(send_clo_20228);
  instr_struct(&unit_struct_20227, 1, 0);
  return unit_struct_20227;
}

clc_ptr lam_20242(clc_ptr _20236, clc_env env)
{
  clc_ptr send_clo_20237; clc_ptr send_clo_20240; clc_ptr tmp_20239;
  clc_ptr tmp_20241; clc_ptr true_c2_20238;
  instr_send(&send_clo_20237, env[1]);
  instr_struct(&true_c2_20238, 2, 0);
  instr_call(&tmp_20239, send_clo_20237, true_c2_20238);
  instr_free_clo(send_clo_20237);
  instr_send(&send_clo_20240, tmp_20239);
  instr_call(&tmp_20241, send_clo_20240, _20236);
  instr_free_clo(send_clo_20240);
  return tmp_20241;
}

clc_ptr printerr_20244(clc_ptr _20234, clc_env env)
{
  clc_ptr clo_20243;
  instr_clo(&clo_20243, &lam_20242, 17, env, 1, _20234);
  return clo_20243;
}

clc_ptr close_err_20252(clc_ptr _20247, clc_env env)
{
  clc_ptr false_c3_20250; clc_ptr send_clo_20249; clc_ptr tmp_20251;
  clc_ptr unit_struct_20248;
  instr_send(&send_clo_20249, _20247);
  instr_struct(&false_c3_20250, 3, 0);
  instr_call(&tmp_20251, send_clo_20249, false_c3_20250);
  instr_free_clo(send_clo_20249);
  instr_struct(&unit_struct_20248, 1, 0);
  return unit_struct_20248;
}

clc_ptr lam_20265(clc_ptr _20259, clc_env env)
{
  clc_ptr _20262; clc_ptr _20263; clc_ptr case_20260; clc_ptr n_20261;
  clc_ptr sig_intro_c13_20264;
  switch(((clc_node)_20259)->tag){
    case 22: instr_free_struct(_20259);
             instr_mov(&case_20260, 0);
             break;
    case 23:
      instr_mov(&n_20261, ((clc_node)_20259)->data[0]);
      instr_mov(&_20262, ((clc_node)_20259)->data[1]);
      instr_mov(&_20263, ((clc_node)_20259)->data[2]);
      instr_free_struct(_20259);
      instr_struct(&sig_intro_c13_20264, 13, 2,
        _20262, _20263);
      instr_mov(&case_20260, sig_intro_c13_20264);
      break;}
  return case_20260;
}

clc_ptr lam_20267(clc_ptr n_20257, clc_env env)
{
  clc_ptr clo_20266;
  instr_clo(&clo_20266, &lam_20265, 21, env, 1, n_20257);
  return clo_20266;
}

clc_ptr head_20269(clc_ptr A_20255, clc_env env)
{
  clc_ptr clo_20268;
  instr_clo(&clo_20268, &lam_20267, 19, env, 1, A_20255);
  return clo_20268;
}

clc_ptr lam_20288(clc_ptr _20286, clc_env env)
{
  clc_ptr tmp_20287;
  instr_call(&tmp_20287, _20286, env[1]);
  instr_free_clo(_20286);
  return tmp_20287;
}

clc_ptr lam_20290(clc_ptr _20284, clc_env env)
{
  clc_ptr clo_20289;
  instr_clo(&clo_20289, &lam_20288, 30, env, 1, _20284);
  return clo_20289;
}

clc_ptr lam_20295(clc_ptr _20281, clc_env env)
{
  clc_ptr _20293; clc_ptr _20294; clc_ptr case_20282; clc_ptr clo_20291;
  clc_ptr n_20292;
  switch(((clc_node)_20281)->tag){
    case 22:
      instr_free_struct(_20281);
      instr_clo(&clo_20291, &lam_20290, 28, env, 1, _20281);
      instr_mov(&case_20282, clo_20291);
      break;
    case 23:
      instr_mov(&n_20292, ((clc_node)_20281)->data[0]);
      instr_mov(&_20293, ((clc_node)_20281)->data[1]);
      instr_mov(&_20294, ((clc_node)_20281)->data[2]);
      instr_free_struct(_20281);
      instr_mov(&case_20282, 0);
      break;}
  return case_20282;
}

clc_ptr lam_20297(clc_ptr n_20279, clc_env env)
{
  clc_ptr clo_20296;
  instr_clo(&clo_20296, &lam_20295, 26, env, 1, n_20279);
  return clo_20296;
}

clc_ptr lam_20324(clc_ptr _20319, clc_env env)
{
  clc_ptr lcons_c23_20322; clc_ptr tmp_20320; clc_ptr tmp_20321;
  clc_ptr tmp_20323;
  instr_call(&tmp_20320, env[36], env[13]);
  instr_call(&tmp_20321, tmp_20320, env[10]);
  instr_struct(&lcons_c23_20322, 23, 3,
    tmp_20321, env[7], _20319);
  instr_call(&tmp_20323, env[1], lcons_c23_20322);
  instr_free_clo(env[1]);
  return tmp_20323;
}

clc_ptr lam_20327(clc_ptr _20311, clc_env env)
{
  clc_ptr clo_20325; clc_ptr tmp_20312; clc_ptr tmp_20313; clc_ptr tmp_20314;
  clc_ptr tmp_20315; clc_ptr tmp_20316; clc_ptr tmp_20317; clc_ptr tmp_20326;
  instr_call(&tmp_20312, env[16], env[15]);
  instr_call(&tmp_20313, tmp_20312, env[13]);
  instr_call(&tmp_20314, tmp_20313, env[11]);
  instr_call(&tmp_20315, tmp_20314, env[8]);
  instr_call(&tmp_20316, tmp_20315, env[6]);
  instr_call(&tmp_20317, tmp_20316, env[1]);
  instr_free_clo(tmp_20316);
  instr_clo(&clo_20325, &lam_20324, 36, env, 1, _20311);
  instr_call(&tmp_20326, tmp_20317, clo_20325);
  instr_free_clo(tmp_20317);
  return tmp_20326;
}

clc_ptr lam_20329(clc_ptr _20309, clc_env env)
{
  clc_ptr clo_20328;
  instr_clo(&clo_20328, &lam_20327, 34, env, 1, _20309);
  return clo_20328;
}

clc_ptr lam_20331(clc_ptr _20303, clc_env env)
{
  clc_ptr _20306; clc_ptr _20307; clc_ptr case_20304; clc_ptr clo_20330;
  clc_ptr n_20305;
  switch(((clc_node)_20303)->tag){
    case 22: instr_free_struct(_20303);
             instr_mov(&case_20304, 0);
             break;
    case 23:
      instr_mov(&n_20305, ((clc_node)_20303)->data[0]);
      instr_mov(&_20306, ((clc_node)_20303)->data[1]);
      instr_mov(&_20307, ((clc_node)_20303)->data[2]);
      instr_free_struct(_20303);
      instr_clo(&clo_20330, &lam_20329, 29, env, 4,
        _20303, n_20305, _20306, _20307);
      instr_mov(&case_20304, clo_20330);
      break;}
  return case_20304;
}

clc_ptr lam_20333(clc_ptr n_20301, clc_env env)
{
  clc_ptr clo_20332;
  instr_clo(&clo_20332, &lam_20331, 27, env, 1, n_20301);
  return clo_20332;
}

clc_ptr lam_20335(clc_ptr m_20276, clc_env env)
{
  clc_ptr _20299; clc_ptr case_20277; clc_ptr clo_20298; clc_ptr clo_20334;
  switch(((clc_node)m_20276)->tag){
    case 4:
      instr_clo(&clo_20298, &lam_20297, 24, env, 1, m_20276);
      instr_mov(&case_20277, clo_20298);
      break;
    case 5:
      instr_mov(&_20299, ((clc_node)m_20276)->data[0]);
      instr_clo(&clo_20334, &lam_20333, 24, env, 2, m_20276, _20299);
      instr_mov(&case_20277, clo_20334);
      break;}
  return case_20277;
}

clc_ptr lam_20337(clc_ptr B_20274, clc_env env)
{
  clc_ptr clo_20336;
  instr_clo(&clo_20336, &lam_20335, 22, env, 1, B_20274);
  return clo_20336;
}

clc_ptr kappend_20339(clc_ptr A_20272, clc_env env)
{
  clc_ptr clo_20338;
  instr_clo(&clo_20338, &lam_20337, 20, env, 1, A_20272);
  return clo_20338;
}

clc_ptr lam_20359(clc_ptr _20358, clc_env env)
{
  
  
  return _20358;
}

clc_ptr lam_20362(clc_ptr _20350, clc_env env)
{
  clc_ptr clo_20360; clc_ptr tmp_20351; clc_ptr tmp_20352; clc_ptr tmp_20353;
  clc_ptr tmp_20354; clc_ptr tmp_20355; clc_ptr tmp_20356; clc_ptr tmp_20361;
  instr_call(&tmp_20351, env[9], env[7]);
  instr_call(&tmp_20352, tmp_20351, 0);
  instr_call(&tmp_20353, tmp_20352, env[5]);
  instr_call(&tmp_20354, tmp_20353, env[3]);
  instr_call(&tmp_20355, tmp_20354, env[1]);
  instr_call(&tmp_20356, tmp_20355, _20350);
  instr_free_clo(tmp_20355);
  instr_clo(&clo_20360, &lam_20359, 29, env, 1, _20350);
  instr_call(&tmp_20361, tmp_20356, clo_20360);
  instr_free_clo(tmp_20356);
  return tmp_20361;
}

clc_ptr lam_20364(clc_ptr _20348, clc_env env)
{
  clc_ptr clo_20363;
  instr_clo(&clo_20363, &lam_20362, 27, env, 1, _20348);
  return clo_20363;
}

clc_ptr lam_20366(clc_ptr n_20346, clc_env env)
{
  clc_ptr clo_20365;
  instr_clo(&clo_20365, &lam_20364, 25, env, 1, n_20346);
  return clo_20365;
}

clc_ptr lam_20368(clc_ptr m_20344, clc_env env)
{
  clc_ptr clo_20367;
  instr_clo(&clo_20367, &lam_20366, 23, env, 1, m_20344);
  return clo_20367;
}

clc_ptr append_20370(clc_ptr A_20342, clc_env env)
{
  clc_ptr clo_20369;
  instr_clo(&clo_20369, &lam_20368, 21, env, 1, A_20342);
  return clo_20369;
}

clc_ptr lam_20380(clc_ptr _20378, clc_env env)
{
  clc_ptr lnil_c22_20379;
  instr_struct(&lnil_c22_20379, 22, 0);
  return lnil_c22_20379;
}

clc_ptr lam_20389(clc_ptr _20384, clc_env env)
{
  clc_ptr lcons_c23_20388; clc_ptr tmp_20385; clc_ptr tmp_20386;
  clc_ptr tmp_20387;
  instr_call(&tmp_20385, env[5], env[4]);
  instr_call(&tmp_20386, tmp_20385, env[2]);
  instr_call(&tmp_20387, tmp_20386, _20384);
  instr_struct(&lcons_c23_20388, 23, 3,
    env[2], _20384, tmp_20387);
  return lcons_c23_20388;
}

clc_ptr lam_20391(clc_ptr n_20375, clc_env env)
{
  clc_ptr _20382; clc_ptr case_20376; clc_ptr clo_20381; clc_ptr clo_20390;
  switch(((clc_node)n_20375)->tag){
    case 4:
      instr_clo(&clo_20381, &lam_20380, 24, env, 1, n_20375);
      instr_mov(&case_20376, clo_20381);
      break;
    case 5:
      instr_mov(&_20382, ((clc_node)n_20375)->data[0]);
      instr_clo(&clo_20390, &lam_20389, 24, env, 2, n_20375, _20382);
      instr_mov(&case_20376, clo_20390);
      break;}
  return case_20376;
}

clc_ptr rep_20393(clc_ptr A_20373, clc_env env)
{
  clc_ptr clo_20392;
  instr_clo(&clo_20392, &lam_20391, 22, env, 1, A_20373);
  return clo_20392;
}

clc_ptr lam_20413(clc_ptr _20408, clc_env env)
{
  clc_ptr _20410; clc_ptr box_intro_c15_20412; clc_ptr case_20409;
  clc_ptr succ_c5_20411;
  switch(((clc_node)_20408)->tag){
    case 15:
      instr_mov(&_20410, ((clc_node)_20408)->data[0]);
      instr_free_struct(_20408);
      instr_struct(&succ_c5_20411, 5, 1,
        _20410);
      instr_struct(&box_intro_c15_20412, 15, 1,
        succ_c5_20411);
      instr_mov(&case_20409, box_intro_c15_20412);
      break;}
  return case_20409;
}

clc_ptr lam_20419(clc_ptr _20400, clc_env env)
{
  clc_ptr _20405; clc_ptr _20406; clc_ptr box_intro_c15_20403;
  clc_ptr case_20401; clc_ptr clo_20414; clc_ptr n_20404; clc_ptr tmp_20415;
  clc_ptr tmp_20416; clc_ptr tmp_20417; clc_ptr tmp_20418;
  clc_ptr zero_c4_20402;
  switch(((clc_node)_20400)->tag){
    case 22:
      instr_free_struct(_20400);
      instr_struct(&zero_c4_20402, 4, 0);
      instr_struct(&box_intro_c15_20403, 15, 1,
        zero_c4_20402);
      instr_mov(&case_20401, box_intro_c15_20403);
      break;
    case 23:
      instr_mov(&n_20404, ((clc_node)_20400)->data[0]);
      instr_mov(&_20405, ((clc_node)_20400)->data[1]);
      instr_mov(&_20406, ((clc_node)_20400)->data[2]);
      instr_free_struct(_20400);
      instr_clo(&clo_20414, &lam_20413, 27, env, 4,
        _20400, n_20404, _20405, _20406);
      instr_call(&tmp_20415, env[4], env[3]);
      instr_call(&tmp_20416, tmp_20415, n_20404);
      instr_call(&tmp_20417, tmp_20416, _20406);
      instr_call(&tmp_20418, clo_20414, tmp_20417);
      instr_free_clo(clo_20414);
      instr_mov(&case_20401, tmp_20418);
      break;}
  return case_20401;
}

clc_ptr lam_20421(clc_ptr n_20398, clc_env env)
{
  clc_ptr clo_20420;
  instr_clo(&clo_20420, &lam_20419, 25, env, 1, n_20398);
  return clo_20420;
}

clc_ptr length_20423(clc_ptr A_20396, clc_env env)
{
  clc_ptr clo_20422;
  instr_clo(&clo_20422, &lam_20421, 23, env, 1, A_20396);
  return clo_20422;
}

clc_ptr string_of_nat_20547(clc_ptr _20426, clc_env env)
{
  clc_ptr _20469; clc_ptr Ascii_c16_20436; clc_ptr Ascii_c16_20445;
  clc_ptr Ascii_c16_20454; clc_ptr Ascii_c16_20463; clc_ptr Ascii_c16_20478;
  clc_ptr Ascii_c16_20487; clc_ptr Ascii_c16_20496; clc_ptr Ascii_c16_20505;
  clc_ptr Ascii_c16_20514; clc_ptr Ascii_c16_20523; clc_ptr Ascii_c16_20543;
  clc_ptr EmptyString_c17_20464; clc_ptr EmptyString_c17_20524;
  clc_ptr EmptyString_c17_20544; clc_ptr String_c18_20465;
  clc_ptr String_c18_20466; clc_ptr String_c18_20467;
  clc_ptr String_c18_20468; clc_ptr String_c18_20525;
  clc_ptr String_c18_20526; clc_ptr String_c18_20527;
  clc_ptr String_c18_20528; clc_ptr String_c18_20529;
  clc_ptr String_c18_20530; clc_ptr String_c18_20545; clc_ptr case_20427;
  clc_ptr false_c3_20428; clc_ptr false_c3_20433; clc_ptr false_c3_20435;
  clc_ptr false_c3_20437; clc_ptr false_c3_20440; clc_ptr false_c3_20441;
  clc_ptr false_c3_20443; clc_ptr false_c3_20446; clc_ptr false_c3_20450;
  clc_ptr false_c3_20451; clc_ptr false_c3_20453; clc_ptr false_c3_20455;
  clc_ptr false_c3_20458; clc_ptr false_c3_20470; clc_ptr false_c3_20474;
  clc_ptr false_c3_20475; clc_ptr false_c3_20479; clc_ptr false_c3_20483;
  clc_ptr false_c3_20485; clc_ptr false_c3_20488; clc_ptr false_c3_20491;
  clc_ptr false_c3_20492; clc_ptr false_c3_20493; clc_ptr false_c3_20497;
  clc_ptr false_c3_20500; clc_ptr false_c3_20501; clc_ptr false_c3_20502;
  clc_ptr false_c3_20506; clc_ptr false_c3_20507; clc_ptr false_c3_20509;
  clc_ptr false_c3_20510; clc_ptr false_c3_20511; clc_ptr false_c3_20512;
  clc_ptr false_c3_20513; clc_ptr false_c3_20515; clc_ptr false_c3_20516;
  clc_ptr false_c3_20518; clc_ptr false_c3_20520; clc_ptr false_c3_20521;
  clc_ptr false_c3_20522; clc_ptr false_c3_20535; clc_ptr false_c3_20536;
  clc_ptr false_c3_20538; clc_ptr false_c3_20540; clc_ptr false_c3_20541;
  clc_ptr tmp_20531; clc_ptr tmp_20532; clc_ptr tmp_20533; clc_ptr tmp_20534;
  clc_ptr tmp_20546; clc_ptr true_c2_20429; clc_ptr true_c2_20430;
  clc_ptr true_c2_20431; clc_ptr true_c2_20432; clc_ptr true_c2_20434;
  clc_ptr true_c2_20438; clc_ptr true_c2_20439; clc_ptr true_c2_20442;
  clc_ptr true_c2_20444; clc_ptr true_c2_20447; clc_ptr true_c2_20448;
  clc_ptr true_c2_20449; clc_ptr true_c2_20452; clc_ptr true_c2_20456;
  clc_ptr true_c2_20457; clc_ptr true_c2_20459; clc_ptr true_c2_20460;
  clc_ptr true_c2_20461; clc_ptr true_c2_20462; clc_ptr true_c2_20471;
  clc_ptr true_c2_20472; clc_ptr true_c2_20473; clc_ptr true_c2_20476;
  clc_ptr true_c2_20477; clc_ptr true_c2_20480; clc_ptr true_c2_20481;
  clc_ptr true_c2_20482; clc_ptr true_c2_20484; clc_ptr true_c2_20486;
  clc_ptr true_c2_20489; clc_ptr true_c2_20490; clc_ptr true_c2_20494;
  clc_ptr true_c2_20495; clc_ptr true_c2_20498; clc_ptr true_c2_20499;
  clc_ptr true_c2_20503; clc_ptr true_c2_20504; clc_ptr true_c2_20508;
  clc_ptr true_c2_20517; clc_ptr true_c2_20519; clc_ptr true_c2_20537;
  clc_ptr true_c2_20539; clc_ptr true_c2_20542;
  switch(((clc_node)_20426)->tag){
    case 4:
      instr_struct(&false_c3_20428, 3, 0);
      instr_struct(&true_c2_20429, 2, 0);
      instr_struct(&true_c2_20430, 2, 0);
      instr_struct(&true_c2_20431, 2, 0);
      instr_struct(&true_c2_20432, 2, 0);
      instr_struct(&false_c3_20433, 3, 0);
      instr_struct(&true_c2_20434, 2, 0);
      instr_struct(&false_c3_20435, 3, 0);
      instr_struct(&Ascii_c16_20436, 16, 8,
        false_c3_20428, true_c2_20429, true_c2_20430, true_c2_20431,
        true_c2_20432, false_c3_20433, true_c2_20434, false_c3_20435);
      instr_struct(&false_c3_20437, 3, 0);
      instr_struct(&true_c2_20438, 2, 0);
      instr_struct(&true_c2_20439, 2, 0);
      instr_struct(&false_c3_20440, 3, 0);
      instr_struct(&false_c3_20441, 3, 0);
      instr_struct(&true_c2_20442, 2, 0);
      instr_struct(&false_c3_20443, 3, 0);
      instr_struct(&true_c2_20444, 2, 0);
      instr_struct(&Ascii_c16_20445, 16, 8,
        false_c3_20437, true_c2_20438, true_c2_20439, false_c3_20440,
        false_c3_20441, true_c2_20442, false_c3_20443, true_c2_20444);
      instr_struct(&false_c3_20446, 3, 0);
      instr_struct(&true_c2_20447, 2, 0);
      instr_struct(&true_c2_20448, 2, 0);
      instr_struct(&true_c2_20449, 2, 0);
      instr_struct(&false_c3_20450, 3, 0);
      instr_struct(&false_c3_20451, 3, 0);
      instr_struct(&true_c2_20452, 2, 0);
      instr_struct(&false_c3_20453, 3, 0);
      instr_struct(&Ascii_c16_20454, 16, 8,
        false_c3_20446, true_c2_20447, true_c2_20448, true_c2_20449,
        false_c3_20450, false_c3_20451, true_c2_20452, false_c3_20453);
      instr_struct(&false_c3_20455, 3, 0);
      instr_struct(&true_c2_20456, 2, 0);
      instr_struct(&true_c2_20457, 2, 0);
      instr_struct(&false_c3_20458, 3, 0);
      instr_struct(&true_c2_20459, 2, 0);
      instr_struct(&true_c2_20460, 2, 0);
      instr_struct(&true_c2_20461, 2, 0);
      instr_struct(&true_c2_20462, 2, 0);
      instr_struct(&Ascii_c16_20463, 16, 8,
        false_c3_20455, true_c2_20456, true_c2_20457, false_c3_20458,
        true_c2_20459, true_c2_20460, true_c2_20461, true_c2_20462);
      instr_struct(&EmptyString_c17_20464, 17, 0);
      instr_struct(&String_c18_20465, 18, 2,
        Ascii_c16_20463, EmptyString_c17_20464);
      instr_struct(&String_c18_20466, 18, 2,
        Ascii_c16_20454, String_c18_20465);
      instr_struct(&String_c18_20467, 18, 2,
        Ascii_c16_20445, String_c18_20466);
      instr_struct(&String_c18_20468, 18, 2,
        Ascii_c16_20436, String_c18_20467);
      instr_mov(&case_20427, String_c18_20468);
      break;
    case 5:
      instr_mov(&_20469, ((clc_node)_20426)->data[0]);
      instr_struct(&false_c3_20470, 3, 0);
      instr_struct(&true_c2_20471, 2, 0);
      instr_struct(&true_c2_20472, 2, 0);
      instr_struct(&true_c2_20473, 2, 0);
      instr_struct(&false_c3_20474, 3, 0);
      instr_struct(&false_c3_20475, 3, 0);
      instr_struct(&true_c2_20476, 2, 0);
      instr_struct(&true_c2_20477, 2, 0);
      instr_struct(&Ascii_c16_20478, 16, 8,
        false_c3_20470, true_c2_20471, true_c2_20472, true_c2_20473,
        false_c3_20474, false_c3_20475, true_c2_20476, true_c2_20477);
      instr_struct(&false_c3_20479, 3, 0);
      instr_struct(&true_c2_20480, 2, 0);
      instr_struct(&true_c2_20481, 2, 0);
      instr_struct(&true_c2_20482, 2, 0);
      instr_struct(&false_c3_20483, 3, 0);
      instr_struct(&true_c2_20484, 2, 0);
      instr_struct(&false_c3_20485, 3, 0);
      instr_struct(&true_c2_20486, 2, 0);
      instr_struct(&Ascii_c16_20487, 16, 8,
        false_c3_20479, true_c2_20480, true_c2_20481, true_c2_20482,
        false_c3_20483, true_c2_20484, false_c3_20485, true_c2_20486);
      instr_struct(&false_c3_20488, 3, 0);
      instr_struct(&true_c2_20489, 2, 0);
      instr_struct(&true_c2_20490, 2, 0);
      instr_struct(&false_c3_20491, 3, 0);
      instr_struct(&false_c3_20492, 3, 0);
      instr_struct(&false_c3_20493, 3, 0);
      instr_struct(&true_c2_20494, 2, 0);
      instr_struct(&true_c2_20495, 2, 0);
      instr_struct(&Ascii_c16_20496, 16, 8,
        false_c3_20488, true_c2_20489, true_c2_20490, false_c3_20491,
        false_c3_20492, false_c3_20493, true_c2_20494, true_c2_20495);
      instr_struct(&false_c3_20497, 3, 0);
      instr_struct(&true_c2_20498, 2, 0);
      instr_struct(&true_c2_20499, 2, 0);
      instr_struct(&false_c3_20500, 3, 0);
      instr_struct(&false_c3_20501, 3, 0);
      instr_struct(&false_c3_20502, 3, 0);
      instr_struct(&true_c2_20503, 2, 0);
      instr_struct(&true_c2_20504, 2, 0);
      instr_struct(&Ascii_c16_20505, 16, 8,
        false_c3_20497, true_c2_20498, true_c2_20499, false_c3_20500,
        false_c3_20501, false_c3_20502, true_c2_20503, true_c2_20504);
      instr_struct(&false_c3_20506, 3, 0);
      instr_struct(&false_c3_20507, 3, 0);
      instr_struct(&true_c2_20508, 2, 0);
      instr_struct(&false_c3_20509, 3, 0);
      instr_struct(&false_c3_20510, 3, 0);
      instr_struct(&false_c3_20511, 3, 0);
      instr_struct(&false_c3_20512, 3, 0);
      instr_struct(&false_c3_20513, 3, 0);
      instr_struct(&Ascii_c16_20514, 16, 8,
        false_c3_20506, false_c3_20507, true_c2_20508, false_c3_20509,
        false_c3_20510, false_c3_20511, false_c3_20512, false_c3_20513);
      instr_struct(&false_c3_20515, 3, 0);
      instr_struct(&false_c3_20516, 3, 0);
      instr_struct(&true_c2_20517, 2, 0);
      instr_struct(&false_c3_20518, 3, 0);
      instr_struct(&true_c2_20519, 2, 0);
      instr_struct(&false_c3_20520, 3, 0);
      instr_struct(&false_c3_20521, 3, 0);
      instr_struct(&false_c3_20522, 3, 0);
      instr_struct(&Ascii_c16_20523, 16, 8,
        false_c3_20515, false_c3_20516, true_c2_20517, false_c3_20518,
        true_c2_20519, false_c3_20520, false_c3_20521, false_c3_20522);
      instr_struct(&EmptyString_c17_20524, 17, 0);
      instr_struct(&String_c18_20525, 18, 2,
        Ascii_c16_20523, EmptyString_c17_20524);
      instr_struct(&String_c18_20526, 18, 2,
        Ascii_c16_20514, String_c18_20525);
      instr_struct(&String_c18_20527, 18, 2,
        Ascii_c16_20505, String_c18_20526);
      instr_struct(&String_c18_20528, 18, 2,
        Ascii_c16_20496, String_c18_20527);
      instr_struct(&String_c18_20529, 18, 2,
        Ascii_c16_20487, String_c18_20528);
      instr_struct(&String_c18_20530, 18, 2,
        Ascii_c16_20478, String_c18_20529);
      instr_call(&tmp_20531, env[20], String_c18_20530);
      instr_call(&tmp_20532, env[0], _20469);
      instr_call(&tmp_20533, tmp_20531, tmp_20532);
      instr_call(&tmp_20534, env[20], tmp_20533);
      instr_struct(&false_c3_20535, 3, 0);
      instr_struct(&false_c3_20536, 3, 0);
      instr_struct(&true_c2_20537, 2, 0);
      instr_struct(&false_c3_20538, 3, 0);
      instr_struct(&true_c2_20539, 2, 0);
      instr_struct(&false_c3_20540, 3, 0);
      instr_struct(&false_c3_20541, 3, 0);
      instr_struct(&true_c2_20542, 2, 0);
      instr_struct(&Ascii_c16_20543, 16, 8,
        false_c3_20535, false_c3_20536, true_c2_20537, false_c3_20538,
        true_c2_20539, false_c3_20540, false_c3_20541, true_c2_20542);
      instr_struct(&EmptyString_c17_20544, 17, 0);
      instr_struct(&String_c18_20545, 18, 2,
        Ascii_c16_20543, EmptyString_c17_20544);
      instr_call(&tmp_20546, tmp_20534, String_c18_20545);
      instr_mov(&case_20427, tmp_20546);
      break;}
  return case_20427;
}

clc_ptr lam_20597(clc_ptr _20595, clc_env env)
{
  clc_ptr case_20596;
  switch(((clc_node)_20595)->tag){
    case 1: instr_mov(&case_20596, env[32]);
            break;}
  return case_20596;
}

clc_ptr lam_20601(clc_ptr _20587, clc_env env)
{
  clc_ptr _20589; clc_ptr case_20588; clc_ptr clo_20598;
  clc_ptr stdout_20590; clc_ptr tmp_20591; clc_ptr tmp_20592;
  clc_ptr tmp_20593; clc_ptr tmp_20599; clc_ptr tmp_20600;
  switch(((clc_node)_20587)->tag){
    case 15:
      instr_mov(&_20589, ((clc_node)_20587)->data[0]);
      instr_free_struct(_20587);
      instr_call(&tmp_20591, env[14], env[1]);
      instr_call(&tmp_20592, env[5], _20589);
      instr_call(&tmp_20593, tmp_20591, tmp_20592);
      instr_free_clo(tmp_20591);
      instr_mov(&stdout_20590, tmp_20593);
      instr_clo(&clo_20598, &lam_20597, 29, env, 3,
        stdout_20590, _20587, _20589);
      instr_call(&tmp_20599, env[13], stdout_20590);
      instr_call(&tmp_20600, clo_20598, tmp_20599);
      instr_free_clo(clo_20598);
      instr_mov(&case_20588, tmp_20600);
      break;}
  return case_20588;
}

int main()
{
  clc_ptr _217; clc_ptr addn_3; clc_ptr addn_20118; clc_ptr append_176;
  clc_ptr append_20371; clc_ptr bar_214; clc_ptr baz_215; clc_ptr cat_67;
  clc_ptr cat_20156; clc_ptr clo_20602; clc_ptr close_err_130;
  clc_ptr close_err_20253; clc_ptr close_in_114; clc_ptr close_in_20211;
  clc_ptr close_out_122; clc_ptr close_out_20232; clc_ptr foo_213;
  clc_ptr head_140; clc_ptr head_20270; clc_ptr kappend_151;
  clc_ptr kappend_20340; clc_ptr length_198; clc_ptr length_20424;
  clc_ptr lt_84; clc_ptr lt_20174; clc_ptr printerr_125;
  clc_ptr printerr_20245; clc_ptr printline_117; clc_ptr printline_20224;
  clc_ptr readline_109; clc_ptr readline_20203; clc_ptr rep_189;
  clc_ptr rep_20394; clc_ptr stderr_rec_102; clc_ptr stderr_rec_20189;
  clc_ptr stderr_t_108; clc_ptr stdin_rec_94; clc_ptr stdin_rec_20179;
  clc_ptr stdin_t_106; clc_ptr stdout_216; clc_ptr stdout_rec_98;
  clc_ptr stdout_rec_20184; clc_ptr stdout_t_107; clc_ptr string_of_nat_210;
  clc_ptr string_of_nat_20548; clc_ptr strlen_74; clc_ptr strlen_20166;
  clc_ptr subn_9; clc_ptr subn_20138; clc_ptr succ_c5_20551;
  clc_ptr succ_c5_20552; clc_ptr succ_c5_20553; clc_ptr succ_c5_20554;
  clc_ptr succ_c5_20555; clc_ptr succ_c5_20561; clc_ptr succ_c5_20562;
  clc_ptr succ_c5_20563; clc_ptr succ_c5_20564; clc_ptr succ_c5_20565;
  clc_ptr succ_c5_20571; clc_ptr succ_c5_20572; clc_ptr succ_c5_20573;
  clc_ptr succ_c5_20574; clc_ptr succ_c5_20575; clc_ptr succ_c5_20578;
  clc_ptr succ_c5_20579; clc_ptr succ_c5_20580; clc_ptr succ_c5_20581;
  clc_ptr succ_c5_20582; clc_ptr succ_c5_20605; clc_ptr succ_c5_20606;
  clc_ptr succ_c5_20607; clc_ptr succ_c5_20608; clc_ptr succ_c5_20609;
  clc_ptr succ_c5_20612; clc_ptr succ_c5_20613; clc_ptr succ_c5_20614;
  clc_ptr succ_c5_20615; clc_ptr succ_c5_20616; clc_ptr tmp_20191;
  clc_ptr tmp_20193; clc_ptr tmp_20195; clc_ptr tmp_20549; clc_ptr tmp_20556;
  clc_ptr tmp_20558; clc_ptr tmp_20559; clc_ptr tmp_20566; clc_ptr tmp_20568;
  clc_ptr tmp_20569; clc_ptr tmp_20576; clc_ptr tmp_20583; clc_ptr tmp_20584;
  clc_ptr tmp_20585; clc_ptr tmp_20603; clc_ptr tmp_20610; clc_ptr tmp_20617;
  clc_ptr tmp_20618; clc_ptr tmp_20619; clc_ptr tmp_20620;
  clc_ptr tt_c1_20190; clc_ptr tt_c1_20192; clc_ptr tt_c1_20194;
  clc_ptr tt_c1_20557; clc_ptr tt_c1_20567; clc_ptr zero_c4_20550;
  clc_ptr zero_c4_20560; clc_ptr zero_c4_20570; clc_ptr zero_c4_20577;
  clc_ptr zero_c4_20604; clc_ptr zero_c4_20611;
  clc_env env = 0;
  instr_init();
  instr_clo(&addn_20118, &addn_20117, 0, env, 1, 0);
  instr_mov(&addn_3, addn_20118);
  instr_clo(&subn_20138, &subn_20137, 0, env, 2, addn_3, 0);
  instr_mov(&subn_9, subn_20138);
  instr_clo(&cat_20156, &cat_20155, 0, env, 3, subn_9, addn_3, 0);
  instr_mov(&cat_67, cat_20156);
  instr_clo(&strlen_20166, &strlen_20165, 0, env, 4,
    cat_67, subn_9, addn_3, 0);
  instr_mov(&strlen_74, strlen_20166);
  instr_clo(&lt_20174, &lt_20173, 0, env, 5,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&lt_84, lt_20174);
  instr_clo(&stdin_rec_20179, &stdin_rec_20178, 0, env, 6,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdin_rec_94, stdin_rec_20179);
  instr_clo(&stdout_rec_20184, &stdout_rec_20183, 0, env, 7,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stdout_rec_98, stdout_rec_20184);
  instr_clo(&stderr_rec_20189, &stderr_rec_20188, 0, env, 8,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&stderr_rec_102, stderr_rec_20189);
  instr_struct(&tt_c1_20190, 1, 0);
  instr_call(&tmp_20191, stdin_rec_94, tt_c1_20190);
  instr_mov(&stdin_t_106, tmp_20191);
  instr_struct(&tt_c1_20192, 1, 0);
  instr_call(&tmp_20193, stdout_rec_98, tt_c1_20192);
  instr_mov(&stdout_t_107, tmp_20193);
  instr_struct(&tt_c1_20194, 1, 0);
  instr_call(&tmp_20195, stderr_rec_102, tt_c1_20194);
  instr_mov(&stderr_t_108, tmp_20195);
  instr_clo(&readline_20203, &readline_20202, 0, env, 12,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&readline_109, readline_20203);
  instr_clo(&close_in_20211, &close_in_20210, 0, env, 13,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_in_114, close_in_20211);
  instr_clo(&printline_20224, &printline_20223, 0, env, 14,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&printline_117, printline_20224);
  instr_clo(&close_out_20232, &close_out_20231, 0, env, 15,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_out_122, close_out_20232);
  instr_clo(&printerr_20245, &printerr_20244, 0, env, 16,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&printerr_125, printerr_20245);
  instr_clo(&close_err_20253, &close_err_20252, 0, env, 17,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&close_err_130, close_err_20253);
  instr_clo(&head_20270, &head_20269, 0, env, 18,
    close_err_130, printerr_125, close_out_122, printline_117, close_in_114,
    readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102,
    stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&head_140, head_20270);
  instr_clo(&kappend_20340, &kappend_20339, 0, env, 19,
    head_140, close_err_130, printerr_125, close_out_122, printline_117,
    close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106,
    stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67,
    subn_9, addn_3, 0);
  instr_mov(&kappend_151, kappend_20340);
  instr_clo(&append_20371, &append_20370, 0, env, 20,
    kappend_151, head_140, close_err_130, printerr_125, close_out_122,
    printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107,
    stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84,
    strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&append_176, append_20371);
  instr_clo(&rep_20394, &rep_20393, 0, env, 21,
    append_176, kappend_151, head_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&rep_189, rep_20394);
  instr_clo(&length_20424, &length_20423, 0, env, 22,
    rep_189, append_176, kappend_151, head_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&length_198, length_20424);
  instr_clo(&string_of_nat_20548, &string_of_nat_20547, 0, env, 23,
    length_198, rep_189, append_176, kappend_151, head_140, close_err_130,
    printerr_125, close_out_122, printline_117, close_in_114, readline_109,
    stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98,
    stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_mov(&string_of_nat_210, string_of_nat_20548);
  instr_call(&tmp_20549, rep_189, 0);
  instr_struct(&zero_c4_20550, 4, 0);
  instr_struct(&succ_c5_20551, 5, 1,
    zero_c4_20550);
  instr_struct(&succ_c5_20552, 5, 1,
    succ_c5_20551);
  instr_struct(&succ_c5_20553, 5, 1,
    succ_c5_20552);
  instr_struct(&succ_c5_20554, 5, 1,
    succ_c5_20553);
  instr_struct(&succ_c5_20555, 5, 1,
    succ_c5_20554);
  instr_call(&tmp_20556, tmp_20549, succ_c5_20555);
  instr_struct(&tt_c1_20557, 1, 0);
  instr_call(&tmp_20558, tmp_20556, tt_c1_20557);
  instr_mov(&foo_213, tmp_20558);
  instr_call(&tmp_20559, rep_189, 0);
  instr_struct(&zero_c4_20560, 4, 0);
  instr_struct(&succ_c5_20561, 5, 1,
    zero_c4_20560);
  instr_struct(&succ_c5_20562, 5, 1,
    succ_c5_20561);
  instr_struct(&succ_c5_20563, 5, 1,
    succ_c5_20562);
  instr_struct(&succ_c5_20564, 5, 1,
    succ_c5_20563);
  instr_struct(&succ_c5_20565, 5, 1,
    succ_c5_20564);
  instr_call(&tmp_20566, tmp_20559, succ_c5_20565);
  instr_struct(&tt_c1_20567, 1, 0);
  instr_call(&tmp_20568, tmp_20566, tt_c1_20567);
  instr_mov(&bar_214, tmp_20568);
  instr_call(&tmp_20569, append_176, 0);
  instr_struct(&zero_c4_20570, 4, 0);
  instr_struct(&succ_c5_20571, 5, 1,
    zero_c4_20570);
  instr_struct(&succ_c5_20572, 5, 1,
    succ_c5_20571);
  instr_struct(&succ_c5_20573, 5, 1,
    succ_c5_20572);
  instr_struct(&succ_c5_20574, 5, 1,
    succ_c5_20573);
  instr_struct(&succ_c5_20575, 5, 1,
    succ_c5_20574);
  instr_call(&tmp_20576, tmp_20569, succ_c5_20575);
  instr_struct(&zero_c4_20577, 4, 0);
  instr_struct(&succ_c5_20578, 5, 1,
    zero_c4_20577);
  instr_struct(&succ_c5_20579, 5, 1,
    succ_c5_20578);
  instr_struct(&succ_c5_20580, 5, 1,
    succ_c5_20579);
  instr_struct(&succ_c5_20581, 5, 1,
    succ_c5_20580);
  instr_struct(&succ_c5_20582, 5, 1,
    succ_c5_20581);
  instr_call(&tmp_20583, tmp_20576, succ_c5_20582);
  instr_call(&tmp_20584, tmp_20583, foo_213);
  instr_call(&tmp_20585, tmp_20584, bar_214);
  instr_free_clo(tmp_20584);
  instr_mov(&baz_215, tmp_20585);
  instr_trg(&stdout_216, &proc_stdout);
  instr_clo(&clo_20602, &lam_20601, 0, env, 28,
    stdout_216, baz_215, bar_214, foo_213, string_of_nat_210, length_198,
    rep_189, append_176, kappend_151, head_140, close_err_130, printerr_125,
    close_out_122, printline_117, close_in_114, readline_109, stderr_t_108,
    stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94,
    lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  instr_call(&tmp_20603, length_198, 0);
  instr_struct(&zero_c4_20604, 4, 0);
  instr_struct(&succ_c5_20605, 5, 1,
    zero_c4_20604);
  instr_struct(&succ_c5_20606, 5, 1,
    succ_c5_20605);
  instr_struct(&succ_c5_20607, 5, 1,
    succ_c5_20606);
  instr_struct(&succ_c5_20608, 5, 1,
    succ_c5_20607);
  instr_struct(&succ_c5_20609, 5, 1,
    succ_c5_20608);
  instr_call(&tmp_20610, addn_3, succ_c5_20609);
  instr_struct(&zero_c4_20611, 4, 0);
  instr_struct(&succ_c5_20612, 5, 1,
    zero_c4_20611);
  instr_struct(&succ_c5_20613, 5, 1,
    succ_c5_20612);
  instr_struct(&succ_c5_20614, 5, 1,
    succ_c5_20613);
  instr_struct(&succ_c5_20615, 5, 1,
    succ_c5_20614);
  instr_struct(&succ_c5_20616, 5, 1,
    succ_c5_20615);
  instr_call(&tmp_20617, tmp_20610, succ_c5_20616);
  instr_call(&tmp_20618, tmp_20603, tmp_20617);
  instr_call(&tmp_20619, tmp_20618, baz_215);
  instr_call(&tmp_20620, clo_20602, tmp_20619);
  instr_free_clo(clo_20602);
  instr_mov(&_217, tmp_20620);
  return 0;
}
