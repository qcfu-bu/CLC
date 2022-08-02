#include "runtime.h"

CLC_ptr _3176(CLC_ptr _3175, CLC_env env)
{
  
  
  return _3175;
}

CLC_ptr _3184(CLC_ptr _3180, CLC_env env)
{
  CLC_ptr succ_c5_3183;
  CLC_ptr tmp_3181;
  CLC_ptr tmp_3182;
  INSTR_call(&tmp_3181, env[3], env[2]);
  INSTR_call(&tmp_3182, tmp_3181, _3180);
  INSTR_struct(&succ_c5_3183, 5, 1, tmp_3182);
  return succ_c5_3183;
}

CLC_ptr addn_3186(CLC_ptr _3172, CLC_env env)
{
  CLC_ptr _3178;
  CLC_ptr case_3173;
  CLC_ptr clo_3177;
  CLC_ptr clo_3185;
  switch(((CLC_node)_3172)->tag){
    case 4:
      INSTR_clo(&clo_3177, &_3176, 4, 0, _3172, env[0], env[1]);
      INSTR_mov(&case_3173, clo_3177);
      break;
    case 5:
      INSTR_mov(&_3178, ((CLC_node)_3172)->data[0]);
      INSTR_clo(&clo_3185, &_3184, 5, 0, _3172, _3178, env[0], env[1]);
      INSTR_mov(&case_3173, clo_3185);
      break;}
  return case_3173;
}

CLC_ptr _3194(CLC_ptr _3192, CLC_env env)
{
  CLC_ptr zero_c4_3193;
  INSTR_struct(&zero_c4_3193, 4, 0);
  return zero_c4_3193;
}

CLC_ptr _3204(CLC_ptr _3198, CLC_env env)
{
  CLC_ptr _3201;
  CLC_ptr case_3199;
  CLC_ptr succ_c5_3200;
  CLC_ptr tmp_3202;
  CLC_ptr tmp_3203;
  switch(((CLC_node)_3198)->tag){
    case 4:
      INSTR_struct(&succ_c5_3200, 5, 1, env[2]);
      INSTR_mov(&case_3199, succ_c5_3200);
      break;
    case 5:
      INSTR_mov(&_3201, ((CLC_node)_3198)->data[0]);
      INSTR_call(&tmp_3202, env[3], env[2]);
      INSTR_call(&tmp_3203, tmp_3202, _3201);
      INSTR_mov(&case_3199, tmp_3203);
      break;}
  return case_3199;
}

CLC_ptr subn_3206(CLC_ptr _3189, CLC_env env)
{
  CLC_ptr _3196;
  CLC_ptr case_3190;
  CLC_ptr clo_3195;
  CLC_ptr clo_3205;
  switch(((CLC_node)_3189)->tag){
    case 4:
      INSTR_clo(&clo_3195, &_3194, 5, 0, _3189, env[0], env[1], env[2]);
      INSTR_mov(&case_3190, clo_3195);
      break;
    case 5:
      INSTR_mov(&_3196, ((CLC_node)_3189)->data[0]);
      INSTR_clo(&clo_3205, &_3204, 6, 0, _3189, _3196, env[0], env[1], env[2]);
      INSTR_mov(&case_3190, clo_3205);
      break;}
  return case_3190;
}

CLC_ptr _3213(CLC_ptr _3212, CLC_env env)
{
  
  
  return _3212;
}

CLC_ptr _3222(CLC_ptr _3218, CLC_env env)
{
  CLC_ptr String_c18_3221;
  CLC_ptr tmp_3219;
  CLC_ptr tmp_3220;
  INSTR_call(&tmp_3219, env[4], env[3]);
  INSTR_call(&tmp_3220, tmp_3219, _3218);
  INSTR_struct(&String_c18_3221, 18, 2, env[2], tmp_3220);
  return String_c18_3221;
}

CLC_ptr cat_3224(CLC_ptr _3209, CLC_env env)
{
  CLC_ptr _3215;
  CLC_ptr _3216;
  CLC_ptr case_3210;
  CLC_ptr clo_3214;
  CLC_ptr clo_3223;
  switch(((CLC_node)_3209)->tag){
    case 17:
      INSTR_clo(&clo_3214, &_3213, 6, 0, _3209, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_3210, clo_3214);
      break;
    case 18:
      INSTR_mov(&_3215, ((CLC_node)_3209)->data[0]);
      INSTR_mov(&_3216, ((CLC_node)_3209)->data[1]);
      INSTR_clo(&clo_3223, &_3222, 8, 0, _3209, _3215, _3216, env[0], env[1], env[2], env[3]);
      INSTR_mov(&case_3210, clo_3223);
      break;}
  return case_3210;
}

CLC_ptr strlen_3234(CLC_ptr _3227, CLC_env env)
{
  CLC_ptr _3230;
  CLC_ptr _3231;
  CLC_ptr case_3228;
  CLC_ptr succ_c5_3233;
  CLC_ptr tmp_3232;
  CLC_ptr zero_c4_3229;
  switch(((CLC_node)_3227)->tag){
    case 17:
      INSTR_struct(&zero_c4_3229, 4, 0);
      INSTR_mov(&case_3228, zero_c4_3229);
      break;
    case 18:
      INSTR_mov(&_3230, ((CLC_node)_3227)->data[0]);
      INSTR_mov(&_3231, ((CLC_node)_3227)->data[1]);
      INSTR_call(&tmp_3232, env[0], _3231);
      INSTR_struct(&succ_c5_3233, 5, 1, tmp_3232);
      INSTR_mov(&case_3228, succ_c5_3233);
      break;}
  return case_3228;
}

CLC_ptr _3240(CLC_ptr _3239, CLC_env env)
{
  
  
  return 0;
}

CLC_ptr lt_3242(CLC_ptr _3237, CLC_env env)
{
  CLC_ptr clo_3241;
  INSTR_clo(&clo_3241, &_3240, 8, 0, _3237, env[0], env[1], env[2], env[3], env[4], env[5]);
  return clo_3241;
}

CLC_ptr stdin_rec_3247(CLC_ptr _3245, CLC_env env)
{
  CLC_ptr case_3246;
  switch(((CLC_node)_3245)->tag){
    case 1: INSTR_mov(&case_3246, 0);
            break;}
  return case_3246;
}

CLC_ptr stdout_rec_3252(CLC_ptr _3250, CLC_env env)
{
  CLC_ptr case_3251;
  switch(((CLC_node)_3250)->tag){
    case 1: INSTR_mov(&case_3251, 0);
            break;}
  return case_3251;
}

CLC_ptr stderr_rec_3257(CLC_ptr _3255, CLC_env env)
{
  CLC_ptr case_3256;
  switch(((CLC_node)_3255)->tag){
    case 1: INSTR_mov(&case_3256, 0);
            break;}
  return case_3256;
}

CLC_ptr readline_3271(CLC_ptr _3266, CLC_env env)
{
  CLC_ptr recv_struct_3270;
  CLC_ptr send_clo_3267;
  CLC_ptr tmp_3269;
  CLC_ptr true_c2_3268;
  INSTR_send(&send_clo_3267, _3266);
  INSTR_struct(&true_c2_3268, 2, 0);
  INSTR_call(&tmp_3269, send_clo_3267, true_c2_3268);
  INSTR_recv(&recv_struct_3270, tmp_3269, 13);
  return recv_struct_3270;
}

CLC_ptr close_in_3276(CLC_ptr _3274, CLC_env env)
{
  CLC_ptr unit_struct_3275;
  INSTR_struct(&unit_struct_3275, 1, 0);
  return unit_struct_3275;
}

CLC_ptr _3287(CLC_ptr _3281, CLC_env env)
{
  CLC_ptr send_clo_3282;
  CLC_ptr send_clo_3285;
  CLC_ptr tmp_3284;
  CLC_ptr tmp_3286;
  CLC_ptr true_c2_3283;
  INSTR_send(&send_clo_3282, env[1]);
  INSTR_struct(&true_c2_3283, 2, 0);
  INSTR_call(&tmp_3284, send_clo_3282, true_c2_3283);
  INSTR_send(&send_clo_3285, tmp_3284);
  INSTR_call(&tmp_3286, send_clo_3285, _3281);
  return tmp_3286;
}

CLC_ptr printline_3289(CLC_ptr _3279, CLC_env env)
{
  CLC_ptr clo_3288;
  INSTR_clo(&clo_3288, &_3287, 17, 0, _3279, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14]);
  return clo_3288;
}

CLC_ptr close_out_3294(CLC_ptr _3292, CLC_env env)
{
  CLC_ptr unit_struct_3293;
  INSTR_struct(&unit_struct_3293, 1, 0);
  return unit_struct_3293;
}

CLC_ptr _3305(CLC_ptr _3299, CLC_env env)
{
  CLC_ptr send_clo_3300;
  CLC_ptr send_clo_3303;
  CLC_ptr tmp_3302;
  CLC_ptr tmp_3304;
  CLC_ptr true_c2_3301;
  INSTR_send(&send_clo_3300, env[1]);
  INSTR_struct(&true_c2_3301, 2, 0);
  INSTR_call(&tmp_3302, send_clo_3300, true_c2_3301);
  INSTR_send(&send_clo_3303, tmp_3302);
  INSTR_call(&tmp_3304, send_clo_3303, _3299);
  return tmp_3304;
}

CLC_ptr printerr_3307(CLC_ptr _3297, CLC_env env)
{
  CLC_ptr clo_3306;
  INSTR_clo(&clo_3306, &_3305, 19, 0, _3297, env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7], env[8], env[9], env[10], env[11], env[12], env[13], env[14], env[15], env[16]);
  return clo_3306;
}

CLC_ptr close_err_3312(CLC_ptr _3310, CLC_env env)
{
  CLC_ptr unit_struct_3311;
  INSTR_struct(&unit_struct_3311, 1, 0);
  return unit_struct_3311;
}

CLC_ptr _3351(CLC_ptr _3349, CLC_env env)
{
  CLC_ptr case_3350;
  switch(((CLC_node)_3349)->tag){
    case 1: INSTR_mov(&case_3350, env[20]);
            break;}
  return case_3350;
}

int main()
{
  CLC_ptr _134;
  CLC_ptr Ascii_c16_3324;
  CLC_ptr Ascii_c16_3333;
  CLC_ptr Ascii_c16_3342;
  CLC_ptr EmptyString_c17_3343;
  CLC_ptr String_c18_3344;
  CLC_ptr String_c18_3345;
  CLC_ptr String_c18_3346;
  CLC_ptr addn_3;
  CLC_ptr addn_3187;
  CLC_ptr cat_67;
  CLC_ptr cat_3225;
  CLC_ptr ch_133;
  CLC_ptr ch_3314;
  CLC_ptr clo_3352;
  CLC_ptr close_err_130;
  CLC_ptr close_err_3313;
  CLC_ptr close_in_114;
  CLC_ptr close_in_3277;
  CLC_ptr close_out_122;
  CLC_ptr close_out_3295;
  CLC_ptr false_c3_3316;
  CLC_ptr false_c3_3319;
  CLC_ptr false_c3_3320;
  CLC_ptr false_c3_3321;
  CLC_ptr false_c3_3322;
  CLC_ptr false_c3_3325;
  CLC_ptr false_c3_3328;
  CLC_ptr false_c3_3329;
  CLC_ptr false_c3_3330;
  CLC_ptr false_c3_3332;
  CLC_ptr false_c3_3334;
  CLC_ptr false_c3_3337;
  CLC_ptr false_c3_3338;
  CLC_ptr false_c3_3339;
  CLC_ptr lt_84;
  CLC_ptr lt_3243;
  CLC_ptr printerr_125;
  CLC_ptr printerr_3308;
  CLC_ptr printline_117;
  CLC_ptr printline_3290;
  CLC_ptr readline_109;
  CLC_ptr readline_3272;
  CLC_ptr stderr_rec_102;
  CLC_ptr stderr_rec_3258;
  CLC_ptr stderr_t_108;
  CLC_ptr stdin_rec_94;
  CLC_ptr stdin_rec_3248;
  CLC_ptr stdin_t_106;
  CLC_ptr stdout_rec_98;
  CLC_ptr stdout_rec_3253;
  CLC_ptr stdout_t_107;
  CLC_ptr strlen_74;
  CLC_ptr strlen_3235;
  CLC_ptr subn_9;
  CLC_ptr subn_3207;
  CLC_ptr tmp_3260;
  CLC_ptr tmp_3262;
  CLC_ptr tmp_3264;
  CLC_ptr tmp_3315;
  CLC_ptr tmp_3347;
  CLC_ptr tmp_3353;
  CLC_ptr tmp_3354;
  CLC_ptr true_c2_3317;
  CLC_ptr true_c2_3318;
  CLC_ptr true_c2_3323;
  CLC_ptr true_c2_3326;
  CLC_ptr true_c2_3327;
  CLC_ptr true_c2_3331;
  CLC_ptr true_c2_3335;
  CLC_ptr true_c2_3336;
  CLC_ptr true_c2_3340;
  CLC_ptr true_c2_3341;
  CLC_ptr tt_c1_3259;
  CLC_ptr tt_c1_3261;
  CLC_ptr tt_c1_3263;
  INSTR_clo(&addn_3187, &addn_3186, 2, 0, 0);
  INSTR_mov(&addn_3, addn_3187);
  INSTR_clo(&subn_3207, &subn_3206, 3, 0, addn_3, 0);
  INSTR_mov(&subn_9, subn_3207);
  INSTR_clo(&cat_3225, &cat_3224, 4, 0, subn_9, addn_3, 0);
  INSTR_mov(&cat_67, cat_3225);
  INSTR_clo(&strlen_3235, &strlen_3234, 5, 0, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&strlen_74, strlen_3235);
  INSTR_clo(&lt_3243, &lt_3242, 6, 0, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&lt_84, lt_3243);
  INSTR_clo(&stdin_rec_3248, &stdin_rec_3247, 7, 0, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdin_rec_94, stdin_rec_3248);
  INSTR_clo(&stdout_rec_3253, &stdout_rec_3252, 8, 0, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stdout_rec_98, stdout_rec_3253);
  INSTR_clo(&stderr_rec_3258, &stderr_rec_3257, 9, 0, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&stderr_rec_102, stderr_rec_3258);
  INSTR_struct(&tt_c1_3259, 1, 0);
  INSTR_call(&tmp_3260, stdin_rec_94, tt_c1_3259);
  INSTR_mov(&stdin_t_106, tmp_3260);
  INSTR_struct(&tt_c1_3261, 1, 0);
  INSTR_call(&tmp_3262, stdout_rec_98, tt_c1_3261);
  INSTR_mov(&stdout_t_107, tmp_3262);
  INSTR_struct(&tt_c1_3263, 1, 0);
  INSTR_call(&tmp_3264, stderr_rec_102, tt_c1_3263);
  INSTR_mov(&stderr_t_108, tmp_3264);
  INSTR_clo(&readline_3272, &readline_3271, 13, 0, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&readline_109, readline_3272);
  INSTR_clo(&close_in_3277, &close_in_3276, 14, 0, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_in_114, close_in_3277);
  INSTR_clo(&printline_3290, &printline_3289, 15, 0, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printline_117, printline_3290);
  INSTR_clo(&close_out_3295, &close_out_3294, 16, 0, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_out_122, close_out_3295);
  INSTR_clo(&printerr_3308, &printerr_3307, 17, 0, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&printerr_125, printerr_3308);
  INSTR_clo(&close_err_3313, &close_err_3312, 18, 0, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_mov(&close_err_130, close_err_3313);
  INSTR_trg(&ch_133, &PROC_stdout);
  INSTR_call(&tmp_3315, printline_117, ch_133);
  INSTR_struct(&false_c3_3316, 3, 0);
  INSTR_struct(&true_c2_3317, 2, 0);
  INSTR_struct(&true_c2_3318, 2, 0);
  INSTR_struct(&false_c3_3319, 3, 0);
  INSTR_struct(&false_c3_3320, 3, 0);
  INSTR_struct(&false_c3_3321, 3, 0);
  INSTR_struct(&false_c3_3322, 3, 0);
  INSTR_struct(&true_c2_3323, 2, 0);
  INSTR_struct(&Ascii_c16_3324, 16, 8, false_c3_3316, true_c2_3317, true_c2_3318, false_c3_3319, false_c3_3320, false_c3_3321, false_c3_3322, true_c2_3323);
  INSTR_struct(&false_c3_3325, 3, 0);
  INSTR_struct(&true_c2_3326, 2, 0);
  INSTR_struct(&true_c2_3327, 2, 0);
  INSTR_struct(&false_c3_3328, 3, 0);
  INSTR_struct(&false_c3_3329, 3, 0);
  INSTR_struct(&false_c3_3330, 3, 0);
  INSTR_struct(&true_c2_3331, 2, 0);
  INSTR_struct(&false_c3_3332, 3, 0);
  INSTR_struct(&Ascii_c16_3333, 16, 8, false_c3_3325, true_c2_3326, true_c2_3327, false_c3_3328, false_c3_3329, false_c3_3330, true_c2_3331, false_c3_3332);
  INSTR_struct(&false_c3_3334, 3, 0);
  INSTR_struct(&true_c2_3335, 2, 0);
  INSTR_struct(&true_c2_3336, 2, 0);
  INSTR_struct(&false_c3_3337, 3, 0);
  INSTR_struct(&false_c3_3338, 3, 0);
  INSTR_struct(&false_c3_3339, 3, 0);
  INSTR_struct(&true_c2_3340, 2, 0);
  INSTR_struct(&true_c2_3341, 2, 0);
  INSTR_struct(&Ascii_c16_3342, 16, 8, false_c3_3334, true_c2_3335, true_c2_3336, false_c3_3337, false_c3_3338, false_c3_3339, true_c2_3340, true_c2_3341);
  INSTR_struct(&EmptyString_c17_3343, 17, 0);
  INSTR_struct(&String_c18_3344, 18, 2, Ascii_c16_3342, EmptyString_c17_3343);
  INSTR_struct(&String_c18_3345, 18, 2, Ascii_c16_3333, String_c18_3344);
  INSTR_struct(&String_c18_3346, 18, 2, Ascii_c16_3324, String_c18_3345);
  INSTR_call(&tmp_3347, tmp_3315, String_c18_3346);
  INSTR_mov(&ch_3314, tmp_3347);
  INSTR_clo(&clo_3352, &_3351, 21, 0, ch_3314, ch_133, close_err_130, printerr_125, close_out_122, printline_117, close_in_114, readline_109, stderr_t_108, stdout_t_107, stdin_t_106, stderr_rec_102, stdout_rec_98, stdin_rec_94, lt_84, strlen_74, cat_67, subn_9, addn_3, 0);
  INSTR_call(&tmp_3353, close_out_122, ch_3314);
  INSTR_call(&tmp_3354, clo_3352, tmp_3353);
  INSTR_mov(&_134, tmp_3354);
  return 0;
}
