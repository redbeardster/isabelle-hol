theory ArrayZero
  imports 
    "AutoCorres2.AutoCorres"
begin

install_C_file "array_zero.c"
autocorres "array_zero.c"

context array_zero_all_impl begin

