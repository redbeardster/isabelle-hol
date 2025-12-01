theory Export_Example
    imports
    Isabelle_C.C_Main
begin

C\<open>
#define TRUE 1
#define FALSE 0

int f(int x ) {x = x + 1; return TRUE;}
\<close>  


end