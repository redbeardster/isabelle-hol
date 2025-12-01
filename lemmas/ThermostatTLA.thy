theory ThermostatTLA
imports "HOL-TLA.TLA"
begin

(*
does not work
*)

consts
 temp, target :: "nat stfun"
assumes basevars: "basevars (temp, target)"

definition Init :: action where
  "Init = (temp$ = #20) \<and> (target$ = #20)"

definition Heat :: action where
  "Heat = (temp$ < target$) \<and> (temp$' = temp$ + #1)"

definition Cool :: action where  
  "Cool = (temp$ > target$) \<and> (temp$' = temp$ - #1)"

definition Stutter :: action where
  "Stutter = (temp$' = temp$) \<and> (target$' = target$)"

definition Next :: action where
  "Next = Heat \<or> Cool \<or> Stutter"

definition ThermostatSpec :: temporal where
  "ThermostatSpec = Init \<and> \<box>[Next]_\<langle>temp, target\<rangle>"

theorem stabilizes: "\<turnstile> ThermostatSpec \<longrightarrow> \<box>(\<bar>temp - target\<bar> \<le> #1)"
  sorry

end