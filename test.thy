theory test
  imports Main 
  HOL.Partial_Function
  "HOL-Library.Monad_Syntax"
begin




type_synonym '\<alpha> parse_result = "('\<alpha> \<times> string)"

\<comment> \<open>The inner option defines parsing success\<close>
type_synonym '\<alpha> parser = "string \<Rightarrow> '\<alpha> parse_result option"

section \<open>Types for the printer\<close>
type_synonym '\<alpha> printer = "'\<alpha> \<Rightarrow> string option"


type_synonym '\<alpha> bidef = "('\<alpha> parser \<times> '\<alpha> printer) option"

(*WF should also include Inl \<Rightarrow> Inl and Inr \<Rightarrow> Inr*)
type_synonym 'a bd = "(string + 'a) \<Rightarrow> ((('a \<times> string) option) + string option) option"


abbreviation "option_lub \<equiv> flat_lub None"

definition "bidef_ord = fun_ord option_ord"
definition "bidef_lub = fun_lub option_lub"

abbreviation "mono_bidef \<equiv> monotone (fun_ord bidef_ord) bidef_ord"

lemma bidef_pfd: "partial_function_definitions bidef_ord (bidef_lub)"
  unfolding bidef_ord_def bidef_lub_def
    apply (rule partial_function_lift)
    by (rule flat_interpretation)

lemma bidef_lub_empty: "bidef_lub {} = (\<lambda> _. None)"
  unfolding bidef_lub_def img_lub_def flat_lub_def fun_lub_def
  by (auto simp: fun_eq_iff)


interpretation bidef:
partial_function_definitions "bidef_ord" "bidef_lub"
rewrites "flat_lub None {} \<equiv> None"
  apply (rule bidef_pfd)
  by(simp add: flat_lub_def)

declaration \<open>Partial_Function.init "bidef" \<^term>\<open>bidef.fixp_fun\<close>
  \<^term>\<open>bidef.mono_body\<close> @{thm bidef.fixp_rule_uc} @{thm bidef.fixp_induct_uc}
  (NONE)\<close>

definition fail where
  "fail = Some ((\<lambda>i. None), (\<lambda>i. None))"

definition return :: "'a \<Rightarrow> 'a bidef" where
  "return x = Some ((\<lambda>i. Some (x, i)), (\<lambda>i. if i=x then Some [] else None))"

definition if_then_else :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> '\<gamma> bidef \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<beta> + '\<gamma>) bidef" where
  "if_then_else a a2b c b2a = ( do {
      p_a \<leftarrow> a;
      
      
      undefined

})"


end