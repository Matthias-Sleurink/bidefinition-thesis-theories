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
      p_a \<leftarrow> a; \<comment> \<open>Not sure what this means, we are supposed to create a bidef in this monad, where None means nonterm\<close>
      
      undefined
})"


\<comment> \<open>IDEA: We let the bidef be one function\<close>
(*WF should also include Inl \<Rightarrow> Inl and Inr \<Rightarrow> Inr in wf*)
type_synonym 'a bd_aux = "(string + 'a) \<Rightarrow> ((('a \<times> string)) + string) option"


definition parse_aux :: "'a bd_aux \<Rightarrow> 'a parser" where
  "parse_aux bd_aux s = map_option projl (bd_aux (Inl s))"

definition print_aux :: "'a bd_aux \<Rightarrow> 'a printer" where
  "print_aux bd_aux s = map_option projr (bd_aux (Inr s))"

fun bdc_aux :: "('a parser) \<Rightarrow> ('a printer) \<Rightarrow> 'a bd_aux" where
  "bdc_aux parser printer (Inl s) = map_option Inl (parser s)"
| "bdc_aux parser printer (Inr t) = map_option Inr (printer t)"

lemma bdc_aux_def:
  "bdc_aux parser printer = (\<lambda> Inl s \<Rightarrow> map_option Inl (parser s) | Inr t \<Rightarrow> map_option Inr (printer t))"
  by (auto simp add: fun_eq_iff split: sum.splits)

lemma pp_bdc:
  "parse_aux (bdc_aux p pr) = p"
  "print_aux (bdc_aux p pr) = pr"
  unfolding parse_aux_def print_aux_def bdc_aux_def
  by (auto simp add: fun_eq_iff map_option.compositionality map_option.identity comp_def split: sum.splits)

definition wf_bd_aux :: "'a bd_aux \<Rightarrow> bool" where
  "wf_bd_aux bd_aux \<equiv> ( \<forall> s r. bd_aux (Inl s) = Some r \<longrightarrow> isl r) \<and> (\<forall> t r. (bd_aux (Inr t) = Some r \<longrightarrow> \<not>isl r))"

lemma bd_aux_wf_bdc:
  "wf_bd_aux (bdc_aux pa pr)"
  unfolding bdc_aux_def wf_bd_aux_def
  by auto

lemma bdc_aux_tuple:
  "wf_bd_aux bd \<Longrightarrow> wf_bd_aux bd' \<Longrightarrow> parse_aux bd = parse_aux bd' \<Longrightarrow> print_aux bd = print_aux bd' \<Longrightarrow> bd = bd'"
  unfolding bdc_aux_def parse_aux_def print_aux_def wf_bd_aux_def
  apply (clarsimp simp add: fun_eq_iff)
  subgoal for x
    apply (cases x)
    subgoal for a
      
      apply( cases \<open>bd x\<close>; simp; cases \<open>bd' x\<close>; simp)
        apply (auto  dest: spec[of _ a])
      by (metis option.inject option.simps(9) sum.expand)
    subgoal for b
      apply( cases \<open>bd x\<close>; simp; cases \<open>bd' x\<close>; simp)
        apply (auto  dest: spec[of _ b])
      by (metis option.inject option.simps(9) sum.expand)
    done
  done


lemma bdc_aux_all:
  assumes "wf_bd_aux bd"
  shows "bdc_aux (parse_aux bd) (print_aux bd) = bd"
  by (simp add: assms bdc_aux_tuple bd_aux_wf_bdc pp_bdc(1) pp_bdc(2))

typedef 'a bd = "Collect wf_bd_aux :: 'a bd_aux set"
  apply (rule exI[of _ \<open>\<lambda>x. None\<close>])
  by (simp add: wf_bd_aux_def)
print_theorems

setup_lifting type_definition_bd

lift_definition parse :: "'a bd \<Rightarrow> 'a parser" is parse_aux . 
lift_definition print :: "'a bd \<Rightarrow> 'a printer" is print_aux .
lift_definition bdc :: "'a parser \<Rightarrow> 'a printer \<Rightarrow> 'a bd" is bdc_aux by (simp add: bd_aux_wf_bdc)

lemma bdc'_tuple:
  "parse bd = parse bd' \<Longrightarrow> print bd = print bd' \<Longrightarrow> bd = bd'"
  apply transfer
  by (simp add: bdc_aux_tuple)

lemma bdc'_all:
  shows "bdc (parse bd) (print bd) = bd"
  apply transfer
  by (simp add: bdc_aux_all)

lifting_update bd.lifting
lifting_forget bd.lifting

definition bd_bottom :: "'a bd" where
  "bd_bottom = bdc (\<lambda>x. None) (\<lambda>x. None)"



interpretation bd:
  partial_function_definitions "flat_ord bd_bottom" "flat_lub bd_bottom"
  rewrites "flat_lub bd_bottom {} \<equiv> bd_bottom"
by (rule flat_interpretation)(simp add: flat_lub_def)

abbreviation "bd_ord \<equiv> flat_ord bd_bottom"
abbreviation "mono_bd \<equiv> monotone (fun_ord bd_ord) bd_ord"
(*
lemma fixp_induct_bd:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a bd" and
    C :: "('b \<Rightarrow> 'a bd) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_bd (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub (flat_lub bd_bottom)) (fun_ord bd_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x y. (\<And>x y. U f x = Some y \<Longrightarrow> P x y) \<Longrightarrow> U (F f) x = Some y \<Longrightarrow> P x y"
  assumes defined: "U f x = Some y"
  shows "P x y"
  using step defined bd.fixp_induct_uc[of U F C, OF mono eq inverse2 option_admissible]
  unfolding fun_lub_def flat_lub_def by(auto 9 2)
*)

declaration \<open>Partial_Function.init "bd" \<^term>\<open>bd.fixp_fun\<close>
  \<^term>\<open>bd.mono_body\<close> @{thm bd.fixp_rule_uc} @{thm bd.fixp_induct_uc}
  (NONE)\<close> (*SOME @{thm fixp_induct_option}*)

\<comment> \<open>Define basics here\<close>
(*
return, fail(bottom?)
ite, bind (derive?), (derive) then, else, etc


For partial function needs a parameter, add a unit/dummy parameter
*)

\<comment> \<open>problem here, the types are all wrong. a expects a str+'a, but we get a str+('a+'c)\<close>
\<comment> \<open>This might be resolvable, but I'll have to think about it more.\<close>
definition ite :: "'a bd_aux \<Rightarrow> ('a \<Rightarrow> 'b bd) \<Rightarrow> 'c bd_aux \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a + 'c) bd" where
  "ite a a2b c b2a i = (
      case i of
        \<comment> \<open>parsing\<close>
        Inl l \<Rightarrow> undefined
        \<comment> \<open>printing 'a\<close>
      | Inr (Inl rl) \<Rightarrow> undefined
        \<comment> \<open>printing 'c\<close>
      | Inr (Inr rr) \<Rightarrow> c rr

)"


end