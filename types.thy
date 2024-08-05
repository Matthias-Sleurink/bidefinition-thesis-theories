theory types
  imports Main
          HOL.Partial_Function
          "HOL-Library.Complete_Partial_Order2"

          \<comment> \<open>This must be imported last as Eisbach ruins the simpset when imported before cpo2\<close>
          "HOL-Eisbach.Eisbach" \<comment> \<open>For the method bidef_init\<close>
begin

section \<open>Introduction\<close>
text  \<open>
To reduce Isabelle startup times we will split out most things into their own files.
This will help Isabelle proof as many things as possible in parallel,
and will also clarify the source dependencies.
\<close>

section \<open>Types for the parser\<close>

type_synonym '\<alpha> parse_result = "('\<alpha> \<times> string)"

\<comment> \<open>The outer option defines termination,
    The inner option defines parsing success\<close>
type_synonym '\<alpha> parser = "string \<Rightarrow> '\<alpha> parse_result option option"

\<comment> \<open>this is to make the parsers easier to write.
   Some (Some xyz) can be confusing to read, so we can use this to help explain what's what..\<close>
definition terminate_with where [simp]: "terminate_with = Some"


section \<open>NER\<close>
text \<open>NEW lemmas are lemmas about the Nonterm, Error, and Result state of the parsers.
      These lemmas aim to shortcut the source of the parser to jump to the result.
      This simplifies proofs using the parsers and combinators.
\<close>

named_theorems NER_simps
named_theorems NER_high_level_simps
text \<open>The high level simps are tried before the NER_simps,
      this allows us to have rules for a combinator,
      and also have rules for specific invocations of a combinator.\<close>

definition is_nonterm :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> bool" where
  "is_nonterm p i \<longleftrightarrow> p i = None"

definition is_error :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> bool" where
  "is_error p i \<longleftrightarrow> p i = Some None"

definition has_result :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "has_result p i r l \<longleftrightarrow> p i = Some (Some (r, l))"

definition has_result_c :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "has_result_c p c r l \<longleftrightarrow> has_result p (c@l) r l"

definition has_result_ci :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> string \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "has_result_ci p i c r l \<longleftrightarrow> has_result_c p c r l \<and> i = c@l"

lemma leftover_determ:
  assumes "has_result p i r l"
  assumes "has_result p i r l'"
  shows "l = l'"
  using assms unfolding has_result_def
  by clarsimp

lemma result_leftover_determ:
  assumes "has_result p i r  l"
  assumes "has_result p i r' l'"
  shows "r = r' \<and> l = l'"
  using assms unfolding has_result_def
  by clarsimp


lemma bottom_has_result[NER_simps, cont_intro]:
  "has_result (\<lambda>a. None) i r l \<longleftrightarrow> False"
  by (clarsimp simp add: has_result_def)
lemma bottom_is_error[NER_simps, cont_intro]:
  "is_error (\<lambda>a. None) i \<longleftrightarrow> False"
  by (clarsimp simp add: is_error_def)
lemma bottom_is_nonterm[NER_simps, cont_intro]:
  "is_nonterm (\<lambda>a. None) i \<longleftrightarrow> True"
  by (clarsimp simp add: is_nonterm_def)



\<comment> \<open>list_upto is important for instantiating the existentials in has_result_c proofs\<close>
fun dropLastN :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "dropLastN a l = take (length l - a) l"

definition list_upto :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_upto longer shorter = dropLastN (length shorter) longer"

lemma list_upto_simps[simp]:
  "list_upto l l = []"
  by (clarsimp simp add: list_upto_def)

lemma hd_list_upto:
  assumes "length longer > length shorter"
  assumes "P (hd longer)"
  shows "P (hd (list_upto longer shorter))"
  using assms
  by (induction longer; clarsimp simp add: list_upto_def)
  

lemma list_upto_take_cons:
  assumes "\<exists>c. l = c@s"
  assumes "l' = list_upto l s"
  shows "l' @ s = l"
  using assms
  apply (induction s arbitrary: l l')
  subgoal by (simp add: list_upto_def)
  unfolding list_upto_def
  by force

lemma list_upto_cons_second:
  assumes "\<exists>c. l = c@s"
  shows "(list_upto l s) @ s = l"
  using list_upto_take_cons[OF assms, of \<open>list_upto l s\<close>]
  by fast

lemma list_upto_self:
  "list_upto (ca @ l) l = ca"
  unfolding list_upto_def
  by force
  

lemma has_result_implies_not_is_error:
  "has_result p i r l \<Longrightarrow> \<not> is_error p i"
  by (simp add: has_result_def is_error_def)

lemma has_result_implies_not_is_nonterm:
  "has_result p i r l \<Longrightarrow> \<not> is_nonterm p i"
  by (simp add: has_result_def is_nonterm_def)

lemma is_error_implies_not_has_result:
  "is_error p i \<Longrightarrow> (\<nexists> r l . has_result p i r l)"
  by (simp add: has_result_def is_error_def)

lemma is_nonterm_implies_not_has_result:
  "is_nonterm p i \<Longrightarrow> (\<nexists> r l . has_result p i r l)"
  by (simp add: has_result_def is_nonterm_def)

lemma has_result_exhaust:
  "\<not>is_error   p i \<and> \<not>is_nonterm p i            \<Longrightarrow> \<exists>r l. has_result p i r l"
  "\<not>is_error   p i \<and> (\<nexists>r l. has_result p i r l) \<Longrightarrow> is_nonterm p i"
  "\<not>is_nonterm p i \<and> (\<nexists>r l. has_result p i r l) \<Longrightarrow> is_error p i"
  subgoal unfolding is_error_def has_result_def is_nonterm_def by force
  using \<open>\<not> is_error p i \<and> \<not> is_nonterm p i \<Longrightarrow> \<exists>r l. has_result p i r l\<close>
  by blast+



text \<open>Some basic NER simps that are so quick to prove
      they are not worth splitting into their own file.\<close>

subsection \<open>NER for if\<close>
lemma if_is_nonterm[NER_simps]:
  "is_nonterm (if B then T else F) i \<longleftrightarrow> (if B then is_nonterm T i else is_nonterm F i)"
  by simp

lemma if_is_error[NER_simps]:
  "is_error (if B then T else F) i \<longleftrightarrow> (if B then is_error T i else is_error F i)"
  by simp

lemma if_has_result[NER_simps]:
  "has_result (if B then T else F) i r l \<longleftrightarrow> (if B then has_result T i r l else has_result F i r l)"
  by simp

lemma if_has_result_c[NER_simps]:
  "has_result_c (if B then T else F) c r l \<longleftrightarrow> (if B then has_result_c T c r l else has_result_c F c r l)"
  by simp

lemma if_has_result_ci:
  "has_result_ci (if B then T else F) i c r l \<longleftrightarrow> (if B then has_result_ci T i c r l else has_result_ci F i c r l)"
  by simp



subsection \<open>NER for inlined bind\<close>
lemma bind_is_nonterm[NER_simps]:
  "is_nonterm (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i \<longleftrightarrow> is_nonterm A i \<or> (\<exists>r l. has_result A i r l \<and> is_nonterm (B r) l)"
  by (simp add: is_nonterm_def has_result_def split: option.splits)

lemma bind_is_error[NER_simps]:
  "is_error (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i \<longleftrightarrow> is_error A i \<or> (\<exists>r l. has_result A i r l \<and> is_error (B r) l)"
  by (clarsimp simp add: is_error_def has_result_def split: option.splits)

lemma bind_has_result[NER_simps]:
  "has_result (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i r l \<longleftrightarrow> (\<exists>r' l'. has_result A i r' l' \<and> has_result (B r') l' r l)"
  by (clarsimp simp add: has_result_def split: option.splits)

\<comment> \<open>Version for has_result_c and has_result_ci are later since they depend on PNGI\<close>



section \<open>Types for the printer\<close>
type_synonym '\<alpha> printer = "'\<alpha> \<Rightarrow> string option option"

section \<open>FP NER\<close>
definition p_has_result :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "p_has_result fp v s \<longleftrightarrow> fp v = Some (Some s)"

definition p_is_error :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "p_is_error fp v \<longleftrightarrow> fp v = Some None"

definition p_is_nonterm :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "p_is_nonterm fp v \<longleftrightarrow> fp v = None"

named_theorems fp_NER
named_theorems print_empty \<comment> \<open>Used mainly for FPCI below\<close>

lemma p_has_result_deterministic: \<comment> \<open>it might be worth it also doing these for the others.\<close>
  assumes "p_has_result pri i r"
  assumes "p_has_result pri i r'"
  shows "r = r'"
  using assms unfolding p_has_result_def
  by simp

lemma p_has_result_impl_not_error:
  "p_has_result fp v s \<Longrightarrow> \<not>p_is_error fp v"
  unfolding p_has_result_def p_is_error_def
  by simp

lemma p_is_error_impl_not_result:
  "p_is_error fp v \<Longrightarrow> \<nexists> s. p_has_result fp v s"
  unfolding p_is_error_def p_has_result_def
  by simp

lemma p_has_result_eq_not_is_error:
  "(\<exists> s. p_has_result fp v s) \<longleftrightarrow> \<not>p_is_error fp v \<and> \<not>p_is_nonterm fp v"
  unfolding p_is_error_def p_has_result_def p_is_nonterm_def
  by auto

lemma p_has_result_bottom[fp_NER, cont_intro]:
  "p_has_result (\<lambda>a. None) e i \<longleftrightarrow> False"
  by (clarsimp simp add: p_has_result_def)

lemma p_is_error_bottom[fp_NER, cont_intro]:
  "p_is_error (\<lambda>a. None) e \<longleftrightarrow> False"
  by (clarsimp simp add: p_is_error_def)

lemma p_is_nonterm_bottom[fp_NER, cont_intro]:
  "p_is_nonterm (\<lambda>a. None) e \<longleftrightarrow> True"
  by (clarsimp simp add: p_is_nonterm_def)



section \<open>Underlying bidefinition type\<close>
type_synonym 'a bd_aux = "(string + 'a) \<Rightarrow> ((('a \<times> string) option) + (string option)) option"

definition wf_bd_aux :: "'a bd_aux \<Rightarrow> bool" where
  "wf_bd_aux bd \<longleftrightarrow> ( \<forall> s r. bd (Inl s) = Some r \<longrightarrow> isl r) \<and> (\<forall> t r. (bd (Inr t) = Some r \<longrightarrow> \<not>isl r))"

definition first :: "'a bd_aux \<Rightarrow> 'a parser" where
  "first bd s = map_option projl (bd (Inl s))"

definition second :: "'a bd_aux \<Rightarrow> 'a printer" where
  "second bd s = map_option projr (bd (Inr s))"

fun bdc_aux :: "'a parser \<Rightarrow> 'a printer \<Rightarrow> 'a bd_aux" where
  "bdc_aux parser printer (Inl s) = map_option Inl (parser s)"
| "bdc_aux parser printer (Inr t) = map_option Inr (printer t)"

lemma bdc_aux_def:
  "bdc_aux parser printer = (\<lambda> Inl s \<Rightarrow> map_option Inl (parser s) | Inr t \<Rightarrow> map_option Inr (printer t))"
  by (auto simp add: fun_eq_iff split: sum.splits)

lemma bdc_first_second:
  "first (bdc_aux p pr) = p"
  "second (bdc_aux p pr) = pr"
  unfolding first_def second_def bdc_aux_def
  by (auto simp add: fun_eq_iff map_option.compositionality comp_def map_option.identity)

lemma bdc_aux_tuple:
  "wf_bd_aux bd \<Longrightarrow> wf_bd_aux bd' \<Longrightarrow> first bd = first bd' \<Longrightarrow> second bd = second bd' \<Longrightarrow> bd = bd'"
  unfolding bdc_aux_def first_def second_def wf_bd_aux_def
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

lemma bdc_aux_first_second:
  assumes "wf_bd_aux bd"
  shows "bdc_aux (first bd) (second bd) = bd"
  using assms
  apply (auto simp add: bdc_aux_def wf_bd_aux_def fun_eq_iff first_def second_def map_option.compositionality split: sum.splits)
  by (simp add: map_option_cong option.map_ident)+

lemma bd_aux_wf_bdc:
  "wf_bd_aux (bdc_aux pa pr)"
  unfolding bdc_aux.simps wf_bd_aux_def
  by auto

abbreviation bd_aux_ord :: "'a bd_aux \<Rightarrow> 'a bd_aux \<Rightarrow> bool" where "bd_aux_ord \<equiv> fun_ord (flat_ord None)"

lemma bd_aux_ord_f_f:
  assumes "wf_bd_aux bd"
  assumes "wf_bd_aux bd'"
  shows "bd_aux_ord bd bd' \<longleftrightarrow> fun_ord (flat_ord None) (first bd) (first bd') \<and> fun_ord (flat_ord None) (second bd) (second bd')"
  using assms
  unfolding wf_bd_aux_def
            fun_ord_def flat_ord_def first_def second_def
  apply auto
  by (smt (z3) assms(1) assms(2) bdc_aux.simps(1) bdc_aux.simps(2) bdc_aux_first_second first_def second_def set_sum_sel(1) setl.cases sum.collapse(2))

definition bd_aux_lub :: "'a bd_aux set \<Rightarrow> 'a bd_aux" where "bd_aux_lub = fun_lub (flat_lub None)"


\<comment> \<open> 1. \<And>x1. \<forall>bd\<in>s. (\<forall>s r. bd (Inl s) = Some r \<longrightarrow> isl r) \<and> (\<forall>t r. bd (Inr t) = Some r \<longrightarrow> \<not> isl r) \<Longrightarrow>
          option_lub {y. \<exists>f\<in>s. y = f (Inl x1)} =
          map_option Inl (option_lub {y. \<exists>f\<in>s. y = map_option projl (f (Inl x1))})\<close>


lemma map_option_trans:
  assumes "\<forall>bd \<in> s. wf_bd_aux bd"
  shows "{y. \<exists>f\<in>s. y = f (Inl x1)} = map_option Inl ` {y. \<exists>f\<in>s. y = map_option projl (f (Inl x1))}"
  using assms
  apply (auto simp add: wf_bd_aux_def)
  by (smt (verit, best) assms bdc_aux.simps(1) bdc_aux_first_second first_def image_eqI mem_Collect_eq)+


lemma map_option_trans2:
  assumes "\<forall>bd \<in> s. wf_bd_aux bd"
  shows "{y. \<exists>f\<in>s. y = f (Inr x1)} = map_option Inr ` {y. \<exists>f\<in>s. y = map_option projr (f (Inr x1))}"
  using assms
  apply (auto simp add: wf_bd_aux_def)
  by (smt (verit, best) assms bdc_aux.simps(2) bdc_aux_first_second second_def image_eqI mem_Collect_eq)+

lemma flat_lub_map_option:
  assumes "Complete_Partial_Order.chain option_ord s"
  shows "flat_lub None (map_option f ` s) = map_option f (flat_lub None s)"
  using assms
  by (smt (verit) chain_imageI flat_lub_in_chain flat_ord_def image_iff option.lub_upper option.simps(8))


lemma bd_lub_componentwise:
  assumes "Complete_Partial_Order.chain (fun_ord option_ord) s"
  assumes "\<forall>bd \<in> s. wf_bd_aux bd"
  shows "bd_aux_lub s = bdc_aux (fun_lub (flat_lub None) (first ` s)) (fun_lub (flat_lub None) (second ` s))"
  unfolding wf_bd_aux_def bdc_aux_def bd_aux_lub_def
            fun_lub_def first_def second_def
  apply (auto simp add: fun_eq_iff map_option_trans assms(2) map_option_trans2 split: sum.splits)
  subgoal
    apply (subst flat_lub_map_option)
    subgoal
      using assms(1)
      by (smt (verit) CollectD chain_def flat_ord_def fun_ord_def option.map_disc_iff)
    by simp
  subgoal 
    apply (subst flat_lub_map_option)
    subgoal
      using assms(1)
      by (smt (verit) CollectD chain_def flat_ord_def fun_ord_def option.map_disc_iff)
    by simp
  done


section \<open>Bidefinition types\<close>


typedef 'a bd = "Collect wf_bd_aux :: 'a bd_aux set"
  apply (rule exI[of _ \<open>\<lambda>x. None\<close>])
  by (simp add: wf_bd_aux_def)

setup_lifting type_definition_bd

lift_definition parse :: "'a bd \<Rightarrow> 'a parser" is first .
lift_definition print :: "'a bd \<Rightarrow> 'a printer" is second .
lift_definition bdc :: "'a parser \<Rightarrow> 'a printer \<Rightarrow> 'a bd" is bdc_aux by (simp add: bd_aux_wf_bdc)

definition bd_ord :: "'a bd \<Rightarrow> 'a bd \<Rightarrow> bool" where
  "bd_ord bd bd' \<longleftrightarrow> fun_ord (flat_ord None) (parse bd) (parse bd') \<and> fun_ord (flat_ord None) (print bd) (print bd')"

definition bd_lub :: "'a bd set \<Rightarrow> 'a bd" where
  "bd_lub s = bdc (fun_lub (flat_lub None) (parse ` s)) (fun_lub (flat_lub None) (print ` s))"


lemma bdc'_tuple:
  "parse bd = parse bd' \<Longrightarrow> print bd = print bd' \<Longrightarrow> bd = bd'"
  apply transfer
  by (simp add: bdc_aux_tuple)

lemma bdc_parse_print_all[simp]:
  shows "bdc (parse bd) (print bd) = bd"
  apply transfer
  by (simp add: bdc_aux_first_second)

lemma pp_bdc'[simp]:
  "parse (bdc p pr) = p"
  "print (bdc p pr) = pr"
   by (transfer; (simp_all add: bdc_first_second))+

lemma bd_lub_aux_trans:
  assumes "Complete_Partial_Order.chain (fun_ord option_ord) (Rep_bd ` s)"
  shows "bd_lub s = Abs_bd (fun_lub (flat_lub None) (Rep_bd ` s))"
  unfolding bd_lub_def
  apply (subst bd_lub_componentwise[unfolded bd_aux_lub_def])
  subgoal by (simp add: assms)
  subgoal apply simp
    using Rep_bd by blast
  apply (simp add: bdc.abs_eq)
  apply transfer
  by fastforce



lifting_update bd.lifting
lifting_forget bd.lifting

lemma bdc_eq_iff:
  "bdc a b = bdc a' b' \<longleftrightarrow> a=a' \<and> b=b'"
  by (metis pp_bdc'(1) pp_bdc'(2))

lemma bd_eq_iff:
  "a = b \<longleftrightarrow> (parse a = parse b) \<and> (print a = print b)"
  using bdc'_tuple by auto


lemma bd_ord_f:
  "bd_ord a b = fun_ord (flat_ord None) (Rep_bd a) (Rep_bd b)"
  by (metis Rep_bd bd_aux_ord_f_f bd_ord_def mem_Collect_eq parse.rep_eq print.rep_eq)

lemma partial_fun_defs_cong:
  assumes "partial_function_definitions ord lub"
  assumes "\<forall>c. Complete_Partial_Order.chain (ord) c \<longrightarrow> lub c = lub' c"
  shows "partial_function_definitions ord lub'"
proof -
  interpret partial_function_definitions ord lub by fact
  show ?thesis
    apply unfold_locales
    subgoal
      using leq_refl by blast
    subgoal
      using leq_trans by blast
    subgoal
      using leq_antisym by blast
    subgoal 
      using assms(2) lub_upper by force
    subgoal
      using assms(2) lub_least by force
    done
qed

lemma bd_partial_function_definitions:
  "partial_function_definitions bd_ord bd_lub"
  unfolding partial_function_definitions_def
  apply auto
  subgoal by (simp add: bd_ord_f fun_ord_def option.leq_refl)
  subgoal
    unfolding bd_ord_f
    using flat_interpretation partial_function_definitions.leq_trans partial_function_lift by fastforce
  subgoal
    by (meson bd_ord_def bdc'_tuple option.partial_function_definitions_axioms partial_function_definitions.leq_antisym partial_function_lift)
  subgoal
    unfolding bd_ord_f
    using bd_lub_aux_trans
    by (smt (verit) CollectD Rep_bd Rep_bd_inverse bd_aux_lub_def bd_lub_componentwise bdc.rep_eq chain_imageI imageE image_eqI option.partial_function_definitions_axioms partial_function_definitions_def partial_function_lift)
  subgoal
    unfolding bd_ord_f
    using bd_lub_aux_trans
    by (smt (verit) CollectD Rep_bd Rep_bd_inverse bd_aux_lub_def bd_lub_componentwise bdc.rep_eq chain_imageI imageE option.partial_function_definitions_axioms partial_function_definitions.lub_least partial_function_lift)
  done

lemma bd_lub_bdc:
  "bd_lub {} = bdc (\<lambda>_. None) (\<lambda>_. None)"
  unfolding bd_lub_def flat_lub_def
  by clarsimp

interpretation bd:
  partial_function_definitions "bd_ord" "bd_lub"
  rewrites "bd_lub {} \<equiv> bdc (\<lambda>_. None) (\<lambda>_. None)"
  by (clarsimp simp add: bd_partial_function_definitions bd_lub_bdc)+
print_theorems
abbreviation "mono_bd \<equiv> monotone (fun_ord bd_ord) bd_ord"

\<comment> \<open>TODO: We don't have a fixp_induct rule.\<close>
declaration \<open>Partial_Function.init "bd" \<^term>\<open>bd.fixp_fun\<close>
  \<^term>\<open>bd.mono_body\<close> @{thm bd.fixp_rule_uc} @{thm bd.fixp_strong_induct_uc} (*was: fixp_induct_uc*)
  (NONE)\<close> (*SOME @{thm bd.fixp_strong_induct_uc} or NONE*)

\<comment> \<open>This is the same prover that the partial_function package uses under the hood to proof mono for function bodies.\<close>
method_setup pf_mono_prover = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Partial_Function.mono_tac ctxt))\<close> \<open>Monotonicity prover of the partial function package.\<close>

lemma mono_bdc_const[partial_function_mono]:
  shows "mono_bd (\<lambda>f. (bdc parser printer))"
  by pf_mono_prover

\<comment> \<open>Old typename fix\<close>
type_synonym '\<alpha> bidef = "'\<alpha> bd"



section \<open>PASI, PNGI\<close>
named_theorems PASI_PNGI
named_theorems PASI_PNGI_intros

\<comment> \<open>Do for this subgoal and repeat for each newly created subgoal, try to solve via assumption, if not, apply an intro rule, if not, use mp with intro rule, if not, use clarsimp with PASI_PNGI_intros.\<close>
method pasi_pngi = (repeat_new \<open>assumption | rule PASI_PNGI_intros |  rule mp, rule PASI_PNGI_intros | clarsimp simp add: PASI_PNGI_intros\<close>)


\<comment> \<open>PASI, Parser Always Shrinks Input (Including it being a tail of the input)\<close>
definition PASI :: "'\<alpha> parser \<Rightarrow> bool" where
  "PASI p \<longleftrightarrow> (\<forall> i r l. has_result p i r l \<longrightarrow> (\<exists> c. (i = c @ l \<and> c \<noteq> [])))"

\<comment> \<open>PNGI, Parser Never Grows Input (Including it being a tail of the input)\<close>
definition PNGI :: "'\<alpha> parser \<Rightarrow> bool" where
  "PNGI p \<longleftrightarrow> (\<forall> i r l. has_result p i r l \<longrightarrow> (\<exists> c. i = c @ l))"


lemma PASI_as_has_result:
  assumes "PASI p"
  shows "has_result p i r l \<longrightarrow> length i > length l"
  using assms PASI_def
  by fastforce

lemma PNGI_as_has_result:
  assumes "PNGI p"
  shows "has_result p i r l \<longrightarrow> length i \<ge> length l"
  using assms PNGI_def
  by fastforce

lemma PNGI_empty_int_empty_res:
  assumes "PNGI p"
  shows "has_result p [] r l \<longrightarrow> l = []"
  using assms unfolding PNGI_def by blast

\<comment> \<open>This would not be bad to have in the PASI intros, but it's also not great since this almost always applies, but is basically never the solution.\<close>
\<comment> \<open>Can we somehow set this up such that it is only applied if we know PASI from an assm?\<close>
lemma PASI_implies_PNGI:
  "PASI p \<longrightarrow> PNGI p"
  using PASI_def PNGI_def
  by fast

lemma PASI_implies_PNGI_meta:
  "PASI p \<Longrightarrow> PNGI p"
  using PASI_def PNGI_def
  by fast


lemma PASI_implies_res_length_shorter:
  assumes "PASI p"
  shows "has_result p i r l \<longrightarrow> length i > length l"
  using PASI_def assms
  by fastforce

lemma PASI_implies_no_result_from_empty:
  assumes "PASI p"
  shows "\<not>has_result p [] r l"
  using PASI_def assms
  by fast

lemma PASI_implies_error_from_empty:
  assumes "PASI p"
  assumes "\<not>is_nonterm p []"
  shows "is_error p []"
  using assms(2)
        PASI_implies_no_result_from_empty[OF assms(1)]
        has_result_exhaust(3)
  by blast

lemma if_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PNGI (parse T)"
  assumes "PNGI (parse F)"
  shows "PNGI (parse (if P then T else F))"
  by (simp add: assms)

lemma if_PNGI_p[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PNGI (parse (T p))"
  assumes "PNGI (parse (F p))"
  shows "PNGI (parse (if P p then T p else F p))"
  using assms
  by (rule if_PNGI)

lemma if_PASI[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PASI (parse T)"
  assumes "PASI (parse F)"
  shows "PASI (parse (if P then T else F))"
  by (simp add: assms)

lemma if_PASI_p[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PASI (parse (T p))"
  assumes "PASI (parse (F p))"
  shows "PASI (parse (if P p then T p else F p))"
  using assms
  by (rule if_PASI)



lemma bind_has_result_c_isar:
  assumes "PNGI A"
  assumes "\<And>r. PNGI (B r)"
  shows "has_result_c (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) c r l
        \<longleftrightarrow> (\<exists>r' c' c''. c = (c'@c'') \<and> has_result_c A c' r' (c''@l) \<and> has_result_c (B r') c'' r l)"
  unfolding has_result_c_def
  apply (subst bind_has_result[of B A \<open>c@l\<close> r l])
  unfolding has_result_def
  apply auto
  subgoal for r' l'
  proof -
    assume A: "A (c @ l) = Some (Some (r', l'))"
    assume B: "B r' l' = Some (Some (r, l))"

    obtain c1 where P1: "c@l = c1@l'" by (metis A PNGI_def assms(1) has_result_def)
    obtain c2 where P2: "l' = c2@l" by (metis B PNGI_def assms(2) has_result_def)

    have C: "c1 @ c2 = c" using P1 P2 by simp
    have D: "has_result A (c1@c2@l) r' (c2@l)" by (metis A P1 P2 has_result_def)

    from A B C D show ?thesis
      unfolding has_result_def
      apply clarsimp
      apply (rule exI[of _ r'])
      apply (rule exI[of _ c1])
      apply (rule exI[of _ c2])
      using assms[unfolded PNGI_def has_result_def]
      by auto
    qed
  done


lemma bind_has_result_c[NER_simps]:
  assumes "PNGI A"
  assumes "\<And>r. PNGI (B r)"
  shows "has_result_c (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) c r l
        \<longleftrightarrow> (\<exists>r' c' c''. c = (c'@c'') \<and> has_result_c A c' r' (c''@l) \<and> has_result_c (B r') c'' r l)"
  unfolding has_result_c_def
  apply (subst bind_has_result[of B A \<open>c@l\<close> r l])
  unfolding has_result_def
  apply auto
  subgoal for r' l'
    apply (rule exI[of _ r'])
    by (metis PNGI_def append.assoc append_same_eq assms(1) assms(2) has_result_def)
  done


lemma bind_has_result_ci:
  assumes "PNGI A"
  assumes "\<And>r. PNGI (B r)"
  shows "has_result_ci (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i c r l \<longleftrightarrow>
          (\<exists>r' l' c' c''. c = c'@c'' \<and> has_result_ci A i c' r' l' \<and> has_result_ci (B r') l' c'' r l)"
  unfolding has_result_ci_def has_result_c_def has_result_def
  using bind_has_result[of B A i r l]
        assms[unfolded PNGI_def has_result_def]
  apply (auto split: option.splits)
  subgoal by fastforce
  subgoal by fastforce
  done


section \<open>Well formed\<close>

definition parser_can_parse_print_result :: "'\<alpha> parser \<Rightarrow> '\<alpha> printer \<Rightarrow> bool" where
  "parser_can_parse_print_result par pri \<longleftrightarrow>
      (\<forall>(t :: '\<alpha>) pr. p_has_result pri t pr \<longrightarrow> has_result par pr t [])"

\<comment> \<open>note how due to the parse '015' = 15 print 15 = '15' issue we cannot attach the text here.\<close>
definition printer_can_print_parse_result :: "'\<alpha> parser \<Rightarrow> '\<alpha> printer \<Rightarrow> bool" where
  "printer_can_print_parse_result par pri \<longleftrightarrow>
      (\<forall>(t :: '\<alpha>) i l. has_result par i t l \<longrightarrow> (\<exists>pr. p_has_result pri t pr))"


definition bidef_well_formed :: "'\<alpha> bidef \<Rightarrow> bool" where
  "bidef_well_formed bi = (PNGI (parse bi) \<and>
                           parser_can_parse_print_result (parse bi) (print bi) \<and>
                           printer_can_print_parse_result (parse bi) (print bi)
                           )"
named_theorems bi_well_formed_simps

\<comment> \<open>The idea is to do get_pngi[of assms(...)]\<close>
lemma get_pngi:
  assumes "bidef_well_formed a"
  shows "PNGI (parse a)"
  using assms[unfolded bidef_well_formed_def]
  by blast

lemma get_pngi_unfold:
  assumes "bidef_well_formed a"
  shows "\<forall> i r l. has_result (parse a) i r l \<longrightarrow> (\<exists> c. i = c @ l)"
  using assms[unfolded bidef_well_formed_def] PNGI_def
  by fast

lemma test: \<comment> \<open>Shows that you can apply it in this way.\<close>
  assumes "bidef_well_formed a"
  shows "PNGI (parse a)"
  by (rule get_pngi[OF assms(1)])

lemma get_parser_can_parse:
  assumes "bidef_well_formed a"
  shows "parser_can_parse_print_result (parse a) (print a)"
  using assms[unfolded bidef_well_formed_def]
  by blast

lemma get_parser_can_parse_unfold:
  assumes "bidef_well_formed a"
  shows "(\<forall>(t :: '\<alpha>) pr. p_has_result (print a) t pr \<longrightarrow> has_result (parse a) pr t [])"
  using assms[unfolded bidef_well_formed_def parser_can_parse_print_result_def]
  by blast

lemma get_printer_can_print:
  assumes "bidef_well_formed a"
  shows "printer_can_print_parse_result (parse a) (print a)"
  using assms[unfolded bidef_well_formed_def]
  by blast

lemma get_printer_can_print_unfold:
  assumes "bidef_well_formed a"
  shows "(\<forall>(t :: '\<alpha>) i l. has_result (parse a) i t l \<longrightarrow> (\<exists>pr. p_has_result (print a) t pr))"
  using assms[THEN get_printer_can_print, unfolded printer_can_print_parse_result_def]
  by blast


lemma conjI3:
  "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> A \<and> B \<and> C"
  by blast

method wf_init = ((simp only: bidef_well_formed_def); (rule conjI3))

lemma print_results_always_same:
  assumes "p_has_result printer ojb res1"
  assumes "p_has_result printer ojb res2"
  shows "res1 = res2"
  using assms
  by (simp add: p_has_result_def)


lemma print_result_is_canon_result:
  assumes "bidef_well_formed bd"
  assumes "p_has_result (print bd) obj canon"
  shows "has_result (parse bd) canon obj []"
  using assms
  by (simp add: bidef_well_formed_def parser_can_parse_print_result_def)

lemma print_result_is_canon_result2:
  assumes "bidef_well_formed bd"
  assumes "p_has_result (print bd) obj canon"
  assumes "has_result (parse bd) canon obj2 []"
  shows "obj = obj2"
  using assms
  unfolding bidef_well_formed_def parser_can_parse_print_result_def
  by (simp add: p_has_result_def has_result_def)

lemma wf_pasi_no_empty_print:
  assumes wf_a: "bidef_well_formed A"
  assumes pa_a: "PASI (parse A)"
  shows "\<nexists> i. p_has_result (print A) i []"
  using PASI_implies_no_result_from_empty[OF pa_a]
        wf_a[THEN get_parser_can_parse_unfold]
  by blast



section \<open>Charset, first_chars\<close>
\<comment> \<open>Charset\<close>
text \<open>
The idea here is that a parser has a set of characters it can parse.
And a printer has a set of characters that can be the first in a print result.
So, we can set up non-interference, if there is no overlap.
\<close>

\<comment> \<open>This is an underestimation if your parser is not PNGI.\<close>
definition charset :: "'a parser \<Rightarrow> char set" where
  "charset p = \<Union> {set c | r l c. has_result p (c@l) r l}"

definition charset2 :: "'a parser \<Rightarrow> char set" where
  "charset2 p = \<Union> {set c | r l c. has_result_c p c r l}"

lemma charset_charset2:
  "charset = charset2"
  unfolding charset_def charset2_def has_result_c_def
  by simp

definition charset_must :: "'a parser \<Rightarrow> char set" where
  "charset_must p = \<Inter> {set c | r l c. has_result p (c@l) r l}"

definition charset_must2 :: "'a parser \<Rightarrow> char set" where
  "charset_must2 p = \<Inter> {set c | r l c. has_result_c p c r l}"

lemma charset_must_charset_must2:
  "charset_must = charset_must2"
  unfolding charset_must_def charset_must2_def has_result_c_def
  by simp

definition first_chars :: "'a printer \<Rightarrow> char set" where
  "first_chars p = {hd pr | i pr. p_has_result p i pr \<and> pr \<noteq> []}"


lemma charset_first_chars:
  assumes "(charset parser \<inter> first_chars printer) = {}"
  assumes "p_has_result printer i ipr"
  assumes "PASI parser"
  shows "\<not>(\<exists>r l. has_result parser ipr r l)"
  using assms[unfolded charset_def first_chars_def PASI_def]
  apply clarsimp
  subgoal for r l
    apply (cases \<open>l = ipr\<close>)
    subgoal (* l = ipr *) by fast
    using iffD1[OF PASI_def assms(3), rule_format, of ipr r l]
    by force
  done

lemma in_charset_eq_exists_result:
  "c \<in> charset parser \<longleftrightarrow> (\<exists>cs r l. has_result parser (cs@l) r l \<and> c \<in> set cs)"
  unfolding charset_def
  by blast

lemma in_charset_eq_exists_result_c:
  "c \<in> charset parser \<longleftrightarrow> (\<exists>cs r l. has_result_c parser cs r l \<and> c \<in> set cs)"
  unfolding charset_def has_result_c_def
  by blast


\<comment> \<open>Some extension of this where ipr must be in leftover if we feed it t@ipr?\<close>
lemma charset_first_chars:
  assumes "(charset parser \<inter> first_chars printer) = {}"
  assumes "p_has_result printer i ipr"
  assumes "PNGI parser"
  assumes "has_result parser (t@ipr@t') r l"
  \<comment> \<open>Basically, ipr cannot be in the consumed chars.\<close>
  shows "\<exists>t''. l = t''@ipr@t'"
  oops

lemma charset_not_in_c:
  assumes "(charset parser \<inter> first_chars printer) = {}"
  assumes "p_has_result printer i ipr"
  assumes "ipr \<noteq> []"
  assumes "has_result_c parser c r l"
  shows "hd ipr \<notin> set c"
  using assms
  unfolding charset_charset2
            charset2_def first_chars_def
  by blast



\<comment> \<open>Characters that cannot extend\<close>
named_theorems peek_past_end_simps
definition does_not_peek_past_end :: "'a parser \<Rightarrow> bool" where
  "does_not_peek_past_end p \<longleftrightarrow> (\<forall> c r l l'. has_result p (c@l) r l \<longrightarrow> has_result p (c@l') r l')"

lemma no_peek_past_end_wf_stronger:
  assumes "does_not_peek_past_end (parse A)"
  assumes "bidef_well_formed A"
  assumes "p_has_result (print A) i ipr"
  shows "\<And>cs. has_result (parse A) (ipr@cs) i cs"
  using assms[unfolded does_not_peek_past_end_def bidef_well_formed_def parser_can_parse_print_result_def]
  apply auto
  by (metis append.right_neutral)

lemma consecutive_parses_proof_for_thesis:
  assumes wfa: "bidef_well_formed A"
  assumes wfb: "bidef_well_formed B"
  assumes dnppea: "does_not_peek_past_end (parse A)"
  assumes printeda: "p_has_result (print A) a ar"
  assumes printedb: "p_has_result (print B) b br"
  shows "has_result (parse A) (ar@br) a br \<and> has_result (parse B) br b []"
  apply (insert printeda printedb)
  apply (rule conjI)
  subgoal
    apply (insert dnppea[unfolded does_not_peek_past_end_def, rule_format, of ar \<open>[]\<close> a br, simplified])
    apply (insert wfa[THEN get_parser_can_parse_unfold, rule_format, of a ar])
    by blast
  subgoal
    using wfb[THEN get_parser_can_parse_unfold]
    by blast
  done



(*Attempt 3, hd being a partial function is biting us in the ass, so let's not use it.*)
definition does_not_consume_past_char3 :: "'a parser \<Rightarrow> char \<Rightarrow> bool" where
  "does_not_consume_past_char3 p ch \<longleftrightarrow> (\<forall>c r l l'.
         has_result p (c@l) r l \<longrightarrow> (has_result p c r [] \<and> has_result p (c@(ch#l')) r (ch#l')))"

lemma no_consume_past3_wf_stronger:
  assumes "does_not_consume_past_char3 (parse A) ch"
  assumes "bidef_well_formed A"
  assumes "p_has_result (print A) i ipr"
  shows "\<And>cs. cs=[] \<or> hd cs = ch \<longrightarrow> has_result (parse A) (ipr@cs) i cs"
  subgoal for cs
    using assms(1)[unfolded does_not_consume_past_char3_def, rule_format, of ipr \<open>[]\<close> i cs]
          assms(2)[THEN get_parser_can_parse_unfold, rule_format, of i \<open>ipr@[]\<close>]
          assms(3)
    by (metis append.right_neutral assms(1) does_not_consume_past_char3_def list.collapse)
  done


lemma does_not_consume_past_any_char3_eq_not_peek_past_end:
  shows "(\<forall>ch. does_not_consume_past_char3 A ch) \<longleftrightarrow> does_not_peek_past_end A"
  unfolding does_not_consume_past_char3_def does_not_peek_past_end_def
  by (metis neq_Nil_conv self_append_conv)

lemma dnppe_implies_dncpc:
  assumes "does_not_peek_past_end A"
  shows "does_not_consume_past_char3 A c"
  using assms does_not_consume_past_any_char3_eq_not_peek_past_end by blast


section \<open>Does not consume past consumed by other parser\<close>
definition does_not_consume_past_parse_consume :: "'a parser \<Rightarrow> 'b parser \<Rightarrow> bool" where
  "does_not_consume_past_parse_consume p p' \<longleftrightarrow> (\<forall>c r l l' c2 r2 l2.
         has_result p (c@l) r l \<and> has_result p' (c2@l2) r2 l2 \<longrightarrow> (has_result p c r [] \<and> has_result p (c@(c2@l')) r (c2@l')))"

definition does_not_conusme_past_parse_consume_or_if_empty :: "'a parser \<Rightarrow> 'b parser \<Rightarrow> 'c parser \<Rightarrow> bool" where
  "does_not_conusme_past_parse_consume_or_if_empty A B C \<longleftrightarrow> (\<forall> c r l c2 r2 l2 c3 r3 l3 l' l''.
        has_result A (c@l) r l \<longrightarrow> has_result B (c2@l2) r2 l2 \<longrightarrow> has_result C (c3@l3) r3 l3 \<longrightarrow> (has_result A c r [] \<and> (if c2 = [] then (has_result A (c@(c3@l')) r (c3@l')) else (has_result A (c@(c2@l'')) r (c2@l'')))))"




section \<open>First printed character\<close>
\<comment> \<open>Which characters can be the first printed char?\<close>
fun const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  "const a _ = a"

named_theorems fpci_simps
definition first_printed_chari :: "'a printer \<Rightarrow> 'a \<Rightarrow> char \<Rightarrow> bool" where
  "first_printed_chari p i c \<equiv> (\<exists>t. p_has_result p i t \<and> t\<noteq>[] \<and> (hd t) = c)"

lemma empty_result_means_no_first_char[fpci_simps]:
  assumes "p_has_result p i []"
  shows "first_printed_chari p i c \<longleftrightarrow> False"
  using assms unfolding first_printed_chari_def
  by (simp add: print_results_always_same)

lemma fpci_bottom[fpci_simps]:
  "first_printed_chari (\<lambda>_. None) i c \<longleftrightarrow> False"
  by (clarsimp simp add: first_printed_chari_def fp_NER)



section \<open>First parsed character\<close>
text \<open>The problem with fpci above is that more than just the printed text can be parsed.
      So, in some cases we only know that some text can be parsed, and then we know nothing applicable to fpci.
      Thus, we need to capture this info on the other side.\<close>
definition fpc :: "'a parser \<Rightarrow> 'a \<Rightarrow> char \<Rightarrow> bool" where
  "fpc p t c \<longleftrightarrow> (\<exists>cs l. has_result p (c#cs@l) t l)"

named_theorems fpc_simps

lemma fpci_implies_fpc:
  assumes "bidef_well_formed A"
  assumes "\<exists>i. first_printed_chari (print A) i c"
  shows "\<exists>i. fpc (parse A) i c"
  unfolding fpc_def
  using assms(2)[unfolded first_printed_chari_def]
  apply clarsimp
  subgoal for i t
    using assms(1)[THEN get_parser_can_parse_unfold, rule_format, of i t]
    apply clarsimp
    apply (rule exI[of _ i])
    apply (rule exI[of _ \<open>tl t\<close>])
    apply (rule exI[of _ \<open>[]\<close>])
    by clarsimp
  done


definition fpc2 :: "'a parser \<Rightarrow> char \<Rightarrow> bool" where
  "fpc2 p c \<longleftrightarrow> (\<exists>i r l. has_result p (c#i) r l)"

lemma fpci_implies_fpc2:
  assumes "bidef_well_formed A"
  assumes "\<exists>i. first_printed_chari (print A) i c"
  shows "fpc2 (parse A) c"
  unfolding fpc2_def
  using assms(2)[unfolded first_printed_chari_def]
  apply clarsimp
  subgoal for i t
    using assms(1)[THEN get_parser_can_parse_unfold, rule_format, of i t]
    apply clarsimp
    apply (rule exI[of _ \<open>tl t\<close>])
    apply (rule exI[of _ i])
    apply (rule exI[of _ \<open>[]\<close>])
    by clarsimp
  done

section \<open>chars_can_be_dropped\<close>
text \<open>The idea here is that some parsers may drop initial characters and still have the same result.
Consider for example the parser that removes all leading whitespace and the parses a non whitespace character.
For this parser it does not matter if a prefix is removed, as long as said prefix is whitespace only.\<close>
definition chars_can_be_dropped :: "'a parser \<Rightarrow> char set \<Rightarrow> bool" where
  "chars_can_be_dropped p cs = (\<forall> i r l. has_result p i r l \<longrightarrow> has_result p (dropWhile (\<lambda>c. c \<in> cs) i) r l)"


lemma no_consume_past_parse_from_no_consume_past_char_fpc:
  assumes change_leftover: "(\<exists>l2 r2. has_result (parse B) l2 r2 l2) \<Longrightarrow> (\<And>c l l' r. has_result (parse A) (c @ l) r l \<Longrightarrow> has_result (parse A) (c @ l') r l')"
  assumes fpc: "\<And>i c. fpc (parse B) i c \<Longrightarrow> does_not_consume_past_char3 (parse A) c"
  shows "does_not_consume_past_parse_consume (parse A) (parse B)"
  apply (clarsimp simp add: does_not_consume_past_parse_consume_def)
  subgoal for c r l l' c2 r2 l2
    apply (cases c2; clarsimp)
    subgoal
      using change_leftover[of c l r]
      by (metis append.right_neutral)
    subgoal for c2' c2s
      using fpc[unfolded fpc_def does_not_consume_past_char3_def, rule_format, of c2' r2 c l r \<open>c2s@l'\<close>]
      by blast
    done
  done



section \<open>Admissible\<close>
text \<open>These lemmas are needed for admissibility proving, which are required to use the induction rules for partial functions.\<close>


\<comment> \<open>TODO: move these to types\<close>
lemma mcont_parse[cont_intro]:
  "mcont bd.lub_fun bd.le_fun (flat_lub None) (flat_ord None) (\<lambda>x. parse (x U) i)"
  apply (rule)
  subgoal
    apply (rule monotoneI)
    by (simp add: bd_ord_def fun_ord_def)
  apply (rule cont_intro)
  unfolding bd_ord_def fun_ord_def
  apply (rule contI)
  unfolding bd_lub_def
  apply clarsimp
  by (smt (verit, ccfv_SIG) Inf.INF_cong fun_lub_apply image_image)

lemma mcont_print[cont_intro]:
  "mcont bd.lub_fun bd.le_fun (flat_lub None) (flat_ord None) (\<lambda>x. print (x U) i)"
  apply (rule)
  subgoal
    apply (rule monotoneI)
    by (simp add: bd_ord_def fun_ord_def)
  apply (rule cont_intro)
  unfolding bd_ord_def fun_ord_def
  apply (rule contI)
  unfolding bd_lub_def
  apply clarsimp
  by (smt (verit, ccfv_SIG) Inf.INF_cong fun_lub_apply image_image)

lemma admissible_PNGI[cont_intro]:
  "bd.admissible (\<lambda>expressionR. PNGI (parse (expressionR U)))"
  unfolding PNGI_def
  unfolding has_result_def
  by simp

lemma strict_PNGI[cont_intro]:
  "PNGI ((\<lambda>u. None))"
  by (simp add: PNGI_def has_result_def)


lemma admissible_PASI[cont_intro]:
  "bd.admissible (\<lambda>expressionR. PASI (parse (expressionR U)))"
  unfolding PASI_def
  unfolding has_result_def
  by simp

lemma strict_PASI[cont_intro]:
  "PASI ((\<lambda>u. None))"
  by (simp add: PASI_def has_result_def)


lemma admissible_no_empty_print_result[cont_intro]:
  "bd.admissible (\<lambda>r. \<not> p_has_result (print (r U)) e [])"
  unfolding p_has_result_def
  by simp



lemma admissible_parser_can_parse[cont_intro]:
  "bd.admissible (\<lambda>expressionR. parser_can_parse_print_result (parse (expressionR ())) (print (expressionR ())))"
  unfolding parser_can_parse_print_result_def p_has_result_def has_result_def
  by simp

lemma admissible_exist_printable[cont_intro]:
  "bd.admissible (\<lambda>expressionR. \<exists>s. print (expressionR ()) t = Some (Some s))"
  apply (rule ccpo.admissibleI)
  unfolding bd_ord_def fun_ord_def fun_lub_def bd_lub_def
  apply clarsimp
  by (smt (z3) all_not_in_conv chain_def flat_ord_def mem_Collect_eq option.lub_upper option.simps(3))

lemma admissible_parse_result_eq[cont_intro]:
  "bd.admissible (\<lambda>expressionR. parse (expressionR ()) i \<noteq> Some (Some (t, l)))"
  by simp

lemma admissible_printer_can_print[cont_intro]:
  "bd.admissible (\<lambda>expressionR. printer_can_print_parse_result (parse (expressionR ())) (print (expressionR ())))"
  unfolding printer_can_print_parse_result_def p_has_result_def has_result_def
  by simp

lemma admissible_WF[cont_intro]:
  "bd.admissible (\<lambda>expressionR. bidef_well_formed ((expressionR ())))"
  unfolding bidef_well_formed_def
  by simp

lemma strict_WF[cont_intro]:
  "bidef_well_formed (bdc (\<lambda>u. None) (\<lambda>u. None))"
  unfolding bidef_well_formed_def
  by (simp add: strict_PNGI parser_can_parse_print_result_def p_has_result_def printer_can_print_parse_result_def has_result_def)

lemma admissible_fpci_not_in_set[cont_intro]:
  "bd.admissible (\<lambda>expressionR. first_printed_chari (print (expressionR ())) i c \<longrightarrow> c \<notin> S)"
  unfolding first_printed_chari_def p_has_result_def
  by simp

lemma admissible_can_drop_leftover[cont_intro]:
  "bd.admissible (\<lambda>expressionR. (\<forall>c l l' r. has_result (parse (expressionR ())) (c @ l @ l') r (l @ l') \<longrightarrow> has_result (parse (expressionR ())) (c @ l) r l))"
  unfolding has_result_def
  by simp

lemma bottom_no_empty_result[cont_intro]:
  "\<And>r x. has_result (\<lambda>a. None) [] r x \<Longrightarrow> False"
  unfolding has_result_def
  by clarsimp

lemma admissible_no_empty_parse_result[cont_intro]:
  "bd.admissible (\<lambda>JsonR. \<forall>r x. \<not> has_result (parse (JsonR ())) [] r x)"
  unfolding has_result_def
  by clarsimp

lemma bottom_has_no_fpc[cont_intro]:
  "\<not>fpc (\<lambda>a. None) i c"
  unfolding fpc_def has_result_def
  by fastforce

lemma admissible_fpc_not_in_set[cont_intro]:
  "bd.admissible (\<lambda>JsonR. \<forall>i c. fpc (parse (JsonR ())) i c \<longrightarrow> c \<notin> S)"
  unfolding fpc_def has_result_def by fastforce

lemma admissible_no_consume_past_char3[cont_intro]:
  "bd.admissible (\<lambda>JsonR. does_not_consume_past_char3 (parse (JsonR ())) C)"
  unfolding does_not_consume_past_char3_def has_result_def
  by clarsimp

lemma bottom_no_consume_past_char3[cont_intro]:
  "does_not_consume_past_char3 (\<lambda>a. None) C"
  unfolding does_not_consume_past_char3_def
  by (clarsimp simp add: NER_simps)

lemma bottom_drop_past_leftover[cont_intro]:
  "(\<forall>c l l' r. has_result (\<lambda>a. None) (c @ l @ l') r (l @ l') \<longrightarrow> has_result (\<lambda>a. None) (c @ l) r l)"
  by (clarsimp simp add: NER_simps)

lemma admissible_error_on_empty[cont_intro]:
  "bd.admissible (\<lambda>I. is_error (parse (I ())) [])"
  by (clarsimp simp add: is_error_def)


lemma admissible_exist_error_means_error_empty[cont_intro]:
  "bd.admissible (\<lambda>JsonR. (\<exists>i. is_error (parse (JsonR ())) i \<longrightarrow> is_error (parse (JsonR ())) []))"
  by clarsimp

lemma bottom_nonterm:
  "is_nonterm (\<lambda>a. None) i"
  by (clarsimp simp add: is_nonterm_def)

lemma fpci_bottom2:
  "first_printed_chari (\<lambda>a. None) i c \<Longrightarrow> False"
  unfolding first_printed_chari_def p_has_result_def
  by clarsimp


\<comment> \<open>Is false.\<close>
lemma bottom_error_empty[cont_intro]:
  "is_error (\<lambda>a. None) []"
  apply (clarsimp simp add: NER_simps)
  oops

end
