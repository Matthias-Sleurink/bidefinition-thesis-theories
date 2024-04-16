theory types
  imports Main
          HOL.Partial_Function
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



\<comment> \<open>list_upto is important for instantiating the existentials in has_result_c proofs\<close>
fun dropLastN :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "dropLastN a l = take (length l - a) l"

definition list_upto :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_upto longer shorter = dropLastN (length shorter) longer"

lemma list_upto_take_cons:
  assumes "\<exists>c. l = c@s"
  assumes "l' = list_upto l s"
  shows "l' @ s = l"
  using assms
  apply (induction s arbitrary: l l')
  subgoal by (simp add: list_upto_def)
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


interpretation bd:
  partial_function_definitions "bd_ord" "bd_lub"
  (* rewrites "bd_lub {} \<equiv> bdc (\<lambda>_. None) (\<lambda>_. None)" *)
  by (rule bd_partial_function_definitions)

abbreviation "mono_bd \<equiv> monotone (fun_ord bd_ord) bd_ord"

\<comment> \<open>TODO: We don't have a fixp_induct rule.\<close>
declaration \<open>Partial_Function.init "bd" \<^term>\<open>bd.fixp_fun\<close>
  \<^term>\<open>bd.mono_body\<close> @{thm bd.fixp_rule_uc} @{thm bd.fixp_induct_uc}
  (NONE)\<close> (*SOME @{thm fixp_induct_option}*)


lemma mono_bdc_const[partial_function_mono]:
  shows "mono_bd (\<lambda>f. (bdc parser printer))"
  by (simp add: bd_ord_def flat_ord_def fun_ord_def monotoneI)

\<comment> \<open>Old typename fix\<close>
type_synonym '\<alpha> bidef = "'\<alpha> bd"



section \<open>PASI, PNGI\<close>
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


lemma PASI_implies_PNGI:
  "PASI p \<longrightarrow> PNGI p"
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

lemma if_PNGI:
  assumes "PNGI (parse T)"
  assumes "PNGI (parse F)"
  shows "PNGI (parse (if P then T else F))"
  by (simp add: assms)

lemma if_PNGI_p:
  assumes "PNGI (parse (T p))"
  assumes "PNGI (parse (F p))"
  shows "PNGI (parse (if P p then T p else F p))"
  using assms
  by (rule if_PNGI)

lemma if_PASI:
  assumes "PASI (parse T)"
  assumes "PASI (parse F)"
  shows "PASI (parse (if P then T else F))"
  by (simp add: assms)

lemma if_PASI_p:
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

lemma test:
  assumes "bidef_well_formed a"
  shows "PNGI (parse a)"
  by (rule get_pngi[OF assms(1)])

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



end
