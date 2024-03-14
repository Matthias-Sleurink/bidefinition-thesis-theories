theory test_fun_ord
  imports Main 
  HOL.Partial_Function
  "HOL-Library.Monad_Syntax"
begin




type_synonym '\<alpha> parse_result = "('\<alpha> \<times> string)"

\<comment> \<open>The inner option defines parsing success\<close>
type_synonym '\<alpha> parser = "string \<Rightarrow> '\<alpha> parse_result option option"

section \<open>Types for the printer\<close>
type_synonym '\<alpha> printer = "'\<alpha> \<Rightarrow> string option option"

abbreviation "option_lub \<equiv> flat_lub None"

definition "bidef_ord = fun_ord option_ord"
definition "bidef_lub = fun_lub option_lub"

abbreviation "mono_bidef \<equiv> monotone (fun_ord bidef_ord) bidef_ord"

\<comment> \<open>IDEA: We let the bidef be one function\<close>
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

\<comment> \<open>Where is this used? TODO, remove?\<close>
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


\<comment> \<open>a bd takes an argument and returns either the result, or terminates\<close>
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

typedef 'a bd = "Collect wf_bd_aux :: 'a bd_aux set"
  apply (rule exI[of _ \<open>\<lambda>x. None\<close>])
  by (simp add: wf_bd_aux_def)
print_theorems

setup_lifting type_definition_bd

lift_definition parse :: "'a bd \<Rightarrow> 'a parser" is first .
lift_definition print :: "'a bd \<Rightarrow> 'a printer" is second .
lift_definition bdc :: "'a parser \<Rightarrow> 'a printer \<Rightarrow> 'a bd" is bdc_aux by (simp add: bd_aux_wf_bdc)


definition bd_ord :: "'a bd \<Rightarrow> 'a bd \<Rightarrow> bool" where
  "bd_ord bd bd' \<longleftrightarrow> fun_ord (flat_ord None) (parse bd) (parse bd') \<and> fun_ord (flat_ord None) (print bd) (print bd')"

definition bd_lub :: "'a bd set \<Rightarrow> 'a bd" where
  "bd_lub s = bdc (fun_lub (flat_lub None) (parse ` s)) (fun_lub (flat_lub None) (print ` s))"

\<comment> \<open>We need to move all the stuff from the typedef and lifting below to the typedef and lifting here\<close>
\<comment> \<open>After that we focus on making ITE, and then mono ITE, and then many0, and after that the other basics\<close>

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

lemma test1:
  "Abs_bd (bdc_aux a b) = bdc a b"
  by (simp add: bdc.abs_eq)

lemma bd_lub_aux_trans:
  assumes "Complete_Partial_Order.chain (fun_ord option_ord) (Rep_bd ` s)"
  shows "bd_lub s = Abs_bd (fun_lub (flat_lub None) (Rep_bd ` s))"
  unfolding bd_lub_def
  apply (subst bd_lub_componentwise[unfolded bd_aux_lub_def])
  subgoal by (simp add: assms)
  subgoal apply simp
    using Rep_bd by blast
  apply (simp add: test1)
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

definition is_nonterm :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> bool" where
  "is_nonterm p i \<longleftrightarrow> p i = None"

definition is_error :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> bool" where
  "is_error p i \<longleftrightarrow> p i = Some None"

definition has_result :: "'a parser \<Rightarrow> string \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> bool" where
  "has_result p i r l \<longleftrightarrow> p i = Some (Some (r, l))"


definition p_is_nonterm :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "p_is_nonterm fp v \<longleftrightarrow> fp v = None"

definition p_is_error :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "p_is_error fp v \<longleftrightarrow> fp v = Some None"

definition p_has_result :: "'a printer \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> bool" where
  "p_has_result p i r \<longleftrightarrow> p i = Some (Some r)"


definition parser_can_parse_print_result :: "'\<alpha> parser \<Rightarrow> '\<alpha> printer \<Rightarrow> bool" where
  "parser_can_parse_print_result par pri \<longleftrightarrow>
      (\<forall>(t :: '\<alpha>) pr. p_has_result pri t pr \<longrightarrow> has_result par pr t [])"

\<comment> \<open>note how due to the parse '015' = 15 print 15 = '15' issue we cannot attach the text here.\<close>
definition printer_can_print_parse_result :: "'\<alpha> parser \<Rightarrow> '\<alpha> printer \<Rightarrow> bool" where
  "printer_can_print_parse_result par pri \<longleftrightarrow>
      (\<forall>(t :: '\<alpha>) i l. has_result par i t l \<longrightarrow> (\<exists>pr. p_has_result pri t pr))"


definition bidef_well_formed :: "'\<alpha> bd \<Rightarrow> bool" where
  "bidef_well_formed bi = (parser_can_parse_print_result (parse bi) (print bi) \<and>
                           printer_can_print_parse_result (parse bi) (print bi))"


definition PASI :: "'a parser \<Rightarrow> bool" where
  "PASI p \<longleftrightarrow> (\<forall>i r l. has_result p i r l \<longrightarrow> length i > length l)"

definition PNGI :: "'a parser \<Rightarrow> bool" where
  "PNGI p \<longleftrightarrow> (\<forall>i r l. has_result p i r l \<longrightarrow> length i \<ge> length l)"




\<comment> \<open>Define basics here\<close>
(*
return, fail(bottom?)
ite, bind (derive?), (derive) then, else, etc


For partial function needs a parameter, add a unit/dummy parameter
*)

\<comment> \<open>Since this is a value, and not a function, ML does not allow us to have this be polymorphic.\<close>
\<comment> \<open>As such, we remove this equation from the code set.\<close>
\<comment> \<open>And then use the fail' and fail = fail' () fun and lemma\<close>
\<comment> \<open>to create the code equations for codegen.\<close>
definition fail :: "'x bd" where [code del]:
  "fail = bdc (\<lambda>_. Some None) (\<lambda>_. Some None)"

fun fail' :: "unit \<Rightarrow> 'a bd" where
  "fail' _ = bdc (\<lambda>_. Some None) (\<lambda>_. Some None)"

lemma [code_unfold]: "fail = fail' ()"
  by (simp add: fail_def)

lemma fail_has_result:
  "has_result (parse fail) i r l \<longleftrightarrow> False"
  unfolding fail_def has_result_def pp_bdc'(1)
  by simp

lemma fail_is_error:
  "is_error (parse fail) i \<longleftrightarrow> True"
  unfolding fail_def is_error_def pp_bdc'(1)
  by simp

lemma fail_is_nonterm:
  "is_nonterm (parse fail) i \<longleftrightarrow> False"
  unfolding fail_def is_nonterm_def pp_bdc'(1)
  by simp



definition return :: "'a \<Rightarrow> 'a bd" where
  "return t = bdc (\<lambda>i. Some (Some (t, i))) (\<lambda>t'. if t' = t then Some (Some []) else Some None)"
                                   
fun pr_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a parse_result \<Rightarrow>  'b parse_result" where
  "pr_map f (pr, pl) = (f pr, pl)"

fun opr_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a parse_result option \<Rightarrow>  'b parse_result option" where
  "opr_map f None = None"
| "opr_map f (Some p) = Some (pr_map f p)"

lemma opr_map_cases:
  "opr_map f i = (case i of None \<Rightarrow> None | (Some p) \<Rightarrow> Some (pr_map f p))"
  by (cases i) simp_all

fun oopr_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a parse_result option option \<Rightarrow> 'b parse_result option option" where
  "oopr_map f None = None"
| "oopr_map f (Some r) = Some (opr_map f r)"

lemma oopr_map_cases:
  "oopr_map f i = (
    case i of
      None \<Rightarrow> None
    | (Some None) \<Rightarrow> Some None
    | (Some (Some p)) \<Rightarrow> Some (Some (pr_map f p)))"
  by (auto split: option.splits)

lemma oopr_simps[simp]:
  "oopr_map f pr = None \<longleftrightarrow> pr = None"
  "oopr_map f pr = Some None \<longleftrightarrow> pr = Some None"
  "None \<noteq> oopr_map f pr \<longleftrightarrow> pr \<noteq> None"
  "Some None \<noteq> oopr_map f pr \<longleftrightarrow> pr \<noteq> Some None"
  subgoal using oopr_map.elims by auto
  subgoal using oopr_map.elims by force
  subgoal using oopr_map.elims by fastforce
  subgoal using \<open>(oopr_map f pr = Some None) = (pr = Some None)\<close> by fastforce
  done

lemma oopr_map_eq_iff[simp]:
  "oopr_map f1 None = oopr_map f2 None"
  "oopr_map f1 (Some None) = oopr_map f2 (Some None)"
  "oopr_map f1 (Some (Some (r1, l1))) = oopr_map f2 (Some (Some (r2, l2))) \<longleftrightarrow> (f1 r1, l1) = (f2 r2, l2)"
  by auto

lemma oopr_map_Inl_Inr_eq_iff[simp]:
  "oopr_map Inr pr1 = oopr_map Inr pr2 \<longleftrightarrow> pr1 = pr2"
  "oopr_map Inl pr1 = oopr_map Inl pr2 \<longleftrightarrow> pr1 = pr2"
  subgoal
    apply (cases pr1; cases pr2; clarsimp)
    subgoal for r1 r2
      by (cases r1; cases r2; clarsimp)
    done
  subgoal
    apply (cases pr1; cases pr2; clarsimp)
    subgoal for r1 r2
      by (cases r1; cases r2; clarsimp)
    done
  done

lemma oopr_map_Inl_Inr_neq_iff[simp]:
  "oopr_map Inr pr1 \<noteq> oopr_map Inr pr2 \<longleftrightarrow> pr1 \<noteq> pr2"
  "oopr_map Inl pr1 \<noteq> oopr_map Inl pr2 \<longleftrightarrow> pr1 \<noteq> pr2"
  by auto

fun else_parser :: "'a parser \<Rightarrow> 'b parser \<Rightarrow> ('a + 'b) parser" where
  "else_parser a b i = (
    case a i of
      None \<Rightarrow> None
    | Some (Some (r, l)) \<Rightarrow> Some (Some (Inl r, l))
    | Some None \<Rightarrow> (
        case b i of
          None \<Rightarrow> None
        | Some None \<Rightarrow> Some None
        | Some (Some (r, l)) \<Rightarrow> Some (Some (Inr r, l))
))"

fun else_printer :: "'a printer \<Rightarrow> 'b printer \<Rightarrow> ('a + 'b) printer" where
  "else_printer a b i = (
    case i of
      Inl l \<Rightarrow> a l
    | Inr r \<Rightarrow> b r
)"

definition belse :: "'a bd \<Rightarrow> 'b bd \<Rightarrow> ('a + 'b) bd" where
  "belse a b = bdc (else_parser (parse a) (parse b)) (else_printer (print a) (print b))"

lemma mono_else[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "mono_bd B"
  shows "mono_bd (\<lambda>f. belse (A f) (B f))"
  using assms
  apply -
  unfolding belse_def else_parser.simps else_printer.simps
            monotone_def le_fun_def flat_ord_def fun_ord_def bd_ord_def
  apply (auto simp add: bdc_eq_iff fun_eq_iff)
  subgoal
    apply (clarsimp split: option.splits)
    apply (smt (verit, ccfv_threshold) option.distinct(1))+
    subgoal by (smt (verit, del_insts) option.distinct(1) option.inject)
    subgoal by (smt (verit, ccfv_threshold) option.distinct(1) option.inject)
    subgoal by (smt option.distinct(1) option.inject)
    subgoal by (smt (verit, ccfv_threshold) option.distinct(1) option.inject)
    subgoal by (smt (verit, ccfv_threshold) fst_eqD option.discI option.sel snd_eqD)
    subgoal by (smt option.distinct(1) option.inject)
    subgoal by (smt (verit, del_insts) option.distinct(1) option.inject)
    subgoal by (smt (verit, ccfv_threshold) option.discI option.inject)
    subgoal by (smt (z3) fstI option.inject option.simps(3) sndI)
    done
  subgoal
    apply (clarsimp split: sum.splits)
    subgoal by blast
    subgoal by blast
    done
  done

fun ite_parser :: "'a parser \<Rightarrow> ('a \<Rightarrow> 'b parser) \<Rightarrow> 'c parser \<Rightarrow> ('b + 'c) parser" where
  "ite_parser a a2b c i = (
    case a i of
      None \<Rightarrow> None \<comment> \<open>Nonterm of a, nonterm the whole thing\<close>
    | Some (None) \<Rightarrow> oopr_map Inr (c i) \<comment> \<open>Failure of a, run c\<close>
    | Some (Some (r, l)) \<Rightarrow> oopr_map Inl (a2b r l) \<comment> \<open>Success of a, create and run b\<close>
  )"
print_theorems

fun ite_printer :: "'a printer \<Rightarrow> ('a \<Rightarrow> 'b printer) \<Rightarrow> 'c printer \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b + 'c) printer" where
  "ite_printer pa a2pb pc b2a (Inl b) = (let a = b2a b in
    case pa a of
      None \<Rightarrow> None \<comment> \<open>Nonterm\<close>
    | Some None \<Rightarrow> Some None \<comment> \<open>Failure\<close>
    | Some (Some r) \<Rightarrow> ( case a2pb a b of
        None \<Rightarrow> None \<comment> \<open>Nonterm\<close>
      | Some None \<Rightarrow> Some None \<comment> \<open>Failure\<close>
      | Some (Some r') \<Rightarrow> Some ( Some (r@r'))
))"
| "ite_printer pa a2pb pc b2a (Inr c) = (
    pc c
)"
print_theorems

lemma ite_printer_cases:
  "ite_printer pa a2pb pc b2a i = (case i of
  Inr c \<Rightarrow> pc c
| Inl b \<Rightarrow> (let a = b2a b in
    case pa a of
      None \<Rightarrow> None \<comment> \<open>Nonterm\<close>
    | Some None \<Rightarrow> Some None \<comment> \<open>Failure\<close>
    | Some (Some r) \<Rightarrow> ( case a2pb a b of
        None \<Rightarrow> None \<comment> \<open>Nonterm\<close>
      | Some None \<Rightarrow> Some None \<comment> \<open>Failure\<close>
      | Some (Some r') \<Rightarrow> Some ( Some (r@r')))))"
  by (auto split: sum.splits)

definition ite :: "'a bd \<Rightarrow> ('a \<Rightarrow> 'b bd) \<Rightarrow> 'c bd \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b + 'c) bd" where
  "ite a a2b c b2a = bdc (ite_parser (parse a) (parse o a2b) (parse c)) (ite_printer (print a) (print o a2b) (print c) b2a)"

\<comment> \<open>We can use this special const case if the passed in function is not used in the parser or printer constructors\<close>
lemma mono_bdc_const[partial_function_mono]:
  shows "mono_bd (\<lambda>f. (bdc parser printer))"
  by (simp add: bd_ord_def flat_ord_def fun_ord_def monotoneI)

lemma mono_ite[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. ite (A f) (\<lambda>y. B y f) (C f) trans_f)"
  unfolding ite_def monotone_def
  apply clarsimp
  apply (subst bd_ord_def)
  apply (subst fun_ord_def)
  apply (auto split: option.splits simp add: flat_ord_def)
  subgoal using ma
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def
    by (smt (verit, del_insts) option.discI)
  subgoal using mc
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def
    by blast
  subgoal using ma
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def
    by (metis option.inject option.simps(3))
  subgoal using ma
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def
    by (smt (verit, del_insts) option.distinct(1))
  subgoal using ma 
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def oopr_map_cases
    apply (auto split: option.splits)
    by (smt (verit, ccfv_threshold) option.distinct(1) option.inject)+
  subgoal for x' y' xa' a b aa ba using ma mb
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def
    proof -
      assume "\<forall>xa. (\<forall>xb. parse (x' xa) xb = None \<or> parse (x' xa) xb = parse (y' xa) xb) \<and> (\<forall>xb. print (x' xa) xb = None \<or> print (x' xa) xb = print (y' xa) xb)"
      assume "parse (A x') xa' = Some (Some (a, b))"
      assume "parse (A y') xa' = Some (Some (aa, ba))"
      assume "parse (B a x') b \<noteq> parse (B aa y') ba"
      assume "\<forall>x y. (\<forall>xa. (\<forall>xb. parse (x xa) xb = None \<or> parse (x xa) xb = parse (y xa) xb) \<and> (\<forall>xb. print (x xa) xb = None \<or> print (x xa) xb = print (y xa) xb)) \<longrightarrow> (\<forall>xa. parse (A x) xa = None \<or> parse (A x) xa = parse (A y) xa) \<and> (\<forall>xa. print (A x) xa = None \<or> print (A x) xa = print (A y) xa)"
      assume "\<And>y. \<forall>x ya. (\<forall>xa. (\<forall>xb. parse (x xa) xb = None \<or> parse (x xa) xb = parse (ya xa) xb) \<and> (\<forall>xb. print (x xa) xb = None \<or> print (x xa) xb = print (ya xa) xb)) \<longrightarrow> (\<forall>xa. parse (B y x) xa = None \<or> parse (B y x) xa = parse (B y ya) xa) \<and> (\<forall>xa. print (B y x) xa = None \<or> print (B y x) xa = print (B y ya) xa)"
      have "B a x' \<noteq> B aa x' \<or> b \<noteq> ba \<or> parse (B a x') b = parse (B aa x') ba"
        by force
      thus ?thesis
        by (smt (verit, ccfv_threshold) \<open>\<And>y. \<forall>x ya. (\<forall>xa. (\<forall>xb. parse (x xa) xb = None \<or> parse (x xa) xb = parse (ya xa) xb) \<and> (\<forall>xb. print (x xa) xb = None \<or> print (x xa) xb = print (ya xa) xb)) \<longrightarrow> (\<forall>xa. parse (B y x) xa = None \<or> parse (B y x) xa = parse (B y ya) xa) \<and> (\<forall>xa. print (B y x) xa = None \<or> print (B y x) xa = print (B y ya) xa)\<close> \<open>\<forall>x y. (\<forall>xa. (\<forall>xb. parse (x xa) xb = None \<or> parse (x xa) xb = parse (y xa) xb) \<and> (\<forall>xb. print (x xa) xb = None \<or> print (x xa) xb = print (y xa) xb)) \<longrightarrow> (\<forall>xa. parse (A x) xa = None \<or> parse (A x) xa = parse (A y) xa) \<and> (\<forall>xa. print (A x) xa = None \<or> print (A x) xa = print (A y) xa)\<close> \<open>\<forall>xa. (\<forall>xb. parse (x' xa) xb = None \<or> parse (x' xa) xb = parse (y' xa) xb) \<and> (\<forall>xb. print (x' xa) xb = None \<or> print (x' xa) xb = print (y' xa) xb)\<close> \<open>parse (A x') xa' = Some (Some (a, b))\<close> \<open>parse (A y') xa' = Some (Some (aa, ba))\<close> \<open>parse (B a x') b \<noteq> parse (B aa y') ba\<close> option.discI option.sel prod.inject)
    qed
  subgoal
    unfolding monotone_def bd_ord_def flat_ord_def fun_ord_def ite_printer_cases
    apply (auto simp add: Let_def split: sum.splits)
    subgoal using ma[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
      apply (auto split: option.splits)
      apply -
      subgoal by (smt (verit, del_insts) option.simps(3))
      subgoal by (smt (verit, ccfv_threshold) option.distinct(1))
      subgoal by (smt (verit, ccfv_threshold) option.distinct(1))
      subgoal by (smt (verit, ccfv_threshold) option.discI option.inject)
      subgoal by (smt (verit, del_insts) option.discI option.inject)
      subgoal using mb[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
        by (smt (verit, ccfv_threshold) option.distinct(1))
      subgoal using mb[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
        by (smt (verit, del_insts) option.distinct(1))
      subgoal using mb[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
        by (smt (verit, ccfv_threshold) option.distinct(1) option.sel)
      subgoal by (smt (verit, del_insts) option.inject option.simps(3))
      subgoal using mb[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
        by (smt (verit, del_insts) option.inject option.simps(3))
      subgoal using mb[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
        by (metis option.inject option.simps(3))
      done
    subgoal using mc[unfolded monotone_def bd_ord_def flat_ord_def fun_ord_def]
      by blast
    done
  done

definition transform :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a bd \<Rightarrow> 'b bd" where
  "transform a2b b2a bd = bdc
                            ((oopr_map a2b) o (parse bd))
                            ((print bd) o b2a)"


declare [[show_types=false]]
lemma mono_transform[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. transform f_trans f_trans' (A f))"
  using assms
  unfolding transform_def monotone_def bd_ord_def flat_ord_def fun_ord_def
  apply (auto simp add: oopr_map_cases split: option.splits)
  subgoal by (smt (verit, del_insts) option.simps(3))
  subgoal by (smt (verit, ccfv_threshold) option.discI option.inject)
  subgoal by (smt (verit, ccfv_threshold) option.distinct(1))
  subgoal by (smt (verit, ccfv_threshold) option.discI option.inject)
  subgoal by (smt (verit, ccfv_threshold) fst_conv option.distinct(1) option.sel)
  subgoal by (smt (verit, del_insts) option.distinct(1) option.inject prod.inject)
  done


\<comment> \<open>or, dep_then\<close>
definition bind :: "'a bd \<Rightarrow> ('a \<Rightarrow> 'b bd) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b bd" where
  "bind a a2bd b2a = transform projl Inl (ite a a2bd (fail :: unit bd) b2a)"

declare [[show_types=false]]
lemma mono_bind[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  shows "mono_bd (\<lambda>f. bind (A f) (\<lambda>y. B y f) transf)"
  by (simp add: bind_def mono_transform mono_ite ma mb bd.const_mono)+

definition or :: "'a bd \<Rightarrow> 'b bd \<Rightarrow> ('a + 'b) bd" where
  "or a b = ite a return b id"

definition bthen :: "'a bd \<Rightarrow> 'b bd \<Rightarrow> ('a \<times> 'b) bd"  where
  "bthen a b = bind a (\<lambda>ar. transform (Pair ar) snd b) fst"


fun one_char_parser :: "char parser" where
  "one_char_parser [] = Some None"
| "one_char_parser (c#cs) = Some (Some (c, cs))"

fun one_char_printer :: "char printer" where
  "one_char_printer c = Some (Some [c])"

definition one_char :: "char bd" where
  "one_char = bdc one_char_parser one_char_printer"

definition char_if :: "(char \<Rightarrow> bool) \<Rightarrow> char bd" where
  "char_if p = bind one_char (\<lambda>r. if p r then (return r) else (fail :: char bd)) id"

definition this_char :: "char \<Rightarrow> char bd" where
  "this_char c = char_if ((=) c)"

definition in_set :: "char set \<Rightarrow> char bd" where
  "in_set s = char_if (\<lambda>i. i \<in> s)"

value "parse one_char ''apple''"
value "parse one_char ''''"
value "parse (in_set {CHR ''a''}) ''apple''"
value "parse (in_set {CHR ''p''}) ''pple''"
value "parse (in_set {CHR ''p''}) ''ple''"
value "parse (in_set {CHR ''l''}) ''le''"
value "parse (in_set {CHR ''e''}) ''e''"
value "parse (in_set {CHR '' ''}) ''''"


definition eof :: "unit bd" where
  "eof = transform
          \<comment> \<open>Undefined here is safe since the ite below never returns a Inl\<close>
          (\<lambda>r. case r of Inl _ \<Rightarrow> undefined | Inr () \<Rightarrow> ())
          (Inr :: unit \<Rightarrow> (char+unit))
          (ite one_char (\<lambda>_. fail :: char bd) (return ()) id)"

fun sum_take :: "('a + 'a) \<Rightarrow> 'a" where
  "sum_take (Inl a) = a"
| "sum_take (Inr a) = a"

\<comment> \<open>bind a (\r. bind (many a) \rr. r#rr) sounds like a great idea, but does not allow an empty list result\<close>
partial_function (bd) many :: "'a bd \<Rightarrow> 'a list bd" where [code]:
  "many a = transform
              sum_take
              Inl
              (ite
                a \<comment> \<open>test\<close>
                (\<lambda>r. bind (many a) (\<lambda> rr. return (r#rr)) tl) \<comment> \<open>then\<close>
                (return []) \<comment> \<open>else\<close>
                (hd) \<comment> \<open>'a list \<Rightarrow> 'a (transform result of then back into result for test)\<close>
               )
"

value "parse (many one_char) ''apple''"
value "parse (many (this_char CHR ''a'')) ''apple''"
value "parse ((this_char CHR ''a'')) ''apple''"

end