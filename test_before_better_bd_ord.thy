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

typedef 'a bd = "Collect wf_bd_aux :: 'a bd_aux set"
  apply (rule exI[of _ \<open>\<lambda>x. None\<close>])
  by (simp add: wf_bd_aux_def)
print_theorems

setup_lifting type_definition_bd

lift_definition parse :: "'a bd \<Rightarrow> 'a parser" is first .
lift_definition print :: "'a bd \<Rightarrow> 'a printer" is second .
lift_definition bdc :: "'a parser \<Rightarrow> 'a printer \<Rightarrow> 'a bd" is bdc_aux by (simp add: bd_aux_wf_bdc)

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

lifting_update bd.lifting
lifting_forget bd.lifting


abbreviation bd_bottom :: "'a bd" where
  "bd_bottom \<equiv> bdc (\<lambda>x. None) (\<lambda>x. None)"

lemma bdc_eq_iff:
  "bdc a b = bdc a' b' \<longleftrightarrow> a=a' \<and> b=b'"
  by (metis pp_bdc'(1) pp_bdc'(2))

lemma bd_eq_iff:
  "a = b \<longleftrightarrow> (parse a = parse b) \<and> (print a = print b)"
  using bdc'_tuple by auto

definition "t1 = fun_ord"
definition "t2 = flat_ord"

interpretation bd:
  partial_function_definitions "flat_ord bd_bottom" "flat_lub bd_bottom"
  rewrites "flat_lub bd_bottom {} \<equiv> bd_bottom"
by (rule flat_interpretation)(simp add: flat_lub_def)
                          
abbreviation "bd_ord \<equiv> flat_ord bd_bottom"
abbreviation "mono_bd \<equiv> monotone (fun_ord bd_ord) bd_ord"

lemma bd_ord_piecewise:
  "bd_ord a b = (parse a = (\<lambda>x. None) \<and> print a = (\<lambda>x. None) \<or> parse a = parse b \<and> print a = print b)"
  unfolding flat_ord_def
  by (simp add: bd_eq_iff)

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


definition has_result :: "'a parser \<Rightarrow> string \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> bool" where
  "has_result p i r l \<longleftrightarrow> p i = Some (Some (r, l))"

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
  "fail = bd_bottom"

fun fail' :: "unit \<Rightarrow> 'a bd" where
  "fail' _ = bd_bottom"

lemma [code_unfold]: "fail = fail' ()"
  by (simp add: fail_def)


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

(*
  assumes wfa: "\<And>f. bidef_well_formed (A f)"
  assumes wfc: "\<And>f. bidef_well_formed (B f)"

  assumes PASIA: "\<And>f. PASI (parse (A f))"
  assumes PASIC: "\<And>f. PASI (parse (B f))"
*)

declare [[show_types]]
lemma mono_else[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "mono_bd B"
  shows "mono_bd (\<lambda>f. belse (A f) (B f))"
  using assms
  apply -
  unfolding belse_def else_parser.simps else_printer.simps
            monotone_def le_fun_def flat_ord_def fun_ord_def
  apply (auto simp add: bdc_eq_iff fun_eq_iff)
  subgoal sorry
  subgoal sorry
  subgoal 
    apply (auto split: sum.splits option.splits)
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      \<comment> \<open>\<forall>xa. x xa = bd_bottom \<or> x xa = y xa\<close>
      \<comment> \<open>print (B x) x2 \<noteq> print (B y) x2\<close>
      \<comment> \<open>parse (B x) xb = None\<close>
      \<comment> \<open>parse (A x) xb = Some (Some (a, b))\<close>
      \<comment> \<open>goal: False\<close>
      \<comment> \<open>connection? only through x, xb\<close>
      sorry
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    subgoal
      by (metis option.distinct(1) pp_bdc'(1))
    sorry
  subgoal 
    apply (auto split: sum.splits)
    subgoal by (metis pp_bdc'(2))
    subgoal
      \<comment> \<open>\<forall>xa. x xa = bd_bottom \<or> x xa = y xa;\<close>
      \<comment> \<open>A x x1 != A y x1\<close>
      \<comment> \<open>goal: B x x2 = None\<close>
      \<comment> \<open>Only related through x.\<close>
      sorry
    subgoal
      \<comment> \<open> \<forall>xa. x xa = bd_bottom \<or> x xa = y xa;\<close>
      \<comment> \<open>print (B x) x2 \<noteq> print (B y) x2\<close>
      \<comment> \<open>goal: print (A x) x1 = None\<close>
      \<comment> \<open>only related to x.\<close>
      sorry
    subgoal
      by (metis pp_bdc'(2))
    done
  oops

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
  by (rule bd.const_mono)

lemma mono_bdc[partial_function_mono]:
  assumes "mono_bd (\<lambda>f. (bdc (parser f) (\<lambda>_. None)))"
  assumes "mono_bd (\<lambda>f. (bdc (\<lambda>_. None) (printer f)))"
  shows "mono_bd (\<lambda>f. (bdc (parser f) (printer f)))"
  using assms
  oops \<comment> \<open>There is something here, but it'd be best to escape from bdc, not use it again in the assms\<close>
  
lemma mono_bdc_bdc_aux[partial_function_mono]:
  assumes "mono_bd (\<lambda>f. bdc_aux (parser f) (printer f))"
  shows "mono_bd (\<lambda>f. bdc (parser f) (printer f))"
  oops

lemma forall_eq_schematic:
  "(\<forall>x. t = x \<longrightarrow> F x) \<longleftrightarrow> F t"
  by (rule simp_thms(42))

lemma forall_eq_schematic2:
  "(\<forall>x. (t = x \<longrightarrow> F x) \<and> (t = x \<longrightarrow> F2 x)) \<longleftrightarrow> (F t \<and> F2 t)"
  by blast


declare [[show_types=false]]
lemma mono_ite[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. ite (A f) (\<lambda>y. B y f) (C f) trans_f)"
  using assms
  apply -
  unfolding ite_def
  unfolding monotone_def 
  apply auto
  unfolding fun_ord_def
  
  
  
  unfolding ite_def ite_parser.simps ite_printer_cases
            monotone_def le_fun_def flat_ord_def fun_ord_def
  




declare [[show_types]]
lemma mono_ite[partial_function_mono]:
  assumes wfa: "\<And>f. bidef_well_formed (A f)"
  assumes wfb: "\<And>f. \<forall> i r l. has_result (parse (A f)) i r l \<longrightarrow> bidef_well_formed (B r f)"
  assumes wfc: "\<And>f. bidef_well_formed (C f)"
  assumes wfcpra: "\<And>f. \<forall>i it. p_has_result (print (C f)) i it \<longrightarrow> \<not>(\<exists>r l. has_result (parse (A f)) it r l)"
  assumes wftrans: "\<And>f. \<forall> i r l r' l'. (has_result (parse (A f)) i r l \<and> has_result (parse (B r f)) l r' l') \<longrightarrow> (\<exists>t. p_has_result (print (A f)) (trans_f r') t)"


  assumes PASIA: "\<And>f. PASI (parse (A f))"
  assumes PASIB: "\<And>f. \<forall> i r l. has_result (parse (A f)) i r l \<longrightarrow> PASI (parse (B r f))"
  assumes PASIC: "\<And>f. PASI (parse (C f))"

  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. ite (A f) (\<lambda>y. B y f) (C f) trans_f)"
  using assms
  apply -
  unfolding ite_def ite_parser.simps ite_printer_cases
            monotone_def le_fun_def flat_ord_def fun_ord_def
            bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
              has_result_def p_has_result_def
            PASI_def
  apply (clarsimp simp add: bdc_eq_iff fun_eq_iff)
  subgoal for x y \<comment> \<open>These are the two compared functions, x is smaller than y\<close>
    apply (auto simp add: split: option.splits)
    apply -
      \<comment> \<open>Sledgehammer finds solutions for 6/18 subgoals before wfcpra\<close>
      \<comment> \<open>And the same amount after.\<close>
      \<comment> \<open>And the same after PASI\<close>
      \<comment> \<open>And the same after wftrans\<close>
    
    subgoal  \<comment> \<open>found\<close> sorry
    subgoal  \<comment> \<open>found\<close> sorry
    subgoal for i opr de
      apply (cases de)
      subgoal for a
        apply (cases \<open>print (A x) (trans_f a)\<close>; clarsimp)
        subgoal for opr_r
          apply (cases opr_r; clarsimp)
          subgoal by (metis (mono_tags, lifting) option.distinct(1) pp_bdc'(2))
          subgoal by (metis (full_types) option.distinct(1) pp_bdc'(2))
          done
        done
      subgoal for b
        \<comment> \<open>It's requiring the result to be None here, but it's not entirely clear to me why.\<close>
        \<comment> \<open>Could it be that the flat_ord is making it hard here? Possibly we just need a fun_ord here?\<close>
        
        apply auto
        supply [[show_types=false]]
        apply (rule spec[of _ x])
        
        sorry
             \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>found\<close> sorry
    subgoal for s opr s' d s''
      apply (cases opr)
      subgoal \<comment> \<open>opr = None\<close>
        apply auto
        
        sorry
      subgoal by (metis (no_types) option.distinct(1) option.sel pp_bdc'(1))
             \<comment> \<open>not found\<close>  sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    subgoal  \<comment> \<open>not found\<close> sorry
    done
  oops
    


declare [[show_types]]
\<comment> \<open>supply [[show_types=false]]\<close>
lemma mono_ite[partial_function_mono]:
  assumes wfa: "\<And>f. bidef_well_formed (A f)"
  assumes wfb: "\<And>f. \<forall> i r l. has_result (parse (A f)) i r l \<longrightarrow> bidef_well_formed (B r f)"
  assumes wfc: "\<And>f. bidef_well_formed (C f)"
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. ite (A f) (\<lambda>y. B y f) (C f) trans_f)"
  using assms
  apply -
  unfolding ite_def ite_parser.simps ite_printer_cases
            monotone_def le_fun_def flat_ord_def fun_ord_def
            bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
              has_result_def p_has_result_def
  apply (auto simp add: bdc_eq_iff Let_def)
  subgoal for x y \<comment> \<open>The two functions that are compared in LE fashion, with x being smaller\<close>
    apply (auto simp add: fun_eq_iff)
    subgoal for xa xaa
      apply (cases \<open>parse (A x) xaa\<close>; clarsimp)
      subgoal for a
        apply (cases a; clarsimp)
        subgoal
          apply (cases \<open>(parse (C x) xaa)\<close>; clarsimp)
          subgoal for aa
            apply (cases \<open>parse (A x) xa\<close>; cases \<open>(parse (C x) xa)\<close>; clarsimp)
            subgoal by (metis (mono_tags, lifting) option.case_eq_if option.distinct(1) pp_bdc'(1))
            subgoal by (metis (mono_tags, lifting) option.case_eq_if option.discI pp_bdc'(1))
            subgoal for ab
              apply (cases ab; clarsimp; cases \<open>parse (A y) xa\<close>; clarsimp)
              subgoal by (metis (mono_tags, lifting) oopr_map.simps(1) option.discI option.discI option.sel option.simps(4) pp_bdc'(1) pp_bdc'(1))
              subgoal by (metis option.discI pp_bdc'(1))
              subgoal for r xr ac
                apply (cases \<open>(parse (B r x) xr)\<close>; clarsimp; cases ac; clarsimp)
                subgoal apply (cases \<open>parse (C y) xa\<close>; clarsimp)
                  by (metis option.discI pp_bdc'(1))
                subgoal for ad xrr
                  apply (cases \<open>parse (B ad y) xrr\<close>; clarsimp)
                  
                  
                  sorry
                subgoal
                  by (metis option.discI option.inject pp_bdc'(1))
                subgoal
                  
                done
              done
            sorry
          done
        sorry
      done
    done
  oops


lemma mono_ite[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. ite (A f) (\<lambda>y. B y f) (C f) trans_f)"
  using assms
  apply -
  unfolding ite_def monotone_def
  apply (simp add: bd_ord_piecewise)
  apply auto
  subgoal for x y
    unfolding ite_parser.simps
    apply (auto simp add: fun_eq_iff split!: option.splits)
      apply (auto simp add: oopr_map_cases split: option.splits)
                        apply (metis option.distinct(1) option.sel prod.sel(1) snd_conv)
    sorry
    subgoal for aa
      apply (drule spec[of _ x, THEN spec[of _ y]]) 
      apply (auto)

      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      thm spec[of _ x, THEN spec[of _ y]]
      apply (drule mp)+

definition transform :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a bd \<Rightarrow> 'b bd" where
  "transform a2b b2a bd = bdc
                            ((opr_map a2b) o (parse bd))
                            ((print bd) o b2a)"

\<comment> \<open>or, dep_then\<close>
definition bind :: "'a bd \<Rightarrow> ('a \<Rightarrow> 'b bd) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b bd" where
  "bind a a2bd b2a = transform projl Inl (ite a a2bd (fail :: unit bd) b2a)"

definition or :: "'a bd \<Rightarrow> 'b bd \<Rightarrow> ('a + 'b) bd" where
  "or a b = ite a return b id"

definition bthen :: "'a bd \<Rightarrow> 'b bd \<Rightarrow> ('a \<times> 'b) bd"  where
  "bthen a b = bind a (\<lambda>ar. transform (Pair ar) snd b) fst"


fun one_char_parser :: "char parser" where
  "one_char_parser [] = None"
| "one_char_parser (c#cs) = Some (c, cs)"

fun one_char_printer :: "char printer" where
  "one_char_printer c = Some [c]"

definition one_char :: "char bd" where
  "one_char = bdc one_char_parser one_char_printer"

definition char_if :: "(char \<Rightarrow> bool) \<Rightarrow> char bd" where
  "char_if p = bind one_char (\<lambda>r. if p r then (return r) else (fail :: char bd)) id"

definition this_char :: "char \<Rightarrow> char bd" where
  "this_char c = char_if ((=) c)"

definition in_set :: "char set \<Rightarrow> char bd" where
  "in_set s = char_if (\<lambda>i. i \<in> s)"

value "parse one_char ''apple''"

definition "t \<equiv> parse (in_set {CHR ''a''}) ''apple''"

\<comment> \<open>NOTE: I assume that it's the lifted type here that causes issues?\<close>
\<comment> \<open>       Show the two files to Peter to see what he thinks and if this is solvable\<close>

SML_file f.ml
export_code t  in SML
  module_name test file f.ml

value "t"

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
                (hd) \<comment> \<open>'a list \<Rightarrow> 'a (transform result of b back into result for a)\<close>
               )
"

end