theory basic_dependent_if_then_else
  imports types
          basic_transform
begin

text \<open>This is the second base combinator.
      It runs the first parser, if successful the result is used to create a second parser and run that.
      If that created parser fails then this parser fails.
      If the first parser fails then the third parser is ran.
      The result is a sum type with result of either the second or the third parser.
      An assumption is that the result of the first parser can be re-created from the result of the second.
\<close>

\<comment> \<open>Some util functions\<close>

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

lemma oopr_map_Inl_Inr_neq[simp]:
  "oopr_map Inr pr1 \<noteq> Some (Some (Inl r, l))"
  "oopr_map Inl pr1 \<noteq> Some (Some (Inr r, l))"
  by (auto simp add: oopr_map_cases split: option.splits)

lemma oopr_map_has_result_eq_iff[simp]:
  "oopr_map Inl (parse p al) = Some (Some (Inl lr, l)) \<longleftrightarrow> has_result (parse p) al lr l"
  "oopr_map Inr (parse p al) = Some (Some (Inr lr, l)) \<longleftrightarrow> has_result (parse p) al lr l"
  by (auto simp add: oopr_map_cases has_result_def split: option.splits)



\<comment> \<open>The actual bidef\<close>

fun ite_parser :: "'a parser \<Rightarrow> ('a \<Rightarrow> 'b parser) \<Rightarrow> 'c parser \<Rightarrow> ('b + 'c) parser" where
  "ite_parser a a2b c i = (
    case a i of
      None \<Rightarrow> None \<comment> \<open>Nonterm of a, nonterm the whole thing\<close>
    | Some (None) \<Rightarrow> oopr_map Inr (c i) \<comment> \<open>Failure of a, run c\<close>
    | Some (Some (r, l)) \<Rightarrow> oopr_map Inl (a2b r l) \<comment> \<open>Success of a, create and run b\<close>
  )"

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

definition if_then_else :: "'a bd \<Rightarrow> ('a \<Rightarrow> 'b bd) \<Rightarrow> 'c bd \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b + 'c) bd" where
  "if_then_else a a2b c b2a = bdc (ite_parser (parse a) (parse o a2b) (parse c)) (ite_printer (print a) (print o a2b) (print c) b2a)"



\<comment> \<open>Monotone\<close>

lemma mono_if_then_else[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. if_then_else (A f) (\<lambda>y. B y f) (C f) trans_f)"
  unfolding if_then_else_def monotone_def
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



\<comment> \<open>NER\<close>
lemma if_then_else_is_nonterm[NER_simps]:
  "is_nonterm (parse (if_then_else ab a2bb cb b2a)) i \<longleftrightarrow> is_nonterm (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_nonterm (parse (a2bb r)) l) \<or> (is_error (parse ab) i \<and> is_nonterm (parse cb) i)"
  "is_nonterm (ite_parser ap a2bp cp)           i \<longleftrightarrow> is_nonterm ap i         \<or> (\<exists> r l. has_result ap i r l         \<and> is_nonterm (a2bp r) l)         \<or> (is_error ap i         \<and> is_nonterm cp i)"
  by (simp add: if_then_else_def is_nonterm_def has_result_def is_error_def split: option.splits)+

lemma if_then_else_is_error[NER_simps]:
  "is_error (parse (if_then_else ab a2bb cb b2a)) i \<longleftrightarrow> (is_error (parse ab) i \<and> is_error (parse cb) i) \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_error (parse (a2bb r)) l)"
  "is_error (ite_parser ap a2bp cp)           i \<longleftrightarrow> (is_error ap i         \<and> is_error cp i)         \<or> (\<exists> r l. has_result ap i r l         \<and> is_error (a2bp r) l)"
  by (simp add: if_then_else_def is_error_def has_result_def split: option.splits)+

lemma if_then_else_has_result[NER_simps]:
  "has_result (parse (if_then_else ab a2bb cb b2a)) i (Inl lr) l \<longleftrightarrow> (\<exists> ar al. has_result (parse ab) i ar al \<and> has_result (parse (a2bb ar)) al lr l)"
  "has_result (parse (if_then_else ab a2bb cb b2a)) i (Inr rr) l \<longleftrightarrow> is_error (parse ab) i \<and> has_result (parse cb) i rr l"
  "has_result (ite_parser ap a2bp cp) i (Inl lr) l \<longleftrightarrow> (\<exists> ar al. has_result ap i ar al \<and> has_result (a2bp ar) al lr l)"
  "has_result (ite_parser ap a2bp cp) i (Inr rr) l \<longleftrightarrow> is_error ap i \<and> has_result cp i rr l"
  by (simp add: if_then_else_def has_result_def is_error_def oopr_map_cases split: option.splits)+

lemma if_then_else_has_result_no_split[NER_simps]:
  "has_result (parse (if_then_else ab a2bb cb b2a)) i r l \<longleftrightarrow> (
      case r of
        Inl lr \<Rightarrow> (\<exists> ar al. has_result (parse ab) i ar al \<and> has_result (parse (a2bb ar)) al lr l)
      | Inr rr \<Rightarrow> (is_error (parse ab) i \<and> has_result (parse cb) i rr l))"
  "has_result (ite_parser ap a2bp cp) i r l \<longleftrightarrow> (
      case r of
        Inl lr \<Rightarrow> (\<exists> ar al. has_result ap i ar al \<and> has_result (a2bp ar) al lr l)
      | Inr rr \<Rightarrow> (is_error ap i \<and> has_result cp i rr l))"
  by (simp add: NER_simps split: sum.splits)+ 

lemma if_then_else_has_result_c[NER_simps]:
  assumes "PNGI (parse ab)"
  assumes "\<forall>a. PNGI (parse (a2bb a))"
  assumes "PNGI (parse ac)"
  shows
  "has_result_c (parse (if_then_else ab a2bb cb b2a)) c (Inl lr) l \<longleftrightarrow> (\<exists> ar c' c''. c = c' @ c'' \<and> has_result_c (parse ab) c' ar (c''@l) \<and> has_result_c (parse (a2bb ar)) c'' lr l)"
  "has_result_c (parse (if_then_else ab a2bb cb b2a)) c (Inr rr) l \<longleftrightarrow> is_error (parse ab) (c@l) \<and> has_result_c (parse cb) c rr l"
  unfolding has_result_c_def
  apply auto
  \<comment> \<open>This first subgoal is a lot harder if we use if_then_else_has_result.\<close>
  \<comment> \<open>So, we first split into subgoals without it, and then we solve the other subgoals with it.\<close>
  subgoal
    unfolding if_then_else_def ite_parser.simps has_result_def
    apply (auto split: option.splits)
    subgoal for ar al
      apply (rule exI[of _ ar])
      \<comment> \<open>al = c'' @l\<close>
      \<comment> \<open>c@l = c' @ c'' @ l\<close>
      \<comment> \<open>So, c' = (c@l) upto c'' @ l = (c@l) upto al\<close>
      apply (rule exI[of _ \<open>list_upto (c@l) al\<close>])
      \<comment> \<open>c'' = drop (length (list_upto (c @ l) al)) c\<close>
      apply (rule exI[of _ \<open>drop (length (list_upto (c @ l) al)) c\<close>])
      using assms(1)[unfolded PNGI_def has_result_def, rule_format, of \<open>c@l\<close> ar al]
      using assms(2)[unfolded PNGI_def, rule_format, of ar al lr l]
      by (auto simp add: list_upto_def has_result_def)
    done
  by (auto simp add: if_then_else_has_result)


lemma if_then_else_has_result_ci[NER_simps]:
  assumes "PNGI (parse ab)"
  assumes "\<forall>a. PNGI (parse (a2bb a))"
  assumes "PNGI (parse ac)"
  shows
  "has_result_ci (parse (if_then_else ab a2bb cb b2a)) i c (Inl lr) l \<longleftrightarrow> (\<exists> ar c' c''. c = c' @ c'' \<and> has_result_ci (parse ab) i c' ar (c''@l) \<and> has_result_ci (parse (a2bb ar)) (c''@l) c'' lr l)"
  "has_result_ci (parse (if_then_else ab a2bb cb b2a)) i c (Inr rr) l \<longleftrightarrow> is_error (parse ab) (c@l)  \<and> has_result_ci (parse cb) i c rr l"
  subgoal
    using if_then_else_has_result_c(1)[OF assms, of cb b2a c lr l]
    apply (auto simp add: has_result_ci_def)
    by blast
  subgoal
    using if_then_else_has_result_c(2)[OF assms, of cb b2a c rr l]
    by (clarsimp simp add: has_result_ci_def)
  done



\<comment> \<open>FP NER\<close>
lemma if_then_else_p_is_error[fp_NER]:
  "p_is_error (print (if_then_else ab a2bb cb b2a)) (Inl lr) \<longleftrightarrow> (let a = b2a lr in (p_is_error (print ab) a \<or> (\<not>p_is_nonterm (print ab) a \<and> p_is_error (print (a2bb a)) lr)))"
  "p_is_error (print (if_then_else ab a2bb cb b2a)) (Inr rr) \<longleftrightarrow> p_is_error (print cb) rr"

  "p_is_error (ite_printer ap a2bp cp b2a) (Inl lr) \<longleftrightarrow> (let a = b2a lr in (p_is_error ap a \<or> (\<not>p_is_nonterm ap a \<and> p_is_error (a2bp a) lr)))"
  "p_is_error (ite_printer ap a2bp cp b2a) (Inr rr) \<longleftrightarrow> p_is_error cp rr"
  by (auto simp add: if_then_else_def ite_printer_cases p_is_error_def p_is_nonterm_def Let_def split: option.splits)

lemma if_then_else_p_has_result[fp_NER]:
  "p_has_result (print (if_then_else ab a2bb cb b2a)) (Inl lr) str \<longleftrightarrow> (\<exists> astr bstr. str = astr@bstr \<and> (let a = b2a lr in (p_has_result (print ab) a astr \<and> p_has_result (print (a2bb a)) lr bstr)))"
  "p_has_result (print (if_then_else ab a2bb cb b2a)) (Inr rr) str \<longleftrightarrow> p_has_result (print cb) rr str"

  "p_has_result (ite_printer ap a2bp cp b2a) (Inl lr) str \<longleftrightarrow> (\<exists> astr bstr. str = astr@bstr \<and> (let a = b2a lr in (p_has_result ap a astr \<and> p_has_result (a2bp a) lr bstr)))"
  "p_has_result (ite_printer ap a2bp cp b2a) (Inr rr) str \<longleftrightarrow> p_has_result cp rr str"
  by (auto simp add: if_then_else_def p_has_result_def Let_def split: option.splits)

lemma if_then_else_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (if_then_else ab a2bb cb b2a)) (Inl lr) \<longleftrightarrow> (let a = b2a lr in (p_is_nonterm (print ab) a \<or> (\<not>p_is_error (print ab) a \<and> p_is_nonterm (print (a2bb a)) lr)))"
  "p_is_nonterm (print (if_then_else ab a2bb cb b2a)) (Inr rr) \<longleftrightarrow> p_is_nonterm (print cb) rr"

  "p_is_nonterm (ite_printer ap a2bp cp b2a) (Inl lr) \<longleftrightarrow> (let a = b2a lr in (p_is_nonterm ap a \<or> (\<not>p_is_error ap a \<and> p_is_nonterm (a2bp a) lr)))"
  "p_is_nonterm (ite_printer ap a2bp cp b2a) (Inr rr) \<longleftrightarrow> p_is_nonterm cp rr"
  by (auto simp add: if_then_else_def ite_printer_cases p_is_error_def p_is_nonterm_def Let_def split: option.splits)



\<comment> \<open>PNGI, PASI\<close>
lemma PNGI_dep_if_then_else:
  assumes "PNGI (parse ab)"
  assumes "\<forall> i r l. has_result (parse ab) i r l \<longrightarrow> PNGI (parse (a2bb r))"
  assumes "PNGI (parse cb)"
  shows "PNGI (parse (if_then_else ab a2bb cb b2a))"
  using assms
  apply (simp add: PNGI_def NER_simps split: sum.splits)
  by fastforce

lemma PNGI_dep_if_then_else_all:
  assumes "PNGI (parse ab)"
  assumes "\<forall> i. PNGI (parse (a2bb i))"
  assumes "PNGI (parse cb)"
  shows "PNGI (parse (if_then_else ab a2bb cb b2a))"
  using assms
  apply (simp add: PNGI_def NER_simps split: sum.splits)
  by fastforce

lemma PASI_dep_if_then_else:
  assumes "PASI (parse ab)"
  assumes "\<forall> i. PASI (parse (a2bb i))"
  assumes "PASI (parse cb)"
  shows "PASI (parse (if_then_else ab a2bb cb b2a))"
  using assms
  apply (simp add: PASI_def NER_simps split: sum.splits)
  by fastforce

lemma dep_if_then_else_PASI_PASI_PNGI_PASI:
  assumes "PASI (parse ab)"
  assumes "\<forall> i. PNGI (parse (a2bb i))"
  assumes "PASI (parse cb)"
  shows "PASI (parse (if_then_else ab a2bb cb b2a))"
  using assms
  apply (simp add: PASI_def PNGI_def NER_simps split: sum.splits)
  by fastforce

lemma dep_if_then_else_PASI_PNGI_PASI_PASI:
  assumes "PNGI (parse ab)"
  assumes "\<forall> i. PASI (parse (a2bb i))"
  assumes "PASI (parse cb)"
  shows "PASI (parse (if_then_else ab a2bb cb b2a))"
  using assms
  apply (simp add: PASI_def PNGI_def NER_simps split: sum.splits)
  by fastforce



\<comment> \<open>Charset\<close>
\<comment> \<open>If ab always fails then a2bb's charset should not be added?\<close>
lemma charset_dep_if_then_else:
  "charset (parse (if_then_else ab a2bb cb b2a)) = charset (parse ab) \<union> (\<Union> {charset (parse (a2bb ar)) | i ar l. has_result (parse ab) i ar l}) \<union> charset (parse cb)"
  unfolding charset_def
  apply (auto simp add: NER_simps split: sum.splits)
  subgoal for x X r l c
    apply (rule exI[of _ X])
    apply (cases r; clarsimp)
    subgoal for a ar al
      apply (rule exI[of _ ar])
      \<comment> \<open>Need both l and al in the leftover position\<close>
      \<comment> \<open>The only place that references them both is \<^term>\<open>has_result (parse (a2bb ar)) al a l\<close>\<close>
      \<comment> \<open>Which does not inspire confidence\<close>
      apply (rule exI[of _ al])
      apply (rule exI[of _ c])
      
      supply [[show_types]]
      
      sorry
    subgoal auto
      
      sorry
    
  oops

lemma charset_dep_if_then_else_subset:
  assumes "PNGI (parse ab)"
  assumes "\<forall>abr. PNGI (parse (a2bb abr))"
  assumes "PNGI (parse cb)"
  shows "charset (parse (if_then_else ab a2bb cb b2a)) \<subseteq> (charset (parse ab) \<union> (\<Union> {charset (parse (a2bb ar)) | ar. True}) \<union> charset (parse cb))"
  using PNGI_dep_if_then_else_all[OF assms]
        assms
  unfolding charset_def PNGI_def
  apply (auto simp add: NER_simps split: sum.splits)
  subgoal for x X r l c
    apply (cases r; clarsimp)
    subgoal for br ar al
      apply (rule exI[of _ \<open>set c\<close>])
      apply clarsimp
      
      apply (rule exI[of _ ar])
      apply (rule exI[of _ l]) \<comment> \<open>or AL here?\<close>
      apply (rule exI[of _ c])
      apply clarsimp
      apply (cases \<open>al = l\<close>)
      subgoal by force
      subgoal
        
        sorry
      
      
      \<comment> \<open>Need both l and al in the leftover position\<close>
      \<comment> \<open>The only place that references them both is \<^term>\<open>has_result (parse (a2bb ar)) al a l\<close>\<close>
      \<comment> \<open>Which does not inspire confidence\<close>
      
      supply [[show_types]]
      
      sorry
    subgoal apply (rule exI[of _ \<open>set c\<close>]) by metis
    done
  oops


lemma first_chars_dep_if_then_else:
  "first_chars (print (if_then_else ab a2bb cb b2a)) = (
    if (\<exists>pi. p_has_result (print ab) pi []) then
      first_chars (print ab) \<union> (\<Union> {first_chars (print (a2bb ar)) | ar . True}) \<union> first_chars (print cb)
    else
      first_chars (print ab) \<union> first_chars (print cb)
)"
  unfolding first_chars_def
  apply (auto simp add: fp_NER)
  oops


lemma first_chars_dep_if_then_else_subset:
  "first_chars (print (if_then_else ab a2bb cb b2a)) \<subseteq> (first_chars (print ab) \<union> (\<Union> {first_chars (print (a2bb ar)) | ar. True}) \<union> first_chars (print cb))"
  unfolding first_chars_def
  apply (auto simp add: fp_NER)
  subgoal for i pr
    apply (cases i)
    subgoal
      apply (auto simp add: if_then_else_p_has_result(1) Let_def)
      subgoal by (meson hd_append2)
      subgoal by (smt (verit, best) CollectI hd_append2 self_append_conv2)
      done
    subgoal
      by (simp add: if_then_else_p_has_result(2))
    done
  done



\<comment> \<open>Does not peek past end\<close>
lemma second_attempt:
  assumes PNGI_A: "PNGI (parse A)"
  assumes PNGI_B: "\<forall>i r. (\<exists>l. has_result (parse A) i r l) \<longrightarrow> PNGI (parse (a2B r))"
  assumes not_peek_past_A: "\<forall>c r. (\<exists>l. has_result (parse A) (c @ l) r l) \<longrightarrow> (\<forall>l'. has_result (parse A) (c @ l') r l')"
  assumes not_peek_past_B: "\<forall>i r. (\<exists>l. has_result (parse A) i r l) \<longrightarrow> (\<forall>c ra. (\<exists>l. has_result (parse (a2B r)) (c @ l) ra l) \<longrightarrow> (\<forall>l'. has_result (parse (a2B r)) (c @ l') ra l'))"
  assumes hr_A: "has_result (parse A) (c @ l) ra la"
  assumes hr_B: "has_result (parse (a2B ra)) la rl l"
  shows "\<exists>cs. has_result (parse A) (c @ l') ra cs \<and> has_result (parse (a2B ra)) cs rl l'"
  proof -
    obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f7: "c @ l = ccs la (c @ l) @ la"
      using hr_A PNGI_A[unfolded PNGI_def] by meson
    obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f8: "la = ccsa l la @ l"
      using hr_B hr_A PNGI_B[unfolded PNGI_def] by meson
    then have "has_result (parse A) (c @ l') ra (ccsa l la @ l')"
      using f7 hr_A not_peek_past_A 
      by (smt (verit, best) append.assoc append_same_eq)
    then show "\<exists>cs. has_result (parse A) (c @ l') ra cs \<and> has_result (parse (a2B ra)) cs rl l'"
      using f8 hr_B not_peek_past_B by metis
  qed



definition A_is_error_on_C_consumed :: "'\<alpha> bidef \<Rightarrow> '\<gamma> bidef \<Rightarrow> bool" where
  "A_is_error_on_C_consumed A C \<longleftrightarrow> (\<forall>c l r l'. has_result (parse C) (c @ l) r l \<longrightarrow> is_error (parse A) (c @ l'))"

lemma if_then_else_does_not_peek_past_end[peek_past_end_simps]:
  assumes "PNGI (parse A)"
  assumes "\<forall> i r l. has_result (parse A) i r l \<longrightarrow> PNGI (parse (a2B r))"
  assumes "PNGI (parse C)"
  assumes "does_not_peek_past_end (parse A)"
  assumes "\<forall> i r l. has_result (parse A) i r l \<longrightarrow> does_not_peek_past_end (parse (a2B r))"
  assumes "does_not_peek_past_end (parse C)"
  assumes "A_is_error_on_C_consumed A C"
  shows "does_not_peek_past_end (parse (if_then_else A a2B C b2a))"
  using assms unfolding does_not_peek_past_end_def
  apply clarsimp \<comment> \<open>\<forall> \<rightarrow> \<And> so that we can use the names\<close>
  subgoal for c r l l'
    apply (cases r) \<comment> \<open>Does the if succeed or not?\<close>
    subgoal for rl \<comment> \<open>r = Inl rl\<close>
      apply (clarsimp simp add: if_then_else_has_result(1))
      subgoal for ra la
        apply (rule exI[of _ ra])
        using second_attempt[of A a2B c l ra la rl l']
        by fast
      done
    subgoal for rr \<comment> \<open>r = Inr rr\<close>
      unfolding A_is_error_on_C_consumed_def
      apply (clarsimp simp add: if_then_else_has_result(2))
      by blast
    done
  done


\<comment> \<open>Does not consume past char.\<close>
\<comment> \<open>Also used for WF\<close>
definition pa_does_not_eat_into_pb :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> bool" where
  "pa_does_not_eat_into_pb ba a2bb \<longleftrightarrow> (
    \<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print (a2bb t1)) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2
)"

lemma if_then_else_does_not_consume_past_char:
  assumes "PNGI (parse A)"
  assumes "\<forall> i r l. has_result (parse A) i r l \<longrightarrow> PNGI (parse (a2B r))"
  assumes "PNGI (parse C)"

  assumes "\<forall> i r l. has_result (parse A) i r l \<longrightarrow> does_not_consume_past_char (parse (a2B r)) ch"
  assumes "does_not_consume_past_char (parse C) ch"

  assumes "A_is_error_on_C_consumed A C"

  assumes "does_not_peek_past_end (parse A)"

  shows "does_not_consume_past_char (parse (if_then_else A a2B C b2a)) ch"
  using assms unfolding does_not_consume_past_char_def does_not_peek_past_end_def
  apply clarsimp \<comment> \<open>\<forall> \<rightarrow> \<And> so that we can use the names\<close>
  subgoal for c r l l'
    apply (cases r) \<comment> \<open>Did we return from a->a2b or c?\<close>
    subgoal for rl
      apply (clarsimp simp add: if_then_else_has_result(1))
      subgoal for ar al
        apply (rule exI[of _ ar])
        apply (clarsimp simp add: PNGI_def)
        proof -
          assume a1: "\<forall>i r l. has_result (parse A) i r l \<longrightarrow> (\<exists>c. i = c @ l)"
          assume a2: "\<forall>i r. (\<exists>l. has_result (parse A) i r l) \<longrightarrow> (\<forall>i ra l. has_result (parse (a2B r)) i ra l \<longrightarrow> (\<exists>c. i = c @ l))"
          assume a3: "\<forall>i r. Ex (has_result (parse A) i r) \<longrightarrow> (\<forall>c ra. (\<exists>l. has_result (parse (a2B r)) (c @ l) ra l) \<longrightarrow> (\<forall>l'. has_result (parse (a2B r)) (c @ ch # l') ra (ch # l')))"
          assume a4: "\<forall>c r. (\<exists>l. has_result (parse A) (c @ l) r l) \<longrightarrow> (\<forall>l'. has_result (parse A) (c @ l') r l')"
          assume a5: "has_result (parse A) (c @ l) ar al"
          assume a6: "has_result (parse (a2B ar)) al rl l"
          obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
            f7: "c @ l = ccs al (c @ l) @ al"
            using a5 a1 by meson
          obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
            f8: "al = ccsa l al @ l"
            using a6 a5 a2 by meson
          have "\<forall>cs. has_result (parse A) (ccs al (c @ l) @ cs) ar cs"
            using f7 a5 a4 by metis
          then show "\<exists>cs. has_result (parse A) (c @ ch # l') ar cs \<and> has_result (parse (a2B ar)) cs rl (ch # l')"
            using f8 f7 a6 a3
            by (smt (verit) append_assoc append_same_eq)
        qed
      done
    subgoal for rr
      unfolding A_is_error_on_C_consumed_def
      apply (clarsimp simp add: if_then_else_has_result(2))
      by blast
    done
  done




\<comment> \<open>First printed char\<close>
lemma if_then_else_fpci_ri:
  assumes "first_printed_chari (print C) ri c"
  shows "first_printed_chari (print (if_then_else A a2B C b2a)) (Inr ri) c"
  using assms unfolding first_printed_chari_def
  by (clarsimp simp add: if_then_else_p_has_result)

lemma if_then_else_fpci_ri_iff:
  shows "first_printed_chari (print (if_then_else A a2B C b2a)) (Inr ri) c \<longleftrightarrow> first_printed_chari (print C) ri c"
  unfolding first_printed_chari_def
  by (clarsimp simp add: if_then_else_p_has_result)

lemma if_then_else_fpci_li_nonempty_A:
  assumes "first_printed_chari (print A) (b2a li) c"
  assumes "\<exists>tb. p_has_result (print (a2B (b2a li))) li tb"
  shows "first_printed_chari (print (if_then_else A a2B C b2a)) (Inl li) c"
  using assms unfolding first_printed_chari_def
  apply (clarsimp simp add: if_then_else_p_has_result)
  by force

lemma if_then_else_fpci_li_empty_A:
  assumes "p_has_result (print A) (b2a li) []"
  assumes "first_printed_chari (print (a2B (b2a li))) li c"
  shows "first_printed_chari (print (if_then_else A a2B C b2a)) (Inl li) c"
  using assms unfolding first_printed_chari_def
  apply (clarsimp simp add: if_then_else_p_has_result)
  by fastforce



\<comment> \<open>Well Formed\<close>
definition b2_wf_for_res_of_b1 :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> bool" where
  "b2_wf_for_res_of_b1 b1 a2bi \<longleftrightarrow> (\<forall> i ra la. has_result (parse b1) i ra la \<longrightarrow> bidef_well_formed (a2bi ra))"

definition b2_res_trans_is_b1_res :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
"b2_res_trans_is_b1_res b1 a2bi b2a \<longleftrightarrow>
                        (\<forall> i ra la. has_result (parse b1) i ra la \<longrightarrow> (
                          \<forall> i2 rb lb. has_result (parse (a2bi ra)) i2 rb lb \<longrightarrow> (
                            b2a rb = ra
)))"

definition b1_then_b2_print_parse_loop :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
  "b1_then_b2_print_parse_loop b1 a2b2 b2a \<longleftrightarrow>
          (\<forall> v1 v2 pr1 pr2 a.
            (p_has_result (print b1) v1 pr1 \<and> p_has_result (print (a2b2 a)) v2 pr2) \<longrightarrow>
               (\<exists>l1 l2. has_result (parse b1) (pr1@pr2) v1 l1 \<and> has_result (parse (a2b2 a)) l1 v2 l2)
)"

definition b1_cannot_parse_b3_print_result :: "'\<alpha> bidef \<Rightarrow> '\<gamma> bidef \<Rightarrow> bool" where
  "b1_cannot_parse_b3_print_result b1 b3 \<longleftrightarrow> (
    \<forall> i pr. p_has_result (print b3) i pr \<longrightarrow> is_error (parse b1) pr
)"

lemma does_not_eat_into_when_no_peek_past:
  assumes "does_not_peek_past_end (parse A)"
  assumes "bidef_well_formed A"
  shows "pa_does_not_eat_into_pb A B"
  using no_peek_past_end_wf_stronger[OF assms]
  unfolding pa_does_not_eat_into_pb_def
  by blast



\<comment> \<open>We for sure should not need all of these assms.\<close>
lemma if_then_else_well_formed:
  assumes "bidef_well_formed ab"
  assumes "b2_wf_for_res_of_b1 ab a2bb"
  assumes "bidef_well_formed cb"
  assumes "b2_res_trans_is_b1_res ab a2bb b2a"
  assumes "b1_then_b2_print_parse_loop ab a2bb b2a"
  assumes "b1_cannot_parse_b3_print_result ab cb"
  assumes "pa_does_not_eat_into_pb ab a2bb"
  shows "bidef_well_formed (if_then_else ab a2bb cb b2a)"
  apply wf_init
  subgoal
    using assms(1, 3)[THEN get_pngi]
          assms(2)[unfolded b2_wf_for_res_of_b1_def bidef_well_formed_def]
          PNGI_dep_if_then_else
    by blast
  subgoal
    using assms
    unfolding bidef_well_formed_def
              parser_can_parse_print_result_def
              b1_then_b2_print_parse_loop_def
              b1_cannot_parse_b3_print_result_def
              pa_does_not_eat_into_pb_def
              b2_wf_for_res_of_b1_def
    apply clarsimp
    subgoal for t pr
      apply (cases t)
       apply (auto simp add: fp_NER)
      subgoal by (metis if_then_else_has_result(1))
      subgoal by (meson if_then_else_has_result(2))
      done
    done
  subgoal
    using assms
    unfolding bidef_well_formed_def
              printer_can_print_parse_result_def
              b2_res_trans_is_b1_res_def
              b2_wf_for_res_of_b1_def
    apply clarsimp
    subgoal for t i x
      apply (cases t)
       apply (auto simp add: fp_NER NER_simps)
      subgoal by (metis if_then_else_p_has_result(1))
      subgoal by (meson if_then_else_p_has_result(2))
      done
    done
  done



end
