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

definition pa_does_not_eat_into_pb :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> bool" where
  "pa_does_not_eat_into_pb ba a2bb \<longleftrightarrow> (
    \<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print (a2bb t1)) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2
)"

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