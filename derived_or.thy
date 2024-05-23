theory derived_or
  imports basic_definitions
begin

text \<open>
Try the first bidef, if it fails, use the second, if the second also fails, fail.
\<close>

definition or :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> ('\<alpha> + '\<beta>) bidef" where
  "or a b = if_then_else a return b (id :: '\<alpha> \<Rightarrow> '\<alpha>)"



\<comment> \<open>NER\<close>
lemma or_is_nonterm[NER_simps]:
  "is_nonterm (parse (or p1 p2)) i \<longleftrightarrow> is_nonterm (parse p1) i \<or> (is_error (parse p1) i \<and> is_nonterm (parse p2) i)"
  by (simp add: or_def NER_simps)

lemma or_is_error[NER_simps]:
  "is_error (parse (or p1 p2)) i \<longleftrightarrow> is_error (parse p1) i \<and> is_error (parse p2) i"
  by (simp add: or_def NER_simps)

lemma or_has_result[NER_simps]:
  "has_result (parse (or p1 p2)) i (Inl lr) l \<longleftrightarrow> has_result (parse p1) i lr l"
  "has_result (parse (or p1 p2)) i (Inr rr) l \<longleftrightarrow> is_error (parse p1) i \<and> has_result (parse p2) i rr l"
  by (simp add: or_def NER_simps)+

lemma or_has_result_non_split[NER_simps]:
  "has_result (parse (or p1 p2)) i r l \<longleftrightarrow> (
      case r of
        Inl lr \<Rightarrow> has_result (parse p1) i lr l
      | Inr rr \<Rightarrow> is_error (parse p1) i \<and> has_result (parse p2) i rr l)"
  by (simp add: or_def NER_simps split: sum.splits)

lemma or_has_result_ci[NER_simps]:
  "has_result_ci (parse (or p1 p2)) i c (Inl lr) l \<longleftrightarrow> has_result_ci (parse p1) i c lr l"
  "has_result_ci (parse (or p1 p2)) i c (Inr rr) l \<longleftrightarrow> is_error (parse p1) i \<and> has_result_ci (parse p2) i c rr l"
  by (auto simp add: has_result_ci_def has_result_c_def NER_simps)+



\<comment> \<open>FP NER\<close>
lemma or_p_has_result[fp_NER]:
  "p_has_result (print (or p1 p2)) (Inl lr) l \<longleftrightarrow> p_has_result (print p1) lr l"
  "p_has_result (print (or p1 p2)) (Inr rr) l \<longleftrightarrow> p_has_result (print p2) rr l"
  by (simp add: or_def fp_NER)+

lemma or_p_has_result_non_split[fp_NER]:
  "p_has_result (print (or p1 p2)) r l \<longleftrightarrow> (case r of
                                                Inl lr \<Rightarrow> p_has_result (print p1) lr l
                                              | Inr rr \<Rightarrow> p_has_result (print p2) rr l)"
  by (simp add: or_def fp_NER split: sum.splits)

lemma or_p_is_error[fp_NER]:
  "p_is_error (print (or p1 p2)) (Inl lr) \<longleftrightarrow> p_is_error (print p1) lr"
  "p_is_error (print (or p1 p2)) (Inr rr) \<longleftrightarrow> p_is_error (print p2) rr"
  by (simp add: or_def fp_NER)+

lemma or_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (or p1 p2)) (Inl lr) \<longleftrightarrow> p_is_nonterm (print p1) lr"
  "p_is_nonterm (print (or p1 p2)) (Inr rr) \<longleftrightarrow> p_is_nonterm (print p2) rr"
  by (simp add: or_def fp_NER)+

lemma or_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (or A B)) (Inl li) [] \<longleftrightarrow> p_has_result (print A) li []"
  "p_has_result (print (or A B)) (Inr ri) [] \<longleftrightarrow> p_has_result (print B) ri []"
  by (clarsimp simp add: or_def print_empty)+

lemma or_print_empty:
  "p_has_result (print (or A B)) i [] \<longleftrightarrow>(
    case i of
      Inl li \<Rightarrow> p_has_result (print A) li []
    | Inr ri \<Rightarrow> p_has_result (print B) ri []
  )"
  by (rule or_p_has_result_non_split)



\<comment> \<open>PNGI, PASI\<close>
lemma or_PNGI[PASI_PNGI]:
  assumes "PNGI (parse a)"
  assumes "PNGI (parse b)"
  shows "PNGI (parse (or a b))"
  using assms
  apply (simp add: PNGI_def NER_simps split: sum.splits)
  by fast

lemma or_PASI[PASI_PNGI]:
  assumes "PASI (parse a)"
  assumes "PASI (parse b)"
  shows "PASI (parse (or a b))"
  using assms
  apply (simp add: PASI_def NER_simps split: sum.splits)
  by blast



\<comment> \<open>Does not peek past end\<close>
lemma or_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  assumes "PNGI (parse A)"
  assumes "does_not_peek_past_end (parse B)"
  assumes "PNGI (parse B)"
  assumes "A_is_error_on_C_consumed A B"
  shows "does_not_peek_past_end (parse (or A B))"
  unfolding or_def
  by (auto simp add: peek_past_end_simps assms return_PNGI)



\<comment> \<open>First printed char\<close>
lemma or_fpci[fpci_simps]:
  "first_printed_chari (print (or A B)) (Inl i) c \<longleftrightarrow> first_printed_chari (print A) i c"
  "first_printed_chari (print (or A B)) (Inr i) c \<longleftrightarrow> first_printed_chari (print B) i c"
  unfolding or_def
  apply (metis eq_id_iff if_then_else_fpci_li_iff if_then_else_fpci_li_nonempty_A return_fpci(2) return_p_has_result(1))
  by (simp add: if_then_else_fpci_ri_iff)



\<comment> \<open>Well Formed\<close>
\<comment> \<open>A print result of b2 must not be parsable by b1\<close>
definition well_formed_or_pair :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> bool" where
  "well_formed_or_pair b1 b2 \<longleftrightarrow> (\<forall> v t. p_has_result (print b2) v t \<longrightarrow> is_error (parse b1) t)"

lemma or_well_formed:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "well_formed_or_pair b1 b2"
  shows "bidef_well_formed (or b1 b2)"
  apply wf_init
  subgoal
    using assms(1,2)[THEN get_pngi] or_PNGI
    by blast
  subgoal
    using assms
    unfolding parser_can_parse_print_result_def
              bidef_well_formed_def
              well_formed_or_pair_def
    apply clarsimp
    unfolding or_has_result_non_split
    apply (clarsimp split: sum.splits)
    by (metis or_p_has_result(1) or_p_has_result(2))
  subgoal
    using assms
    unfolding printer_can_print_parse_result_def
              bidef_well_formed_def
              well_formed_or_pair_def
    apply clarsimp
    unfolding or_p_has_result_non_split
    apply (clarsimp split: sum.splits)
    by (metis or_p_has_result(1, 2) or_has_result(1, 2))
  done

lemma wf_or_pair_eq_wf_or:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  shows "well_formed_or_pair b1 b2 \<longleftrightarrow> bidef_well_formed (or b1 b2)"
  using assms
  apply (auto simp add: or_well_formed) (* wf_or_pair \<rightarrow> wf or is dispatched here *)
  apply (subst (asm) (3) bidef_well_formed_def)
  unfolding well_formed_or_pair_def
            parser_can_parse_print_result_def
  by (auto simp add: fp_NER NER_simps split: sum.splits)


end
