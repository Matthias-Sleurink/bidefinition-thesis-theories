theory derived_eof
  imports basic_definitions
          derived_or
          derived_transform
begin

\<comment> \<open>
The idea here is that if we succeed in parsing one_char, we go to "then", which always fails.
Only if we fail in the if side we go to "else", which succeeds.

\<close>
definition eof :: "unit bidef" where
  "eof = transform
          ((\<lambda>r. case r of Inl _ \<Rightarrow> undefined | Inr () \<Rightarrow> ()) :: ((char+unit) \<Rightarrow> unit))
          ((Inr) :: unit \<Rightarrow> (char+unit))
          (if_then_else one_char (\<lambda>_. (fail :: char bidef)) (return ()) id) \<comment> \<open>:: char+unit bidef\<close>
"



\<comment> \<open>NER\<close>
lemma eof_is_nonterm[NER_simps]:
  "is_nonterm (parse eof) i \<longleftrightarrow> False"
  by (simp add: eof_def NER_simps)

lemma eof_is_error[NER_simps]:
  "is_error (parse eof) i \<longleftrightarrow> i \<noteq> []"
  by (simp add: eof_def NER_simps neq_Nil_conv)

lemma eof_has_result[NER_simps]:
  "has_result (parse eof) i r l \<longleftrightarrow> r = () \<and> i = [] \<and> l = []"
  apply (auto simp add: eof_def NER_simps split: sum.splits)
  by (metis (full_types) old.sum.exhaust old.unit.exhaust)+

lemma eof_has_result_ci[NER_simps]:
  "has_result_ci (parse eof) i c r l \<longleftrightarrow> i = [] \<and> c = [] \<and> r = () \<and> l = []"
  by (auto simp add: has_result_ci_def has_result_c_def NER_simps split: sum.splits)



\<comment> \<open>FP NER\<close>
lemma eof_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print eof) i \<longleftrightarrow> False"
  by (simp add: eof_def fp_NER)

lemma eof_p_is_error[fp_NER]:
  "p_is_error (print eof) i \<longleftrightarrow> False"
  by (simp add: eof_def fp_NER)

lemma eof_p_has_result[fp_NER]:
  "p_has_result (print eof) i t \<longleftrightarrow> t = []"
  by (simp add: eof_def fp_NER)

lemma eof_print_empty[print_empty, fp_NER]:
  "p_has_result (print eof) i [] \<longleftrightarrow> True"
  by (clarsimp simp add: eof_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma eof_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse eof)"
  unfolding eof_def
  \<comment> \<open>Cannot apply intro PASI_PNGI_intros here?\<close>
  unfolding transform_PNGI[symmetric]
  apply (rule PNGI_dep_if_then_else)
  subgoal by (rule one_char_PNGI)
  subgoal by (simp add: fail_PNGI)
  subgoal by (rule return_PNGI)
  done

lemma eof_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse eof) \<longleftrightarrow> False"
  unfolding PASI_def
  by (simp add: NER_simps)



\<comment> \<open>Does not peek past end\<close>
lemma eof_does_not_peek_past_end[peek_past_end_simps]:
  "\<not>does_not_peek_past_end (parse eof)"
  unfolding does_not_peek_past_end_def
  by (auto simp add: NER_simps)



\<comment> \<open>First printed char\<close>
lemma eof_fpci[fpci_simps]:
  shows "\<nexists> i c. first_printed_chari (print eof) i c"
        "first_printed_chari (print eof) i c \<longleftrightarrow> False"
  unfolding first_printed_chari_def
  by (clarsimp simp add: eof_p_has_result)+



\<comment> \<open>Well Formed\<close>
lemma eof_well_formed:
  "bidef_well_formed eof"
  unfolding eof_def
  apply (rule transform_well_formed)
  subgoal
    apply (rule if_then_else_well_formed)
    subgoal by (rule one_char_well_formed)
    subgoal by (simp add: b2_wf_for_res_of_b1_def fail_well_formed)
    subgoal by (rule b_return_well_formed)
    subgoal by (simp add: b2_res_trans_is_b1_res_def NER_simps)
    subgoal by (simp add: b1_then_b2_print_parse_loop_def NER_simps fp_NER)
    subgoal by (simp add: b1_cannot_parse_b3_print_result_def NER_simps fp_NER)
    subgoal by (simp add: pa_does_not_eat_into_pb_def NER_simps fp_NER)
    done
  subgoal
    apply (subst well_formed_transform_funcs_def)
    apply (auto simp add: NER_simps split: sum.splits)
    by (metis (full_types) old.sum.exhaust old.unit.exhaust)+
  done


end
