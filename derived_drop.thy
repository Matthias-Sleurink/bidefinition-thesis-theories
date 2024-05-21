theory derived_drop
  imports basic_definitions
begin

text \<open>
Drop the result, takes an oracle for printing
\<close>

definition drop :: "'\<alpha> bidef \<Rightarrow> '\<alpha> \<Rightarrow> unit bidef" where [code del]:
  "drop A oracle = transform (const ()) (const oracle) A"
 


section NER
lemma drop_is_nonterm[NER_simps]:
  "is_nonterm (parse (drop A oracle)) i \<longleftrightarrow> is_nonterm (parse A) i"
  by (clarsimp simp add: drop_def NER_simps)

lemma drop_is_error[NER_simps]:
  "is_error (parse (drop A oracle)) i \<longleftrightarrow> is_error (parse A) i"
  by (clarsimp simp add: drop_def NER_simps)

lemma drop_has_result[NER_simps]:
  "has_result (parse (drop A oracle)) i r l \<longleftrightarrow> (\<exists>r'. has_result (parse A) i r' l)"
  by (clarsimp simp add: drop_def NER_simps)

lemma drop_has_result_c[NER_simps]:
  "has_result_c (parse (drop A oracle)) c r l \<longleftrightarrow> (\<exists>r'. has_result_c (parse A) c r' l)"
  by (clarsimp simp add: drop_def NER_simps)+

lemma drop_has_result_ci[NER_simps]:
  "has_result_ci (parse (drop A oracle)) i c r l \<longleftrightarrow> (\<exists>r'. has_result_ci (parse A) i c r' l)"
  by (clarsimp simp add: drop_def NER_simps)+



section \<open>fp ner\<close>
lemma drop_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (drop A oracle)) i \<longleftrightarrow> p_is_nonterm (print A) oracle"
  by (clarsimp simp add: drop_def fp_NER)

lemma drop_p_is_error[fp_NER]:
  "p_is_error (print (drop A oracle)) i \<longleftrightarrow> p_is_error (print A) oracle"
  by (clarsimp simp add: drop_def fp_NER)

lemma drop_p_has_result[fp_NER]:
  "p_has_result (print (drop A oracle)) i t \<longleftrightarrow> p_has_result (print A) oracle t"
  by (clarsimp simp add: drop_def fp_NER)

lemma drop_print_empty[print_empty, fp_NER]:
  "p_has_result (print (drop A oracle)) i [] \<longleftrightarrow> p_has_result (print A) oracle []"
  by (rule drop_p_has_result)



section \<open>PNGI, PASI\<close>
lemma drop_PNGI:
  "PNGI (parse (drop A oracle)) \<longleftrightarrow> PNGI (parse A)"
  by (clarsimp simp add: drop_def transform_PNGI[symmetric])


lemma drop_PASI:
  "PASI (parse (drop A oracle)) \<longleftrightarrow> PASI (parse A)"
  by (clarsimp simp add: drop_def transform_PASI[symmetric])



section \<open>Does not peek past end.\<close>
lemma drop_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  shows "does_not_peek_past_end (parse (drop A oracle))"
  using assms unfolding does_not_peek_past_end_def drop_has_result
  by auto



section \<open>Does not consume past char\<close>
lemma drop_does_not_consume_past_char:
  assumes "does_not_consume_past_char (parse A) ch"
  shows "does_not_consume_past_char (parse (drop A oracle)) ch"
  using assms unfolding does_not_consume_past_char_def
  by (auto simp add: NER_simps)

lemma drop_does_not_consume_past_char2:
  assumes "does_not_consume_past_char2 (parse A) ch"
  shows "does_not_consume_past_char2 (parse (drop A oracle)) ch"
  using assms unfolding does_not_consume_past_char2_def
  by (auto simp add: NER_simps)

lemma drop_does_not_consume_past_char3:
  assumes "does_not_consume_past_char3 (parse A) ch"
  shows "does_not_consume_past_char3 (parse (drop A oracle)) ch"
  using assms unfolding does_not_consume_past_char3_def
  by (auto simp add: NER_simps)



section \<open>First printed char\<close>
lemma drop_fpci[fpci_simps]:
  shows "first_printed_chari (print (drop A oracle)) i c \<longleftrightarrow> first_printed_chari (print A) oracle c"
  unfolding drop_def
  by (clarsimp simp add: fpci_simps)+

lemma drop_fpc[fpc_simps]:
  shows "fpc (parse (drop A oracle)) i c \<longleftrightarrow> (\<exists>i'. fpc (parse A) i' c)"
  unfolding drop_def
  by (clarsimp simp add: fpc_simps)+



section well_formed
\<comment> \<open>TODO: This could maybe be simpler since we need to parse less prints?\<close>
lemma drop_well_formed:
  assumes wf_A: "bidef_well_formed A"
  assumes good_oracle: "\<exists>t. p_has_result (print A) oracle t"
  shows "bidef_well_formed (drop A oracle)"
  unfolding drop_def
  apply (rule transform_well_formed3)
  subgoal by (rule wf_A)
  subgoal
    unfolding well_formed_transform_funcs3_def
    apply (auto simp add: good_oracle )
    subgoal using wf_A[THEN get_parser_can_parse_unfold, rule_format, of \<open>oracle\<close>] by blast
    done
  done



end