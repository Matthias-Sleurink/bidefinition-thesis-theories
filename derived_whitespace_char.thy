theory derived_whitespace_char
  imports basic_definitions
          derived_any_from_set
begin

\<comment> \<open>Note, there may be more whitespace characters\<close>
definition whitespace_chars :: "char set" where
  "whitespace_chars = {CHR '' '', CHR ''\<newline>'', CHR 0x09, CHR 0x0D}"
\<comment> \<open>                   space      newline    tab        \r\<close>

lemma whitespace_chars_elements[simp]:
  "CHR '' '' \<in> whitespace_chars"
  "CHR ''\<newline>'' \<in> whitespace_chars"
  "CHR 0x09  \<in> whitespace_chars"
  "CHR 0x0D  \<in> whitespace_chars"
  unfolding whitespace_chars_def
  by simp_all
lemma chars_that_are_not_whitespace[simp]:
  "CHR '','' \<notin> whitespace_chars"
  unfolding whitespace_chars_def
  by simp_all



definition whitespace_char :: "char bidef" where
  "whitespace_char = any_from_set whitespace_chars"



\<comment> \<open>NER\<close>
lemma whitespace_char_is_nonterm[NER_simps]:
  "is_nonterm (parse whitespace_char) i \<longleftrightarrow> False"
  by (simp add: whitespace_char_def any_from_set_is_nonterm)

lemma whitespace_char_is_error[NER_simps]:
  "is_error (parse whitespace_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> whitespace_chars)"
  by (simp add: whitespace_char_def any_from_set_is_error)

lemma whitespace_char_has_result[NER_simps]:
  "has_result (parse whitespace_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> whitespace_chars)"
  by (auto simp add: whitespace_char_def any_from_set_has_result)

lemma whitespace_char_has_result_ci[NER_simps]:
  "has_result_ci (parse whitespace_char) i c r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> whitespace_chars \<and> c = [hd i])"
  unfolding has_result_ci_def has_result_c_def
  apply (auto simp add: whitespace_char_has_result)
  subgoal using list.collapse by fastforce
  subgoal by (metis hd_append2 list.collapse not_Cons_self2 self_append_conv2 tl_append2)
  done



\<comment> \<open>fp NER\<close>
lemma whitespace_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print whitespace_char) i \<longleftrightarrow> False"
  by (simp add: whitespace_char_def any_from_set_p_is_nonterm)

lemma whitespace_char_p_is_error[fp_NER]:
  "p_is_error (print whitespace_char) i \<longleftrightarrow> i \<notin> whitespace_chars"
  by (simp add: whitespace_char_def any_from_set_p_is_error)

lemma whitespace_char_p_has_result[fp_NER]:
  "p_has_result (print whitespace_char) i s \<longleftrightarrow> i \<in> whitespace_chars \<and> s = [i]"
  by (simp add: whitespace_char_def any_from_set_p_has_result)

lemma whitespace_char_print_empty[print_empty, fp_NER]:
  "p_has_result (print whitespace_char) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: whitespace_char_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma whitespace_char_PNGI[PASI_PNGI]:
  "PNGI (parse whitespace_char)"
  unfolding whitespace_char_def
  by (rule any_from_set_PNGI)

lemma whitespace_char_PASI[PASI_PNGI]:
  "PASI (parse whitespace_char)"
  unfolding whitespace_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Does not peek past end\<close>
lemma whitespace_char_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse whitespace_char)"
  unfolding whitespace_char_def
  by (clarsimp simp add: peek_past_end_simps)



\<comment> \<open>First printed char\<close>
lemma whitespace_char_fpci[fpci_simps]:
  shows "first_printed_chari (print whitespace_char) i c \<longleftrightarrow> (i \<in> whitespace_chars \<and> c = i)"
  unfolding first_printed_chari_def
  by (clarsimp simp add: whitespace_char_p_has_result; blast)



\<comment> \<open>Well Formed\<close>
lemma whitespace_char_well_formed:
  "bidef_well_formed whitespace_char"
  by (simp add: whitespace_char_def any_from_set_well_formed)



end