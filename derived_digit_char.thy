theory derived_digit_char
  imports basic_definitions
          derived_any_from_set
begin

definition digit_chars :: "char set" where
  "digit_chars = {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'',
                  CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}"

lemma char_in_digit_chars[simp]:
  "CHR ''0'' \<in> digit_chars"
  "CHR ''1'' \<in> digit_chars"
  "CHR ''2'' \<in> digit_chars"
  "CHR ''3'' \<in> digit_chars"
  "CHR ''4'' \<in> digit_chars"
  "CHR ''5'' \<in> digit_chars"
  "CHR ''6'' \<in> digit_chars"
  "CHR ''7'' \<in> digit_chars"
  "CHR ''8'' \<in> digit_chars"
  "CHR ''9'' \<in> digit_chars"
  unfolding digit_chars_def
  by fast+

lemma char_not_in_digit_chars[simp]:
  "CHR '' '' \<notin> digit_chars"
  "CHR '','' \<notin> digit_chars"
  "CHR ''('' \<notin> digit_chars"
  "CHR '')'' \<notin> digit_chars"
  "CHR ''{'' \<notin> digit_chars"
  "CHR ''}'' \<notin> digit_chars"
  "CHR ''['' \<notin> digit_chars"
  "CHR '']'' \<notin> digit_chars"
  "CHR ''\<newline>'' \<notin> digit_chars"
  "CHR ''-'' \<notin> digit_chars"
  unfolding digit_chars_def
  by fast+



definition digit_char :: "char bidef" where
  "digit_char = any_from_set digit_chars"



\<comment> \<open>NER\<close>
lemma digit_char_is_nonterm[NER_simps]:
  "is_nonterm (parse digit_char) i \<longleftrightarrow> False"
  by (simp add: digit_char_def any_from_set_is_nonterm)

lemma digit_char_is_error[NER_simps]:
  "is_error (parse digit_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> digit_chars)"
  by (simp add: digit_char_def any_from_set_is_error)

lemma digit_char_has_result[NER_simps]:
  "has_result (parse digit_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> digit_chars)"
  by (auto simp add: digit_char_def any_from_set_has_result)

lemma digit_char_has_result_ci[NER_simps]:
  "has_result_ci (parse digit_char) i c r l \<longleftrightarrow> i \<noteq> [] \<and> c = [hd i] \<and> (r = hd i \<and> l = tl i \<and> r \<in> digit_chars)"
  by (auto simp add: digit_char_def any_from_set_has_result_ci)



\<comment> \<open>fp NER\<close>
lemma digit_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print digit_char) i \<longleftrightarrow> False"
  by (simp add: digit_char_def any_from_set_p_is_nonterm)

lemma digit_char_p_is_error[fp_NER]:
  "p_is_error (print digit_char) i \<longleftrightarrow> i \<notin> digit_chars"
  by (simp add: digit_char_def any_from_set_p_is_error)

lemma digit_char_p_has_result[fp_NER]:
  "p_has_result (print digit_char) i s \<longleftrightarrow> i \<in> digit_chars \<and> s = [i]"
  by (simp add: digit_char_def any_from_set_p_has_result)

lemma digit_char_print_empty[print_empty, fp_NER]:
  "p_has_result (print digit_char) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: digit_char_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma digit_char_PNGI[PASI_PNGI]:
  "PNGI (parse digit_char)"
  unfolding digit_char_def
  by (rule any_from_set_PNGI)

lemma digit_char_PASI[PASI_PNGI]:
  "PASI (parse digit_char)"
  unfolding digit_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Does not peek past end\<close>
lemma digit_char_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse digit_char)"
  unfolding digit_char_def
  by (clarsimp simp add: peek_past_end_simps)



\<comment> \<open>First printed char\<close>
lemma digit_char_fpci[fpci_simps]:
  shows "first_printed_chari (print digit_char) i c \<longleftrightarrow> (i \<in> digit_chars \<and> c = i)"
  unfolding first_printed_chari_def
  by (clarsimp simp add: digit_char_p_has_result; blast)



\<comment> \<open>Well Formed\<close>
lemma digit_char_well_formed:
  "bidef_well_formed digit_char"
  by (simp add: digit_char_def any_from_set_well_formed)



end