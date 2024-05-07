theory derived_lowercase_char
  imports basic_definitions
          derived_any_from_set
begin

definition lowercase_chars :: "char set" where
  "lowercase_chars = {CHR ''a'', CHR ''b'', CHR ''c'', CHR ''d'', CHR ''e'', CHR ''f'', CHR ''g'',
                      CHR ''h'', CHR ''i'', CHR ''j'', CHR ''k'', CHR ''l'', CHR ''m'', CHR ''n'',
                      CHR ''o'', CHR ''p'', CHR ''q'', CHR ''r'', CHR ''s'', CHR ''t'', CHR ''u'',
                      CHR ''v'', CHR ''w'', CHR ''x'', CHR ''y'', CHR ''z''}"


definition lowercase_char :: "char bidef" where
  "lowercase_char = any_from_set lowercase_chars"



\<comment> \<open>NER\<close>
lemma lowercase_char_is_nonterm[NER_simps]:
  "is_nonterm (parse lowercase_char) i \<longleftrightarrow> False"
  by (simp add: lowercase_char_def any_from_set_is_nonterm)

lemma lowercase_char_is_error[NER_simps]:
  "is_error (parse lowercase_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> lowercase_chars)"
  by (simp add: lowercase_char_def any_from_set_is_error)

lemma lowercase_char_has_result[NER_simps]:
  "has_result (parse lowercase_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> lowercase_chars)"
  by (auto simp add: lowercase_char_def any_from_set_has_result)

lemma lowercase_char_has_result_ci[NER_simps]:
  "has_result_ci (parse lowercase_char) i c r l \<longleftrightarrow> i \<noteq> [] \<and> c = [hd i] \<and> (r = hd i \<and> l = tl i \<and> r \<in> lowercase_chars)"
  by (auto simp add: lowercase_char_def any_from_set_has_result_ci)



\<comment> \<open>fp NER\<close>
lemma lowercase_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print lowercase_char) i \<longleftrightarrow> False"
  by (simp add: lowercase_char_def any_from_set_p_is_nonterm)

lemma lowercase_char_p_is_error[fp_NER]:
  "p_is_error (print lowercase_char) i \<longleftrightarrow> i \<notin> lowercase_chars"
  by (simp add: lowercase_char_def any_from_set_p_is_error)

lemma lowercase_char_p_has_result[fp_NER]:
  "p_has_result (print lowercase_char) i s \<longleftrightarrow> i \<in> lowercase_chars \<and> s = [i]"
  by (simp add: lowercase_char_def any_from_set_p_has_result)

lemma lowercase_char_print_empty[print_empty, fp_NER]:
  "p_has_result (print lowercase_char) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: lowercase_char_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma lowercase_char_PNGI:
  "PNGI (parse lowercase_char)"
  unfolding lowercase_char_def
  by (rule any_from_set_PNGI)

lemma lowercase_char_PASI:
  "PASI (parse lowercase_char)"
  unfolding lowercase_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Does not peek past end\<close>
lemma lowercase_char_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse lowercase_char)"
  unfolding lowercase_char_def
  by (clarsimp simp add: peek_past_end_simps)



\<comment> \<open>First printed char\<close>
lemma lowercase_char_fpci[fpci_simps]:
  shows "first_printed_chari (print lowercase_char) i c \<longleftrightarrow> (i \<in> lowercase_chars \<and> c = i)"
  unfolding first_printed_chari_def
  by (clarsimp simp add: lowercase_char_p_has_result; blast)



\<comment> \<open>Well Formed\<close>
lemma lowercase_char_well_formed:
  "bidef_well_formed lowercase_char"
  by (simp add: lowercase_char_def any_from_set_well_formed)



end