theory derived_whitespace_char
  imports basic_definitions
          derived_any_from_set
begin

\<comment> \<open>How does one add chars like newline, tab, and return?\<close>
definition whitespace_chars :: "char set" where
  "whitespace_chars = {CHR '' ''}"


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



\<comment> \<open>PNGI, PASI\<close>
lemma whitespace_char_PNGI:
  "PNGI (parse whitespace_char)"
  unfolding whitespace_char_def
  by (rule any_from_set_PNGI)

lemma whitespace_char_PASI:
  "PASI (parse whitespace_char)"
  unfolding whitespace_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Well Formed\<close>
lemma whitespace_char_well_formed:
  "bidef_well_formed whitespace_char"
  by (simp add: whitespace_char_def any_from_set_well_formed)



end