theory derived_uppercase_char
  imports basic_definitions
          derived_any_from_set
begin

definition uppercase_chars :: "char set" where
  "uppercase_chars = {CHR ''A'', CHR ''B'', CHR ''C'', CHR ''D'', CHR ''E'', CHR ''F'', CHR ''G'',
                      CHR ''H'', CHR ''I'', CHR ''J'', CHR ''K'', CHR ''L'', CHR ''M'', CHR ''N'',
                      CHR ''O'', CHR ''P'', CHR ''Q'', CHR ''R'', CHR ''S'', CHR ''T'', CHR ''U'',
                      CHR ''V'', CHR ''W'', CHR ''X'', CHR ''Y'', CHR ''Z''}"


definition uppercase_char :: "char bidef" where
  "uppercase_char = any_from_set uppercase_chars"



\<comment> \<open>NER\<close>
lemma uppercase_char_is_nonterm[NER_simps]:
  "is_nonterm (parse uppercase_char) i \<longleftrightarrow> False"
  by (simp add: uppercase_char_def any_from_set_is_nonterm)

lemma uppercase_char_is_error[NER_simps]:
  "is_error (parse uppercase_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> uppercase_chars)"
  by (simp add: uppercase_char_def any_from_set_is_error)

lemma uppercase_char_has_result[NER_simps]:
  "has_result (parse uppercase_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> uppercase_chars)"
  by (auto simp add: uppercase_char_def any_from_set_has_result)



\<comment> \<open>fp NER\<close>
lemma uppercase_char_p_is_error[fp_NER]:
  "p_is_error (print uppercase_char) i \<longleftrightarrow> i \<notin> uppercase_chars"
  by (simp add: uppercase_char_def any_from_set_p_is_error)

lemma uppercase_char_p_has_result[fp_NER]:
  "p_has_result (print uppercase_char) i s \<longleftrightarrow> i \<in> uppercase_chars \<and> s = [i]"
  by (simp add: uppercase_char_def any_from_set_p_has_result)



\<comment> \<open>Well Formed\<close>
lemma uppercase_char_well_formed:
  "bidef_well_formed uppercase_char"
  by (simp add: uppercase_char_def any_from_set_well_formed)



end