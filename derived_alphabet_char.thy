theory derived_alphabet_char
  imports basic_definitions
          derived_any_from_set
begin

definition alphabet_chars :: "char set" where
  "alphabet_chars = {CHR ''a'', CHR ''b'', CHR ''c'', CHR ''d'', CHR ''e'', CHR ''f'', CHR ''g'',
                     CHR ''h'', CHR ''i'', CHR ''j'', CHR ''k'', CHR ''l'', CHR ''m'', CHR ''n'',
                     CHR ''o'', CHR ''p'', CHR ''q'', CHR ''r'', CHR ''s'', CHR ''t'', CHR ''u'',
                     CHR ''v'', CHR ''w'', CHR ''x'', CHR ''y'', CHR ''z'',
                     CHR ''A'', CHR ''B'', CHR ''C'', CHR ''D'', CHR ''E'', CHR ''F'', CHR ''G'',
                     CHR ''H'', CHR ''I'', CHR ''J'', CHR ''K'', CHR ''L'', CHR ''M'', CHR ''N'',
                     CHR ''O'', CHR ''P'', CHR ''Q'', CHR ''R'', CHR ''S'', CHR ''T'', CHR ''U'',
                     CHR ''V'', CHR ''W'', CHR ''X'', CHR ''Y'', CHR ''Z''}"


definition alphabet_char :: "char bidef" where
  "alphabet_char = any_from_set alphabet_chars"



\<comment> \<open>NER\<close>
lemma alphabet_char_is_nonterm[NER_simps]:
  "is_nonterm (parse alphabet_char) i \<longleftrightarrow> False"
  by (simp add: alphabet_char_def any_from_set_is_nonterm)

lemma alphabet_char_is_error[NER_simps]:
  "is_error (parse alphabet_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> alphabet_chars)"
  by (simp add: alphabet_char_def any_from_set_is_error)

lemma alphabet_char_has_result[NER_simps]:
  "has_result (parse alphabet_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> alphabet_chars)"
  by (auto simp add: alphabet_char_def any_from_set_has_result)



\<comment> \<open>fp NER\<close>
lemma alphabet_char_p_is_error[fp_NER]:
  "p_is_error (print alphabet_char) i \<longleftrightarrow> i \<notin> alphabet_chars"
  by (simp add: alphabet_char_def any_from_set_p_is_error)

lemma alphabet_char_p_has_result[fp_NER]:
  "p_has_result (print alphabet_char) i s \<longleftrightarrow> i \<in> alphabet_chars \<and> s = [i]"
  by (simp add: alphabet_char_def any_from_set_p_has_result)



\<comment> \<open>Well Formed\<close>
lemma alphabet_char_well_formed:
  "bidef_well_formed alphabet_char"
  by (simp add: alphabet_char_def any_from_set_well_formed)



end