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

lemma uppercase_char_has_result_ci[NER_simps]:
  "has_result_ci (parse uppercase_char) i c r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> uppercase_chars \<and> c = [hd i])"
  unfolding has_result_ci_def has_result_c_def
  apply (auto simp add: uppercase_char_has_result)
  subgoal using list.collapse by fastforce
  subgoal by (metis hd_append2 list.collapse not_Cons_self2 self_append_conv2 tl_append2)
  done



\<comment> \<open>fp NER\<close>
lemma uppercase_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print uppercase_char) i \<longleftrightarrow> False"
  by (simp add: uppercase_char_def any_from_set_p_is_nonterm)

lemma uppercase_char_p_is_error[fp_NER]:
  "p_is_error (print uppercase_char) i \<longleftrightarrow> i \<notin> uppercase_chars"
  by (simp add: uppercase_char_def any_from_set_p_is_error)

lemma uppercase_char_p_has_result[fp_NER]:
  "p_has_result (print uppercase_char) i s \<longleftrightarrow> i \<in> uppercase_chars \<and> s = [i]"
  by (simp add: uppercase_char_def any_from_set_p_has_result)



\<comment> \<open>PNGI, PASI\<close>
lemma uppercase_char_PNGI:
  "PNGI (parse uppercase_char)"
  unfolding uppercase_char_def
  by (rule any_from_set_PNGI)

lemma uppercase_char_PASI:
  "PASI (parse uppercase_char)"
  unfolding uppercase_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Does not peek past end\<close>
lemma uppercase_char_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse uppercase_char)"
  unfolding uppercase_char_def
  by (clarsimp simp add: peek_past_end_simps)



\<comment> \<open>First printed char\<close>
lemma uppercase_char_fpci:
  shows "first_printed_chari (print uppercase_char) i c \<longleftrightarrow> (i \<in> uppercase_chars \<and> c = i)"
  unfolding first_printed_chari_def
  by (clarsimp simp add: uppercase_char_p_has_result; blast)



\<comment> \<open>Well Formed\<close>
lemma uppercase_char_well_formed:
  "bidef_well_formed uppercase_char"
  by (simp add: uppercase_char_def any_from_set_well_formed)



end