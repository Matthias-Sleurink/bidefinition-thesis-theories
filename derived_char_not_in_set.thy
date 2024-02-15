theory derived_char_not_in_set
  imports basic_definitions
          derived_char_for_predicate
begin

text \<open>
Parse any character in this set
\<close>

definition char_not_in_set :: "char set \<Rightarrow> char bidef" where
  "char_not_in_set s = char_for_predicate (\<lambda>found. found\<notin>s)"



\<comment> \<open>NER\<close>
lemma char_not_in_set_is_nonterm[NER_simps]:
  "is_nonterm (parse (char_not_in_set s)) i \<longleftrightarrow> False"
  unfolding char_not_in_set_def
  by (simp add: NER_simps)

lemma char_not_in_set_is_error[NER_simps]:
  "is_error (parse (char_not_in_set s)) i \<longleftrightarrow> i = [] \<or> hd i \<in> s"
  unfolding char_not_in_set_def
  by (simp add: NER_simps)

lemma char_not_in_set_has_result[NER_simps]:
  "has_result (parse (char_not_in_set s)) i r l \<longleftrightarrow> i \<noteq> [] \<and> hd i \<notin> s \<and> i = r#l"
  unfolding char_not_in_set_def
  by (simp add: NER_simps)



\<comment> \<open>FP NER\<close>
lemma char_not_in_set_p_is_error[fp_NER]:
  "p_is_error (print (char_not_in_set s)) i \<longleftrightarrow> i \<in> s"
  unfolding char_not_in_set_def
  by (simp add: fp_NER)

lemma char_not_in_set_p_has_result[fp_NER]:
  "p_has_result (print (char_not_in_set s)) i pr \<longleftrightarrow> i\<notin>s \<and> pr = [i]"
  unfolding char_not_in_set_def
  by (auto simp add: fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma char_not_in_set_PNGI:
  "PNGI (parse (char_not_in_set s))"
  unfolding char_not_in_set_def
  by (rule char_for_predicate_PNGI)

lemma char_not_in_set_PASI:
  "PASI (parse (char_not_in_set s))"
  unfolding char_not_in_set_def
  by (rule char_for_predicate_PASI)



\<comment> \<open>Well formed\<close>
lemma char_not_in_set_well_formed[bi_well_formed_simps]:
  "bidef_well_formed (char_not_in_set s)"
  by (simp add: char_not_in_set_def char_for_predicate_well_formed)



\<comment> \<open>Examples\<close>
value "parse (char_not_in_set {CHR ''a'', CHR ''b''}) ''apple'' = Some None"
value "parse (char_not_in_set {CHR ''a'', CHR ''b''}) ''pears'' = Some (Some (CHR ''p'', ''ears''))"



end