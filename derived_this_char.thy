theory derived_this_char
  imports basic_definitions
          derived_any_from_set
begin


definition this_char :: "char \<Rightarrow> char bidef" where
  "this_char c = any_from_set {c}"



\<comment> \<open>NER\<close>
lemma this_char_is_nonterm[NER_simps]:
  "is_nonterm (parse (this_char c)) i \<longleftrightarrow> False"
  unfolding this_char_def
  by (auto simp add: NER_simps)

lemma this_char_is_error[NER_simps]:
  "is_error (parse (this_char c)) i \<longleftrightarrow> i = [] \<or> hd i \<noteq> c"
  unfolding this_char_def
  by (auto simp add: NER_simps)

lemma this_char_has_result[NER_simps]:
  "has_result (parse (this_char c)) i r l \<longleftrightarrow> i \<noteq> [] \<and> i = r#l \<and> c = r"
  unfolding this_char_def
  by (auto simp add: NER_simps)

lemma this_char_has_result_ci[NER_simps]:
  "has_result_ci (parse (this_char char)) i c r l \<longleftrightarrow> i \<noteq> [] \<and> r#l=i \<and> r=char \<and> c=[char]"
  unfolding this_char_def
  by (auto simp add: NER_simps)



\<comment> \<open>FP NER\<close>
lemma this_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (this_char c)) i \<longleftrightarrow> False"
  unfolding this_char_def
  by (auto simp add: fp_NER)

lemma this_char_p_is_error[fp_NER]:
  "p_is_error (print (this_char c)) i \<longleftrightarrow> c \<noteq> i"
  unfolding this_char_def
  by (auto simp add: fp_NER)

lemma this_char_p_has_result[fp_NER]:
  "p_has_result (print (this_char c)) i pr \<longleftrightarrow> i = c \<and> pr = [c]"
  unfolding this_char_def
  by (auto simp add: fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma this_char_PNGI:
  "PNGI (parse (this_char c))"
  unfolding this_char_def
  by (rule any_from_set_PNGI)

lemma this_char_PASI:
  "PASI (parse (this_char c))"
  unfolding this_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Well Formed\<close>
lemma this_char_well_formed[bi_well_formed_simps]:
  "bidef_well_formed (this_char c)"
  unfolding this_char_def
  by (simp add: any_from_set_well_formed)



end