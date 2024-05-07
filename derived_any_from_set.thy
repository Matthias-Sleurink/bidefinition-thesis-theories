theory derived_any_from_set
  imports basic_definitions
          derived_char_for_predicate
begin

text \<open>
Parse any character in this set
\<close>

definition any_from_set :: "char set \<Rightarrow> char bidef" where
  "any_from_set s = char_for_predicate (\<lambda>found. found\<in>s)"



\<comment> \<open>NER\<close>
lemma any_from_set_is_nonterm[NER_simps]:
  "is_nonterm (parse (any_from_set s)) i \<longleftrightarrow> False"
  unfolding any_from_set_def
  by (simp add: NER_simps)

lemma any_from_set_is_error[NER_simps]:
  "is_error (parse (any_from_set s)) i \<longleftrightarrow> i = [] \<or> hd i \<notin> s"
  unfolding any_from_set_def
  by (simp add: NER_simps)

lemma any_from_set_has_result[NER_simps]:
  "has_result (parse (any_from_set s)) i r l \<longleftrightarrow> i \<noteq> [] \<and> hd i \<in> s \<and> i = r#l"
  unfolding any_from_set_def
  by (simp add: NER_simps)

lemma any_from_set_has_result_ci[NER_simps]:
  "has_result_ci (parse (any_from_set s)) i c r l \<longleftrightarrow> i \<noteq> [] \<and> c = [hd i]  \<and> hd i \<in> s \<and> i = r#l"
  unfolding any_from_set_def
  by (simp add: NER_simps)



\<comment> \<open>FP NER\<close>
lemma any_from_set_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (any_from_set s)) i \<longleftrightarrow> False"
  unfolding any_from_set_def
  by (simp add: fp_NER)

lemma any_from_set_p_is_error[fp_NER]:
  "p_is_error (print (any_from_set s)) i \<longleftrightarrow> i \<notin> s"
  unfolding any_from_set_def
  by (simp add: fp_NER)

lemma any_from_set_p_has_result[fp_NER]:
  "p_has_result (print (any_from_set s)) i pr \<longleftrightarrow> i\<in>s \<and> pr = [i]"
  unfolding any_from_set_def
  by (auto simp add: fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma any_from_set_PNGI:
  "PNGI (parse (any_from_set s))"
  unfolding any_from_set_def
  by (rule char_for_predicate_PNGI)

lemma any_from_set_PASI:
  "PASI (parse (any_from_set s))"
  unfolding any_from_set_def
  by (rule char_for_predicate_PASI)



\<comment> \<open>Does not peek past end\<close>
lemma any_from_set_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse (any_from_set s))"
  unfolding any_from_set_def
  by (clarsimp simp add: peek_past_end_simps)



\<comment> \<open>First printed char\<close>
lemma any_from_set_fpci[fpci_simps]:
  shows "first_printed_chari (print (any_from_set S)) i c \<longleftrightarrow> (i\<in>S \<and> c = i)"
  unfolding first_printed_chari_def
  by (clarsimp simp add: any_from_set_p_has_result; blast)



\<comment> \<open>Well formed\<close>
lemma any_from_set_well_formed[bi_well_formed_simps]:
  "bidef_well_formed (any_from_set s)"
  by (simp add: any_from_set_def char_for_predicate_well_formed)


end