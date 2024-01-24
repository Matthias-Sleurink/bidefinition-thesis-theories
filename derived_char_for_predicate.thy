theory derived_char_for_predicate
  imports basic_definitions
          derived_dep_then
begin

definition char_for_predicate :: "(char \<Rightarrow> bool) \<Rightarrow> char bidef" where
  "char_for_predicate p = dep_then one_char (\<lambda>found. if p found then return found else fail) id"



\<comment> \<open>NER\<close>
lemma char_for_predicate_is_nonterm[NER_simps]:
  "is_nonterm (parse (char_for_predicate p)) i \<longleftrightarrow> False"
  by (simp add: char_for_predicate_def NER_simps)

lemma char_for_predicate_is_error[NER_simps]:
  "is_error (parse (char_for_predicate p)) i \<longleftrightarrow> i = [] \<or> (\<not>p (hd i))"
  apply (auto simp add: char_for_predicate_def NER_simps)
  using list.exhaust_sel by auto

lemma char_for_predicate_has_result[NER_simps]:
  "has_result (parse (char_for_predicate p)) i r l \<longleftrightarrow> i\<noteq>[] \<and> p (hd i) \<and> i = r#l"
  unfolding char_for_predicate_def
  apply (simp add: NER_simps)
  by fastforce



\<comment> \<open>fp NER\<close>
lemma char_for_predicate_p_is_error[fp_NER]:
  "p_is_error (print (char_for_predicate p)) i \<longleftrightarrow> \<not>p i"
  by (simp add: char_for_predicate_def fp_NER)

lemma char_for_predicate_p_has_result[fp_NER]:
  "p_has_result (print (char_for_predicate p)) i r \<longleftrightarrow> r = [i] \<and> p i"
  by (auto simp add: char_for_predicate_def fp_NER)



\<comment> \<open>Well Formed\<close>
lemma char_for_predicate_well_formed:
  "bidef_well_formed (char_for_predicate p)"
  apply wf_init
  subgoal by (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
  by (auto simp add: printer_can_print_parse_result_def fp_NER NER_simps)


end