theory derived_any_from_set
  imports basic_definitions
          derived_dep_then
begin

text \<open>
Parse any character in this set
\<close>

definition any_from_set :: "char set \<Rightarrow> char bidef" where
  "any_from_set s = dep_then one_char (\<lambda>found. if found\<in>s then return found else fail) id"



\<comment> \<open>NER\<close>
lemma any_from_set_is_nonterm[NER_simps]:
  "is_nonterm (parse (any_from_set s)) i \<longleftrightarrow> False"
  unfolding any_from_set_def
  by (simp add: NER_simps)

lemma any_from_set_is_error[NER_simps]:
  "is_error (parse (any_from_set s)) i \<longleftrightarrow> i = [] \<or> hd i \<notin> s"
  unfolding any_from_set_def
  apply (auto simp add: NER_simps)
  by (meson list.exhaust_sel)

lemma any_from_set_has_result[NER_simps]:
  "has_result (parse (any_from_set s)) i r l \<longleftrightarrow> i \<noteq> [] \<and> hd i \<in> s \<and> i = r#l"
  unfolding any_from_set_def
  apply (clarsimp simp add: NER_simps)
  by force



\<comment> \<open>FP NER\<close>
lemma any_from_set_p_is_error[fp_NER]:
  "p_is_error (print (any_from_set s)) i \<longleftrightarrow> i \<notin> s"
  unfolding any_from_set_def
  by (auto simp add: fp_NER)

lemma any_from_set_p_has_result[fp_NER]:
  "p_has_result (print (any_from_set s)) i pr \<longleftrightarrow> i\<in>s \<and> pr = [i]"
  unfolding any_from_set_def
  by (auto simp add: fp_NER)



\<comment> \<open>Well formed\<close>
lemma any_from_set_well_formed[bi_well_formed_simps]:
  "bidef_well_formed (any_from_set s)"
  apply wf_init
  subgoal by (auto simp add: parser_can_parse_print_result_def fp_NER NER_simps)
  subgoal by (auto simp add: printer_can_print_parse_result_def fp_NER NER_simps)
  done


end