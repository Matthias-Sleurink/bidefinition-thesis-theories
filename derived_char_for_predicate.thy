theory derived_char_for_predicate
  imports basic_definitions
          derived_dep_then
begin

definition char_for_predicate :: "(char \<Rightarrow> bool) \<Rightarrow> char bidef" where
  "char_for_predicate p = dep_then one_char (\<lambda>found. if p found then return found else fail) id"

export_code char_for_predicate in SML
  module_name tes

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

lemma char_for_predicate_has_result_ci[NER_simps]:
  "has_result_ci (parse (char_for_predicate p)) i c r l \<longleftrightarrow> i\<noteq>[] \<and> c = [hd i] \<and> p (hd i) \<and> i = r#l"
  unfolding char_for_predicate_def has_result_ci_def has_result_c_def
  apply (simp add: NER_simps)
  by fastforce



\<comment> \<open>fp NER\<close>
lemma char_for_predicate_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (char_for_predicate p)) i \<longleftrightarrow> False"
  by (simp add: char_for_predicate_def fp_NER)

lemma char_for_predicate_p_is_error[fp_NER]:
  "p_is_error (print (char_for_predicate p)) i \<longleftrightarrow> \<not>p i"
  by (simp add: char_for_predicate_def fp_NER)

lemma char_for_predicate_p_has_result[fp_NER]:
  "p_has_result (print (char_for_predicate p)) i r \<longleftrightarrow> r = [i] \<and> p i"
  by (auto simp add: char_for_predicate_def fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma char_for_predicate_PNGI:
  "PNGI (parse (char_for_predicate p))"
  unfolding char_for_predicate_def
  apply (rule dep_then_PNGI)
  subgoal by (rule one_char_PNGI)
  by (auto simp add: return_PNGI fail_PNGI)


lemma char_for_predicate_PASI:
  "PASI (parse (char_for_predicate p))"
  unfolding char_for_predicate_def
  apply (rule dep_then_PASI_PASI_PNGI)
  subgoal by (rule one_char_PASI)
  by (simp add: return_PNGI fail_PNGI)



\<comment> \<open>Does not peek past end\<close>
lemma char_for_predicate_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse (char_for_predicate p))"
  unfolding does_not_peek_past_end_def
  by (clarsimp simp add: char_for_predicate_has_result)



\<comment> \<open>First printed char\<close>
lemma char_for_predicate_fpci:
  shows "(P i \<and> c = i) \<longleftrightarrow> first_printed_chari (print (char_for_predicate P)) i c"
  unfolding first_printed_chari_def
  by (clarsimp simp add: char_for_predicate_p_has_result; blast)



\<comment> \<open>Well Formed\<close>
lemma char_for_predicate_well_formed:
  "bidef_well_formed (char_for_predicate p)"
  apply wf_init
  subgoal by (rule char_for_predicate_PNGI)
  subgoal by (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
  subgoal by (auto simp add: printer_can_print_parse_result_def fp_NER NER_simps)
  done


end
