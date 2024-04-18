theory derived_this_string
  imports basic_definitions
          derived_this_char
begin

definition this_string :: "char list \<Rightarrow> char list bidef" where
  "this_string = m_map this_char"


\<comment> \<open>NER\<close>
lemma this_string_is_nonterm[NER_simps]:
  "is_nonterm (parse (this_string s)) i \<longleftrightarrow> False"
  unfolding this_string_def m_map_def
  by (simp add: this_char_is_nonterm mmap_not_nonterm_if_param_never_nonterm)

lemma this_string_is_error[NER_simps]:
  "is_error (parse (this_string [])) i \<longleftrightarrow> False"
  "is_error (parse (this_string (c#cs))) i \<longleftrightarrow> i = [] \<or> (hd i \<noteq> c \<or> is_error (parse (this_string cs)) (tl i))"
  unfolding this_string_def
  subgoal by (simp add: NER_simps)
  apply (subst m_map_is_error)
  using this_char_has_result this_char_is_error by fastforce

lemma this_string_has_result[NER_simps]:
  "has_result (parse (this_string s)) i r l \<longleftrightarrow> s = r \<and> i = r@l"
  unfolding this_string_def
  apply (induction s arbitrary: i r l)
  by (auto simp add: NER_simps)

lemma this_string_has_result_ci[NER_simps]:
  "has_result_ci (parse (this_string s)) i c r l \<longleftrightarrow> r=s \<and> r@l=i \<and> c=s"
  unfolding has_result_ci_def has_result_c_def
  by (auto simp add: NER_simps)



\<comment> \<open>FP ner\<close>
lemma this_string_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (this_string s)) i \<longleftrightarrow> False"
  unfolding this_string_def
  apply (induction s arbitrary: i)
  by (auto simp add: fp_NER)

lemma this_string_p_is_error[fp_NER]:
  "p_is_error (print (this_string s)) i \<longleftrightarrow> s \<noteq> i"
  unfolding this_string_def
  apply (induction s arbitrary: i)
  subgoal by (auto simp add: fp_NER)
  apply (auto simp add: fp_NER)
  by (metis one_char_parser.cases)

lemma this_string_p_has_result[fp_NER]:
  "p_has_result (print (this_string s)) i r \<longleftrightarrow> r = s \<and> i = s"
  unfolding this_string_def
  apply (induction s arbitrary: i r)
  by (auto simp add: fp_NER)



\<comment> \<open>PASI, PNGI\<close>
lemma this_string_PNGI:
  "PNGI (parse (this_string s))"
  by (simp add: this_string_def this_char_PNGI PNGI_m_map)

lemma this_string_PASI:
  "s \<noteq> [] \<Longrightarrow> PASI (parse (this_string s))"
  by (simp add: this_string_def this_char_PASI PASI_m_map)



\<comment> \<open>Well formed\<close>
lemma this_string_wf:
  "bidef_well_formed (this_string s)"
  apply wf_init
  subgoal by (rule this_string_PNGI)
  subgoal by (auto simp add: parser_can_parse_print_result_def fp_NER NER_simps)
  subgoal by (auto simp add: printer_can_print_parse_result_def fp_NER NER_simps)
  done



end
