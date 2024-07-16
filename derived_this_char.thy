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

lemma this_char_print_empty[print_empty, fp_NER]:
  "p_has_result (print (this_char c)) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: this_char_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma this_char_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse (this_char c))"
  unfolding this_char_def
  by (intro PASI_PNGI_intros)

lemma this_char_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse (this_char c))"
  unfolding this_char_def
  by (intro PASI_PNGI_intros)



\<comment> \<open>Does not peek past end\<close>
lemma this_char_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse (this_char c))"
  unfolding this_char_def
  by (clarsimp simp add: peek_past_end_simps)

lemma this_char_does_not_consume_past_char3:
  "does_not_consume_past_char3 (parse (this_char c)) c'"
  by (clarsimp simp add: does_not_consume_past_char3_def NER_simps)


lemma this_char_drop_leftover:
  "has_result (parse (this_char C)) (i @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse (this_char C)) (i@l) r l"
  by (clarsimp simp add: NER_simps)

lemma this_char_drop_leftover_on_error:
  "is_error (parse (this_char C)) (i @ i') \<Longrightarrow> is_error (parse (this_char C)) i"
  by (clarsimp simp add: NER_simps)


\<comment> \<open>First printed char\<close>
lemma this_char_fpci[fpci_simps]:
  "first_printed_chari (print (this_char c)) i c' \<longleftrightarrow> i = c \<and> c' = c"
  by (clarsimp simp add: this_char_def fpci_simps; fast)

lemma this_char_fpc[fpc_simps]:
  "fpc (parse (this_char c)) i c' \<longleftrightarrow> c' = c \<and> c = i"
  by (auto simp add: fpc_def NER_simps)


\<comment> \<open>Well Formed\<close>
lemma this_char_well_formed[bi_well_formed_simps]:
  "bidef_well_formed (this_char c)"
  unfolding this_char_def
  by (simp add: any_from_set_well_formed)



end