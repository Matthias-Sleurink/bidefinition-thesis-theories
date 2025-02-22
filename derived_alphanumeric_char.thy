theory derived_alphanumeric_char
  imports basic_definitions
          derived_any_from_set
          derived_alphabet_char
          derived_digit_char
begin

definition alphanumeric_chars :: "char set" where
  "alphanumeric_chars = alphabet_chars \<union> digit_chars"


definition alphanumeric_char :: "char bidef" where
  "alphanumeric_char = any_from_set alphanumeric_chars"
(*
fun sum_take :: "('\<alpha> + '\<alpha>) \<Rightarrow> '\<alpha>" where
  "sum_take (Inl a) = a"
| "sum_take (Inr a) = a"


definition alphanumeric_char :: "char bidef" where
  "alphanumeric_char = transform
                   (sum_take :: (char+char) \<Rightarrow> char)
                   ((\<lambda>c. if c \<in> lowercase_chars then Inl c else Inr c) :: char \<Rightarrow> (char + char))
                   ((or alphabet_char digit_char) :: (char + char) bidef)"
*)


\<comment> \<open>NER\<close>
lemma alphanumeric_char_is_nonterm[NER_simps]:
  "is_nonterm (parse alphanumeric_char) i \<longleftrightarrow> False"
  by (simp add: alphanumeric_char_def any_from_set_is_nonterm)

lemma alphanumeric_char_is_error[NER_simps]:
  "is_error (parse alphanumeric_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> alphanumeric_chars)"
  by (simp add: alphanumeric_char_def any_from_set_is_error)

lemma alphanumeric_char_has_result[NER_simps]:
  "has_result (parse alphanumeric_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> alphanumeric_chars)"
  by (auto simp add: alphanumeric_char_def any_from_set_has_result)

lemma alphanumeric_char_has_result_ci[NER_simps]:
  "has_result_ci (parse alphanumeric_char) i c r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> alphanumeric_chars \<and> c = [hd i])"
  unfolding has_result_ci_def has_result_c_def
  apply (auto simp add: alphanumeric_char_has_result)
  subgoal using list.collapse by fastforce
  subgoal by (metis hd_append2 list.collapse not_Cons_self2 self_append_conv2 tl_append2)
  done



\<comment> \<open>fp NER\<close>
lemma alphanumeric_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print alphanumeric_char) i \<longleftrightarrow> False"
  by (simp add: alphanumeric_char_def any_from_set_p_is_nonterm)

lemma alphanumeric_char_p_is_error[fp_NER]:
  "p_is_error (print alphanumeric_char) i \<longleftrightarrow> i \<notin> alphanumeric_chars"
  by (simp add: alphanumeric_char_def any_from_set_p_is_error)

lemma alphanumeric_char_p_has_result[fp_NER]:
  "p_has_result (print alphanumeric_char) i s \<longleftrightarrow> i \<in> alphanumeric_chars \<and> s = [i]"
  by (simp add: alphanumeric_char_def any_from_set_p_has_result)

lemma alphanumeric_char_print_empty[print_empty, fp_NER]:
  "p_has_result (print alphanumeric_char) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: alphanumeric_char_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma alphanumeric_char_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse alphanumeric_char)"
  unfolding alphanumeric_char_def
  by (intro PASI_PNGI_intros)

lemma alphanumeric_char_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse alphanumeric_char)"
  unfolding alphanumeric_char_def
  by (intro PASI_PNGI_intros)



\<comment> \<open>Does not peek past end\<close>
lemma alphanumeric_char_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse alphanumeric_char)"
  unfolding alphanumeric_char_def
  by (clarsimp simp add: peek_past_end_simps)



\<comment> \<open>First printed char\<close>
lemma alphanumeric_char_fpci[fpci_simps]:
  shows "first_printed_chari (print alphanumeric_char) i c \<longleftrightarrow> (i \<in> alphanumeric_chars \<and> c = i)"
  unfolding first_printed_chari_def
  by (clarsimp simp add: alphanumeric_char_p_has_result; blast)



\<comment> \<open>Well Formed\<close>
lemma alphanumeric_char_well_formed:
  "bidef_well_formed alphanumeric_char"
  by (simp add: alphanumeric_char_def any_from_set_well_formed)



end