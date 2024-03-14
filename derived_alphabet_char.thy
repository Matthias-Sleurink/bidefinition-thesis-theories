theory derived_alphabet_char
  imports basic_definitions
          derived_any_from_set
          derived_lowercase_char
          derived_uppercase_char
begin

definition alphabet_chars :: "char set" where
  "alphabet_chars = lowercase_chars \<union> uppercase_chars"


definition alphabet_char :: "char bidef" where
  "alphabet_char = any_from_set alphabet_chars"
(*
fun sum_take :: "('\<alpha> + '\<alpha>) \<Rightarrow> '\<alpha>" where
  "sum_take (Inl a) = a"
| "sum_take (Inr a) = a"


definition alphabet_char :: "char bidef" where
  "alphabet_char = transform
                   (sum_take :: (char+char) \<Rightarrow> char)
                   ((\<lambda>c. if c \<in> lowercase_chars then Inl c else Inr c) :: char \<Rightarrow> (char + char))
                   ((or lowercase_char uppercase_char) :: (char + char) bidef)"
*)


\<comment> \<open>NER\<close>
lemma alphabet_char_is_nonterm[NER_simps]:
  "is_nonterm (parse alphabet_char) i \<longleftrightarrow> False"
  by (simp add: alphabet_char_def any_from_set_is_nonterm)

lemma alphabet_char_is_error[NER_simps]:
  "is_error (parse alphabet_char) i \<longleftrightarrow> i = [] \<or> (hd i \<notin> alphabet_chars)"
  by (simp add: alphabet_char_def any_from_set_is_error)

lemma alphabet_char_has_result[NER_simps]:
  "has_result (parse alphabet_char) i r l \<longleftrightarrow> i \<noteq> [] \<and> (r = hd i \<and> l = tl i \<and> r \<in> alphabet_chars)"
  by (auto simp add: alphabet_char_def any_from_set_has_result)



\<comment> \<open>fp NER\<close>
lemma alphabet_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print alphabet_char) i \<longleftrightarrow> False"
  by (simp add: alphabet_char_def any_from_set_p_is_nonterm)

lemma alphabet_char_p_is_error[fp_NER]:
  "p_is_error (print alphabet_char) i \<longleftrightarrow> i \<notin> alphabet_chars"
  by (simp add: alphabet_char_def any_from_set_p_is_error)

lemma alphabet_char_p_has_result[fp_NER]:
  "p_has_result (print alphabet_char) i s \<longleftrightarrow> i \<in> alphabet_chars \<and> s = [i]"
  by (simp add: alphabet_char_def any_from_set_p_has_result)



\<comment> \<open>PNGI, PASI\<close>
lemma alphabet_char_PNGI:
  "PNGI (parse alphabet_char)"
  unfolding alphabet_char_def
  by (rule any_from_set_PNGI)

lemma alphabet_char_PASI:
  "PASI (parse alphabet_char)"
  unfolding alphabet_char_def
  by (rule any_from_set_PASI)



\<comment> \<open>Well Formed\<close>
lemma alphabet_char_well_formed:
  "bidef_well_formed alphabet_char"
  by (simp add: alphabet_char_def any_from_set_well_formed)



end