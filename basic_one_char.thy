theory basic_one_char
  imports types
begin

text \<open>
One char is the base parser.
\<close>

fun one_char_parser :: "char parser" where
  "one_char_parser [] = terminate_with None"
| "one_char_parser (c#cs) = terminate_with (Some (c, cs))"

fun one_char_printer :: "char printer" where
  "one_char_printer c = terminate_with (Some [c])"

definition one_char :: "char bidef" where
  "one_char = bdc one_char_parser one_char_printer"



\<comment> \<open>NER\<close>
lemma one_char_has_result[NER_simps]:
  "has_result (parse one_char)  i r l \<longleftrightarrow> i = r # l"
  "has_result (one_char_parser) i r l \<longleftrightarrow> i = r # l"
  apply (auto simp add: one_char_def has_result_def)
  by ((cases i); auto)+

lemma one_char_is_error[NER_simps]:
  "is_error (parse one_char)  i \<longleftrightarrow> i = []"
  "is_error (one_char_parser) i \<longleftrightarrow> i = []"
  apply (auto simp add: one_char_def is_error_def)
  using one_char_parser.elims by auto

lemma one_char_is_nonterm[NER_simps]:
  "\<not>is_nonterm (parse one_char) i"
  "\<not>is_nonterm one_char_parser  i"
  apply (auto simp add: one_char_def is_nonterm_def)
  by (metis one_char_parser.elims terminate_with_def)+

lemma one_char_has_result_c[NER_simps]:
  "has_result_c (parse one_char)  c r l \<longleftrightarrow> c = [r]"
  "has_result_c (one_char_parser) c r l \<longleftrightarrow> c = [r]"
  by (simp add: has_result_c_def NER_simps)+

lemma one_char_has_result_ci[NER_simps]:
  "has_result_ci (parse one_char)  i c r l \<longleftrightarrow> c = [r] \<and> (c@l) = i"
  "has_result_ci (one_char_parser) i c r l \<longleftrightarrow> c = [r] \<and> (c@l) = i"
  by (auto simp add: has_result_ci_def NER_simps)+



\<comment> \<open>FP NER\<close>
lemma one_char_p_has_result[fp_NER]:
  "p_has_result (print one_char) i s \<longleftrightarrow> [i] = s"
  "p_has_result one_char_printer i s \<longleftrightarrow> [i] = s"
  by (simp add: one_char_def p_has_result_def)+

lemma one_char_p_is_error[fp_NER]:
  "p_is_error (print one_char) i \<longleftrightarrow> False"
  "p_is_error one_char_printer i \<longleftrightarrow> False"
  by (simp add: one_char_def p_is_error_def)+

lemma one_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print one_char) i \<longleftrightarrow> False"
  "p_is_nonterm one_char_printer i \<longleftrightarrow> False"
  by (simp add: one_char_def p_is_nonterm_def)+



\<comment> \<open>PNGI, PASI\<close>
lemma one_char_PNGI:
  "PNGI (parse one_char)"
  by (simp add: PNGI_def NER_simps)

lemma one_char_PASI:
  "PASI (parse one_char)"
  by (simp add: PASI_def NER_simps)



\<comment> \<open>Charset\<close>
lemma charset_one_char:
  "charset (parse one_char) = UNIV"
  unfolding charset_def
  by (auto simp add: NER_simps)

lemma first_chars_one_char:
  "first_chars (print one_char) = UNIV"
  unfolding first_chars_def
  by (clarsimp simp add: fp_NER)



\<comment> \<open>Does not peek past end\<close>
lemma one_char_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse one_char)"
  unfolding does_not_peek_past_end_def
  by (clarsimp simp add: one_char_has_result)



\<comment> \<open>Well Formed\<close>
lemma one_char_well_formed[bi_well_formed_simps]:
  "bidef_well_formed one_char"
  apply wf_init
  subgoal by (rule one_char_PNGI)
  subgoal by (simp add: parser_can_parse_print_result_def NER_simps fp_NER)
  subgoal by (simp add: printer_can_print_parse_result_def fp_NER)
  done



end