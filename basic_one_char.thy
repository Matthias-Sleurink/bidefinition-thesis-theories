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
  "one_char_printer c = Some [c]"

definition one_char :: "char bidef" where
  "one_char = (one_char_parser, one_char_printer)"



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



\<comment> \<open>FP NER\<close>
lemma one_char_p_has_result[fp_NER]:
  "p_has_result (print one_char) i s \<longleftrightarrow> [i] = s"
  "p_has_result one_char_printer i s \<longleftrightarrow> [i] = s"
  by (simp add: one_char_def p_has_result_def)+

lemma one_char_p_is_error[fp_NER]:
  "p_is_error (print one_char) i \<longleftrightarrow> False"
  "p_is_error one_char_printer i \<longleftrightarrow> False"
  by (simp add: one_char_def p_is_error_def)+



\<comment> \<open>PNGI, PASI\<close>
lemma one_char_PNGI:
  "PNGI (parse one_char)"
  by (simp add: PNGI_def NER_simps)

lemma one_char_PASI:
  "PASI (parse one_char)"
  by (simp add: PASI_def NER_simps)



\<comment> \<open>Well Formed\<close>
lemma one_char_well_formed[bi_well_formed_simps]:
  "bidef_well_formed one_char"
  apply wf_init
  subgoal by (simp add: parser_can_parse_print_result_def NER_simps fp_NER)
  subgoal by (simp add: printer_can_print_parse_result_def fp_NER)
  done



end