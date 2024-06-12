theory basic_fail
  imports types
begin

text \<open>
The fail bi-definition never succeeds.
Hence, it also never succeeds printing.
\<close>

\<comment> \<open>Since this is a value, and not a function, ML does not allow us to have this be polymorphic.\<close>
\<comment> \<open>As such, we remove this equation from the code set.\<close>
\<comment> \<open>And then use the fail' and fail = fail' () fun and lemma\<close>
\<comment> \<open>to create the code equations for codegen.\<close>

fun fail_p :: "'\<alpha> parser" where
  "fail_p _ = terminate_with None"
fun fail_pr :: "'\<alpha> printer" where
  "fail_pr _ = terminate_with None"
definition fail :: "'\<alpha> bidef" where [code del]:
  "fail = bdc fail_p fail_pr "

fun fail' :: "unit \<Rightarrow> 'a bd" where
  "fail' _ = bdc (\<lambda>_. Some None) (\<lambda>_. Some None)"

lemma [code_unfold]: "fail = fail' ()"
  by (auto simp add: fail_def bdc_eq_iff)

lemma mono_fail[partial_function_mono]:
  shows "mono_bd (\<lambda>f. fail)"
  by pf_mono_prover



section NER
lemma fail_is_nonterm[NER_simps]:
  "is_nonterm (parse fail) i \<longleftrightarrow> False"
  "is_nonterm fail_p       i \<longleftrightarrow> False"
  by (simp add: fail_def is_nonterm_def)+

lemma fail_is_error[NER_simps]:
  "is_error (parse fail) i \<longleftrightarrow> True"
  "is_error fail_p       i \<longleftrightarrow> True"
  by (simp add: fail_def is_error_def)+

lemma fail_has_result[NER_simps]:
  "has_result (parse fail) i r l \<longleftrightarrow> False"
  "has_result fail_p       i r l \<longleftrightarrow> False"
  by (simp add: fail_def has_result_def)+

lemma fail_has_result_c[NER_simps]:
  "has_result_c (parse fail) c r l \<longleftrightarrow> False"
  "has_result_c fail_p       c r l \<longleftrightarrow> False"
  by (simp add: has_result_c_def fail_has_result)+

lemma fail_has_result_ci[NER_simps]:
  "has_result_ci (parse fail) i c r l \<longleftrightarrow> False"
  "has_result_ci fail_p       i c r l \<longleftrightarrow> False"
  by (simp add: has_result_ci_def fail_has_result_c)+



section \<open>FP NER\<close>
lemma fail_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print fail) i \<longleftrightarrow> False"
  "p_is_nonterm fail_pr i \<longleftrightarrow> False"
  by (simp add: fail_def p_is_nonterm_def)+

lemma fail_p_is_error[fp_NER]:
  "p_is_error (print fail) i \<longleftrightarrow> True"
  "p_is_error fail_pr      i \<longleftrightarrow> True"
  by (simp add: fail_def p_is_error_def)+

lemma fail_p_has_result[fp_NER]:
  "p_has_result (print fail) i r \<longleftrightarrow> False"
  "p_has_result fail_pr      i r \<longleftrightarrow> False"
  by (simp add: fail_def p_has_result_def)+

lemma fail_print_empty[print_empty, fp_NER]:
  "p_has_result (print fail) i [] \<longleftrightarrow> False"
  by (rule fail_p_has_result(1))



section \<open>PASI PNGI\<close>
lemma fail_PNGI[PASI_PNGI]:
  "PNGI (parse fail)"
  by (simp add: PNGI_def NER_simps)

lemma fail_PASI[PASI_PNGI]:
  "PASI (parse fail)"
  by (simp add: PASI_def NER_simps)



section Charset
lemma charset_fail:
  "charset (parse fail) = {}"
  unfolding charset_def
  by (clarsimp simp add: NER_simps)

lemma first_chars_fail:
  "first_chars (print fail) = {}"
  unfolding first_chars_def
  by (clarsimp simp add: fp_NER)



section \<open>Does not peek past end\<close>
lemma fail_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse fail)"
  unfolding does_not_peek_past_end_def
  by (clarsimp simp add: fail_has_result)



section \<open>Does not consume past char\<close>
lemma fail_does_not_consume_past_char3:
  shows "does_not_consume_past_char3 (parse fail) ch"
  unfolding does_not_consume_past_char3_def
  by (clarsimp simp add: fail_has_result)



section \<open>First Printed/Parsed char\<close>
lemma fail_fpci[fpci_simps]:
  shows "\<nexists>i c. first_printed_chari (print fail) i c"
        "first_printed_chari (print fail) i c \<longleftrightarrow> False"
  unfolding first_printed_chari_def
  by (clarsimp simp add: fail_p_has_result)+

lemma fail_fpc[fpc_simps]:
  shows "\<nexists>i c. fpc (parse fail) i c"
        "fpc (parse fail) i c \<longleftrightarrow> False"
  unfolding fpc_def
  by (clarsimp simp add: fail_has_result)+



section \<open>Well Formed\<close>
lemma fail_well_formed:
  "bidef_well_formed fail"
  apply wf_init
  subgoal by (rule fail_PNGI)
  subgoal by (simp add: parser_can_parse_print_result_def fp_NER)
  subgoal by (simp add: printer_can_print_parse_result_def NER_simps)
  done



end