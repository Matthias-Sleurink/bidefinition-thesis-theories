theory basic_return
  imports types
begin

fun return_p :: "'\<alpha> \<Rightarrow> '\<alpha> parser" where
  "return_p d i = terminate_with (Some (d, i))"
fun return_pr :: "'\<alpha> \<Rightarrow> '\<alpha> printer" where
  "return_pr d i = terminate_with (if d=i then Some [] else None)"

definition return :: "'\<alpha> \<Rightarrow> '\<alpha> bidef" where
  "return d = bdc (return_p d) (return_pr d)"

lemma mono_return[partial_function_mono]:
  shows "mono_bd (\<lambda>f. return i)"
  by pf_mono_prover



\<comment> \<open>NER\<close>
lemma return_is_nonterm[NER_simps]:
  "\<not>is_nonterm (parse (return v)) i"
  "\<not>is_nonterm (return_p v) i"
  "\<not>is_nonterm (\<lambda> i. terminate_with (Some (v, i))) i"
  "\<not>is_nonterm (\<lambda> i. Some (Some (v, i))) i"
  by (simp add: return_def is_nonterm_def)+

lemma return_is_error[NER_simps]:
  "\<not>is_error (parse (return v)) i"
  "\<not>is_error (return_p v) i"
  "\<not>is_error (\<lambda> i. terminate_with (Some (v, i))) i"
  "\<not>is_error (\<lambda> i. Some (Some (v, i))) i"
  by (simp add: return_def is_error_def)+

lemma return_has_result[NER_simps]:
  "has_result (parse (return v)) i r l \<longleftrightarrow> v=r \<and> i = l"
  "has_result (return_p v) i r l \<longleftrightarrow> v=r \<and> i = l"
  "has_result (\<lambda> i. terminate_with (Some (v, i))) i r l \<longleftrightarrow> v=r \<and> i = l"
  "has_result (\<lambda> i. Some (Some (v, i))) i r l \<longleftrightarrow> v=r \<and> i = l"
  by (simp add: return_def has_result_def)+

lemma return_has_result_c[NER_simps]:
  "has_result_c (parse (return v))                  c r l \<longleftrightarrow> v=r \<and> c = []"
  "has_result_c (return_p v)                        c r l \<longleftrightarrow> v=r \<and> c = []"
  "has_result_c (\<lambda> i. terminate_with (Some (v, i))) c r l \<longleftrightarrow> v=r \<and> c = []"
  "has_result_c (\<lambda> i. Some (Some (v, i)))           c r l \<longleftrightarrow> v=r \<and> c = []"
  by (simp add: return_def has_result_c_def NER_simps)+

lemma return_has_result_ci[NER_simps]:
  "has_result_ci (parse (return v))                  i c r l \<longleftrightarrow> v=r \<and> c = [] \<and> l = i"
  "has_result_ci (return_p v)                        i c r l \<longleftrightarrow> v=r \<and> c = [] \<and> l = i"
  "has_result_ci (\<lambda> i. terminate_with (Some (v, i))) i c r l \<longleftrightarrow> v=r \<and> c = [] \<and> l = i"
  "has_result_ci (\<lambda> i. Some (Some (v, i)))           i c r l \<longleftrightarrow> v=r \<and> c = [] \<and> l = i"
  by (auto simp add: return_def has_result_ci_def NER_simps)+



\<comment> \<open>FP NER\<close>
lemma return_p_has_result[fp_NER]:
  "p_has_result (print (return v)) v' i \<longleftrightarrow> i = [] \<and> v = v'"
  "p_has_result (return_pr v) v' i \<longleftrightarrow> i = [] \<and> v = v'"
  by (auto simp add: return_def p_has_result_def)+

lemma return_fp_is_error[fp_NER]:
  "p_is_error (print (return v)) v' \<longleftrightarrow> v \<noteq> v'"
  "p_is_error (return_pr v) v' \<longleftrightarrow> v \<noteq> v'"
  by (simp add: p_is_error_def return_def)+

lemma return_fp_is_nonterm[fp_NER]:
  "p_is_nonterm (print (return v)) v' \<longleftrightarrow> False"
  "p_is_nonterm (return_pr v) v' \<longleftrightarrow> False"
  by (simp add: p_is_nonterm_def return_def)+

lemma return_print_empty[print_empty, fp_NER]:
  "p_has_result (print (return v)) i [] \<longleftrightarrow> i = v"
  by (clarsimp simp add: fp_NER; fast)



\<comment> \<open>PNGI, PASI\<close>
lemma return_PNGI[PASI_PNGI]:
  "PNGI (parse (return t))"
  by (simp add: PNGI_def NER_simps)

lemma return_PASI[PASI_PNGI]:
  "PASI (parse (return t)) \<longleftrightarrow> False"
  by (simp add: PASI_def NER_simps)



\<comment> \<open>Charset\<close>
lemma charset_return:
  "charset (parse (return v)) = {}"
  unfolding charset_def
  by (clarsimp simp add: NER_simps)

lemma first_chars_return:
  "first_chars (print (return v)) = {}"
  unfolding first_chars_def
  by (clarsimp simp add: fp_NER)



\<comment> \<open>Does not peek past end\<close>
lemma return_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse (return v))"
  unfolding does_not_peek_past_end_def
  by (clarsimp simp add: return_has_result)


\<comment> \<open>Does not consume past char.\<close>
lemma return_does_not_consume_past_char3:
  shows "does_not_consume_past_char3 (parse (return a)) ch"
  unfolding does_not_consume_past_char3_def
  by (clarsimp simp add: return_has_result)



\<comment> \<open>First printed char\<close>
lemma return_fpci[fpci_simps]:
  shows "\<nexists>v i c. first_printed_chari (print (return v)) i c"
        "first_printed_chari (print (return v)) i c \<longleftrightarrow> False"
  unfolding first_printed_chari_def
  by (clarsimp simp add: return_p_has_result)+

lemma return_fpc[fpc_simps]:
  shows "fpc (parse (return t)) i c \<longleftrightarrow> False"
  unfolding fpc_def return_has_result
  by clarsimp



\<comment> \<open>Well Formed\<close>
lemma b_return_well_formed:
  "bidef_well_formed (return v)"
  apply wf_init
  subgoal by (rule return_PNGI)
  subgoal by (simp add: parser_can_parse_print_result_def
                        return_def fp_NER NER_simps)
  subgoal by (simp add: printer_can_print_parse_result_def
                        return_def fp_NER NER_simps)
  done



end