theory basic_return
  imports types
begin

fun return_p :: "'\<alpha> \<Rightarrow> '\<alpha> parser" where
  "return_p d i = terminate_with (Some (d, i))"
fun return_pr :: "'\<alpha> \<Rightarrow> '\<alpha> printer" where
  "return_pr d i = (if d=i then Some [] else None)"

definition return :: "'\<alpha> \<Rightarrow> '\<alpha> bidef" where
  "return d = (return_p d, return_pr d)"



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



\<comment> \<open>FP NER\<close>
lemma return_p_has_result[fp_NER]:
  "p_has_result (print (return v)) v' i \<longleftrightarrow> i = [] \<and> v = v'"
  "p_has_result (return_pr v) v' i \<longleftrightarrow> i = [] \<and> v = v'"
  by (auto simp add: return_def p_has_result_def)+

lemma return_fp_is_error[fp_NER]:
  "p_is_error (print (return v)) v' \<longleftrightarrow> v \<noteq> v'"
  "p_is_error (return_pr v) v' \<longleftrightarrow> v \<noteq> v'"
  by (simp add: p_is_error_def return_def)+



\<comment> \<open>Well Formed\<close>
lemma b_return_well_formed:
  "bidef_well_formed (return v)"
  apply wf_init
  subgoal by (simp add: parser_can_parse_print_result_def
                        return_def fp_NER NER_simps)
  subgoal by (simp add: printer_can_print_parse_result_def
                        return_def fp_NER NER_simps)
  done



end