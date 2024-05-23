theory derived_separated_by1
  imports basic_definitions
          derived_many
          derived_then
begin

text \<open>
Separated by 1 is not based on separated by itself. As that one has some warts in the impl to allow the 0 case.
\<close>

definition separated_by1 :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> '\<beta> \<Rightarrow> '\<alpha> list bidef" where
  "separated_by1 elem sep oracle = 
        ftransform
        (\<lambda>(x,xs). Some (x#(map snd xs)))
        (\<lambda>i. case i of [] \<Rightarrow> None | x#xs \<Rightarrow> Some (x, map (Pair oracle) xs))
        (b_then elem (many (b_then sep elem)))"



section NER
\<comment> \<open>A better version of this could be made via many not nonterm if underlying never nonterm\<close>
lemma separated_by1_is_nonterm[NER_simps]:
  "is_nonterm (parse (separated_by1 elem sep oracle)) i \<longleftrightarrow> is_nonterm (parse elem) i \<or> (\<exists>r l. has_result (parse elem) i r l \<and> is_nonterm (parse (many (b_then sep elem))) l)"
  by (clarsimp simp add: separated_by1_def NER_simps)

lemma separated_by1_is_error[NER_simps]:
  "is_error (parse (separated_by1 elem sep oracle)) i \<longleftrightarrow> is_error (parse elem) i"
  by (clarsimp simp add: separated_by1_def NER_simps)

lemma separated_by1_has_result_safe[NER_simps]:
  "has_result (parse (separated_by1 elem sep oracle)) i [] l \<longleftrightarrow> False"
  "has_result (parse (separated_by1 elem sep oracle)) i (r#rs) l \<longleftrightarrow> (\<exists>l'. has_result (parse elem) i r l' \<and> (\<exists>ss. length ss = length rs \<and> has_result (parse (many (b_then sep elem))) l' (zip ss rs) l))"
  subgoal by (clarsimp simp add: separated_by1_def NER_simps)
  apply (auto simp add: separated_by1_def NER_simps)
  subgoal for ser l'
    apply (rule exI[of _ l'])
    apply clarsimp
    apply (rule exI[of _ \<open>map fst ser\<close>])
    by (clarsimp simp add: zip_map_fst_snd)
  done

lemma separated_by1_has_result:
  "has_result (parse (separated_by1 elem sep oracle)) i rs l \<longleftrightarrow> (
    case rs of [] \<Rightarrow> False
             | (r#rs') \<Rightarrow> (\<exists>l'. has_result (parse elem) i r l' \<and> (\<exists>ss. length ss = length rs' \<and> has_result (parse (many (b_then sep elem))) l' (zip ss rs') l)))"
  by (cases rs; clarsimp simp add: separated_by1_has_result_safe)



section \<open>FP NER\<close>
lemma separated_by1_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (separated_by1 elem sep oracle)) [] \<longleftrightarrow> False"
  "p_is_nonterm (print (separated_by1 elem sep oracle)) (i#is) \<longleftrightarrow> p_is_nonterm (print elem) i \<or> (\<exists>it. p_has_result (print elem) i it \<and> p_is_nonterm (print (many (b_then sep elem))) (map (Pair oracle) is))"
  subgoal by (clarsimp simp add: separated_by1_def fp_NER)
  by (auto simp add: separated_by1_def fp_NER p_has_result_eq_not_is_error)

lemma separated_by1_p_is_error[fp_NER]:
  "p_is_error (print (separated_by1 elem sep oracle)) [] \<longleftrightarrow> True"
  "p_is_error (print (separated_by1 elem sep oracle)) (i#[]) \<longleftrightarrow> p_is_error (print elem) i"
  "p_is_error (print (separated_by1 elem sep oracle)) (i#is) \<longleftrightarrow> p_is_error (print elem) i \<or> ((\<exists>it. p_has_result (print elem) i it) \<and> (p_is_error (print (many (b_then sep elem))) (map (Pair oracle) is)))"
  subgoal by (clarsimp simp add: separated_by1_def fp_NER)
  subgoal by (clarsimp simp add: separated_by1_def fp_NER)
  by (auto simp add: separated_by1_def fp_NER p_has_result_eq_not_is_error)

lemma separated_by1_p_has_result[fp_NER]:
  "p_has_result (print (separated_by1 elem sep oracle)) [] r \<longleftrightarrow> False"
  "p_has_result (print (separated_by1 elem sep oracle)) (i#[]) r \<longleftrightarrow> p_has_result (print elem) i r"
  "p_has_result (print (separated_by1 elem sep oracle)) (i#is) r \<longleftrightarrow> (\<exists>r1 r2. r=r1@r2 \<and> p_has_result (print elem) i r1 \<and> (p_has_result (print (many (b_then sep elem))) (map (Pair oracle) is) r2))"
  subgoal by (clarsimp simp add: separated_by1_def fp_NER)
  subgoal by (clarsimp simp add: separated_by1_def fp_NER)
  by (auto simp add: separated_by1_def fp_NER)


lemma separated_by1_print_empty[print_empty, fp_NER]:
  "p_has_result (print (separated_by1 elem sep oracle)) [] [] \<longleftrightarrow> False"
  "p_has_result (print (separated_by1 elem sep oracle)) (i#[]) [] \<longleftrightarrow> p_has_result (print elem) i []"
  "p_has_result (print (separated_by1 elem sep oracle)) (i#is) [] \<longleftrightarrow> p_has_result (print elem) i [] \<and> p_has_result (print (many (b_then sep elem))) (map (Pair oracle) is) []"
  by (clarsimp simp add: fp_NER)+



section \<open>PASI PNGI\<close>
lemma separated_by1_PNGI[PASI_PNGI]:
  assumes "PNGI (parse elem)"
  assumes "PASI (parse (b_then sep elem))"
  shows "PNGI (parse (separated_by1 elem sep oracle))"
  by (auto intro!: PASI_PNGI simp add: separated_by1_def assms)
  
lemma separated_by1_PASI[PASI_PNGI]:
  assumes "PASI (parse elem)"
  assumes "PASI (parse (b_then sep elem))"
  shows "PASI (parse (separated_by1 elem sep oracle))"
  unfolding separated_by1_def
  by (clarsimp simp add: ftransform_PASI then_PASI_from_pasi_pngi[OF assms(1)] many_PNGI[OF assms(2)])



section \<open>Does not peek past end\<close>
lemma fail_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse fail)"
  unfolding does_not_peek_past_end_def
  by (clarsimp simp add: fail_has_result)



section \<open>Does not consume past char\<close>
lemma fail_does_not_consume_past_char:
  shows "does_not_consume_past_char (parse fail) ch"
  unfolding does_not_consume_past_char_def
  by (clarsimp simp add: fail_has_result)

lemma fail_does_not_consume_past_char2:
  shows "does_not_consume_past_char2 (parse fail) ch"
  unfolding does_not_consume_past_char2_def
  by (clarsimp simp add: fail_has_result)

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