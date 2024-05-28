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

lemma mono_separated_by1[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "mono_bd B"
  shows "mono_bd (\<lambda>f. separated_by1 (A f) (B f) oracle)"
  unfolding separated_by1_def using assms
  by pf_mono_prover



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
\<comment> \<open>TODO: We should be able to do something similar to then here.\<close>
lemma separated_by1_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse (separated_by1 elem sep oracle))"
  unfolding separated_by1_def
  apply (clarsimp intro!: peek_past_end_simps)
  oops



section \<open>Does not consume past char\<close>
\<comment> \<open>TODO: We should be able to do something similar to then here.\<close>
lemma separated_by1_does_not_consume_past_char3:
  shows "does_not_consume_past_char3 (parse (separated_by1 elem sep oracle)) c"
  unfolding separated_by1_def
  oops



section \<open>First Printed/Parsed char\<close>
lemma separated_by1_fpci[fpci_simps]:
  "first_printed_chari (print (separated_by1 elem sep oracle)) [] c \<longleftrightarrow> False"
  "first_printed_chari (print (separated_by1 elem sep oracle)) [i] c \<longleftrightarrow> first_printed_chari (print elem) i c"
  "first_printed_chari (print (separated_by1 elem sep oracle)) (i#is) c \<longleftrightarrow>(
      if p_has_result (print elem) i [] then
        (first_printed_chari (print (many (b_then sep elem))) (map (Pair oracle) is) c)
      else
        (first_printed_chari (print elem) i c \<and> (\<exists>t. p_has_result (print (many (b_then sep elem))) (map (Pair oracle) is) t))
)"
  unfolding separated_by1_def
  subgoal by (clarsimp simp add: fpci_simps)
  subgoal by (auto simp add: fpci_simps ex_many_p_has_result)
  subgoal by (auto simp add: fpci_simps)
  done



lemma separated_by1_fpc[fpc_simps]:
  \<comment> \<open>TODO: the other cases?\<close>
  "fpc (parse (separated_by1 elem sep oracle)) [] c \<longleftrightarrow> False"
  unfolding separated_by1_def
  by (clarsimp simp add: fpc_simps)



section \<open>Well Formed\<close>
lemma snd_Pair[simp]:
  "snd \<circ> Pair x = id"
  by fastforce

lemma separated_by1_well_formed:
  assumes good_oracle: "\<exists>t. p_has_result (print sep) oracle t"
  assumes wf_elem: "bidef_well_formed elem"
  \<comment> \<open>Allow the user to choose does not peek past char, does not eat into, etc as method for collision.\<close>
  assumes wf_whole: "bidef_well_formed (b_then elem (many (b_then sep elem)))"
  shows "bidef_well_formed (separated_by1 elem sep oracle)"
  unfolding separated_by1_def
  apply (auto intro!: ftransform_well_formed)
  subgoal
    unfolding ftrans_wf_funcs_parser_can_parse_def
    apply (auto simp add: wf_whole[THEN get_parser_can_parse_unfold] split: list.splits)
    subgoal for pr e1 elems
      apply (rule exI[of _ \<open>[]\<close>])
      apply (rule exI[of _ \<open>map (Pair oracle) elems\<close>])
      using wf_whole[THEN get_parser_can_parse_unfold]
      by clarsimp
    done
  subgoal
    unfolding ftrans_wf_funcs_printer_can_print_def
    apply (auto simp add: NER_simps fp_NER wf_elem[THEN get_printer_can_print_unfold])
    subgoal for i l e1 ses l'
      apply (induction ses arbitrary: i l e1 l'; clarsimp simp add: fp_NER) \<comment> \<open>Empty case dispatched\<close>
      unfolding many_p_has_result_safe(2) many_has_result_safe(2) b_then_has_result(1) b_then_p_has_result(1)
      apply (auto simp add: good_oracle)
      using wf_elem[THEN get_printer_can_print_unfold]
      by blast
    done
  subgoal by (rule wf_whole)
  done



end