theory example_small_examples
  imports all_definitions
begin

definition "apple = b_then (this_string ''apple'') (optional (this_char CHR ''s''))"

find_theorems "?A \<longleftrightarrow> ?B" "?B \<Longrightarrow> ?A"

lemma apple_errors_on_empty:
  "is_error (parse apple) []"
  unfolding apple_def
  apply (rule b_then_is_error[THEN iffD2]; clarsimp)
  apply (rule this_string_is_error[THEN iffD2])
  by clarsimp

lemma apple_no_empty_print:
  "\<not>p_has_result (print apple) i []"
  unfolding apple_def
  apply (subst b_then_p_has_result(2))
  apply (subst this_string_p_has_result)
  by blast


definition "two_numbers = b_then nat_b nat_b"
lemma tn_pngi:
  "PNGI (parse two_numbers)"
  unfolding two_numbers_def by pasi_pngi

lemma not_pcppr_two_numbers:
  "\<not>parser_can_parse_print_result (parse two_numbers) (print two_numbers)"
  unfolding parser_can_parse_print_result_def
  apply auto
  apply (rule exI[of _ \<open>1\<close>])
  apply (rule exI[of _ \<open>2\<close>])
  apply (rule exI[of _ \<open>''12''\<close>])
  by (clarsimp simp add: fp_NER two_numbers_def NER_simps)

lemma tn_nwf:
  "\<not>bidef_well_formed two_numbers"
  by (auto simp add: bidef_well_formed_def not_pcppr_two_numbers)


lemma example_does_not_peek_past_char:
  "does_not_peek_past_end (parse (b_then (b_then (this_char CHR ''{'') (many (this_char CHR ''A'')))  (this_char CHR ''}'')))"
  apply (rule then_does_not_peek_past_end_from_fpc)
  subgoal for i c
    apply (insert this_char_fpc[of \<open>CHR ''}''\<close> i c]; clarsimp)
    apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
    subgoal by (rule this_char_does_not_peek_past_end)
    subgoal by pasi_pngi
    subgoal
      unfolding this_char_def any_from_set_def
      using many_char_for_predicate_does_not_consume_past_char3
      by fast
    subgoal by pasi_pngi
    done
  subgoal using this_char_has_result by simp
  subgoal by pasi_pngi
  subgoal by (rule this_char_does_not_peek_past_end)
  subgoal by pasi_pngi
  done

lemma many_two_chars_no_peek_past:
  "does_not_consume_past_char3 (parse (many (b_then (this_char CHR ''A'') (this_char CHR ''B'')))) (CHR ''C'')"
  apply (rule many_does_not_consume_past_char3)
  subgoal by pasi_pngi
  subgoal by pasi_pngi
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal for c l l' r
    apply (rule then_can_drop_leftover[of _ _ c l l' r]; clarsimp?)
    subgoal by (rule this_char_drop_leftover)
    subgoal by pasi_pngi
    subgoal by (rule this_char_drop_leftover)
    subgoal by pasi_pngi
    done
  subgoal
    apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
    subgoal by (rule this_char_does_not_peek_past_end)
    subgoal by pasi_pngi
    subgoal by (rule this_char_does_not_consume_past_char3)
    subgoal by pasi_pngi
    done
  subgoal for i c
    using then_does_not_peek_past_end[OF this_char_does_not_peek_past_end this_char_PNGI this_char_does_not_peek_past_end this_char_PNGI, of \<open>CHR ''A''\<close> \<open>CHR ''B''\<close>]
    using dnppe_implies_dncpc by blast
  done

lemma many_this_char_no_peek_past_any_other_char:
  assumes "C \<noteq> C'"
  shows "does_not_consume_past_char3 (parse (many (this_char C))) C'"
  using assms
  unfolding this_char_def any_from_set_def
  using many_char_for_predicate_does_not_consume_past_char3[of _ \<open>C'\<close>]
  by blast


lemma induct_on_printed_value_example:
  assumes hra: "has_result (parse A) i a []"
  assumes prb: "p_has_result (print (b_then B C)) b_c pr"
  shows "has_result (parse A) (i@pr) a pr"
  apply (insert hra prb)
  apply (cases pr; clarsimp)
  subgoal for pr' prs
    
    sorry
  oops

\<comment> \<open>Empty list case\<close>
definition "empty_list = b_then (char_ws CHR ''['') (ws_char CHR '']'')"

lemma empty_list_no_peek_past_end:
  "does_not_peek_past_end (parse empty_list)"
  unfolding empty_list_def
  apply (rule then_does_not_peek_past_end_with_inner_conflict)
  subgoal by pasi_pngi
  subgoal by pasi_pngi
  subgoal for c1 c2 a l b l'
    by (rule exI[of _ \<open>c2@l'\<close>]; auto simp add: NER_simps split: list.splits)
  done

lemma empty_list_wf:
  "bidef_well_formed empty_list"
  unfolding empty_list_def
  apply (rule b_then_well_formed)
  subgoal by (clarsimp simp add: char_ws_well_formed)
  subgoal by (clarsimp simp add: ws_char_well_formed)  
  unfolding pa_does_not_eat_into_pb_nondep_def
  by (clarsimp simp add: fp_NER NER_simps)

lemma empty_list_example_proof:
  assumes hr1: "has_result (parse (char_ws CHR ''['')) c1 () []"
  assumes hr2: "has_result (parse (ws_char CHR '']'')) c2 () []"
  shows "has_result (parse empty_list) (c1@c2) ((), ()) []"
  apply (insert hr1 hr2; clarsimp simp add: empty_list_def)
  apply (clarsimp simp add: b_then_has_result b_then_p_has_result)
  apply (rule exI[of _ \<open>dropWhile (\<lambda>c. c \<in> whitespace_chars) (tl c1@c2)\<close>]; auto)
  subgoal
    apply (auto simp add: NER_simps split: list.splits)
    apply (rule exI[of _ \<open>tl c1 @ (butlast c2)\<close>]; auto)
    subgoal by (metis snoc_eq_iff_butlast takeWhile_dropWhile_id)
    subgoal
      apply (cases c2; clarsimp split: if_splits)
      by (smt (verit, best) dropWhile_append dropWhile_eq_Nil_conv self_append_conv2 snoc_eq_iff_butlast takeWhile_dropWhile_id)
    done
  subgoal by (auto simp add: NER_simps)
  done

thm print_empty

end