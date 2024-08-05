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



end