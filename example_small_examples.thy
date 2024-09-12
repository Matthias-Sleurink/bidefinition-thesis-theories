theory example_small_examples
  imports all_definitions
begin


\<comment> \<open>Small example showing how a basic bidef could be made:\<close>

fun a_char_parser :: "char parser" where
  "a_char_parser [] = Some None"
| "a_char_parser (c#cs) = Some (Some (c, cs))"

fun a_char_printer :: "char printer" where
  "a_char_printer c = Some (Some [c])"

definition a_char :: "char bidef" where
  "a_char = bdc a_char_parser a_char_printer"

\<comment> \<open>Basic composition operator\<close>
fun compose_parser :: "'a parser \<Rightarrow> 'b parser \<Rightarrow> ('a \<times> 'b) parser" where
  "compose_parser A B i = (case A i of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some (ra, i')) \<Rightarrow> (case B i' of
        None \<Rightarrow> None
      | Some None \<Rightarrow> Some None
      | Some (Some (rb, l)) \<Rightarrow> Some (Some ((ra, rb), l))))"

fun compose_printer :: "'a printer \<Rightarrow> 'b printer \<Rightarrow> ('a \<times> 'b) printer" where
  "compose_printer A B (a,b) = (case A a of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some ra) \<Rightarrow> (case B b of
        None \<Rightarrow> None
      | Some None \<Rightarrow> Some None
      | Some (Some rb) \<Rightarrow> Some (Some (ra @ rb))))"

definition compose :: "'a bidef \<Rightarrow> 'b bidef \<Rightarrow> ('a \<times> 'b) bidef" where
  "compose A B = bdc (compose_parser (parse A) (parse B)) (compose_printer (print A) (print B))"


definition two_chars :: "(char \<times> char) bidef" where
  "two_chars = compose a_char a_char"

lemma two_chars_test:
  "has_result (parse two_chars) ''AB'' (CHR ''A'', CHR ''B'') []"
  unfolding two_chars_def a_char_def compose_def has_result_def
  by force

\<comment> \<open>apple apples example\<close>
definition "apple = b_then (this_string ''apple'') (optional (this_char CHR ''s''))"

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

lemma many_two_chars_no_peek_past_anything_but_A:
  assumes "char \<noteq> CHR ''A''"
  shows "does_not_consume_past_char3 (parse (many (b_then (this_char CHR ''A'') (this_char CHR ''B'')))) char"
  apply (insert assms)
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


\<comment> \<open>many\<close>
\<comment> \<open>Note that this fails on purpose.\<close>
(*
fun many' where
  "many' a = transform
              sum_take
              (\<lambda>l. if l = [] then Inr [] else Inl l) \<comment> \<open>Print time transform: if the list is empty it can from the else branch, else the then branch\<close>
              (if_then_else
                a                                                 \<comment> \<open>test\<close>
                (\<lambda>r. dep_then (many' a) (\<lambda> rr. return (r#rr)) tl) \<comment> \<open>then\<close> \<comment> \<open>tl is the print time transform that tells us to skip printing the first as it came from the test.\<close>
                (return [])                                       \<comment> \<open>else\<close>
                (hd) \<comment> \<open>'a list \<Rightarrow> 'a (print time transform print input to the then branch to one for the test.)\<close>
               )
"
*)

\<comment> \<open>Illogical applications of many\<close>
definition many_fail :: "unit list bidef" where
  "many_fail = many fail"

lemma many_fail_eq_return_empty:
  "has_result (parse many_fail) = has_result (parse (return []))"
  "is_error (parse many_fail) = is_error (parse (return []))"
  "is_nonterm (parse many_fail) = is_nonterm (parse (return []))"

  "p_has_result (print many_fail) = p_has_result (print (return []))"
  "p_is_error (print many_fail) = p_is_error (print (return []))"
  "p_is_nonterm (print many_fail) = p_is_nonterm (print (return []))"
  unfolding many_fail_def
  subgoal
    apply rule
    apply rule
    apply rule
    subgoal for i r l
      apply (auto simp add: NER_simps)
      subgoal by (meson fail_is_error(1) many_has_result_when_first_parse_fails result_leftover_determ)
      subgoal using \<open>has_result (parse (many fail)) i r l \<Longrightarrow> [] = r\<close> many_has_result_safe(1) by blast
      done
    done
  subgoal by (auto simp add: NER_simps)
  subgoal
    apply rule
    apply (auto simp add: NER_simps)
    using many_is_nonterm fail_is_nonterm(1) fail_has_result(1)
    by fast
  subgoal
    apply rule
    apply rule
    apply (auto simp add: fp_NER)
    subgoal by (metis fail_p_has_result(1) many1_p_has_result many1_p_has_result_eq_many_p_has_result many_p_has_result_safe(1))
    subgoal by (metis fail_p_has_result(1) many1_p_has_result many1_p_has_result_eq_many_p_has_result)
    done
  subgoal
    apply rule
    by (auto simp add: fp_NER list_nonempty_induct)
  subgoal
    apply rule
    by (auto simp add: fp_NER)
  done

definition many_return:
  "many_return = many (return ())"



\<comment> \<open>bidef that eats into two of itself and not one.\<close>
definition eat_into_two:
  "eat_into_two = b_then (this_char CHR ''A'') (optional (this_string ''AA''))"


lemma eat_into_two_can_print:
  "p_has_result (print eat_into_two) (CHR ''A'', Some ''AA'') ''AAA''"
  "p_has_result (print eat_into_two) (CHR ''A'', None) ''A''"
  by (clarsimp simp add: eat_into_two fp_NER)+

lemma can_parse_from_many:
  "has_result (parse eat_into_two) ''AAA'' (CHR ''A'', Some ''AA'') []"
  "has_result (parse eat_into_two) ''A'' (CHR ''A'', None) []"
  by (clarsimp simp add: eat_into_two NER_simps)+

lemma many_print:
  "p_has_result (print (many eat_into_two)) [(CHR ''A'', None), (CHR ''A'', None), (CHR ''A'', None)] ''AAA''"
  by (clarsimp simp add: eat_into_two fp_NER)

lemma many_parse:
  "has_result (parse (many eat_into_two)) ''AAA'' [(CHR ''A'', Some ''AA'')] []"
  by (clarsimp simp add: eat_into_two NER_simps)


end