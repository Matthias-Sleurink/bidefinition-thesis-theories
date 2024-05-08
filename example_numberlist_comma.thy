theory example_numberlist_comma
  imports all_definitions
begin

definition separator where
  "separator = b_then (many whitespace_char) (b_then (this_char CHR '','') (many whitespace_char))"

lemma comma_not_whitespace[simp]:
  "CHR '','' \<notin> whitespace_chars"
  by (simp add: whitespace_chars_def)

lemma many_ws_wf:
  "bidef_well_formed (many whitespace_char)"
  by (clarsimp simp add: whitespace_char_def any_from_set_def many_char_for_predicate_well_formed)
lemma many_ws_no_consume_past:
  "does_not_consume_past_char2 (parse (many whitespace_char)) c \<longleftrightarrow> c \<notin> whitespace_chars"
  by (clarsimp simp add: whitespace_char_def any_from_set_def
                         many_char_for_predicate_does_not_consume_past_char)

lemma separator_wf:
  "bidef_well_formed separator"
  unfolding separator_def
  by (auto intro!: b_then_well_formed first_printed_does_not_eat_into
           simp add: many_ws_wf this_char_well_formed
                     this_char_does_not_consume_past_char2
                     fpci_simps print_empty
                     many_ws_no_consume_past)

lemma separator_fpci[fpci_simps]:
  assumes "first_printed_chari (print separator) i c"
  shows "c\<in>({CHR '',''} \<union> whitespace_chars)"
  using assms
  unfolding separator_def
  apply (clarsimp simp add: fpci_simps print_empty split: if_splits)
  subgoal for t
    unfolding whitespace_char_def any_from_set_def
    apply (subst (asm) many_char_for_predicate_fpci[of _ \<open>fst i\<close> c])
    by (clarsimp split: list.splits)
  done

\<comment> \<open>Note how the proof here would be easier if we had some specialised version for is_error P []\<close>
lemma separator_empty_input:
  "is_error (parse (separator)) []"
  unfolding separator_def
  by (clarsimp simp add: NER_simps whitespace_char_def any_from_set_def)
  
lemma PASI_separator:
  "PASI (parse separator)"
  unfolding separator_def
  apply (rule then_PASI_from_pngi_pasi)
  subgoal by (clarsimp simp add: many_PNGI whitespace_char_PASI)
  apply (rule then_PASI_from_pasi_pngi)
  subgoal by (rule this_char_PASI)
  subgoal by (clarsimp simp add: many_PNGI whitespace_char_PASI)
  done

lemma separator_no_consume_past:
  "does_not_consume_past_char2 (parse separator) c \<longleftrightarrow> c \<notin> ({CHR '',''} \<union> whitespace_chars)"
  unfolding does_not_consume_past_char2_def
            separator_def
  apply (clarsimp simp add: NER_simps)
  


definition numberlist :: "nat list bidef" where
  "numberlist = separated_by separator nat_b ([], CHR '','', [])"

lemma numberlist_results:
  "has_result (parse numberlist) ''''       []       ''''"
  "has_result (parse numberlist) '' ''      []       '' ''"
  "has_result (parse numberlist) ''1''      [1]      ''''"
  "has_result (parse numberlist) ''1 ''     [1]      '' ''"
  "has_result (parse numberlist) ''1,2''    [1, 2]   ''''"
  "has_result (parse numberlist) ''1 ,2''   [1, 2]   ''''"
  "has_result (parse numberlist) ''1 , 2''  [1, 2]   ''''"
  "has_result (parse numberlist) ''1, 12''  [1, 12]  ''''"
  "has_result (parse numberlist) ''13, 12'' [13, 12] ''''"
  by eval+

lemma good_oracle:
  "good_separated_by_oracle separator ([], CHR '','', [])"
  unfolding good_separated_by_oracle_def
  by (auto simp add: fp_NER separator_def)

lemma ws_not_digit:
  assumes "c \<in> whitespace_chars"
  shows "c \<notin> derived_digit_char.digit_chars"
        "c \<notin> digit_chars"
  using assms
  unfolding whitespace_chars_def derived_digit_char.digit_chars_def
  by fast+
  
lemma takeWhileAllNot:
  assumes "\<forall>a \<in> set as. \<not>P a"
  shows "takeWhile P as = []"
  using assms
  by (metis list.set_sel(1) takeWhile_eq_Nil_iff)

lemma no_space_in_nat:
  "\<forall>a\<in>set (print_nat n). a \<notin> whitespace_chars"
  using digit_char_p_is_error digit_char_p_no_error ws_not_digit(1)
  by blast

lemma no_space_hd_nat:
  "hd (print_nat n) \<notin> whitespace_chars"
  using ws_not_digit(2) by fastforce

lemma many_ws_has_result:
  "has_result (parse (many whitespace_char)) i r l \<longleftrightarrow> r = takeWhile (\<lambda>c. c\<in>whitespace_chars) i \<and> l = dropWhile (\<lambda>c. c\<in>whitespace_chars) i"
  unfolding whitespace_char_def any_from_set_def
  by (rule many_char_for_predicate_has_result)



lemma numberlist_well_formed:
  "bidef_well_formed numberlist"
  unfolding numberlist_def
  apply (auto intro!: separated_by_well_formed2 first_printed_does_not_eat_into
              simp add: good_oracle nat_b_well_formed separator_wf
                        nat_is_error
                        separator_empty_input
                        PASI_separator
)
  subgoal apply (rule first_printed_does_not_eat_into)
    apply (clarsimp simp add: nat_b_well_formed  nat_does_not_consume_past)
  oops



end
