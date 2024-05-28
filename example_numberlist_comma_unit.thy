theory example_numberlist_comma_unit
  imports all_definitions
begin

definition numberlist_comma_unit :: "nat list bidef" where
  "numberlist_comma_unit = separated_by ws_comma_ws nat_b ()"


lemma numberlist_comma_unit_results:
  "has_result (parse numberlist_comma_unit) ''''       []       ''''"
  "has_result (parse numberlist_comma_unit) '' ''      []       '' ''"
  "has_result (parse numberlist_comma_unit) ''1''      [1]      ''''"
  "has_result (parse numberlist_comma_unit) ''1 ''     [1]      '' ''"
  "has_result (parse numberlist_comma_unit) ''1,2''    [1, 2]   ''''"
  "has_result (parse numberlist_comma_unit) ''1 ,2''   [1, 2]   ''''"
  "has_result (parse numberlist_comma_unit) ''1 , 2''  [1, 2]   ''''"
  "has_result (parse numberlist_comma_unit) ''1, 12''  [1, 12]  ''''"
  "has_result (parse numberlist_comma_unit) ''13, 12'' [13, 12] ''''"
  by eval+

lemma good_oracle:
  "good_separated_by_oracle ws_comma_ws ()"
  unfolding good_separated_by_oracle_def
  by (auto simp add: fp_NER)

lemma ws_not_digit:
  assumes "c \<in> whitespace_chars"
  shows "c \<notin> derived_digit_char.digit_chars"
        "c \<notin> digit_chars"
  using assms
  unfolding whitespace_chars_def derived_digit_char.digit_chars_def
  by fast+

lemma comma_not_digit:
  "CHR '','' \<notin> derived_digit_char.digit_chars"
  "CHR '','' \<notin> meta_digit_to_nat_and_back.digit_chars"
  unfolding derived_digit_char.digit_chars_def
  by fastforce+

lemma no_space_hd_nat:
  "hd (print_nat n) \<notin> whitespace_chars"
  using ws_not_digit(2) by fastforce

lemma numberlist_comma_unit_well_formed:
  "bidef_well_formed numberlist_comma_unit"
  unfolding numberlist_comma_unit_def 
  apply (auto intro!: separated_by_well_formed_no_consume_past_char then_does_not_consume_past3
              simp add: good_oracle nat_b_well_formed ws_comma_ws_well_formed
                        nat_is_error ws_comma_ws_is_error
                        nat_b_PASI
                        ws_comma_ws_does_not_consume_past_char3
                        fpci_simps no_space_hd_nat
                        nat_does_not_consume_past3 comma_not_digit(1)
                        print_empty fpc_def
                        PASI_implies_no_result_from_empty)
  subgoal
    using is_error_implies_not_has_result nat_is_error ws_not_digit(2)
    by fastforce
  done


end
