theory example_char_twice
  imports all_definitions
begin


definition char_twice :: "char bidef" where
  "char_twice = dep_then one_char (\<lambda>c. char_for_predicate (\<lambda>c'. c' = c)) id"
value "parse char_twice ''AA''"
value "parse char_twice ''A''"
value "parse char_twice ''AB''"
value "print char_twice CHR ''A''"
value "print char_twice CHR ''B''"


definition char_twice' :: "char bidef" where
  "char_twice' = ftransform
                    (\<lambda>cs. if fst cs = snd cs then Some (fst cs) else None)
                    (\<lambda>c. Some (c,c))
                    (b_then one_char one_char)"
value "parse char_twice' ''AA''"
value "parse char_twice' ''A''"
value "parse char_twice' ''AB''"
value "print char_twice' CHR ''A''"
value "print char_twice' CHR ''B''"


lemma char_twice_has_result:
  "has_result (parse char_twice) i r l = has_result (parse char_twice') i r l"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: NER_simps)
lemma char_twice_is_error:
  "is_error (parse char_twice) i = is_error (parse char_twice') i"
  unfolding char_twice_def char_twice'_def
  apply (auto simp add: NER_simps) by (metis list.collapse)
lemma char_twice_is_nonterm:
  "is_nonterm (parse char_twice) i = is_nonterm (parse char_twice') i"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: NER_simps)

lemma char_twice_p_has_result:
  "p_has_result (print char_twice) i r = p_has_result (print char_twice') i r"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: fp_NER)
lemma char_twice_p_is_error:
  "p_is_error (print char_twice) i = p_is_error (print char_twice') i"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: fp_NER)
lemma char_twice_p_is_nonterm:
  "p_is_nonterm (print char_twice) i = p_is_nonterm (print char_twice') i"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: fp_NER)


lemma parse_char_twice_eq_char_twice':
  "parse char_twice = parse char_twice'"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: dep_then_def if_then_else_def transform_def ftransform_def b_then_def fail_def char_for_predicate_def return_def
           split: option.splits)

lemma print_char_twice_eq_char_twice':
  "print char_twice = print char_twice'"
  unfolding char_twice_def char_twice'_def
  by (auto simp add: dep_then_def transform_def ftransform_def if_then_else_def one_char_def char_for_predicate_def return_def fail_def b_then_def
           split: option.splits)

end