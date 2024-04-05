theory example_numberlist
  imports all_definitions
begin

definition numberlist :: "nat list bidef" where
  "numberlist = separated_by (many1 whitespace_char) nat_b '' ''"

lemma numberlist_results:
  "has_result (parse numberlist) ''''       []      ''''"
  "has_result (parse numberlist) '' ''      []      '' ''"
  "has_result (parse numberlist) ''1''      [1]     ''''"
  "has_result (parse numberlist) ''1 ''     [1]     '' ''"
  "has_result (parse numberlist) ''1 2''    [1, 2]  ''''"
  "has_result (parse numberlist) ''1 12''   [1, 12] ''''"
  "has_result (parse numberlist) ''1 12 ''  [1, 12] '' ''"
  "has_result (parse numberlist) '' 1 12 '' []      '' 1 12 ''"
  by eval+

lemma good_oracle:
  "good_separated_by_oracle (many1 whitespace_char) '' ''"
  unfolding good_separated_by_oracle_def
  unfolding many1_p_has_result
  by (clarsimp simp add: fp_NER)

lemma ws_not_digit:
  assumes "c \<in> whitespace_chars"
  shows "c \<notin> derived_digit_char.digit_chars"
        "c \<notin> digit_chars"
  using assms
  unfolding whitespace_chars_def derived_digit_char.digit_chars_def
  by fast+
  

\<comment> \<open>TODO: There should be some all chars in second cannot be eaten by first argument here.\<close>
lemma nat_does_not_eat_into_many1_whitespace:
  "pa_does_not_eat_into_pb_nondep nat_b (many1 whitespace_char)"
  unfolding pa_does_not_eat_into_pb_nondep_def
  apply (auto simp add: fp_NER NER_simps ws_not_digit)
  subgoal for n ws ws_pr
    apply (cases ws; clarsimp)
    using takeWhile_tail[of \<open>\<lambda>x. x \<in> derived_digit_char.digit_chars\<close> _ \<open>print_nat n\<close> ws_pr]
          ws_not_digit(1)
    by clarsimp
  done

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


lemma many1_whitespace_does_not_eat_into_nat:
  "pa_does_not_eat_into_pb_nondep (many1 whitespace_char) nat_b"
  unfolding pa_does_not_eat_into_pb_nondep_def
  apply (auto simp add: fp_NER NER_simps ws_not_digit)
  subgoal for ws_i ws_pr n
    apply (subst (asm) whitespace_char_def)
    apply (subst (asm) any_from_set_def)
    using many_char_for_predicate_p_has_result3[of \<open>\<lambda>found. found \<in> whitespace_chars\<close> \<open>tl ws_i\<close> ws_pr]
    using many_char_for_predicate_p_has_result2[of \<open>\<lambda>found. found \<in> whitespace_chars\<close> \<open>tl ws_i\<close> ws_pr]
    apply clarsimp
    apply (subst whitespace_char_def)
    apply (subst any_from_set_def)
    apply (subst many_char_for_predicate_has_result)
    apply auto
    subgoal
      using takeWhileAllNot[of \<open>print_nat n\<close> \<open>\<lambda>found. found \<in> whitespace_chars\<close>]
      by (meson in_mono print_nat_domain ws_not_digit(2))
    subgoal
      using dropWhileNoneTrue[of \<open>print_nat n\<close> \<open>\<lambda>found. found \<in> whitespace_chars\<close>, OF no_space_in_nat]
      by argo
    done
  done

lemma nat_does_not_into_ws_then_nat:
  "pa_does_not_eat_into_pb_nondep nat_b (many (b_then (many1 whitespace_char) nat_b))"
  unfolding pa_does_not_eat_into_pb_nondep_def
  apply (auto simp add: NER_simps fp_NER)
  subgoal for n pri pri_r
    apply (induction pri arbitrary: pri_r)
    apply (auto simp add: NER_simps fp_NER)
    by (clarsimp simp add: takeWhile_tail ws_not_digit(1))
  subgoal for pri pri_r
    apply (induction pri arbitrary: pri_r)
     by (auto simp add: NER_simps fp_NER ws_not_digit(1))
   done

lemma p_has_result_many_whitespace_implies_i_eq_r:
  assumes "p_has_result (print (many whitespace_char)) i r"
  shows "r = i"
  using assms[unfolded whitespace_char_def any_from_set_def]
        many_char_for_predicate_p_has_result2 
  by presburger

lemma aux1:
  assumes "p_has_result (print (many (b_then (many1 whitespace_char) nat_b))) i pr"
  shows "pr = [] \<or> hd pr \<notin> digit_chars"
  using assms
  apply (cases i)
  by (auto simp add: fp_NER ws_not_digit(1))


lemma can_parse_print_result_then_many1_ws_nat:
  "parser_can_parse_print_result (parse (many (b_then (many1 whitespace_char) nat_b)))
     (print (many (b_then (many1 whitespace_char) nat_b)))"
  unfolding parser_can_parse_print_result_def
  apply clarsimp
  subgoal for t pr
    apply (induction t arbitrary: pr)
    subgoal by (clarsimp simp add: fp_NER NER_simps)
    apply (clarsimp simp add: fp_NER NER_simps)
    subgoal for ws n i' i'_pr tl_ws
      using p_has_result_many_whitespace_implies_i_eq_r[of \<open>tl ws\<close> tl_ws]
      apply clarsimp
      \<comment> \<open>l'a = print_nat n @ i'_pr\<close>
      \<comment> \<open>l' = dropWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars) l'a\<close>
      \<comment> \<open>so, l' = dropWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars) (print_nat n @ i'_pr)\<close>
      \<comment> \<open>Where, technically we can remove the print_nat n there, but it's probably better to
          introduce that knowledge into the proof state.\<close>
      apply (rule exI[of _ \<open>dropWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars) (print_nat n @ i'_pr)\<close>])
      apply (rule conjI)
      subgoal
        apply (rule exI[of _ \<open>print_nat n @ i'_pr\<close>])
        apply auto
        subgoal
          \<comment> \<open>TODO\<close>
          sorry
        subgoal
          using print_nat_never_empty print_nat_domain
          \<comment> \<open>TODO, this can be done nice very easily\<close>
          by (metis append_is_Nil_conv digit_chars_def hd_append2 print_nat_hd takeWhile_eq_Nil_iff)
        subgoal
          using aux1[of i' i'_pr]
          apply clarsimp
          apply (cases i'_pr; clarsimp)
          subgoal for i'' i''s
            using takeWhile_tail[of \<open>\<lambda>x. x \<in> derived_digit_char.digit_chars\<close> i'' \<open>print_nat n\<close> i''s]
            by force
          done
        subgoal
          using aux1[of i' i'_pr]
                nat_from_print_nat
                takeWhile_tail[of \<open>\<lambda>x. x \<in> derived_digit_char.digit_chars\<close> \<open>hd i'_pr\<close> \<open>print_nat n\<close> \<open>tl i'_pr\<close>]
          apply auto
          by (metis append_Nil2 dropWhile_dropWhile2 list.exhaust_sel nat_from_print_nat)
        done
      subgoal
        apply clarsimp
        using aux1
        by (metis digit_chars_def dropWhile.simps(1) dropWhile_hd_no_match)
      done
    done
  oops




lemma numberlist_well_formed:
  "bidef_well_formed numberlist"
  unfolding numberlist_def
  apply (rule separated_by_well_formed)
  subgoal by (rule good_oracle)
  subgoal by (rule nat_does_not_eat_into_many1_whitespace)
  subgoal by (rule many1_whitespace_does_not_eat_into_nat)
  subgoal by (rule nat_b_well_formed)
      defer
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (rule nat_does_not_into_ws_then_nat)
  defer defer
  subgoal by (clarsimp simp add: many1_char_for_predicate_well_formed whitespace_char_def any_from_set_def)
  
  
  oops


end
