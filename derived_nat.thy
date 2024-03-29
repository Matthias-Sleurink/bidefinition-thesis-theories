theory derived_nat
  imports basic_definitions
          derived_many1
          derived_digit_char

          meta_digit_to_nat_and_back
begin

lemma digit_chars_eq_digit_chars[simp]:
  "meta_digit_to_nat_and_back.digit_chars = derived_digit_char.digit_chars"
  unfolding digit_chars_def
  by blast



definition nat_b :: "nat bidef" where
  "nat_b = transform
                   nat_from  \<comment> \<open>str \<Rightarrow> nat\<close>
                   print_nat  \<comment> \<open>nat \<Rightarrow> str\<close>
                   (many1 digit_char)  \<comment> \<open>str bidef\<close>
"



\<comment> \<open>NER\<close>
lemma nat_is_nonterm[NER_simps]:
  "is_nonterm (parse nat_b) i \<longleftrightarrow> False"
  unfolding nat_b_def
  apply (clarsimp simp only: NER_simps)
  apply (induction i)
  subgoal
    apply (subst many_is_nonterm(1))
    by (clarsimp simp add: NER_simps)
  subgoal for r rs
    apply (subst many_is_nonterm(1))
    by (clarsimp simp add: NER_simps)
  done

lemma nat_is_error[NER_simps]:
  "is_error (parse nat_b) i \<longleftrightarrow> i = [] \<or> hd i \<notin> digit_chars"
  unfolding nat_b_def
  by (clarsimp simp add: NER_simps)

lemma nat_has_result[NER_simps]:
  "has_result (parse nat_b) i r l \<longleftrightarrow>
        i \<noteq> [] \<and>
        (\<exists> consumed .
              consumed \<noteq> [] \<and>
              consumed @ l = i \<and>
              r = (nat_from consumed) \<and>
              consumed = takeWhile (\<lambda>x. x\<in>digit_chars) i \<and>
              l = dropWhile (\<lambda>x. x\<in>digit_chars) i)"
  apply (simp only: nat_b_def NER_simps digit_char_def any_from_set_def)
  apply auto
  subgoal
    using list.collapse by fastforce
  subgoal
    by (metis dropWhile.simps(2) hd_append2 list.collapse list.sel(3) takeWhile.simps(2) takeWhile_dropWhile_id)
  done



\<comment> \<open>FP ner\<close>
lemma digit_char_p_no_error[fp_NER]:
  shows "\<forall>x\<in>set (print_nat i). \<not> p_is_error (print digit_char) x"
  apply (simp add: fp_NER)
  using print_nat_domain by force

lemma nat_p_is_error[fp_NER]:
  "p_is_error (print (nat_b)) i \<longleftrightarrow> False"
  unfolding nat_b_def
  apply (clarsimp simp add: fp_NER)
  apply auto
  subgoal using digit_chars_def print_nat_hd by presburger
  subgoal by (meson digit_char_p_no_error list.set_sel(2) many_p_no_error print_nat_never_empty)
  done

lemma nat_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (nat_b)) i \<longleftrightarrow> False"
  by (auto simp add: nat_b_def fp_NER)

lemma nat_p_has_result[fp_NER]:
  "p_has_result (print (nat_b)) i r \<longleftrightarrow> r = print_nat i"
  unfolding nat_b_def transform_p_has_result
  apply (clarsimp simp add: many1_p_has_result_eq_many_p_has_result[of \<open>print_nat i\<close> digit_char r])
  unfolding digit_char_def any_from_set_def
  apply (rule many_char_for_predicate_p_has_result)
  using print_nat_domain
  by auto

lemma takeWhileAllTrue:
  assumes "\<forall>a \<in> set as. P a"
  shows "as = takeWhile P as"
  using assms
  by (metis takeWhile_eq_all_conv)

lemma dropWhileAllTrue:
  assumes "\<forall>a \<in> set as. P a"
  shows "[] = dropWhile P as"
  using assms
  by (metis dropWhile_eq_Nil_conv)


lemma nat_b_well_formed:
  "bidef_well_formed nat_b"
  apply wf_init
  subgoal
    unfolding parser_can_parse_print_result_def
    apply (auto simp add: NER_simps fp_NER)
    subgoal for t
      using print_nat_domain[of t]
      using takeWhileAllTrue[of \<open>print_nat t\<close> \<open>(\<lambda>x. x \<in> derived_digit_char.digit_chars)\<close>]
      by auto
    subgoal for t
      using print_nat_domain[of t]
      using dropWhileAllTrue[of \<open>print_nat t\<close> \<open>(\<lambda>x. x \<in> derived_digit_char.digit_chars)\<close>]
      by auto
    done
  subgoal
    unfolding printer_can_print_parse_result_def
    by (auto simp add: NER_simps fp_NER)
  done


lemma nat_b_wf_from_many1:
  "bidef_well_formed nat_b"
  unfolding nat_b_def
  apply (rule transform_well_formed)
  subgoal
    apply (rule many1_well_formed)
    subgoal by (clarsimp simp add: fp_NER NER_simps parse_result_cannot_be_grown_by_printer_def)
    subgoal by (rule digit_char_well_formed)
    subgoal by (simp add: digit_char_is_error)
    done
  unfolding well_formed_transform_funcs_def
  apply (auto simp add: NER_simps fp_NER)
  \<comment> \<open>Counterexample here, v = '01', which gives: nat_from '01' = 1::nat, which gives print_nat 1 = '1' ~= '01'\<close>
  oops

lemma nat_b_wf_from_transform_many1:
  "bidef_well_formed nat_b"
  unfolding nat_b_def
  apply (rule transform_well_formed2)
  subgoal
    apply (rule many1_well_formed)
    subgoal by (clarsimp simp add: fp_NER NER_simps parse_result_cannot_be_grown_by_printer_def)
    subgoal by (rule digit_char_well_formed)
    subgoal by (simp add: digit_char_is_error)
    done
  unfolding well_formed_transform_funcs2_def
  apply (auto simp add: NER_simps fp_NER)
  subgoal
    \<comment> \<open>Counterexample here, v = '01', which gives: nat_from '01' = 1::nat, which gives print_nat 1 = '1' ~= '01'\<close>
    sorry
  subgoal for t l
    by (metis any_from_set_def
              digit_char_def
              many_char_for_pred_well_formed
              nat_from_print_nat
              print_nat_never_empty(2)
              wf_parser_can_parse_print_result_apply)
  oops


end
