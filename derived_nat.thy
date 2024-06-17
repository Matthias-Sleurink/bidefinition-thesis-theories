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

lemma nat_print_empty[print_empty, fp_NER]:
  "p_has_result (print nat_b) n [] \<longleftrightarrow> False"
  by (clarsimp simp add: fp_NER)+



\<comment> \<open>PASI, PNGI\<close>
lemma nat_b_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse nat_b)"
  unfolding nat_b_def
  using transform_PNGI
        many1_PNGI[OF digit_char_PASI]
  by blast

lemma nat_b_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse nat_b)"
  unfolding nat_b_def
  using transform_PASI
        many1_PASI[OF digit_char_PASI]
  by blast



\<comment> \<open>Does not peek past end\<close>
\<comment> \<open>This is the argument that shows that does_not_peek_past_end isn't true for "most" many1 parsers.\<close>
lemma nat_does_peek_past_end[peek_past_end_simps]:
  "\<not>does_not_peek_past_end (parse nat_b)"
  unfolding does_not_peek_past_end_def
  apply clarsimp
  apply (rule exI[of _ \<open>''1''\<close>])
  apply (rule exI[of _ 1])
  apply (rule conjI)
  subgoal by (rule exI[of _ \<open>''''\<close>]; clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>''1''\<close>]; clarsimp simp add: NER_simps)
  done

lemma dropWhile_takeWhile_same_predicate[simp]:
  "dropWhile P (takeWhile P l) = []"
  by (induction l) auto

lemma nat_does_not_consume_past3:
  "does_not_consume_past_char3 (parse nat_b) c \<longleftrightarrow> c \<notin> digit_chars"
  unfolding does_not_consume_past_char3_def
  apply (auto simp add: NER_simps)
  subgoal by (metis dropWhile_eq_Cons_conv self_append_conv2 takeWhile_dropWhile_id)
  subgoal by (metis takeWhile_idem)
  subgoal by (metis dropWhile_takeWhile_same_predicate)
  subgoal by (metis dropWhile_dropWhile2 takeWhile_tail)
  subgoal by (metis dropWhile.simps(2) dropWhile_append set_takeWhileD)
  subgoal by (metis takeWhile_idem)
  subgoal by (metis dropWhile_takeWhile_same_predicate)
  subgoal by (metis dropWhile_dropWhile2 takeWhile_tail)
  subgoal by (metis dropWhile.simps(2) dropWhile_append set_takeWhileD)
  done



\<comment> \<open>First printed char\<close>
lemma nat_fpci[fpci_simps]:
  "first_printed_chari (print nat_b) n c \<longleftrightarrow> hd (print_nat n) = c"
  unfolding first_printed_chari_def
  by (clarsimp simp add: fp_NER)



\<comment> \<open>WF\<close>
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

lemma dropWhileNoneTrue:
  assumes "\<forall>a \<in> set as. \<not>P a"
  shows "dropWhile P as = as"
  using assms dropWhile_eq_self_iff hd_in_set
  by auto

lemma nat_b_well_formed:
  "bidef_well_formed nat_b"
  apply wf_init
  subgoal by (rule nat_b_PNGI)
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
    subgoal by (rule digit_char_PASI)
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
    subgoal by (rule digit_char_PASI)
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


lemma nat_b_wf_from_transform_many1:
  "bidef_well_formed nat_b"
  unfolding nat_b_def
  apply (rule transform_well_formed3)
  subgoal
    apply (rule many1_well_formed)
    subgoal by (clarsimp simp add: fp_NER NER_simps parse_result_cannot_be_grown_by_printer_def)
    subgoal by (rule digit_char_well_formed)
    subgoal by (simp add: digit_char_is_error)
    subgoal by (rule digit_char_PASI)
    done
  unfolding well_formed_transform_funcs3_def
  apply (auto simp add: NER_simps fp_NER)
  subgoal for i v l
    apply (unfold many1_p_has_result)
    apply (auto simp add: fp_NER NER_simps)
    subgoal
      using digit_chars_eq_digit_chars print_nat_hd by presburger
    subgoal
      unfolding digit_char_def any_from_set_def
      apply (rule exI[of _ \<open>tl (print_nat (nat_from v))\<close>])
      using many_char_for_predicate_p_has_result[of \<open>tl (print_nat (nat_from v))\<close>]
            print_nat_domain print_nat_never_empty
      by (metis digit_char_p_is_error digit_char_p_no_error list.set_sel(2)) 
    done
  subgoal for t r
    by (metis any_from_set_def digit_char_def many_char_for_pred_well_formed nat_from_print_nat print_nat_never_empty(1) print_result_is_canon_result)
  done

lemma print_nat_takeWhile[simp]:
  "takeWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars)         (print_nat n) = print_nat n"
  "takeWhile (\<lambda>x. x \<in> meta_digit_to_nat_and_back.digit_chars) (print_nat n) = print_nat n"
  unfolding derived_digit_char.digit_chars_def
  using digit_char_p_is_error digit_char_p_no_error
  by (clarsimp; blast)+

lemma print_nat_dropWhile[simp]:
  "dropWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars)         ((print_nat n) @ t) = dropWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars)         t"
  "dropWhile (\<lambda>x. x \<in> meta_digit_to_nat_and_back.digit_chars) ((print_nat n) @ t) = dropWhile (\<lambda>x. x \<in> meta_digit_to_nat_and_back.digit_chars) t"
  unfolding derived_digit_char.digit_chars_def
  using digit_char_p_is_error digit_char_p_no_error
  by (clarsimp; blast)+

lemma print_nat_hd_derived[simp]:
  "hd (print_nat a) \<in> derived_digit_char.digit_chars"
  using digit_chars_eq_digit_chars print_nat_hd by presburger

lemma nat_b_leftover_can_be_dropped:
  "has_result (parse nat_b) (c @ l2) r (l@l2) \<Longrightarrow> has_result (parse nat_b) c r l"
  apply (cases c; clarsimp)
  subgoal by(insert nat_b_PNGI[unfolded PNGI_def, rule_format, of l2 r \<open>l@l2\<close>]; clarsimp simp add: NER_simps)
  subgoal for c' cs
    apply (cases l; clarsimp)
    subgoal by (clarsimp simp add: NER_simps split: if_splits)
    subgoal for l' ls
      apply (cases \<open>l' \<in> digit_chars\<close>; clarsimp simp add: NER_simps split: if_splits)
      subgoal by (metis dropWhile_eq_Cons_conv)
      subgoal by (metis dropWhile_eq_Cons_conv takeWhile_tail)
      done
    done
  done


lemma nat_b_error_leftover_can_be_dropped:
  "is_error (parse nat_b) (c @ l2) \<Longrightarrow> is_error (parse nat_b) c"
  by (clarsimp simp add: NER_simps)

end
