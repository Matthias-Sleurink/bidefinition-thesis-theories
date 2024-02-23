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



end