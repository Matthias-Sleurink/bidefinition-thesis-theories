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
  "has_result (parse nat_b) i r l \<longleftrightarrow> i \<noteq> [] \<and> (\<exists> consumed . consumed \<noteq> [] \<and> i = consumed @ l \<and> r = (nat_from consumed) \<and> consumed = takeWhile (\<lambda>x. x\<in>digit_chars) i \<and> l = dropWhile (\<lambda>x. x\<in>digit_chars) i)"
  unfolding nat_b_def
  apply (auto simp add: NER_simps)
  subgoal by (simp add: takeWhile_eq_Nil_iff)
  subgoal
          
    sorry
  subgoal
    
    sorry
  subgoal by (metis \<open>\<And>r'. \<lbrakk>r' \<noteq> []; i \<noteq> []; hd r' = hd i; hd i \<in> derived_digit_char.digit_chars; has_result (parse (many digit_char)) (tl i) (tl r') l; r = nat_from r'\<rbrakk> \<Longrightarrow> i = takeWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars) i @ l\<close> append_eq_conv_conj dropWhile_eq_drop)
  subgoal
    
    sorry


end