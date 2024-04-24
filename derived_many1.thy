theory derived_many1
  imports basic_definitions
          derived_many
          derived_then
begin

\<comment> \<open>Seems like we might want a fallible transform here\<close>
definition many1 :: "'\<alpha> bidef \<Rightarrow> '\<alpha> list bidef" where
  "many1 a = ftransform
                (\<lambda> (r, rs). Some (r#rs)) \<comment> \<open>pair to list\<close>
                (\<lambda> l. if l = [] then None else Some (hd l, tl l)) \<comment> \<open>list to pair\<close>
                (b_then a (many a)) \<comment> \<open>pair parser\<close>
"



\<comment> \<open>NER\<close>
lemma many1_is_nonterm[NER_simps]:
  "is_nonterm (parse (many1 a)) i \<longleftrightarrow> is_nonterm (parse a) i \<or> (\<exists>r l. has_result (parse a) i r l \<and> is_nonterm (parse (many a)) l)"
  by (simp add: many1_def NER_simps)

lemma many1_is_error[NER_simps]:
  "is_error (parse (many1 a)) i \<longleftrightarrow> is_error (parse a) i"
  by (simp add: many1_def NER_simps)

lemma many1_has_result[NER_simps]:
  "has_result (parse (many1 a)) i r l \<longleftrightarrow> r \<noteq> [] \<and> (\<exists> l'. has_result (parse a) i (hd r) l' \<and> has_result (parse (many a)) l' (tl r) l)"
  apply (clarsimp simp add: many1_def NER_simps)
  by fastforce

lemma many1_result_only_if_nonempty:
  assumes "has_result (parse (many1 bi)) i r l"
  shows "r \<noteq> []"
  using assms
  by (simp add: NER_simps)

lemma many1_no_result_if_empty:
  shows "\<not>has_result (parse (many1 bi)) i [] l"
  by (simp add: many1_has_result)




\<comment> \<open>FP ner\<close>
lemma many1_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (many1 a)) i \<longleftrightarrow> i\<noteq>[] \<and> (p_is_nonterm (print a) (hd i) \<or> (\<not> p_is_error (print a) (hd i) \<and> p_is_nonterm (print (many a)) (tl i)))"
  by (simp add: many1_def fp_NER)

lemma many1_p_is_error[fp_NER]:
  "p_is_error (print (many1 a)) i \<longleftrightarrow> i = [] \<or> p_is_error (print a) (hd i) \<or> (\<not>p_is_nonterm (print a) (hd i) \<and> p_is_error (print (many a)) (tl i))"
  by (simp add: many1_def fp_NER)

lemma many1_p_has_result[fp_NER]:
  "p_has_result (print (many1 a)) i r \<longleftrightarrow> (\<exists> r1 r2. r = r1@r2 \<and> i \<noteq> [] \<and> p_has_result (print a) (hd i) r1 \<and> p_has_result (print (many a)) (tl i) r2)"
  by (auto simp add: many1_def fp_NER)

lemma many1_p_has_result_eq_many_p_has_result:
  assumes "i \<noteq> []"
  shows "p_has_result (print (many1 b)) i r \<longleftrightarrow> p_has_result (print (many b)) i r"
  using assms
  by auto (metis list.collapse many1_p_has_result many_p_has_result_safe(2))+
  

lemma many1_p_has_result_only_if_nonempty:
  assumes "p_has_result (print (many1 a)) i r"
  shows "i \<noteq> []"
  using assms
  by (auto simp add: fp_NER)

lemma many1_p_no_result_empty[fp_NER]:
  shows "\<not>p_has_result (print (many1 bi)) [] r"
  using many1_p_has_result_only_if_nonempty by blast



\<comment> \<open>PNGI, PASI\<close>
lemma many1_PNGI_from_PNGI:
  assumes "PNGI (parse p)"
  shows "PNGI (parse (many1 p))"
  unfolding many1_def
  apply (rule ftransform_PNGI)
  apply (rule then_PNGI)
  subgoal by (rule assms)
  apply (rule many_PNGI)
  oops

lemma many1_PNGI:
  assumes "PASI (parse p)"
  shows "PNGI (parse (many1 p))"
  unfolding many1_def
  apply (rule ftransform_PNGI)
  apply (rule then_PNGI)
  subgoal by (clarsimp simp add: assms PASI_implies_PNGI)
  apply (rule many_PNGI)
  by (rule assms)

lemma many1_PASI:
  assumes "PASI (parse p)"
  shows "PASI (parse (many1 p))"
  unfolding many1_def
  apply (rule ftransform_PASI)
  apply (rule then_PASI_from_pasi_pngi)
  subgoal by (rule assms(1))
  apply (rule many_PNGI)
  by (rule assms(1))


lemma printer_can_print_parse_result_many1:
  assumes "printer_can_print_parse_result (parse b) (print b) \<or> bidef_well_formed b"
  shows "printer_can_print_parse_result (parse (many1 b)) (print (many1 b))"
  using assms unfolding bidef_well_formed_def printer_can_print_parse_result_def
  apply clarsimp
  subgoal for ts i l
    apply (induction ts arbitrary: i l)
    subgoal using many1_no_result_if_empty by blast
    apply (auto simp add: fp_NER NER_simps)
    subgoal for t ts' i' l'' l'
      by (metis (no_types) list.collapse list.sel(3) many1_p_has_result many1_p_has_result_eq_many_p_has_result many_has_result_safe(2) many_p_has_result_safe(1) neq_Nil_conv)
    subgoal
      by (metis list.distinct(1) many1_p_has_result_eq_many_p_has_result many_has_result_safe(2) printer_can_print_parse_result_def printer_can_print_parse_result_many)
    done
  done



\<comment> \<open>Does not peek past end\<close>
\<comment> \<open>This is the argument that shows that does_not_peek_past_end isn't true for "most" many1 parsers.\<close>
lemma many1_does_peek_past_end[peek_past_end_simps]:
  assumes "\<exists> i r l. has_result (parse b) i r l \<and> is_error (parse b) l"
  assumes "PNGI (parse b)"
  shows "\<not>does_not_peek_past_end (parse (many1 b))"
  unfolding does_not_peek_past_end_def
  using assms[unfolded PNGI_def]
  apply (auto simp add: NER_simps)
  subgoal for i r l
    apply (rule exI[of _ \<open>list_upto i l\<close>])
    apply (rule exI[of _ \<open>[r]\<close>])
    apply clarsimp
    apply (rule conjI)
    subgoal
      apply (rule exI[of _ l])
      apply (rule exI[of _ l])
      apply (clarsimp simp add: NER_simps)
      using list_upto_take_cons[of i l \<open>list_upto i l\<close>]
      by presburger
    subgoal
      by (metis is_error_implies_not_has_result many_has_result_safe(1))
    done
  done



\<comment> \<open>Well Formed\<close>
lemma many1_well_formed:
  assumes "parse_result_cannot_be_grown_by_printer (parse b) (print (many b))"
  assumes "bidef_well_formed b"
  assumes "is_error (parse b) []" \<comment> \<open>can get this from PASI\<close>
  assumes "PASI (parse b)"
  shows "bidef_well_formed (many1 b)"
  apply wf_init
  subgoal using many1_PNGI[OF assms(4)] by fast
  subgoal
    unfolding parser_can_parse_print_result_def
    apply clarsimp \<comment> \<open>To move \<forall> to \<And>\<close>
    subgoal for ts pr
      apply (induction ts arbitrary: pr)
      subgoal using many1_p_no_result_empty by blast
      subgoal for t ts' pr'
        using assms[unfolded parse_result_cannot_be_grown_by_printer_def bidef_well_formed_def parser_can_parse_print_result_def]
        apply (auto simp add: fp_NER NER_simps)
        by (smt (verit) append.right_neutral append_eq_append_conv2 assms(1) assms(2) can_parse_print_result same_append_eq well_formed_does_not_grow_by_printer)
      done
    done
  subgoal
    apply (rule printer_can_print_parse_result_many1)
    using assms(2) by blast
  done


lemma many1_well_formed_from_many:
  assumes "bidef_well_formed (many b)"
  shows "bidef_well_formed (many1 b)"
  apply wf_init
  subgoal
    using assms[unfolded bidef_well_formed_def]
    by (metis PNGI_def many1_has_result many_has_result_safe(2))
  subgoal
    using assms[unfolded bidef_well_formed_def]
    unfolding parser_can_parse_print_result_def
    by (metis many1_has_result many1_p_has_result many_has_result_safe(2) many_p_has_result_safe(2))
  subgoal
    using assms[unfolded bidef_well_formed_def]
    unfolding printer_can_print_parse_result_def
    by (metis many1_has_result many1_p_has_result many_has_result_safe(2) many_p_has_result_safe(2))
  done


lemma many1_char_for_predicate_p_has_result2:
  assumes "p_has_result (print (many1 (char_for_predicate p))) i r"
  shows "r = i"
  using assms
  apply (induction i arbitrary: r; clarsimp simp add: fp_NER)
  subgoal for i iss isspr tli_pr
    by (rule many_char_for_predicate_p_has_result2[of p iss isspr])
  done

lemma many1_char_for_predicate_p_has_result3:
  assumes "p_has_result (print (many1 (char_for_predicate p))) i r"
  shows "\<forall> i' \<in> set i. p i'"
  using assms
  apply -
  apply (clarsimp simp add: fp_NER)
  subgoal for i' tl_r
    using many_char_for_predicate_p_has_result3[of p \<open>tl i\<close> tl_r]
    apply clarsimp
    by (metis list.collapse set_ConsD)
  done

lemma many1_char_for_predicate_well_formed:
  shows "bidef_well_formed (many1 (char_for_predicate P))"
  by (simp add: many1_well_formed_from_many many_char_for_predicate_well_formed)


end
