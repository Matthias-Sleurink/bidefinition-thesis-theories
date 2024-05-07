theory derived_then_drop_second
  imports basic_definitions
          derived_then
begin

\<comment> \<open>The choice to go for a '\<beta> as oracle and not an '\<alpha> \<Rightarrow> '\<beta> might be wrong?\<close>
definition then_drop_second :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> '\<beta> \<Rightarrow> '\<alpha> bidef" where
  "then_drop_second ab bb b = transform
                              (fst :: ('\<alpha>\<times>'\<beta>) \<Rightarrow> '\<alpha>)
                              ((\<lambda> a. (a, b)) :: '\<alpha> \<Rightarrow> ('\<alpha>\<times>'\<beta>))
                              (b_then ab bb :: ('\<alpha>\<times>'\<beta>) bidef)"



\<comment> \<open>NER\<close>
lemma then_drop_second_is_nonterm[NER_simps]:
  "is_nonterm (parse (then_drop_second ab bb b)) i \<longleftrightarrow> is_nonterm (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_nonterm (parse bb) l)"
  by (simp add: then_drop_second_def NER_simps)

lemma then_drop_second_is_error[NER_simps]:
  "is_error (parse (then_drop_second ab bb b)) i \<longleftrightarrow> is_error (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_error (parse bb) l)"
  by (simp add: then_drop_second_def NER_simps)

lemma then_drop_second_has_result[NER_simps]:
  "has_result (parse (then_drop_second ab bb b)) i ra l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> (\<exists> rb. has_result (parse bb) l' rb l))"
  by (auto simp add: then_drop_second_def NER_simps split: prod.splits)

lemma then_drop_second_has_result_ci[NER_simps]:
  assumes "PNGI (parse ab)"
  assumes "PNGI (parse bb)"
  shows
  "has_result_ci (parse (then_drop_second ab bb b)) i c ra l \<longleftrightarrow> (\<exists> c' c''. c'@c''=c \<and> has_result_ci (parse ab) i c' ra (c''@l) \<and> (\<exists> rb. has_result_ci (parse bb) (c''@l) c'' rb l))"
  apply (auto simp add: has_result_ci_def has_result_c_def then_drop_second_has_result)
  subgoal for l' rb
    apply (rule exI[of _ \<open>list_upto (c@l) l'\<close>])
    apply (rule exI[of _ \<open>list_upto l' l\<close>])
    using list_upto_take_cons[of \<open>c@l\<close> l'] list_upto_take_cons[of l' l]
          assms[unfolded PNGI_def]
    by force
  done



\<comment> \<open>FP NER\<close>
lemma then_drop_second_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (then_drop_second ab bb b)) va \<longleftrightarrow> p_is_nonterm (print ab) va \<or> (\<not>p_is_error (print ab) va \<and> p_is_nonterm (print bb) b)"
  by (simp add: then_drop_second_def fp_NER split: prod.splits)+

lemma then_drop_second_p_is_error[fp_NER]:
  "p_is_error (print (then_drop_second ab bb b)) va \<longleftrightarrow> p_is_error (print ab) va \<or> (\<not>p_is_nonterm (print ab) va \<and> p_is_error (print bb) b)"
  by (simp add: then_drop_second_def fp_NER split: prod.splits)+

lemma then_drop_second_p_has_result[fp_NER]:
  "p_has_result (print (then_drop_second ab bb b)) va t \<longleftrightarrow> (\<exists>ta tb.  t = ta@tb \<and> p_has_result (print ab) va ta \<and> p_has_result (print bb) b tb)"
  by (auto simp add: then_drop_second_def fp_NER split: prod.splits)+

lemma then_drop_second_print_empty[print_empty, fp_NER]:
  "p_has_result (print (then_drop_second A B oracle)) i [] \<longleftrightarrow> p_has_result (print A) i [] \<and> p_has_result (print B) oracle []"
  by (clarsimp simp add: then_drop_second_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma then_drop_second_PNGI:
  assumes "PNGI (parse ab)"
  assumes "PNGI (parse bb)"
  shows "PNGI (parse (then_drop_second ab bb b))"
  unfolding then_drop_second_def
  unfolding transform_PNGI[symmetric]
  apply (rule then_PNGI)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  done


lemma then_drop_second_PASI:
  assumes "PASI (parse ab)"
  assumes "PASI (parse bb)"
  shows "PASI (parse (then_drop_second ab bb b))"
  unfolding then_drop_second_def
  unfolding transform_PASI[symmetric]
  apply (rule then_PASI)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  done



\<comment> \<open>Does not peek past end\<close>
lemma then_drop_second_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  assumes "PNGI (parse A)"
  assumes "does_not_peek_past_end (parse B)"
  assumes "PNGI (parse B)"
  assumes "pa_does_not_eat_into_pb_nondep A B"
  shows "does_not_peek_past_end (parse (then_drop_second A B oracle))"
  unfolding does_not_peek_past_end_def
  apply (clarsimp simp add: NER_simps)
  proof -
    fix c r l l' l'a rb
    assume hr_A: "has_result (parse A) (c @ l) r l'"
    assume hr_B: "has_result (parse B) l' rb l"
    obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f3: "c @ l = ccs l' (c @ l) @ l'"
      using hr_A by (meson assms(2)[unfolded PNGI_def])
    obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f4: "l' = ccsa l l' @ l"
      using hr_B by (meson assms(4)[unfolded PNGI_def])
    have "\<forall>cs. has_result (parse A) (ccs l' (c @ l) @ cs) r cs"
      using f3 hr_A by (metis (full_types) assms(1) does_not_peek_past_end_def)
    then show "\<exists>cs. has_result (parse A) (c @ l'a) r cs \<and> (\<exists>b. has_result (parse B) cs b l'a)"
      using f4 f3 hr_B
      by (smt (z3) append.assoc append_same_eq assms(3) does_not_peek_past_end_def)
  qed



\<comment> \<open>First printed char\<close>
lemma then_drop_second_fpci[fpci_simps]:
  "first_printed_chari (print (then_drop_second A B oracle)) i c \<longleftrightarrow>(
    if p_has_result (print A) i [] then
      (first_printed_chari (print B) oracle c)
    else
      (first_printed_chari (print A) i c \<and> (\<exists>t. p_has_result (print B) oracle t))
  )"
  by (clarsimp simp add: then_drop_second_def fpci_simps)



\<comment> \<open>well formed\<close>

lemma b_then_drop_second_wf_derived:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  assumes "\<exists> it. has_result (parse b2) it b []"
  shows "bidef_well_formed (then_drop_second b1 b2 b)"
  unfolding then_drop_second_def
  apply (rule transform_well_formed)
  subgoal
    apply (rule b_then_well_formed)
    subgoal by (rule assms(1))
    subgoal by (rule assms(2))
    subgoal by (rule assms(3))
    done
  subgoal
    unfolding well_formed_transform_funcs_def
    using assms(4)
    apply (auto simp add: NER_simps)
    (* Here we clearly see that the definition of transform well formed requires us to be
        well formed over both bidefs, but since we only get the result of the second we cannot
        be well formed over both bidefs (I claim, but do not prove this).
       As such the proof below is provided. It shows that we _can_ be well formed,
        as long as the oracle provided is good, and that the parsers do not eat into each other. *)
    sorry
  oops

lemma then_drop_second_well_formed:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  assumes "\<exists>i. has_result (parse b2) i b []"
  shows   "bidef_well_formed (then_drop_second b1 b2 b)"
  apply wf_init
  subgoal
    using assms(1,2)[THEN get_pngi]
          then_drop_second_PNGI
    by fast
  subgoal
    using assms(2, 3, 4)
    unfolding bidef_well_formed_def (* assms(2) *)
                parser_can_parse_print_result_def
                parser_can_parse_print_result_def
              pa_does_not_eat_into_pb_nondep_def (* assms(3) *)
    apply (unfold then_drop_second_has_result)
    apply (unfold then_drop_second_p_has_result)
    by fast
  subgoal
    using assms(1, 2, 4)
    unfolding bidef_well_formed_def (* assms(1, 2) *) 
                printer_can_print_parse_result_def
    apply (unfold then_drop_second_has_result)
    apply (unfold then_drop_second_p_has_result)
    by fast
  done



\<comment> \<open>Examples:\<close>
value "parse (then_drop_second one_char one_char (CHR ''p'')) ''apples''"
value "print (then_drop_second one_char one_char (CHR ''p'')) CHR ''b''"

end
