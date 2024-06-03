theory derived_then_drop_first
  imports basic_definitions
          derived_then
begin

definition then_drop_first :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> '\<alpha> \<Rightarrow> '\<beta> bidef" where
  "then_drop_first ab bb a = transform
                              (snd :: ('\<alpha>\<times>'\<beta>) \<Rightarrow> '\<beta>)
                              ((\<lambda> b. (a, b)) :: '\<beta> \<Rightarrow> ('\<alpha>\<times>'\<beta>))
                              (b_then ab bb :: ('\<alpha>\<times>'\<beta>) bidef)"



\<comment> \<open>NER\<close>
lemma then_drop_first_is_nonterm[NER_simps]:
  "is_nonterm (parse (then_drop_first ab bb a)) i \<longleftrightarrow> is_nonterm (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_nonterm (parse bb) l)"
  by (simp add: then_drop_first_def NER_simps)

lemma then_drop_first_is_error[NER_simps]:
  "is_error (parse (then_drop_first ab bb a)) i \<longleftrightarrow> is_error (parse (b_then ab bb)) i"
  by (simp add: then_drop_first_def NER_simps)

lemma then_drop_first_has_result[NER_simps]:
  "has_result (parse (then_drop_first ab bb a)) i rb l \<longleftrightarrow> (\<exists> l' ra. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l)"
  by (auto simp add: then_drop_first_def NER_simps split: prod.splits)



\<comment> \<open>FP NER\<close>
lemma then_drop_first_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (then_drop_first ab bb a)) vb \<longleftrightarrow> p_is_nonterm (print ab) a \<or> (\<not>p_is_error (print ab) a \<and> p_is_nonterm (print bb) vb)"
  by (simp add: then_drop_first_def fp_NER split: prod.splits)+

lemma then_drop_first_p_is_error[fp_NER]:
  "p_is_error (print (then_drop_first ab bb a)) vb \<longleftrightarrow> p_is_error (print ab) a \<or> (\<not>p_is_nonterm (print ab) a \<and> p_is_error (print bb) vb)"
  by (simp add: then_drop_first_def fp_NER split: prod.splits)+

lemma then_drop_first_p_has_result[fp_NER]:
  "p_has_result (print (then_drop_first ab bb a)) vb t \<longleftrightarrow> (\<exists>ta tb.  t = ta@tb \<and> p_has_result (print ab) a ta \<and> p_has_result (print bb) vb tb)"
  by (auto simp add: then_drop_first_def fp_NER split: prod.splits)+

lemma then_drop_first_print_empty[print_empty, fp_NER]:
  "p_has_result (print (then_drop_first A B oracle)) i [] \<longleftrightarrow> p_has_result (print A) oracle [] \<and> p_has_result (print B) i []"
  by (clarsimp simp add: then_drop_first_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma then_drop_first_PNGI[PASI_PNGI]:
  assumes "PNGI (parse ab)"
  assumes "PNGI (parse bb)"
  shows "PNGI (parse (then_drop_first ab bb a))"
  unfolding then_drop_first_def
  unfolding transform_PNGI[symmetric]
  apply (rule then_PNGI)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  done


lemma then_drop_first_PASI:
  assumes "PASI (parse ab)"
  assumes "PASI (parse bb)"
  shows "PASI (parse (then_drop_first ab bb a))"
  unfolding then_drop_first_def
  unfolding transform_PASI[symmetric]
  apply (rule then_PASI)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  done



\<comment> \<open>Does not peek past end\<close>
lemma then_drop_first_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  assumes "PNGI (parse A)"
  assumes "does_not_peek_past_end (parse B)"
  assumes "PNGI (parse B)"
  shows "does_not_peek_past_end (parse (then_drop_first A B oracle))"
  unfolding does_not_peek_past_end_def
  apply (clarsimp simp add: NER_simps)
  by (metis (no_types, opaque_lifting) assms(1,2,3,4) b_then_has_result(1)
                                       then_does_not_peek_past_end does_not_peek_past_end_def)



\<comment> \<open>First printed char\<close>
lemma then_drop_first_fpci[fpci_simps]:
  "first_printed_chari (print (then_drop_first A B oracle)) i c \<longleftrightarrow>(
    if p_has_result (print A) oracle [] then
      (first_printed_chari (print B) i c)
    else
      (first_printed_chari (print A) oracle c \<and> (\<exists>t. p_has_result (print B) i t))
  )"
  by (clarsimp simp add: then_drop_first_def fpci_simps)



\<comment> \<open>well formed\<close>

lemma b_then_drop_first_wf_derived:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  assumes "\<exists> it. has_result (parse b2) it b []"
  shows "bidef_well_formed (then_drop_first b1 b2 b)"
  unfolding then_drop_first_def
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

lemma then_drop_first_well_formed:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  assumes "\<exists>i. has_result (parse b1) i a []"
  shows   "bidef_well_formed (then_drop_first b1 b2 a)"
  apply wf_init
  subgoal
    using assms(1,2)[THEN get_pngi]
          then_drop_first_PNGI
    by fast
  subgoal
    using assms(2, 3, 4) (*It seems to me like for assm(4) here we don't really need this specific print, just any print for b2 or b1.*)
    unfolding bidef_well_formed_def (* assms(2) *)
                parser_can_parse_print_result_def
                parser_can_parse_print_result_def
              pa_does_not_eat_into_pb_nondep_def (* assms(3) *)
    apply (unfold then_drop_first_has_result)
    apply (unfold then_drop_first_p_has_result)
    by fast
  subgoal
    using assms(1, 2, 4)
    unfolding bidef_well_formed_def (* assms(1, 2) *) 
                printer_can_print_parse_result_def
    apply (unfold then_drop_first_has_result)
    apply (unfold then_drop_first_p_has_result)
    by blast
  done



\<comment> \<open>Examples:\<close>
value "parse (then_drop_first one_char one_char (CHR ''a'')) ''apples''"
value "print (then_drop_first one_char one_char (CHR ''a'')) CHR ''p''"

end
