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



\<comment> \<open>FP NER\<close>
lemma then_drop_second_p_is_error[fp_NER]:
  "p_is_error (print (then_drop_second ab bb b)) va \<longleftrightarrow> p_is_error (print ab) va \<or> p_is_error (print bb) b"
  by (simp add: then_drop_second_def fp_NER split: prod.splits)+

lemma then_drop_second_p_has_result[fp_NER]:
  "p_has_result (print (then_drop_second ab bb b)) va t \<longleftrightarrow> (\<exists>ta tb.  t = ta@tb \<and> p_has_result (print ab) va ta \<and> p_has_result (print bb) b tb)"
  by (auto simp add: then_drop_second_def fp_NER split: prod.splits)+



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