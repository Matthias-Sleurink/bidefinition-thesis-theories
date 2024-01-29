theory derived_then
  imports basic_definitions
          derived_dep_then
begin

\<comment> \<open>Annoying: cannot call this "then" as it is a keyword\<close>

definition b_then2 :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> ('\<alpha> \<times> '\<beta>) bidef" where
  "b_then2 ab bb = dep_then ab (\<lambda>a. transform (\<lambda> b. (a, b)) (\<lambda> (a', b). b) bb) (\<lambda> (a', b). a')"


definition b_then :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> ('\<alpha> \<times> '\<beta>) bidef" where
  "b_then ab bb = dep_then ab (\<lambda>a. transform (Pair a) snd bb) fst"



\<comment> \<open>NER\<close>
lemma b_then_is_nonterm[NER_simps]:
  "is_nonterm (parse (b_then ab bb)) i \<longleftrightarrow> is_nonterm (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_nonterm (parse bb) l)"
  by (simp add: b_then_def NER_simps)

lemma b_then_is_error[NER_simps]:
  "is_error (parse (b_then ab bb)) i \<longleftrightarrow> is_error (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_error (parse bb) l)"
  by (simp add: b_then_def NER_simps)

lemma b_then_has_result[NER_simps]:
  "has_result (parse (b_then ab bb)) i (ra, rb) l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l)"
  "has_result (parse (b_then ab bb)) i r l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i (fst r) l' \<and> has_result (parse bb) l' (snd r) l)"
  "has_result (parse (b_then ab bb)) i r l \<longleftrightarrow> (case r of (ra, rb) \<Rightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l))"
  by (auto simp add: b_then_def NER_simps split: prod.splits) fastforce+



\<comment> \<open>FP NER\<close>
lemma b_then_p_is_error[fp_NER]:
  "p_is_error (print (b_then ab bb)) (va, vb) \<longleftrightarrow> p_is_error (print ab) va \<or> p_is_error (print bb) vb"
  "p_is_error (print (b_then ab bb)) v \<longleftrightarrow> p_is_error (print ab) (fst v) \<or> p_is_error (print bb) (snd v)"
  "p_is_error (print (b_then ab bb)) v \<longleftrightarrow> (case v of (va, vb) \<Rightarrow> p_is_error (print ab) va \<or> p_is_error (print bb) vb)"
  by (simp add: b_then_def fp_NER split: prod.splits)+

lemma b_then_p_has_result[fp_NER]:
  "p_has_result (print (b_then ab bb)) (va, vb) t \<longleftrightarrow> (\<exists>ta tb. ta@tb = t \<and> p_has_result (print ab) va ta \<and> p_has_result (print bb) vb tb)"
  "p_has_result (print (b_then ab bb)) v t \<longleftrightarrow> (\<exists>ta tb. ta@tb = t \<and> p_has_result (print ab) (fst v) ta \<and> p_has_result (print bb) (snd v) tb)"
  "p_has_result (print (b_then ab bb)) v t \<longleftrightarrow> (case v of (va, vb) \<Rightarrow> (\<exists>ta tb. ta@tb = t \<and> p_has_result (print ab) va ta \<and> p_has_result (print bb) vb tb))"
  by (simp add: b_then_def fp_NER split: prod.splits)+



\<comment> \<open>well formed\<close>

definition pa_does_not_eat_into_pb_nondep :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> bool" where
  "pa_does_not_eat_into_pb_nondep ba bb \<longleftrightarrow> (
    \<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print bb) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2
)"


lemma b_then_wf_derived:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  shows "bidef_well_formed (b_then b1 b2)"
  unfolding b_then_def
  apply (rule dep_then_well_formed)
  subgoal by (rule assms(1))
  subgoal
    unfolding well_formed_dep_then_pair_def
    apply (rule conjI3)
    subgoal
      unfolding b2_wf_for_all_res_of_b1_def
                bidef_well_formed_def
                parser_can_parse_print_result_def
                printer_can_print_parse_result_def
      apply (clarsimp)
      using assms(2)[unfolded bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def]
            assms(3)[unfolded pa_does_not_eat_into_pb_nondep_def]
      apply (auto simp add: NER_simps fp_NER)
      subgoal for i ra la b x a
        (* Nitpick finds a counterexample here. *)
        sorry
      subgoal by (metis snd_conv transform_p_has_result(1))
      done
    subgoal
      unfolding reversed_b2_result_is_b1_result_def
      by (simp add: NER_simps)
    subgoal
      unfolding pa_does_not_eat_into_pb_def
      using assms(3)[unfolded pa_does_not_eat_into_pb_nondep_def]
            assms(2)[unfolded bidef_well_formed_def]
      by (auto simp add: NER_simps fp_NER)
    done
  oops


\<comment> \<open>For all the parse results that the two can have, ensure that they can be re-parsed from the text if appended.\<close>
definition well_formed_b_then_pair :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> bool" where
  "well_formed_b_then_pair b1 b2 \<longleftrightarrow>
          (\<forall> v1 v2 pr1 pr2.
            (p_has_result (print b1) v1 pr1 \<and> p_has_result (print b2) v2 pr2) \<longrightarrow>
              (\<exists>l1 l2. has_result (parse b1) (pr1@pr2) v1 l1 \<and> has_result (parse b2) l1 v2 l2)
)"

lemma b_then_well_formed:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "well_formed_b_then_pair b1 b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  shows   "bidef_well_formed (b_then b1 b2)"
  apply wf_init
  subgoal
    using assms(3, 3)
    unfolding parser_can_parse_print_result_def
              well_formed_b_then_pair_def
              pa_does_not_eat_into_pb_nondep_def
    apply (unfold b_then_has_result(3))
    apply (unfold b_then_p_has_result(3))
    apply auto
    by (meson assms(2) assms(4) bidef_well_formed_def pa_does_not_eat_into_pb_nondep_def parser_can_parse_print_result_def)
  subgoal
    using assms(1,2)
    unfolding printer_can_print_parse_result_def
              bidef_well_formed_def
    apply (unfold b_then_has_result(3))
    apply (unfold b_then_p_has_result(3))
    by fast
  done

end