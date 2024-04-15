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

lemma b_then_is_error_from_first:
  assumes "is_error (parse ab) i"
  shows "is_error (parse (b_then ab bb)) i"
  by (auto simp add: NER_simps assms)

lemma b_then_has_result[NER_simps]:
  "has_result (parse (b_then ab bb)) i (ra, rb) l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l)"
  "has_result (parse (b_then ab bb)) i r l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i (fst r) l' \<and> has_result (parse bb) l' (snd r) l)"
  "has_result (parse (b_then ab bb)) i r l \<longleftrightarrow> (case r of (ra, rb) \<Rightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l))"
  by (auto simp add: b_then_def NER_simps split: prod.splits) fastforce+



\<comment> \<open>FP NER\<close>
lemma b_then_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (b_then ab bb)) (va, vb) \<longleftrightarrow> p_is_nonterm (print ab) va \<or> (\<not>p_is_error (print ab) va \<and> p_is_nonterm (print bb) vb)"
  "p_is_nonterm (print (b_then ab bb)) v \<longleftrightarrow> p_is_nonterm (print ab) (fst v) \<or> (\<not>p_is_error (print ab) (fst v) \<and> p_is_nonterm (print bb) (snd v))"
  "p_is_nonterm (print (b_then ab bb)) v \<longleftrightarrow> (case v of (va, vb) \<Rightarrow> p_is_nonterm (print ab) va \<or> (\<not>p_is_error (print ab) va \<and> p_is_nonterm (print bb) vb))"
  by (simp add: b_then_def fp_NER Let_def split: prod.splits)+

lemma b_then_p_is_error[fp_NER]:
  "p_is_error (print (b_then ab bb)) (va, vb) \<longleftrightarrow> p_is_error (print ab) va \<or> (\<not>p_is_nonterm (print ab) va \<and> p_is_error (print bb) vb)"
  "p_is_error (print (b_then ab bb)) v \<longleftrightarrow> p_is_error (print ab) (fst v) \<or> (\<not>p_is_nonterm (print ab) (fst v) \<and> p_is_error (print bb) (snd v))"
  "p_is_error (print (b_then ab bb)) v \<longleftrightarrow> (case v of (va, vb) \<Rightarrow> p_is_error (print ab) va \<or> (\<not>p_is_nonterm (print ab) va \<and> p_is_error (print bb) vb))"
  by (simp add: b_then_def fp_NER Let_def split: prod.splits)+

lemma b_then_p_has_result[fp_NER]:
  "p_has_result (print (b_then ab bb)) (va, vb) t \<longleftrightarrow> (\<exists>ta tb. ta@tb = t \<and> p_has_result (print ab) va ta \<and> p_has_result (print bb) vb tb)"
  "p_has_result (print (b_then ab bb)) v t \<longleftrightarrow> (\<exists>ta tb. ta@tb = t \<and> p_has_result (print ab) (fst v) ta \<and> p_has_result (print bb) (snd v) tb)"
  "p_has_result (print (b_then ab bb)) v t \<longleftrightarrow> (case v of (va, vb) \<Rightarrow> (\<exists>ta tb. ta@tb = t \<and> p_has_result (print ab) va ta \<and> p_has_result (print bb) vb tb))"
  by (simp add: b_then_def fp_NER split: prod.splits)+



\<comment> \<open>PNGI, PASI\<close>
lemma then_PNGI:
  assumes "PNGI (parse ab)"
  assumes "PNGI (parse bb)"
  shows "PNGI (parse (b_then ab bb))"
  unfolding b_then_def
  apply (rule dep_then_PNGI)
  subgoal by (rule assms(1))
  subgoal
    using transform_PNGI assms(2)
    by blast
  done

lemma then_PASI:
  assumes "PASI (parse ab)"
  assumes "PASI (parse bb)"
  shows "PASI (parse (b_then ab bb))"
  unfolding b_then_def
  apply (rule dep_then_PASI)
  subgoal by (rule assms(1))
  subgoal
    using transform_PASI assms(2)
    by blast
  done

lemma then_PASI_from_pasi_pngi:
  assumes "PASI (parse ab)"
  assumes "PNGI (parse bb)"
  shows "PASI (parse (b_then ab bb))"
  unfolding b_then_def
  apply (rule dep_then_PASI_PASI_PNGI)
  subgoal by (rule assms(1))
  subgoal
    apply (subst transform_PNGI[symmetric])
    by (clarsimp simp add: assms(2))
  done

lemma then_PASI_from_pngi_pasi:
  assumes "PNGI (parse ab)"
  assumes "PASI (parse bb)"
  shows "PASI (parse (b_then ab bb))"
  unfolding b_then_def
  apply (rule dep_then_PASI_PNGI_PASI)
  subgoal by (rule assms(1))
  subgoal
    apply (subst transform_PASI[symmetric])
    by (clarsimp simp add: assms(2))
  done



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
      subgoal using transform_PNGI by blast
      subgoal for i r l b x last
        \<comment> \<open>not really viable here since last is not mentioned in any other assumption\<close>
        sorry
      subgoal by (metis snd_conv transform_p_has_result)
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

lemma b_then_well_formed:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "pa_does_not_eat_into_pb_nondep b1 b2"
  shows   "bidef_well_formed (b_then b1 b2)"
  apply wf_init
  subgoal by (rule then_PNGI[OF assms(1,2)[THEN get_pngi]])
  subgoal
    using assms(2, 3)
    unfolding bidef_well_formed_def (* assms(2) *)
                parser_can_parse_print_result_def
              pa_does_not_eat_into_pb_nondep_def (* assms(4) *)
    apply (unfold b_then_has_result(3))
    apply (unfold b_then_p_has_result(3))
    by fast
  subgoal
    using assms(1,2)
    unfolding printer_can_print_parse_result_def
              bidef_well_formed_def
    apply (unfold b_then_has_result(3))
    apply (unfold b_then_p_has_result(3))
    by fast
  done

value "one_char"
value "parse one_char ''abcd''"
value "parse (b_then one_char one_char) ''abcd''"

lemma first_char_not_in_charset_implies_pa_does_not_eat_into_pb_nondep:
  assumes "bidef_well_formed a"
  assumes "(first_chars (print b) \<inter> charset (parse a)) = {}"
  shows "pa_does_not_eat_into_pb_nondep a b"
  using assms[unfolded first_chars_def charset_def]
  unfolding pa_does_not_eat_into_pb_nondep_def bidef_well_formed_def parser_can_parse_print_result_def
  apply auto
  oops







end
