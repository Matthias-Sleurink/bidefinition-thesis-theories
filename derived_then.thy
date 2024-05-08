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

lemma b_then_is_error_from_second:
  assumes "has_result (parse ab) i r l"
  assumes "is_error (parse bb) l"
  shows "is_error (parse (b_then ab bb)) i"
  using assms
  by (clarsimp simp add: NER_simps)



lemma b_then_has_result[NER_simps]:
  "has_result (parse (b_then ab bb)) i (ra, rb) l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l)"
  "has_result (parse (b_then ab bb)) i r l \<longleftrightarrow> (\<exists> l'. has_result (parse ab) i (fst r) l' \<and> has_result (parse bb) l' (snd r) l)"
  "has_result (parse (b_then ab bb)) i r l \<longleftrightarrow> (case r of (ra, rb) \<Rightarrow> (\<exists> l'. has_result (parse ab) i ra l' \<and> has_result (parse bb) l' rb l))"
  by (auto simp add: b_then_def NER_simps split: prod.splits) fastforce+

lemma b_then_has_result_ci[NER_simps]:
  assumes "PNGI (parse ab)"
  assumes "PNGI (parse bb)"
  shows
  "has_result_ci (parse (b_then ab bb)) i c (ra, rb) l \<longleftrightarrow> (\<exists> c' c''. c'@c''=c \<and> has_result_ci (parse ab) i c' ra      (c''@l) \<and> has_result_ci (parse bb) (c''@l) c'' rb      l)"
  "has_result_ci (parse (b_then ab bb)) i c r        l \<longleftrightarrow> (\<exists> c' c''. c'@c''=c \<and> has_result_ci (parse ab) i c' (fst r) (c''@l) \<and> has_result_ci (parse bb) (c''@l) c'' (snd r) l)"
  "has_result_ci (parse (b_then ab bb)) i c r        l \<longleftrightarrow> (case r of (ra, rb) \<Rightarrow> (\<exists> c' c''. c'@c''=c \<and> has_result_ci (parse ab) i c' ra (c''@l) \<and> has_result_ci (parse bb) (c''@l) c'' rb l))"
  apply (auto simp add: has_result_ci_def has_result_c_def NER_simps split: prod.splits)
  subgoal for l'
    apply (rule exI[of _ \<open>list_upto (c@l) l'\<close>])
    apply (rule exI[of _ \<open>list_upto l' l\<close>])
    using list_upto_take_cons[of \<open>c@l\<close> l']
          assms[unfolded PNGI_def]
    apply auto
    subgoal by (metis list_upto_take_cons append.assoc append_same_eq)
    subgoal by (metis list_upto_take_cons)
    subgoal by (metis list_upto_take_cons append.assoc append_same_eq)
    subgoal by (metis list_upto_take_cons)
    done
  subgoal for l'
    apply (rule exI[of _ \<open>list_upto (c@l) l'\<close>])
    apply (rule exI[of _ \<open>list_upto l' l\<close>])
    using list_upto_take_cons[of \<open>c@l\<close> l']
          assms[unfolded PNGI_def]
    apply auto
    subgoal by (metis list_upto_take_cons append.assoc append_same_eq)
    subgoal by (metis list_upto_take_cons)
    subgoal by (metis list_upto_take_cons append.assoc append_same_eq)
    subgoal by (metis list_upto_take_cons)
    done
  subgoal for r1 r2 l'
    apply (rule exI[of _ \<open>list_upto (c@l) l'\<close>])
    apply (rule exI[of _ \<open>list_upto l' l\<close>])
    using list_upto_take_cons[of \<open>c@l\<close> l']
          assms[unfolded PNGI_def]
    apply auto
    subgoal by (metis list_upto_take_cons append_assoc append_same_eq)
    subgoal by (metis list_upto_take_cons)
    subgoal by (metis list_upto_take_cons append.assoc append_same_eq)
    subgoal by (metis list_upto_take_cons)
    done
  done



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

lemma b_then_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (b_then A B)) (ia, ib) [] \<longleftrightarrow> p_has_result (print A) ia [] \<and> p_has_result (print B) ib []"
  by (clarsimp simp add: b_then_def print_empty)

lemma b_then_print_empty:
  "p_has_result (print (b_then A B)) i [] \<longleftrightarrow> p_has_result (print A) (fst i) [] \<and> p_has_result (print B) (snd i) []"
  by (clarsimp simp add: b_then_def print_empty)



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



\<comment> \<open>Does not peek past end\<close>
lemma then_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  assumes "PNGI (parse A)"
  assumes "does_not_peek_past_end (parse B)"
  assumes "PNGI (parse B)"
  shows "does_not_peek_past_end (parse (b_then A B))"
  unfolding does_not_peek_past_end_def
  apply (clarsimp simp add: NER_simps)
  proof -
    fix c a b l l' l'a
    assume hr_A: "has_result (parse A) (c @ l) a l'"
    assume hr_B: "has_result (parse B) l' b l"
    have f3: "\<forall>cs csa csb csc. (cs::char list) @ csb @ csa \<noteq> csc @ csa \<or> cs @ csb = csc"
      by auto
    obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f5: "c @ l = ccsa l' (c @ l) @ l'"
      using hr_A by (meson assms(2)[unfolded PNGI_def])
    obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f4: "l' = ccs l l' @ l"
      using hr_B by (meson assms(4)[unfolded PNGI_def])
    have "\<forall>cs csa. cs @ l \<noteq> csa @ l' \<or> csa @ ccs l l' = cs"
      using f4 f3 by metis
    then have "\<forall>cs. ccsa l' (c @ l) @ ccs l l' @ cs = c @ cs"
      using f5 append_eq_appendI by blast
    then show "\<exists>cs. has_result (parse A) (c @ l'a) a cs \<and> has_result (parse B) cs b l'a"
    using f4 hr_B hr_A by (metis assms(1, 3)[unfolded does_not_peek_past_end_def])
  qed


\<comment> \<open>Mainly for WF\<close>
definition pa_does_not_eat_into_pb_nondep :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> bool" where
  "pa_does_not_eat_into_pb_nondep ba bb \<longleftrightarrow> (
    \<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print bb) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2
)"

lemma then_does_not_consume_past_char:
  assumes "bidef_well_formed A"
  assumes "bidef_well_formed B"
  assumes "pa_does_not_eat_into_pb_nondep A B"
  assumes "does_not_consume_past_char2 (parse B) c"
  shows "does_not_consume_past_char2 (parse (b_then A B)) c"
  using assms
  unfolding does_not_consume_past_char2_def pa_does_not_eat_into_pb_nondep_def bidef_well_formed_def
            printer_can_print_parse_result_def parser_can_parse_print_result_def PNGI_def
  apply (auto simp add: NER_simps)
  subgoal
    sorry
  subgoal for c a b l l' l''
    apply (rule exI[of _ \<open>drop (length (c@l) - length l') (c@l'')\<close>])
    \<comment> \<open>This proof idea is sound I'm just not sure if we have the right preconditions here.\<close>
    \<comment> \<open>This seems like it would be doable with the idea of charset and printables as well.\<close>
    apply (auto) 
    subgoal
      sorry
    subgoal
      
      sorry
    sorry
  


\<comment> \<open>First printed char\<close>
lemma then_fpci[fpci_simps]:
  "first_printed_chari (print (b_then A B)) i c \<longleftrightarrow> (
    if p_has_result (print A) (fst i) [] then
      (first_printed_chari (print B) (snd i) c)
    else
      (first_printed_chari (print A) (fst i) c \<and> (\<exists>t. p_has_result (print B) (snd i) t))
  )"
  unfolding b_then_def
  by (auto simp add: dep_then_fpci transform_fpci2 fp_NER)



\<comment> \<open>well formed\<close>

lemma does_not_peek_past_end_implies_does_not_eat_into:
  assumes "does_not_peek_past_end (parse A)"
  assumes "bidef_well_formed A"
  shows "pa_does_not_eat_into_pb_nondep A B"
  using no_peek_past_end_wf_stronger[OF assms(1, 2)]
        pa_does_not_eat_into_pb_nondep_def
  by blast

lemma first_printed_does_not_eat_into:
  assumes "bidef_well_formed A"
  assumes "bidef_well_formed B"
  assumes "\<forall>i c. first_printed_chari (print B) i c \<longrightarrow> does_not_consume_past_char2 (parse A) c"
  shows "pa_does_not_eat_into_pb_nondep A B"
  using assms
  unfolding pa_does_not_eat_into_pb_nondep_def
            first_printed_chari_def does_not_consume_past_char2_def
            bidef_well_formed_def parser_can_parse_print_result_def
  by (metis append.right_neutral)



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



lemma b_then_well_formed_does_not_peek_past:
  assumes "bidef_well_formed A"
  assumes "bidef_well_formed B"
  assumes "does_not_peek_past_end (parse A)"
  shows "bidef_well_formed (b_then A B)"
  by (clarsimp simp add: assms b_then_well_formed
                         does_not_peek_past_end_implies_does_not_eat_into)



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
