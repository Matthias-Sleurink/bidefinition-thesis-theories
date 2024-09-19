theory derived_then
  imports basic_definitions
          derived_dep_then
begin

\<comment> \<open>Annoying: cannot call this "then" as it is a keyword\<close>

definition b_then2 :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> ('\<alpha> \<times> '\<beta>) bidef" where
  "b_then2 ab bb = dep_then ab (\<lambda>a. transform (\<lambda> b. (a, b)) (\<lambda> (a', b). b) bb) (\<lambda> (a', b). a')"


definition b_then :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> ('\<alpha> \<times> '\<beta>) bidef" where
  "b_then ab bb = dep_then ab (\<lambda>a. transform (Pair a) snd bb) fst"

lemma mono_then[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "mono_bd B"
  shows "mono_bd (\<lambda>f. b_then (A f) (B f))"
  unfolding b_then_def using ma mb
  by pf_mono_prover



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

lemma then_result_always_same:
  assumes E_rs_eq: "\<And> i r l. has_result (parse E) i r l \<Longrightarrow> E_r = r"
  assumes S_rs_eq: "\<And> i r l. has_result (parse S) i r l \<Longrightarrow> S_r = r"
  shows "has_result (parse (b_then S E)) i r l \<Longrightarrow> (S_r, E_r) = r"
  by (clarsimp simp add: NER_simps assms)


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

lemma b_then_print_empty[print_empty]:
  "p_has_result (print (b_then A B)) i [] \<longleftrightarrow> p_has_result (print A) (fst i) [] \<and> p_has_result (print B) (snd i) []"
  by (clarsimp simp add: b_then_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma then_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PNGI (parse ab)"
  assumes "PNGI (parse bb)"
  shows "PNGI (parse (b_then ab bb))"
  unfolding b_then_def
  by (clarsimp simp add: assms PASI_PNGI_intros)

lemma then_PASI[PASI_PNGI_intros]:
  assumes "PASI (parse ab)"
  assumes "PASI (parse bb)"
  shows "PASI (parse (b_then ab bb))"
  unfolding b_then_def
  by (clarsimp simp add: assms PASI_PNGI_intros)

lemma then_PASI_from_pasi_pngi[PASI_PNGI_intros]:
  assumes "PASI (parse ab)"
  assumes "PNGI (parse bb)"
  shows "PASI (parse (b_then ab bb))"
  unfolding b_then_def
  by (clarsimp simp add: assms PASI_PNGI_intros)

lemma then_PASI_from_pngi_pasi[PASI_PNGI_intros]:
  assumes "PNGI (parse ab)"
  assumes "PASI (parse bb)"
  shows "PASI (parse (b_then ab bb))"
  unfolding b_then_def
  by (clarsimp simp add: assms PASI_PNGI_intros)



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


lemma then_does_not_peek_past_end_with_inner_conflict[peek_past_end_simps]:
  assumes A_pngi: "PNGI (parse A)"
  assumes B_pngi: "PNGI (parse B)"
  assumes exist_leftover_a: "\<And>ca cb a l b l''. \<lbrakk>has_result (parse A) (ca @ cb @ l) a (cb @ l); has_result (parse B) (cb @ l) b l\<rbrakk> \<Longrightarrow> \<exists>l'. has_result (parse A) (ca @ cb @ l'') a l' \<and> has_result (parse B) l' b l''"
  shows "does_not_peek_past_end (parse (b_then A B))"
  unfolding does_not_peek_past_end_def
  apply (clarsimp simp add: NER_simps)
  subgoal for c a b l l' l''
    apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>c@l\<close> a l']; clarsimp)
    subgoal for ca
      apply (insert B_pngi[unfolded PNGI_def, rule_format, of \<open>l'\<close> b l]; clarsimp)
      subgoal for cb
        \<comment> \<open>If there is conflict inside we don't know how to resolve it.\<close>
        \<comment> \<open>We might be able to create a few more primitives to resolve that conflict\<close>
        \<comment> \<open>But it makes more sense to give it back to where this is applied, and just ask them to resolve it.\<close>
        by (rule exist_leftover_a)
      done
    done
  done



lemma then_does_not_peek_past_end_from_fpc[peek_past_end_simps]:
  assumes fpc_B_dncpc_A:  "\<And>i c. fpc (parse B) i c \<Longrightarrow> does_not_consume_past_char3 (parse A) c"
  assumes b_parse_empty_case: "\<And> ca l a b l'. \<lbrakk>has_result (parse A) (ca @ l) a l; has_result (parse B) l b l\<rbrakk> \<Longrightarrow> has_result (parse A) (ca @ l') a l'"
  assumes A_pngi: "PNGI (parse A)"

  assumes B_dnppe: "does_not_peek_past_end (parse B)"
  assumes B_pngi: "PNGI (parse B)"
  shows "does_not_peek_past_end (parse (b_then A B))"
  unfolding does_not_peek_past_end_def
  apply (clarsimp simp add: NER_simps)
  subgoal for c a b l l' l''
    apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>c@l\<close> a l']; clarsimp)
    subgoal for ca
      apply (insert B_pngi[unfolded PNGI_def, rule_format, of \<open>l'\<close> b l]; clarsimp)
      subgoal for cb
        apply (rule exI[of _ \<open>cb@l''\<close>]; auto)
        subgoal
          apply (cases cb; clarsimp)
          subgoal \<comment> \<open>empty\<close> by (rule b_parse_empty_case)
          subgoal for cb' cbs \<comment> \<open>nonEmpty\<close>
            using fpc_B_dncpc_A[unfolded fpc_def does_not_consume_past_char3_def,
                                rule_format, of cb' b ca \<open>cb@l\<close> a \<open>cbs@l''\<close>,
                                OF exI[of _ cbs], OF exI[of _ l]]
            by fastforce
          done
        subgoal by (rule B_dnppe[unfolded does_not_peek_past_end_def, rule_format])
        done
      done
    done
  done


\<comment> \<open>Mainly for WF\<close>
definition pa_does_not_eat_into_pb_nondep :: "'\<alpha> bidef \<Rightarrow> '\<beta> bidef \<Rightarrow> bool" where
  "pa_does_not_eat_into_pb_nondep ba bb \<longleftrightarrow> (
    \<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print bb) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2
)"


lemma then_does_not_consume_past_char_from_first_no_peek_past_end:
  assumes dnppe: "does_not_peek_past_end (parse A)"
  assumes pngiA: "PNGI (parse A)"
  assumes dncpc: "does_not_consume_past_char3 (parse B) c"
  assumes pgniB: "PNGI (parse B)"
  shows "does_not_consume_past_char3 (parse (b_then A B)) c"
  unfolding does_not_consume_past_char3_def
  apply (clarsimp simp add: NER_simps)
  subgoal for c ra rb l l'
    apply (insert pngiA[unfolded PNGI_def, rule_format, of \<open>c@l\<close> ra l']; clarsimp)
    subgoal for ca
      apply (insert dnppe[unfolded does_not_peek_past_end_def, rule_format, of ca l' ra]; clarsimp; rule conjI)
      subgoal
        apply (insert pgniB[unfolded PNGI_def, rule_format, of l' rb l]; clarsimp)
        using dncpc[unfolded does_not_consume_past_char3_def] by fast
      subgoal
        apply (insert pgniB[unfolded PNGI_def, rule_format, of l' rb l]; clarsimp)
        using dncpc[unfolded does_not_consume_past_char3_def] by fast
      done
    done
  done

lemma then_does_not_consume_past_parse_consume:
  assumes A_can_drop_leftover: "\<And>c l l' r. has_result (parse A) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse A) (c @ l) r l"
  assumes B_can_drop_leftover: "\<And>c l l' r. has_result (parse B) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse B) (c @ l) r l"
  assumes A_pngi: "PNGI (parse A)"
  assumes B_pngi: "PNGI (parse B)"
  assumes A_dncppc_B: "does_not_consume_past_parse_consume (parse A) (parse B)"
  assumes B_dncppc_C: "does_not_consume_past_parse_consume (parse B) (parse C)"
  shows "does_not_consume_past_parse_consume (parse (b_then A B)) (parse C)"
  unfolding does_not_consume_past_parse_consume_def
  apply (auto simp add: NER_simps)
  subgoal for ca ra rb l cc bi rc lc
    apply (insert B_pngi[unfolded PNGI_def, rule_format, of bi rb l]; clarsimp)
    subgoal for cb
      apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>ca@l\<close> ra \<open>cb@l\<close>]; clarsimp)
      subgoal for ca
        apply (rule exI[of _ cb]; rule conjI)
        subgoal using A_can_drop_leftover[of ca cb l ra] by blast
        subgoal using B_can_drop_leftover[of cb \<open>[]\<close> l rb, simplified] by blast
        done
      done
    done
  subgoal for c a b l l' cc l'a r2 l2
    apply (insert B_pngi[unfolded PNGI_def, rule_format, of l'a b l]; clarsimp)
    subgoal for cb
      apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>c@l\<close> a \<open>cb@l\<close>]; clarsimp)
      subgoal for ca
        apply (rule exI[of _ \<open>cb @ cc @ l'\<close>]; rule conjI)
        subgoal
          using A_dncppc_B[unfolded does_not_consume_past_parse_consume_def, rule_format, of ca \<open>cb@l\<close> a cb l b \<open>cc@l'\<close>]
          by blast
        subgoal
          using B_dncppc_C[unfolded does_not_consume_past_parse_consume_def, rule_format, of cb l b cc l2 r2 l']
          by blast
        done
      done
    done
  done


lemma then_does_not_consume_past_parse_consume_or_if_empty_B:
  assumes A_can_drop_leftover: "\<And>c l l' r. has_result (parse A) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse A) (c @ l) r l"
  assumes B_can_drop_leftover: "\<And>c l l' r. has_result (parse B) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse B) (c @ l) r l"
  assumes A_pngi: "PNGI (parse A)"
  assumes B_pngi: "PNGI (parse B)"
  assumes A_dncppc_B_oie_C: "does_not_conusme_past_parse_consume_or_if_empty (parse A) (parse B) (parse C)"
  assumes B_dncppc_C: "does_not_consume_past_parse_consume (parse B) (parse C)"
  shows "does_not_consume_past_parse_consume (parse (b_then A B)) (parse C)"
  unfolding does_not_consume_past_parse_consume_def
  apply (auto simp add: NER_simps)
  subgoal for ca ra rb l cc bi rc lc
    apply (insert B_pngi[unfolded PNGI_def, rule_format, of bi rb l]; clarsimp)
    subgoal for cb
      apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>ca@l\<close> ra \<open>cb@l\<close>]; clarsimp)
      subgoal for ca
        apply (rule exI[of _ cb]; rule conjI)
        subgoal using A_can_drop_leftover[of ca cb l ra] by blast
        subgoal using B_can_drop_leftover[of cb \<open>[]\<close> l rb, simplified] by blast
        done
      done
    done
  subgoal for c a b l l' cc l'a r2 l2
    apply (insert B_pngi[unfolded PNGI_def, rule_format, of l'a b l]; clarsimp)
    subgoal for cb
      apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>c@l\<close> a \<open>cb@l\<close>]; clarsimp)
      subgoal for ca
        apply (rule exI[of _ \<open>cb @ cc @ l'\<close>]; rule conjI)
        subgoal
          by (insert A_dncppc_B_oie_C[unfolded does_not_conusme_past_parse_consume_or_if_empty_def,
                     rule_format, of ca \<open>cb@l\<close> a cb l b cc l2 r2 l' \<open>cc@l'\<close>]; clarsimp split: if_splits)
        subgoal
          using B_dncppc_C[unfolded does_not_consume_past_parse_consume_def, rule_format, of cb l b cc l2 r2 l']
          by blast
        done
      done
    done
  done



lemma then_can_drop_leftover:
  assumes A_can_drop_leftover: "\<And>c l l' r. has_result (parse A) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse A) (c @ l) r l"
  assumes A_pngi: "PNGI (parse A)"

  assumes B_can_drop_leftover: "\<And>c l l' r. has_result (parse B) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse B) (c @ l) r l"
  assumes B_pngi: "PNGI (parse B)"

  shows "has_result (parse (b_then A B)) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse (b_then A B)) (c @ l) r l"
  apply (clarsimp simp add: NER_simps)
  subgoal for la
    apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>c@l@l'\<close> \<open>fst r\<close> la]; clarsimp)
    subgoal for ca
      apply (insert B_pngi[unfolded PNGI_def, rule_format, of la \<open>snd r\<close> \<open>l@l'\<close>]; clarsimp)
      subgoal for cb
        apply (rule exI[of _ \<open>cb@l\<close>]; rule conjI)
        subgoal by (rule A_can_drop_leftover[of ca \<open>cb@l\<close> l' \<open>fst r\<close>, simplified])
        subgoal by (rule B_can_drop_leftover[of cb l l' \<open>snd r\<close>])
        done
      done
    done
  done

lemma length_lt_eq_append_exI:
  assumes "i @ i' = cA @ l"
  assumes "length cA < length i"
  shows "\<exists>ci. i = cA@ci"
  using assms
  by (metis append_eq_append_conv2 length_append not_add_less1)
lemma length_mt_eq_append_exI:
  assumes "i @ i' = cA @ l"
  assumes "\<not> length cA < length i"
  shows "\<exists>i''. cA = i@i''"
  using assms
  by (metis append.right_neutral append_eq_append_conv length_lt_eq_append_exI linorder_neqE_nat)


lemma then_can_drop_leftover_on_error:
  assumes A_can_drop_leftover_error: "\<And>i i' i''. is_error (parse A) (i @ i') \<Longrightarrow> is_error (parse A) i"
  assumes A_pngi: "PNGI (parse A)"
  assumes A_no_nonterm_i: "\<not>is_nonterm (parse A) i" \<comment> \<open>If this term is inconvenient, use the version below.\<close>

  assumes remove_into_A_means_error_A_or_error_B: "\<And>i' r l. \<lbrakk>i'\<noteq> []; has_result (parse A) (i @ i' @ l) r l; is_error (parse B) l\<rbrakk> \<Longrightarrow> (is_error (parse A) i \<or> (\<exists>r l. has_result (parse A) i r l \<and> is_error (parse B) l))"

  assumes A_can_drop_leftover: "\<And>c l l' r. has_result (parse A) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse A) (c @ l) r l"
  assumes B_can_drop_leftover_error: "\<And>i i' i''. is_error (parse B) (i @ i') \<Longrightarrow> is_error (parse B) i"

  assumes AB_error: "is_error (parse (b_then A B)) (i @ i')"
  shows "is_error (parse (b_then A B)) i"
  apply (insert AB_error)
  apply (auto simp add: NER_simps)
  subgoal by (rule A_can_drop_leftover_error)
  subgoal for r l
    \<comment> \<open>A has a result from i@i', and B errors on the leftover l.\<close>
    \<comment> \<open>Assuming that A having a result from i and B does not error from the leftover.\<close>
    apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>i@i'\<close> r l]; clarsimp)
    subgoal for cA
      \<comment> \<open>We want to split into two cases. Either I is wholly consumed, or it is not.\<close>
      apply (cases \<open>length i > length cA\<close>)
      subgoal
        apply (insert length_lt_eq_append_exI[of i i' cA l]; clarsimp)
        subgoal for cI
          apply (insert A_can_drop_leftover[of cA cI i' r]; clarsimp)
          using B_can_drop_leftover_error[of cI i'] by blast
        done
      subgoal
        \<comment> \<open>cA is longer than i.\<close>
        \<comment> \<open>So, we are trying to drop into the territory of A.\<close>
        \<comment> \<open>So, we need to show that if this happens either A fails, or it creates a leftover that makes B fail.\<close>
        apply (insert length_mt_eq_append_exI[of i i' cA l]; clarsimp)
        subgoal for i''
          apply (cases i''; clarsimp)
          subgoal \<comment> \<open>i'' is empty, so now we can do the same argument as above\<close>
            apply (insert A_can_drop_leftover[of i \<open>[]\<close> l r, simplified]; clarsimp)
            by (insert B_can_drop_leftover_error[of \<open>[]\<close> l, simplified]; clarsimp)
          subgoal for is' iss
            \<comment> \<open>Either removing is'#iss makes A error, or it makes it succeed with some result.\<close>
            \<comment> \<open>We require that if it does succeed with some leftover that that leftover makes B error.\<close>
            apply (cases \<open>\<exists>r l. has_result (parse A) i r l\<close>)
            subgoal
              \<comment> \<open>There is some way to make a result from i.\<close>
              \<comment> \<open>Now we need either that the leftover cannot be used by B or that actually this is not possible because of A.\<close>
              apply (insert remove_into_A_means_error_A_or_error_B[of \<open>is'#iss\<close> l]; clarsimp)
              by blast
            subgoal
              using has_result_exhaust(3)[of \<open>parse A\<close> i] A_no_nonterm_i
              by fast
            done
          done
        done
      done
    done
  done


lemma then_can_drop_leftover_on_error_when_first_no_error:
  assumes A_can_drop_leftover_error: "\<And>i i' i''. is_error (parse A) (i @ i') \<Longrightarrow> is_error (parse A) i"
  assumes A_pngi: "PNGI (parse A)"
  assumes A_can_has_result_or_A_no_nonterm_i: "(\<forall>is' iss r. (has_result (parse A) (i @ is' # iss @ l) r l \<and> i' = is' # iss @ l) \<longrightarrow> (\<exists>r l. has_result (parse A) i r l)) \<or> (\<not>is_nonterm (parse A) i)"

  assumes remove_into_A_means_error_A_or_error_B: "\<And>i' r l. \<lbrakk>i'\<noteq> []; has_result (parse A) (i @ i' @ l) r l; is_error (parse B) l\<rbrakk> \<Longrightarrow> (is_error (parse A) i \<or> (\<exists>r l. has_result (parse A) i r l \<and> is_error (parse B) l))"

  assumes A_can_drop_leftover: "\<And>c l l' r. has_result (parse A) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse A) (c @ l) r l"
  assumes B_can_drop_leftover_error: "\<And>i i' i''. is_error (parse B) (i @ i') \<Longrightarrow> is_error (parse B) i"

  assumes AB_error: "is_error (parse (b_then A B)) (i @ i')"
  shows "is_error (parse (b_then A B)) i"
  apply (insert AB_error)
  apply (auto simp add: NER_simps)
  subgoal by (rule A_can_drop_leftover_error)
  subgoal for r l
    \<comment> \<open>A has a result from i@i', and B errors on the leftover l.\<close>
    \<comment> \<open>Assuming that A having a result from i and B does not error from the leftover.\<close>
    apply (insert A_pngi[unfolded PNGI_def, rule_format, of \<open>i@i'\<close> r l]; clarsimp)
    subgoal for cA
      \<comment> \<open>We want to split into two cases. Either I is wholly consumed, or it is not.\<close>
      apply (cases \<open>length i > length cA\<close>)
      subgoal
        apply (insert length_lt_eq_append_exI[of i i' cA l]; clarsimp)
        subgoal for cI
          apply (insert A_can_drop_leftover[of cA cI i' r]; clarsimp)
          using B_can_drop_leftover_error[of cI i'] by blast
        done
      subgoal
        \<comment> \<open>cA is longer than i.\<close>
        \<comment> \<open>So, we are trying to drop into the territory of A.\<close>
        \<comment> \<open>So, we need to show that if this happens either A fails, or it creates a leftover that makes B fail.\<close>
        apply (insert length_mt_eq_append_exI[of i i' cA l]; clarsimp)
        subgoal for i''
          apply (cases i''; clarsimp)
          subgoal \<comment> \<open>i'' is empty, so now we can do the same argument as above\<close>
            apply (insert A_can_drop_leftover[of i \<open>[]\<close> l r, simplified]; clarsimp)
            by (insert B_can_drop_leftover_error[of \<open>[]\<close> l, simplified]; clarsimp)
          subgoal for is' iss
            \<comment> \<open>Either removing is'#iss makes A error, or it makes it succeed with some result.\<close>
            \<comment> \<open>We require that if it does succeed with some leftover that that leftover makes B error.\<close>
            apply (cases \<open>\<exists>r l. has_result (parse A) i r l\<close>)
            subgoal
              \<comment> \<open>There is some way to make a result from i.\<close>
              \<comment> \<open>Now we need either that the leftover cannot be used by B or that actually this is not possible because of A.\<close>
              apply (insert remove_into_A_means_error_A_or_error_B[of \<open>is'#iss\<close> l]; clarsimp)
              by blast
            subgoal
              using has_result_exhaust(3)[of \<open>parse A\<close> i] A_can_has_result_or_A_no_nonterm_i
              apply auto
              by (metis Cons_eq_append_conv list.simps(3) remove_into_A_means_error_A_or_error_B)
            done
          done
        done
      done
    done
  done



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

\<comment> \<open>The last two assms can be replaced with does_not_peek_past_end.\<close>
\<comment> \<open>Is there some nice way of having two alternative assms?\<close>
lemma then_does_not_consume_past3:
  assumes wf_A: "bidef_well_formed A"
  assumes wf_B: "bidef_well_formed B"
  assumes dncpc_B_c: "does_not_consume_past_char3 (parse B) c"
  assumes fpc_B_dncpc_A: "\<And>i c. fpc (parse B) i c \<longrightarrow> does_not_consume_past_char3 (parse A) c"
  assumes no_empty_res_B: "\<nexists>r l. has_result (parse B) [] r l"
  shows "does_not_consume_past_char3 (parse (b_then A B)) c"
  unfolding does_not_consume_past_char3_def
  apply auto
  subgoal for c'' a b l
    apply (clarsimp simp add: NER_simps)
    subgoal for l'
      using wf_B[THEN get_pngi_unfold, rule_format, of l' b l]
      apply clarsimp
      subgoal for c'
        using wf_A[THEN get_pngi_unfold, rule_format, of \<open>c''@l\<close> a \<open>c'@l\<close>]
        apply clarsimp
        subgoal for c
          apply (rule exI[of _ c'])
          apply (rule conjI)
          subgoal
            \<comment> \<open>\<^term>\<open>does_not_peek_past_end (parse A)\<close> would solve it.\<close>
            using dncpc_B_c[unfolded does_not_consume_past_char3_def]
            apply (cases c')
            subgoal
              using no_empty_res_B
              apply clarsimp
              \<comment> \<open>We have has_result A c@l a l.\<close>
              \<comment> \<open>We need has_result A c   a []\<close>
              \<comment> \<open>It seems like we can remove no empty res B by having this as a precondition?\<close>
              
              by force \<comment> \<open>Figure out if we can remove no_empty_res_B somehow?\<close>
            subgoal using fpc_B_dncpc_A[unfolded does_not_consume_past_char3_def fpc_def] by fastforce
            done
          subgoal
            using dncpc_B_c[unfolded does_not_consume_past_char3_def] by fastforce
          done
        done
      done
    done
  subgoal for cs a b l l'
    apply (clarsimp simp add: NER_simps)
    subgoal for l''
      using wf_A[THEN get_pngi_unfold, rule_format, of \<open>cs@l\<close> a l'']
      using wf_B[THEN get_pngi_unfold, rule_format, of l'' b l]
      apply clarsimp
      subgoal for c' c''
        apply (rule exI[of _ \<open>c'' @ c # l'\<close>])
        apply (rule conjI)
        subgoal
          \<comment> \<open>\<^term>\<open>does_not_peek_past_end (parse A)\<close> would solve it.\<close>
          using dncpc_B_c[unfolded does_not_consume_past_char3_def]
          apply (cases c'')
          subgoal using no_empty_res_B by blast \<comment> \<open>This can also be proven in a few other ways.\<close>
          subgoal using fpc_B_dncpc_A[unfolded does_not_consume_past_char3_def fpc_def] by fastforce
          done
        subgoal using dncpc_B_c[unfolded does_not_consume_past_char3_def] by fastforce
        done
      done
    done
  done


lemma then_does_not_consume_past3_from_can_drop_leftover:
  assumes wf_A: "bidef_well_formed A"
  assumes wf_B: "bidef_well_formed B"
  assumes dncpc_B_c: "does_not_consume_past_char3 (parse B) c"
  assumes fpc_B_dncpc_A: "\<And>i c. fpc (parse B) i c \<longrightarrow> does_not_consume_past_char3 (parse A) c"
  assumes dncpc_A_c: "does_not_consume_past_char3 (parse A) c"
  assumes A_drop_leftover_after: "\<And>c c' l a. has_result (parse A) (c @ c' @ l) a (c' @ l) \<Longrightarrow> has_result (parse A) (c @ c') a c'"
  shows "does_not_consume_past_char3 (parse (b_then A B)) c"
  unfolding does_not_consume_past_char3_def
  apply auto
  subgoal for c'' a b l
    apply (clarsimp simp add: NER_simps)
    subgoal for l'
      using wf_B[THEN get_pngi_unfold, rule_format, of l' b l]
      apply clarsimp
      subgoal for c'
        using wf_A[THEN get_pngi_unfold, rule_format, of \<open>c''@l\<close> a \<open>c'@l\<close>]
        apply clarsimp
        subgoal for c
          apply (rule exI[of _ c']; rule conjI)
          subgoal by (rule A_drop_leftover_after)
          subgoal using dncpc_B_c[unfolded does_not_consume_past_char3_def] by fastforce
          done
        done
      done
    done
  subgoal for cs a b l l'
    apply (clarsimp simp add: NER_simps)
    subgoal for l''
      using wf_A[THEN get_pngi_unfold, rule_format, of \<open>cs@l\<close> a l'']
      using wf_B[THEN get_pngi_unfold, rule_format, of l'' b l]
      apply clarsimp
      subgoal for c' c''
        apply (rule exI[of _ \<open>c'' @ c # l'\<close>])
        apply (rule conjI)
        subgoal
          \<comment> \<open>\<^term>\<open>does_not_peek_past_end (parse A)\<close> would solve it.\<close>
          using dncpc_B_c[unfolded does_not_consume_past_char3_def]
          apply (cases c''; clarsimp)
          subgoal
            using dncpc_A_c[unfolded does_not_consume_past_char3_def] by fast
          subgoal using fpc_B_dncpc_A[unfolded does_not_consume_past_char3_def fpc_def] by fastforce
          done
        subgoal using dncpc_B_c[unfolded does_not_consume_past_char3_def] by fastforce
        done
      done
    done
  done



\<comment> \<open>well formed\<close>

lemma does_not_peek_past_end_implies_does_not_eat_into:
  assumes "does_not_peek_past_end (parse A)"
  assumes "bidef_well_formed A"
  shows "pa_does_not_eat_into_pb_nondep A B"
  using no_peek_past_end_wf_stronger[OF assms(1, 2)]
        pa_does_not_eat_into_pb_nondep_def
  by blast

lemma first_printed_does_not_eat_into3:
  assumes "bidef_well_formed A"
  assumes "\<forall>i c. first_printed_chari (print B) i c \<longrightarrow> does_not_consume_past_char3 (parse A) c"
  shows "pa_does_not_eat_into_pb_nondep A B"
  using assms(1)[THEN get_parser_can_parse, unfolded parser_can_parse_print_result_def]
  using assms(2)[unfolded first_printed_chari_def]
  unfolding pa_does_not_eat_into_pb_nondep_def
  using no_consume_past3_wf_stronger[OF _ assms(1)]
  by fastforce



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
              pa_does_not_eat_into_pb_nondep_def (* assms(3) *)
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



\<comment> \<open>Note that this is not the most general, as here we require pr2 to be the leftover.\<close>
\<comment> \<open>It could be better to require that the parser for bb can still parse the leftover into the same result.\<close>
definition no_collision:
  "no_collision ba bb \<longleftrightarrow> (\<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print bb) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2)"

thm no_collision[of b1 b2]

lemma b_then_well_formed_for_thesis:
  assumes "bidef_well_formed b1"
  assumes "bidef_well_formed b2"
  assumes "no_collision b1 b2"
  shows   "bidef_well_formed (b_then b1 b2)"
  apply wf_init
  subgoal by (rule then_PNGI[OF assms(1,2)[THEN get_pngi]])
  subgoal
    unfolding parser_can_parse_print_result_def
    apply (unfold b_then_has_result(3))
    apply (unfold b_then_p_has_result(3))
    apply clarsimp
    using assms(3)[unfolded no_collision]
    using assms(1,2)[THEN get_parser_can_parse_unfold]
    by fast
  subgoal
    unfolding printer_can_print_parse_result_def
    apply (unfold b_then_has_result(3))
    apply (unfold b_then_p_has_result(3))
    apply auto
    using assms(1,2)[THEN get_printer_can_print_unfold]
    by fast+
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
