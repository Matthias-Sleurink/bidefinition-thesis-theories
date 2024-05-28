theory derived_dep_then
  imports basic_definitions
begin

definition dep_then :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<beta> bidef" where
  "dep_then ab a2bb b2a = (transform projl Inl (if_then_else ab a2bb (fail :: unit bidef) b2a))"



\<comment> \<open>Monotone\<close>
declare [[show_types=false]]
lemma mono_dep_then[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "\<And>y. mono_bd (\<lambda>f. B y f)"
  shows "mono_bd (\<lambda>f. dep_then (A f) (\<lambda>y. B y f) transf)"
  unfolding dep_then_def
  using ma mb
  by pf_mono_prover



\<comment> \<open>NER\<close>
lemma dep_then_is_nonterm[NER_simps]:
  "is_nonterm (parse (dep_then ab a2bb b2a)) i \<longleftrightarrow> is_nonterm (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_nonterm (parse (a2bb r)) l)"
  by (simp add: dep_then_def NER_simps)+

lemma dep_then_is_error[NER_simps]:
  "is_error (parse (dep_then ab a2bb b2a)) i \<longleftrightarrow> is_error (parse ab) i \<or> (\<exists> r l. has_result (parse ab) i r l \<and> is_error (parse (a2bb r)) l)"
  by (simp add: dep_then_def NER_simps)+

lemma dep_then_has_result[NER_simps]:
  "has_result  (parse (dep_then ab a2bb b2a)) i r l \<longleftrightarrow> (\<exists> r' l'. has_result (parse ab) i r' l' \<and> has_result (parse (a2bb r')) l' r l)"
  apply (auto simp add: dep_then_def NER_simps split: sum.splits)
  subgoal by (metis (full_types) old.sum.exhaust old.unit.exhaust)
  using Inl_Inr_False
  by blast

lemma dep_then_has_result_ci[NER_simps]:
  assumes "PNGI (parse ab)"
  assumes "\<And>i r l. has_result (parse ab) i r l \<longrightarrow> PNGI (parse (a2bb r))"
  shows
  "has_result_ci (parse (dep_then ab a2bb b2a)) i c r l \<longleftrightarrow>
    (\<exists> r' c' c''. (c'@c'') = c \<and>
        has_result_ci (parse ab) i c' r' (c''@l) \<and>
        has_result_ci (parse (a2bb r')) (c''@l) c'' r l)"
  unfolding has_result_ci_def has_result_c_def
  apply (auto simp add: NER_simps)
  subgoal for r' l'
    apply (rule exI[of _ r'])
    apply (rule exI[of _ \<open>list_upto (c@l) l'\<close>])
    apply (rule exI[of _ \<open>list_upto l'    l\<close>])
    using list_upto_take_cons
    apply auto
    subgoal by (metis PNGI_def list_upto_take_cons assms(1,2) append_assoc append_same_eq)
    subgoal by (metis PNGI_def list_upto_take_cons assms(1,2))
    subgoal by (metis PNGI_def list_upto_take_cons assms(1,2) append.assoc append_same_eq)
    subgoal by (metis PNGI_def list_upto_take_cons assms(  2))
    done
  subgoal for r' c' c''
    apply (rule exI[of _ r'])
    apply (rule exI[of _ \<open>(c'' @ l)\<close>])
    by blast
  done



\<comment> \<open>FP NER\<close>
lemma dep_then_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (dep_then ab a2bb b2a)) b \<longleftrightarrow> (
        let a = b2a b in p_is_nonterm (print ab) a \<or> (\<not>p_is_error (print ab) a \<and> p_is_nonterm (print (a2bb a)) b))"
  by (simp add: dep_then_def fp_NER)

lemma dep_then_p_is_error[fp_NER]:
  "p_is_error (print (dep_then ab a2bb b2a)) b \<longleftrightarrow> (
        let a = b2a b in p_is_error (print ab) a \<or> (\<not>p_is_nonterm (print ab) a \<and> p_is_error (print (a2bb a)) b))"
  by (simp add: dep_then_def fp_NER)

lemma dep_then_p_has_result[fp_NER]:
  "p_has_result (print (dep_then ab a2bb b2a)) b t \<longleftrightarrow> (
      let a = b2a b in (\<exists> ra rb. ra@rb = t \<and> p_has_result (print ab) a ra \<and> p_has_result (print (a2bb a)) b rb))"
  by (auto simp add: dep_then_def fp_NER Let_def)

lemma dep_then_print_empty[print_empty, fp_NER]:
  "p_has_result (print (dep_then ab a2bb b2a)) i [] \<longleftrightarrow> (
    let a = b2a i in p_has_result (print ab) a [] \<and> p_has_result (print (a2bb a)) i [])"
  by (clarsimp simp add: dep_then_def print_empty)



\<comment> \<open>PNGI, PASI\<close>
lemma dep_then_PNGI:
  assumes "PNGI (parse ab)"
  assumes "\<forall>i. PNGI (parse (a2bb i))"
  shows "PNGI (parse (dep_then ab a2bb b2a))"
  unfolding dep_then_def
  unfolding transform_PNGI[symmetric, of projl Inl]
  apply (rule PNGI_dep_if_then_else_all)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  subgoal by (rule fail_PNGI)
  done

lemma dep_then_PNGI_for_ab_results[PASI_PNGI]:
  assumes "PNGI (parse ab)"
  assumes "\<forall>i r l. has_result (parse ab) i r l \<longrightarrow> PNGI (parse (a2bb r))"
  shows "PNGI (parse (dep_then ab a2bb b2a))"
  unfolding dep_then_def
  unfolding transform_PNGI[symmetric, of projl Inl]
  apply (rule PNGI_dep_if_then_else)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  subgoal by (rule fail_PNGI)
  done

lemma dep_then_PASI:
  assumes "PASI (parse ab)"
  assumes "\<forall>i. PASI (parse (a2bb i))"
  shows "PASI (parse (dep_then ab a2bb b2a))"
  unfolding dep_then_def
  unfolding transform_PASI[symmetric, of projl Inl]
  apply (rule PASI_dep_if_then_else)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  subgoal by (rule fail_PASI)
  done


lemma dep_then_PASI_PASI_PNGI:
  assumes "PASI (parse ab)"
  assumes "\<forall>i. PNGI (parse (a2bb i))"
  shows "PASI (parse (dep_then ab a2bb b2a))"
  unfolding dep_then_def
  unfolding transform_PASI[symmetric, of projl Inl]
  apply (rule dep_if_then_else_PASI_PASI_PNGI_PASI)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  subgoal by (rule fail_PASI)
  done

lemma dep_then_PASI_PNGI_PASI:
  assumes "PNGI (parse ab)"
  assumes "\<forall>i. PASI (parse (a2bb i))"
  shows "PASI (parse (dep_then ab a2bb b2a))"
  unfolding dep_then_def
  unfolding transform_PASI[symmetric, of projl Inl]
  apply (rule dep_if_then_else_PASI_PNGI_PASI_PASI)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  subgoal by (rule fail_PASI)
  done


\<comment> \<open>Does not peek past end\<close>
lemma dep_then_does_not_peek_past_end[peek_past_end_simps]:
  assumes "PNGI (parse A)"
  assumes "\<forall> i r l. has_result (parse A) i r l \<longrightarrow> PNGI (parse (a2B r))"
  assumes "does_not_peek_past_end (parse A)"
  assumes "\<forall> i r l. has_result (parse A) i r l \<longrightarrow> does_not_peek_past_end (parse (a2B r))"
  shows "does_not_peek_past_end (parse (dep_then A a2B b2a))"
  unfolding does_not_peek_past_end_def dep_then_has_result
  apply clarsimp  \<comment> \<open>\<forall> \<rightarrow> \<And> so that we can use the names\<close>
  subgoal for c r l r' l' l''
    apply (rule exI[of _ r'])
  proof -
    assume hr_A: "has_result (parse A) (c @ l) r' l'"
    assume hr_B: "has_result (parse (a2B r')) l' r l"
    obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f3: "c @ l = ccs l' (c @ l) @ l'"
      using hr_A by (meson assms(1)[unfolded PNGI_def])
    obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f4: "l' = ccsa l l' @ l"
      using hr_A hr_B by (meson assms(2)[unfolded PNGI_def])
    then have "has_result (parse A) (c @ l'') r' (ccsa l l' @ l'')"
      using f3 hr_A by (smt (verit, best) append.assoc append_same_eq assms(3) does_not_peek_past_end_def)
    then show "\<exists>cs. has_result (parse A) (c @ l'') r' cs \<and> has_result (parse (a2B r')) cs r l''"
      using f4 hr_B by (metis (no_types) assms(4) does_not_peek_past_end_def)
  qed
  done



\<comment> \<open>First printed char\<close>
lemma dep_then_fpci[fpci_simps]:
  shows "first_printed_chari (print (dep_then A a2B b2a)) i c \<longleftrightarrow>
          (if (p_has_result (print A) (b2a i) []) then
            (first_printed_chari (print (a2B (b2a i))) i c)
          else
            (first_printed_chari (print A) (b2a i) c \<and> (\<exists>t. p_has_result (print (a2B (b2a i))) i t))
)"
  unfolding dep_then_def
  by (simp add: if_then_else_fpci_li_iff transform_fpci2)



\<comment> \<open>Well Formed\<close>

\<comment> \<open>For all two print texts, the parser for ba only consumes its own section.\<close>
definition pa_does_not_eat_into_pb :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> bool" where
  "pa_does_not_eat_into_pb ba a2bb \<longleftrightarrow> (
    \<forall> t1 pr1 t2 pr2. p_has_result (print ba) t1 pr1 \<and> p_has_result (print (a2bb t1)) t2 pr2
        \<longrightarrow> has_result (parse ba) (pr1@pr2) t1 pr2
)"

definition b2_wf_for_all_res_of_b1 :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> bool" where
  "b2_wf_for_all_res_of_b1 b1 a2bi \<longleftrightarrow> (\<forall> i ra la. has_result (parse b1) i ra la \<longrightarrow> bidef_well_formed (a2bi ra))"

\<comment> \<open>This feels very stringent it should be possible to allow it to not be ra, but to be something that then print, parses to ra?\<close>
definition reversed_b2_result_is_b1_result :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
"reversed_b2_result_is_b1_result b1 a2bi b2a \<longleftrightarrow>
                        (\<forall> i ra la. has_result (parse b1) i ra la \<longrightarrow> (
                          \<forall> i2 rb lb. has_result (parse (a2bi ra)) i2 rb lb \<longrightarrow> (
                            b2a rb = ra
)))"

definition well_formed_dep_then_pair :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
  "well_formed_dep_then_pair bi1 a2bi2 b2a \<longleftrightarrow>
                              b2_wf_for_all_res_of_b1 bi1 a2bi2 \<and>
                              reversed_b2_result_is_b1_result bi1 a2bi2 b2a \<and>
                              pa_does_not_eat_into_pb bi1 a2bi2
"


lemma dep_then_well_formed:
  assumes "bidef_well_formed ba"
  assumes "well_formed_dep_then_pair ba a2bb b2a"
  shows "bidef_well_formed (dep_then ba a2bb b2a)"
  apply wf_init
  subgoal using assms(2)[unfolded well_formed_dep_then_pair_def b2_wf_for_all_res_of_b1_def bidef_well_formed_def]
                assms(1)[THEN get_pngi]
                dep_then_PNGI_for_ab_results
    by blast
  subgoal
    using assms
    unfolding bidef_well_formed_def
              parser_can_parse_print_result_def
              well_formed_dep_then_pair_def
              b2_wf_for_all_res_of_b1_def
              pa_does_not_eat_into_pb_def
    unfolding dep_then_has_result(1) dep_then_p_has_result(1)
    by metis
  subgoal
    using assms
    unfolding bidef_well_formed_def
              printer_can_print_parse_result_def
              well_formed_dep_then_pair_def
              b2_wf_for_all_res_of_b1_def
              reversed_b2_result_is_b1_result_def
    unfolding dep_then_p_has_result(1) dep_then_has_result(1)
    by metis
  done



end
