theory derived_dep_then
  imports basic_definitions
begin

definition dep_then :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<beta> bidef" where
  "dep_then ab a2bb b2a = (transform projl Inl (if_then_else ab a2bb (fail :: unit bidef) b2a))"



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



\<comment> \<open>FP NER\<close>
lemma dep_then_p_is_error[fp_NER]:
  "p_is_error (print (dep_then ab a2bb b2a)) b \<longleftrightarrow> (
        let a = b2a b in p_is_error (print ab) a \<or> p_is_error (print (a2bb a)) b)"
  by (simp add: dep_then_def fp_NER)

lemma dep_then_p_has_result[fp_NER]:
  "p_has_result (print (dep_then ab a2bb b2a)) b t \<longleftrightarrow> (
      let a = b2a b in (\<exists> ra rb. ra@rb = t \<and> p_has_result (print ab) a ra \<and> p_has_result (print (a2bb a)) b rb))"
  by (auto simp add: dep_then_def fp_NER Let_def)



\<comment> \<open>PNGI, PASI\<close>
lemma dep_then_PNGI:
  assumes "PNGI (parse ab)"
  assumes "\<forall>i. PNGI (parse (a2bb i))"
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