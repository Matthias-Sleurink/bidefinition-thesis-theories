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



\<comment> \<open>Well Formed\<close>
definition appended_results_must_be_parsable :: "'\<alpha> bidef \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
  "appended_results_must_be_parsable b1 a2b2 b2a \<longleftrightarrow>
          (\<forall> v1 v2 pr1 pr2 a.
            (p_has_result (print b1) v1 pr1 \<and> p_has_result (print (a2b2 a)) v2 pr2) \<longrightarrow>
               (\<exists>l1 l2. has_result (parse b1) (pr1@pr2) v1 l1 \<and> has_result (parse (a2b2 a)) l1 v2 l2)
)
"
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
                              appended_results_must_be_parsable bi1 a2bi2 b2a
"

lemma dep_then_well_formed:
  assumes "bidef_well_formed ba"
  assumes "well_formed_dep_then_pair ba a2bb b2a"
  shows "bidef_well_formed (dep_then ba a2bb b2a)"
  apply wf_init
  subgoal
    using assms
    unfolding bidef_well_formed_def
              well_formed_dep_then_pair_def
              appended_results_must_be_parsable_def
              parser_can_parse_print_result_def
    unfolding dep_then_has_result(1) dep_then_p_has_result(1)
    by metis
  subgoal
    using assms
    unfolding bidef_well_formed_def
              well_formed_dep_then_pair_def
              b2_wf_for_all_res_of_b1_def
              reversed_b2_result_is_b1_result_def
              printer_can_print_parse_result_def
    unfolding dep_then_p_has_result(1) dep_then_has_result(1)
    by metis
  done



end