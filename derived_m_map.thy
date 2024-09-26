theory derived_m_map
  imports basic_definitions
          derived_dep_then
          derived_then \<comment> \<open>for pa_does_not_eat_into_pb_nondep\<close>
begin

fun m_map :: "('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> '\<alpha> list \<Rightarrow> '\<beta> list bidef" where
  "m_map f []     = return []"
| "m_map f (a#as) = ftransform
                        (Some)
                        (\<lambda>[] \<Rightarrow> None
                         |(i#is) \<Rightarrow> Some (i#is))
                        (dep_then (f a) (\<lambda>B. dep_then (m_map f as) (\<lambda>Bs. return (B#Bs)) tl) hd)"
print_theorems \<comment> \<open>Do we want to hide the simps from the simp set?\<close>


lemma mono_m_map[partial_function_mono]:
  assumes ma: "\<And>p. mono_bd (A p)"
  shows "mono_bd (\<lambda>f. m_map (\<lambda>p. A p f) ps)"
  apply (induction ps)
  subgoal unfolding m_map.simps by pf_mono_prover
  subgoal for a ps
    unfolding m_map.simps using ma
    by pf_mono_prover
  done


lemma m_map_is_nonterm[NER_simps]:
  "is_nonterm (parse (m_map tc []    )) i \<longleftrightarrow> False"
  "is_nonterm (parse (m_map tc (a#as))) i \<longleftrightarrow> is_nonterm (parse (tc a)) i \<or>
                            (\<exists> r l. has_result (parse (tc a)) i r l \<and> is_nonterm (parse (m_map tc as)) l)"
  by (clarsimp simp add: NER_simps)+

lemma mmap_not_nonterm_if_param_never_nonterm:
  assumes "\<forall>x s. \<not>is_nonterm (parse (p x)) s"
  shows "\<not>is_nonterm (parse (m_map p l)) s"
  using assms
  by (induction l arbitrary: s) (clarsimp simp add: NER_simps)+

lemma m_map_is_error[NER_simps]:
  "is_error (parse (m_map tc []    )) i \<longleftrightarrow> False"
  "is_error (parse (m_map tc (a#as))) i \<longleftrightarrow> is_error (parse (tc a)) i \<or>
                            (\<exists> r l. has_result (parse (tc a)) i r l \<and> is_error (parse (m_map tc as)) l)"
  by (clarsimp simp add: NER_simps)+

lemma m_map_has_result[NER_simps]:
  "has_result (parse (m_map tc []    )) i r l \<longleftrightarrow> i = l \<and> r = []"
  "has_result (parse (m_map tc (a#as))) i r l \<longleftrightarrow> (\<exists> r' l' rs. has_result (parse (tc a)) i r' l' \<and>
                                                        has_result (parse (m_map tc as)) l' rs l \<and>
                                                        r = r'#rs)"
  by (auto simp add: NER_simps)+

lemma m_map_has_result_same_length:
  "has_result (parse (m_map tc as)) i r l \<Longrightarrow> length as = length r"
  by (induction as arbitrary: i r l) (auto simp add: NER_simps)

lemma m_map_has_result_not_same_length:
  "length as \<noteq> length r \<Longrightarrow> \<not>has_result (parse (m_map tc as)) i r l"
  by (induction as arbitrary: i r l) (auto simp add: NER_simps)



\<comment> \<open>FP_ner\<close>
lemma m_map_p_is_error[fp_NER]:
  "p_is_error (print (m_map bc [])) i \<longleftrightarrow> i \<noteq> []"
  "p_is_error (print (m_map bc (a#as))) i \<longleftrightarrow> (\<exists>i' is ir. i=[] \<or> (i = i'#is \<and>
                                                       (p_is_error (print (bc a)) i' \<or>
                                                        (p_has_result (print (bc a)) i' ir \<and>
                                                         p_is_error (print (m_map bc as)) is))))"
  subgoal by (auto simp add: fp_NER)
  by (induction i; auto simp add: fp_NER Let_def p_has_result_eq_not_is_error)

lemma m_map_p_has_result[fp_NER]:
  "p_has_result (print (m_map bc []))     i t \<longleftrightarrow> i = [] \<and> t = []"
  "p_has_result (print (m_map bc (a#as))) i t \<longleftrightarrow> (\<exists> i' is t' ts . p_has_result (print (bc a)) i' t' \<and>
                                                        p_has_result (print (m_map bc as)) is ts \<and>
                                                        i = i'#is \<and> t = t'@ts)"
  apply (induction i; auto simp add: fp_NER)+
  by fastforce+

lemma m_map_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (m_map bc [])) i \<longleftrightarrow> False"
  "p_is_nonterm (print (m_map bc (a#as))) i \<longleftrightarrow> (\<exists>i' is ir. i = i'#is \<and>
                                                       (p_is_nonterm (print (bc a)) i' \<or>
                                                        (p_has_result (print (bc a)) i' ir \<and>
                                                         p_is_nonterm (print (m_map bc as)) is)))"
  by (induction i; auto simp add: fp_NER p_has_result_eq_not_is_error)+

lemma m_map_p_has_result_same_length:
  "p_has_result (print (m_map bc as)) is t \<Longrightarrow> length as = length is"
  by (induction as arbitrary:  \<open>is\<close> t) (auto simp add: fp_NER Let_def split: list.splits)

lemma m_map_pr_has_result_not_same_length:
  "length as \<noteq> length is \<Longrightarrow> \<not>p_has_result (print (m_map bc as)) is t"
  "length as \<noteq> length is \<Longrightarrow> p_is_error (print (m_map bc as)) is \<or> p_is_nonterm (print (m_map bc as)) is"
  apply (induction as arbitrary: \<open>is\<close> t)
  by (auto simp add: fp_NER Let_def split:list.splits)+
  

lemma m_map_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (m_map a2A []    )) []     [] \<longleftrightarrow> True"
  "p_has_result (print (m_map a2A (a#as))) (i#is) [] \<longleftrightarrow> p_has_result (print (a2A a)) i [] \<and> p_has_result (print (m_map a2A as)) is []"
  by (clarsimp simp add: fp_NER)+

lemma m_map_print_empty:
  "p_has_result (print (m_map a2A as)) is [] \<longleftrightarrow>(
    case as of
      [] \<Rightarrow> is=[]
    | (a#as') \<Rightarrow> (
      case is of [] \<Rightarrow> False | (i#is') \<Rightarrow>
        p_has_result (print (a2A a)) i [] \<and> p_has_result (print (m_map a2A as')) is' []
      ))"
  by (auto simp add: fp_NER split: list.splits)


\<comment> \<open>PNGI, PASI\<close>
lemma PNGI_m_map[PASI_PNGI, PASI_PNGI_intros]:
  assumes "\<forall>e\<in>set l. PNGI (parse (b e))"
  shows "PNGI (parse (m_map b l))"
  using assms
  apply (induction l)
  unfolding PNGI_def
  apply (auto simp add: NER_simps)
  by fastforce

lemma PNGI_m_map_all[PASI_PNGI]:
  assumes "\<And>e. PNGI (parse (b e))"
  shows "PNGI (parse (m_map b l))"
  using assms
  apply (induction l)
  unfolding PNGI_def
  apply (auto simp add: NER_simps)
  by fastforce

lemma PASI_m_map[PASI_PNGI, PASI_PNGI_intros]:
  assumes "\<forall>e\<in>set l. PASI (parse (b e))"
  assumes "l \<noteq> []"
  shows "PASI (parse (m_map b l))"
  using assms
  apply (induction l)
  unfolding PASI_def
  apply (auto simp add: NER_simps)
  by (metis (no_types, lifting) Nil_is_append_conv append.assoc m_map_has_result(1))



\<comment> \<open>Does not peek past end\<close>
lemma m_map_does_not_peek_past_end[peek_past_end_simps]:
  assumes "\<And>a. PNGI (parse (e2b a))"                      \<comment> \<open>TODO: constrain this to a\<in>as?\<close>
  assumes "\<And>a. does_not_peek_past_end (parse (e2b a))"    \<comment> \<open>TODO: constrain this to a\<in>as?\<close>
  shows "does_not_peek_past_end (parse (m_map e2b as))"
  using assms(1, 2) unfolding does_not_peek_past_end_def
  apply (induction as; clarsimp simp add: NER_simps)
  \<comment> \<open>This ISAR proof transplanted from and name-fixed from the sledgehammer generated proof at\<close>
  \<comment> \<open>then_does_not_peek_past_end (which is not in scope here)\<close>
  proof -
    fix a as c l r' l' l'a rs
    assume dnppe_induct: "\<forall>c r. (\<exists>l. has_result (parse (m_map e2b as)) (c @ l) r l) \<longrightarrow> (\<forall>l'. has_result (parse (m_map e2b as)) (c @ l') r l')"
    assume hr_A: "has_result (parse (e2b a)) (c @ l) r' l'"
    assume hr_B: "has_result (parse (m_map e2b as)) l' rs l"
    have f3: "\<forall>cs csa csb csc. (cs::char list) @ csb @ csa \<noteq> csc @ csa \<or> cs @ csb = csc"
      by auto
    obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
       f5: "c @ l = ccsa l' (c @ l) @ l'"
      using hr_A by (meson assms(1)[unfolded PNGI_def])
    obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f4: "l' = ccs l l' @ l"
      using hr_B by (meson PNGI_def PNGI_m_map[of as e2b] assms(1))
    have "\<forall>cs csa. cs @ l \<noteq> csa @ l' \<or> csa @ ccs l l' = cs"
      using f4 f3 by metis
    then have "\<forall>cs. ccsa l' (c @ l) @ ccs l l' @ cs = c @ cs"
      using f5 append_eq_appendI by blast
    then show "\<exists>cs. has_result (parse (e2b a)) (c @ l'a) r' cs \<and> has_result (parse (m_map e2b as)) cs rs l'a"
      using f4 hr_B hr_A dnppe_induct
      by (metis assms(2)[unfolded does_not_peek_past_end_def])
  qed




\<comment> \<open>First printed char\<close>
lemma m_map_fpci_empty[fpci_simps]:
  shows "\<not>first_printed_chari (print (m_map e2A [])) i c"
  unfolding first_printed_chari_def
  using m_map_p_has_result(1)
  by auto

lemma m_map_fpci_cons:
  assumes "first_printed_chari (print (e2A e)) i c"
  assumes "\<exists>ts. p_has_result (print (m_map e2A es)) is ts"
  shows "first_printed_chari (print (m_map e2A (e#es))) (i#is) c"
  using assms m_map_p_has_result unfolding first_printed_chari_def
  by fastforce

lemma m_map_fpci_cons_empty:
  assumes "p_has_result (print (e2A e)) i []"
  assumes "first_printed_chari (print (m_map e2A es)) is c"
  shows "first_printed_chari (print (m_map e2A (e#es))) (i#is) c"
  using assms m_map_p_has_result unfolding first_printed_chari_def
  by auto fastforce
  


lemma m_map_fpci_cons_iff[fpci_simps]:
  shows "first_printed_chari (print (m_map e2A (e#es))) (i#is) c \<longleftrightarrow>(
          if p_has_result (print (e2A e)) i [] then
            (first_printed_chari (print (m_map e2A es)) is c)
          else
            ((\<exists>t. p_has_result (print (m_map e2A es)) is t) \<and> first_printed_chari (print (e2A e)) i c)
)"
  unfolding first_printed_chari_def
  using m_map_p_has_result
  apply auto
      apply (clarsimp simp add: fp_NER Let_def)
  subgoal by (metis append_self_conv2 print_results_always_same)
  subgoal by (clarsimp simp add: fp_NER Let_def) fastforce
  subgoal by (clarsimp simp add: fp_NER)
  subgoal by (clarsimp simp add: fp_NER Let_def) (metis hd_append2)
  subgoal by (clarsimp simp add: fp_NER Let_def) fastforce
  done


\<comment> \<open>FPC\<close>
lemma m_map_fpc_nil[fpc_simps]:
  shows "fpc (parse (m_map a2B [])) i c \<longleftrightarrow> False"
  unfolding fpc_def m_map_has_result
  by clarsimp


\<comment> \<open>well formed\<close>
lemma m_map_well_formed_empty[bi_well_formed_simps]:
  shows "bidef_well_formed (m_map a2bi [])"
  apply wf_init
  unfolding parser_can_parse_print_result_def printer_can_print_parse_result_def
  subgoal by pasi_pngi
  by (auto simp add: fp_NER NER_simps)+

lemma m_map_well_formed_one[bi_well_formed_simps]:
  assumes "bidef_well_formed (a2bi x)"
  shows "bidef_well_formed (m_map a2bi [x])"
  using assms PNGI_m_map
  unfolding bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
            m_map_has_result \<comment> \<open>Due to these being stuck in Ex we cannot unfold normally.\<close>
            m_map_p_has_result
  by (metis list.discI list.set_cases self_append_conv set_ConsD)


lemma return_can_be_ignored:
  assumes "derived_dep_then.pa_does_not_eat_into_pb A (\<lambda>_. B)"
  shows "derived_dep_then.pa_does_not_eat_into_pb A (\<lambda>b. dep_then B (\<lambda>bs. return (b # bs)) tl)"
  using assms unfolding derived_dep_then.pa_does_not_eat_into_pb_def
  by (clarsimp simp add: fp_NER Let_def)

lemma dep_from_nondep:
  assumes "pa_does_not_eat_into_pb_nondep A B"
  shows "derived_dep_then.pa_does_not_eat_into_pb A (\<lambda>_. B)"
  using assms unfolding pa_does_not_eat_into_pb_def pa_does_not_eat_into_pb_nondep_def
  by blast


lemma m_map_well_formed_derived[bi_well_formed_simps]:
  assumes all_wf: "\<forall>i\<in>set is. bidef_well_formed (a2bi i)"
  \<comment> \<open>Not eat into here is not really satisfying but allows users to choose the method themselves.\<close>
  assumes not_eat_into: "\<And>i is. pa_does_not_eat_into_pb_nondep (a2bi i) (derived_m_map.m_map a2bi is)"
  shows "bidef_well_formed (m_map a2bi is)"
  using all_wf
  apply (induction \<open>is\<close>; clarsimp)
  subgoal by (rule b_return_well_formed)
  subgoal for i is'
    apply (rule ftransform_well_formed2)
    subgoal by (auto simp add: well_formed_ftransform_funcs_def NER_simps fp_NER split: list.splits)
    apply (rule dep_then_well_formed)
     defer
    subgoal
      apply (auto simp add: well_formed_dep_then_pair_def)
      subgoal
        apply (auto simp add: b2_wf_for_all_res_of_b1_def)
        apply (rule dep_then_well_formed; assumption?) \<comment> \<open>Induction step here\<close>
        apply (auto simp add: well_formed_dep_then_pair_def)
        subgoal by (clarsimp simp add: b2_wf_for_all_res_of_b1_def b_return_well_formed)
        subgoal by (clarsimp simp add: reversed_b2_result_is_b1_result_def NER_simps)
        subgoal
          apply (clarsimp simp add: pa_does_not_eat_into_pb_def fp_NER)
          using get_parser_can_parse_unfold by blast
        done
      subgoal by (clarsimp simp add: reversed_b2_result_is_b1_result_def NER_simps)
      apply (rule return_can_be_ignored)
      apply (rule dep_from_nondep)
      using not_eat_into by blast
    subgoal by blast
    done
  done



end
