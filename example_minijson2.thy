theory example_minijson2
  imports all_definitions
begin


datatype MJ
  = J nat
  | RJ MJ

abbreviation "E_chr \<equiv> CHR ''E''"

definition MJ_J :: "MJ bd" where
  "MJ_J = ftransform
              (\<lambda>l. Some (J (length l)))
              (\<lambda>J n \<Rightarrow> Some (replicate n E_chr)
               |RJ a \<Rightarrow> None)
              (separated_by (ws_char_ws CHR '','')  (this_char E_chr) ())"

lemma mono_MJ_J[partial_function_mono]:
  shows "mono_bd (\<lambda>f. MJ_J)"
  by pf_mono_prover

lemma MJ_J_is_error[NER_simps]:
  "is_error (parse MJ_J) i \<longleftrightarrow> False"
  by (clarsimp simp add: NER_simps MJ_J_def)
lemma MJ_J_is_nonterm[NER_simps]:
  "is_nonterm (parse MJ_J) i \<longleftrightarrow> False"
  apply (clarsimp simp add: NER_simps MJ_J_def)
  using many_not_nonterm_when_base_not_nonterm[OF _ then_PASI[OF ws_char_ws_PASI this_char_PASI]]
        b_then_is_nonterm this_char_is_nonterm ws_char_ws_is_nonterm
  by blast

\<comment> \<open>Note sure if this is all that good.\<close>
lemma MJ_J_p_has_result[fp_NER]:
  "p_has_result (print MJ_J) i r \<longleftrightarrow> (case i of
        RJ _ \<Rightarrow> False
      | J n \<Rightarrow> (if n = 0 then r = [] else
                (if n = 1 then r = [E_chr] else
                  (\<exists>r'. p_has_result (print (many (b_then (ws_char_ws CHR '','') (this_char E_chr)))) (replicate (n-1) ((), E_chr)) r' \<and> r = E_chr # r'))))"
  apply (cases i; clarsimp)
  subgoal for n
    apply auto
    subgoal by (clarsimp simp add: fp_NER MJ_J_def)
    subgoal by (clarsimp simp add: fp_NER MJ_J_def)
    subgoal by (clarsimp simp add: fp_NER MJ_J_def)
    subgoal by (clarsimp simp add: fp_NER MJ_J_def)
    subgoal
      apply (clarsimp simp add: MJ_J_def fp_NER)
      apply (cases n; clarsimp)
      by (clarsimp simp add: fp_NER)
    subgoal for r'
      apply (clarsimp simp add: MJ_J_def fp_NER)
      by (cases n; clarsimp simp add: fp_NER)
    done
  subgoal by (clarsimp simp add: MJ_J_def fp_NER)
  done

lemma MJ_J_p_is_error[fp_NER]:
  "p_is_error (print MJ_J) i \<longleftrightarrow> (case i of RJ _ \<Rightarrow> True | J _ \<Rightarrow> False)"
  by (clarsimp simp add: fp_NER MJ_J_def split: MJ.splits)
lemma MJ_J_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print MJ_J) i \<longleftrightarrow> False"
  by (clarsimp simp add: fp_NER MJ_J_def)

lemma MJ_J_result_head:
  "has_result (parse MJ_J) (c @ l) r l \<Longrightarrow> case c of [] \<Rightarrow> True | (c'#cs) \<Rightarrow> c' = E_chr"
  apply (clarsimp simp add: MJ_J_def NER_simps split: list.splits)
  subgoal for r' by (cases r'; clarsimp simp add: NER_simps)
  done


thm separated_by_result_when_elem_result_always_same
lemma MJ_j_wf:
  "bidef_well_formed MJ_J"
  unfolding MJ_J_def
  apply (rule ftransform_well_formed2)
  subgoal
    apply (auto simp add: well_formed_ftransform_funcs_def)
    subgoal for i r l
      apply (rule separated_by_result_when_elem_result_always_same[of \<open>ws_char_ws CHR '',''\<close> \<open>this_char E_chr\<close> E_chr \<open>()\<close> \<open>()\<close> i r l]; clarsimp?)
      subgoal by pasi_pngi
      subgoal by (clarsimp simp add: NER_simps)
      done
    subgoal by (clarsimp simp add: fp_NER split: MJ.splits)
    done
  apply (rule separated_by_well_formed2)
  subgoal by (clarsimp simp add: good_separated_by_oracle_def fp_NER)
  subgoal
    apply (rule first_printed_does_not_eat_into3; clarsimp?)
    subgoal by (rule ws_char_ws_well_formed; clarsimp)
    subgoal for i c
      apply (clarsimp simp add: fpci_simps)
      using ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> E_chr, simplified]
      by blast
    done
  subgoal by (rule this_char_well_formed)
  subgoal by (rule ws_char_ws_well_formed; clarsimp)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal
    apply (rule does_not_peek_past_end_implies_does_not_eat_into)
    subgoal by (rule this_char_does_not_peek_past_end)
    subgoal by (rule this_char_well_formed)
    done
  subgoal
    apply (rule cannot_be_grown_by_when_no_peek_past)
    subgoal
      apply (rule then_does_not_peek_past_end_from_fpc; clarsimp?)
      subgoal for i c
        apply (clarsimp simp add: fpc_simps)
        using ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> E_chr, simplified]
        by blast
      subgoal for ca l b
        using this_char_PASI[of E_chr, unfolded PASI_def, rule_format, of l b l]
        by blast
      subgoal by pasi_pngi
      subgoal by (rule this_char_does_not_peek_past_end)
      subgoal by pasi_pngi
      done
    subgoal
      apply (rule b_then_well_formed)
      subgoal by (rule ws_char_ws_well_formed; clarsimp)
      subgoal by (rule this_char_well_formed)
      subgoal
        apply (rule first_printed_does_not_eat_into3; clarsimp?)
        subgoal by (rule ws_char_ws_well_formed; clarsimp)
        subgoal for i c
          apply (clarsimp simp add: fpci_simps)
          using ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> E_chr, simplified]
          by blast
        done
      done
    done
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by pasi_pngi
  done


definition MJ_RJ :: "MJ bd \<Rightarrow> MJ bd" where
  "MJ_RJ I = ftransform
                (\<lambda>pr. Some (RJ pr))
                (\<lambda>J n \<Rightarrow> None
                 | RJ i \<Rightarrow> Some i)
                (takeMiddle (this_char CHR ''['') (I) (this_char CHR '']'') (CHR ''['') (CHR '']''))"

lemma mono_MJ_RJ[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. MJ_RJ (A f))"
  unfolding MJ_RJ_def using ma
  by pf_mono_prover

lemma MJ_RJ_p_has_result[fp_NER]:
  "p_has_result (print (MJ_RJ I)) i r \<longleftrightarrow> (case i of J _ \<Rightarrow> False | RJ i' \<Rightarrow> \<exists>r'. p_has_result (print I) i' r' \<and> r = CHR ''['' # r' @ [CHR '']''])"
  by (auto simp add: fp_NER MJ_RJ_def takeMiddle_def split: MJ.splits)

lemma MJ_RJ_is_error[NER_simps]:
  "is_error (parse (MJ_RJ I)) []"
  "is_error (parse (MJ_RJ I)) (E_chr # cs)"
  "is_error (parse (MJ_RJ I)) (CHR '']'' # cs)"
  by (clarsimp simp add: NER_simps MJ_RJ_def takeMiddle_def)+


partial_function (bd) MJ_bd_R :: "unit \<Rightarrow> MJ bd" where
  "MJ_bd_R _ = transform
                (sum_take)
                (\<lambda>J n \<Rightarrow> (Inr (J n))
                 | RJ i \<Rightarrow> (Inl (RJ i)))
                (or
                    (MJ_RJ (MJ_bd_R ()))
                     MJ_J)"
print_theorems

abbreviation "MJ_bd \<equiv> MJ_bd_R ()"

lemma test_flat:
  "has_result (parse MJ_bd) ''EE'' (J 2) []"
  "p_has_result (print MJ_bd) (J 2) ''EE'' "
  subgoal
    apply (subst MJ_bd_R.simps)
    by (clarsimp simp add: NER_simps MJ_RJ_def takeMiddle_def MJ_J_def this_char_def any_from_set_def split: sum.splits)
  subgoal
    apply (subst MJ_bd_R.simps)
    by (clarsimp simp add: fp_NER MJ_J_def this_char_def any_from_set_def numeral_2_eq_2)
  done

lemma tests_deeper:
  "has_result (parse MJ_bd) ''[EE]'' (RJ (J 2)) []"
  "p_has_result (print MJ_bd) (RJ (J 2)) ''[EE]''"
  subgoal
    apply (subst MJ_bd_R.simps)
    apply (clarsimp simp add: NER_simps MJ_RJ_def takeMiddle_def MJ_J_def this_char_def any_from_set_def split: sum.splits)
    apply (subst MJ_bd_R.simps)
    by (clarsimp simp add: NER_simps MJ_RJ_def takeMiddle_def MJ_J_def this_char_def any_from_set_def split: sum.splits)
  subgoal
    apply (subst MJ_bd_R.simps)
    apply (clarsimp simp add: fp_NER MJ_RJ_def takeMiddle_def MJ_J_def)
    apply (subst MJ_bd_R.simps)
    by (clarsimp simp add: fp_NER MJ_J_def this_char_def any_from_set_def numeral_2_eq_2)
  done

\<comment> \<open>So now we try to use the same technique for getting WF to see if there is a fundamental problem or not.\<close>
lemma wf_MJ:
  "bidef_well_formed MJ_bd
   \<and> (does_not_consume_past_char3 (parse MJ_bd) CHR '']'') \<comment> \<open>Needed as assm in the WF proof.\<close>
"
  apply (induction rule: MJ_bd_R.fixp_induct)
  subgoal by clarsimp
  subgoal using strict_WF bottom_no_consume_past_char3 by auto
  subgoal for I
    apply (repeat_new \<open>rule conjI\<close>) \<comment> \<open>Split all the mutual-recursion conjunctions.\<close>
    subgoal \<comment> \<open>WF\<close>
      apply (rule transform_well_formed4)
      subgoal
        apply (auto simp add: well_formed_transform_funcs4_def NER_simps fp_NER MJ_RJ_def takeMiddle_def split: sum.splits MJ.splits)
        subgoal by (metis MJ.distinct(1) sum_take.elims)
        subgoal by (metis sum_take.elims)
        done
      apply (rule or_well_formed2)
      subgoal by (auto simp add: well_formed_or_pair_def fp_NER NER_simps MJ_RJ_def takeMiddle_def split: MJ.splits)
       defer
      subgoal by (rule MJ_j_wf)
      unfolding MJ_RJ_def
      apply (rule ftransform_well_formed2)
      subgoal by (auto simp add: well_formed_ftransform_funcs_def fp_NER NER_simps takeMiddle_def split: MJ.splits)
      unfolding takeMiddle_def
      apply (rule transform_well_formed4)
      subgoal by (clarsimp simp add: well_formed_transform_funcs4_def NER_simps)
      apply (rule b_then_well_formed_does_not_peek_past)
      subgoal by (rule this_char_well_formed)
       defer
      subgoal by (rule this_char_does_not_peek_past_end)
      apply (rule b_then_well_formed)
      subgoal by clarsimp \<comment> \<open>WF I\<close>
      subgoal by (rule this_char_well_formed)
      apply (rule first_printed_does_not_eat_into3)
      subgoal by clarsimp \<comment> \<open>WF I\<close>
      by (clarsimp simp add: fpci_simps)
    subgoal \<comment> \<open>Does not consume past closing bracket\<close>
      apply (rule transform_does_not_consume_past_char3)
      apply (rule or_no_consume_past_char)
      subgoal \<comment> \<open>does_not_consume_past_char3 (parse (MJ_RJ (I ()))) CHR '']''\<close>
        unfolding MJ_RJ_def
        apply (rule ftransform_does_not_consume_past_char3)
        unfolding takeMiddle_def
        apply (rule transform_does_not_consume_past_char3)
        apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
        subgoal by (rule this_char_does_not_peek_past_end)
        subgoal by pasi_pngi
         defer \<comment> \<open>does_not_consume_past_char3 (parse (b_then (I ()) (this_char CHR '']''))) CHR '']''\<close>
        subgoal using get_pngi by pasi_pngi
        apply (rule then_does_not_consume_past3)
        subgoal by clarsimp
        subgoal by (rule this_char_well_formed)
        subgoal by (rule this_char_does_not_consume_past_char3)
        subgoal by (clarsimp simp add: fpc_simps)
        subgoal by (clarsimp simp add: NER_simps)
        done
      subgoal \<comment> \<open>does_not_consume_past_char3 (parse MJ_J) CHR '']''\<close>
        unfolding MJ_J_def
        apply (rule ftransform_does_not_consume_past_char3)
        unfolding this_char_def any_from_set_def
        apply (rule many_char_for_predicate_does_not_consume_past_char3[THEN iffD2])
        by clarsimp
      subgoal for c l r
        apply (insert MJ_J_result_head[of c l r]; cases c; clarsimp)
        subgoal by (rule MJ_RJ_is_error)
        subgoal by (rule MJ_RJ_is_error)
        done
      subgoal for c l l' r
        apply (cases c; clarsimp simp add: MJ_RJ_is_error)
        subgoal for c' cs
          by (insert MJ_J_result_head[of \<open>c'#cs\<close> l r]; clarsimp simp add: MJ_RJ_is_error)
        done
      done
    done
  done


thm bd.fixp_strong_induct_uc


lemma wf_MJ_strong_induct:
  "bidef_well_formed MJ_bd
   \<and> (does_not_consume_past_char3 (parse MJ_bd) CHR '']'') \<comment> \<open>Needed as assm in the WF proof.\<close>
"
  using bd.fixp_strong_induct_uc[OF ]
        MJ_bd_R.mono
  oops
  find_theorems case_prod
  thm bd.fixp_strong_induct_uc
  thm bd.fixp_strong_induct_uc[where P = \<open>\<lambda>inner. bidef_well_formed (inner ()) \<and> (does_not_consume_past_char3 (parse (inner ())) CHR '']'')\<close>
      ,where f = \<open>MJ_bd_R\<close>]
        MJ_bd_R_def
        MJ_bd_R.fixp_induct
        MJ_bd_R.mono
  thm MJ_bd_R.fixp_induct



lemma use_le_fun:
  assumes le: "bd.le_fun I I'"
  shows "False"
  apply (insert le)
  unfolding bd_ord_def fun_ord_def flat_ord_def
  
  oops


lemma use_le_fun:
  assumes "bd.le_fun I I'"
  shows "\<not>is_nonterm (parse (I ())) i \<Longrightarrow> \<not>is_nonterm (parse (I' ())) i"
  using assms unfolding is_nonterm_def bd_ord_def fun_ord_def flat_ord_def
  apply auto
  by (metis option.distinct(1))

find_theorems bd.le_fun

end