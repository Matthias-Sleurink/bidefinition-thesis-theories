theory derived_seperatedby
  imports basic_definitions
          derived_many
          derived_optional
begin

definition seperatedByBase :: "'b bd \<Rightarrow> 'a bd \<Rightarrow> ('a \<times> ('b \<times> 'a) list) bd" where
  "seperatedByBase sep elem = b_then elem (many (b_then sep elem))"

definition seperatedBy :: "'b bd \<Rightarrow> 'a bd \<Rightarrow> 'b \<Rightarrow> 'a list bd" where
  "seperatedBy sep elem sep_oracle =
      transform
         \<comment> \<open>('a \<times> ('b \<times> 'a) list) option \<Rightarrow> 'a list\<close>
        (\<lambda>m_al. case m_al of None \<Rightarrow> [] | Some (a, l) \<Rightarrow> a#(map snd l))
        \<comment> \<open>'a list \<Rightarrow> ('a \<times> ('b \<times> 'a) list) option\<close>
        (\<lambda>l. case l of [] \<Rightarrow> None | (a#as) \<Rightarrow> Some (a, map (Pair sep_oracle) as))
        \<comment> \<open>('a \<times> ('b \<times> 'a) list) option bd\<close>
        (optional (seperatedByBase sep elem))
"



definition good_seperatedBy_oracle :: "'a bidef \<Rightarrow> 'a \<Rightarrow> bool" where
  "good_seperatedBy_oracle sep oracle \<longleftrightarrow> (\<exists>r. p_has_result (print sep) oracle r)"



\<comment> \<open>NER\<close>
\<comment> \<open>Unsatisfying, should create also sep ~= nonterm, elem ~= nonterm, and both ~= nonterm cases\<close>
lemma seperatedBy_is_nonterm[NER_simps]:
  "is_nonterm (parse (seperatedBy sep elem sep_oracle)) i \<longleftrightarrow> 
      (is_nonterm (parse elem) i \<or>
        (\<exists>r l. has_result (parse elem) i r l \<and>
              is_nonterm (parse (many (b_then sep elem))) l))"
  by (simp add: seperatedBy_def seperatedByBase_def NER_simps)

lemma seperatedBy_is_nonterm_wf[NER_simps]:
  assumes "\<nexists>i'. is_nonterm (parse sep) i'"
  assumes "\<nexists>i'. is_nonterm (parse elem) i'"
  assumes "PASI (parse sep)"
  assumes "PASI (parse elem)"
  shows "is_nonterm (parse (seperatedBy sep elem sep_oracle)) i \<longleftrightarrow> False"
  using assms
  unfolding seperatedBy_def seperatedByBase_def
  apply (simp add: NER_simps)
  apply (subst many_not_nonterm_when_base_not_nonterm)
  subgoal by (simp add: NER_simps)
  subgoal by (auto simp add: NER_simps then_PASI)
  subgoal by fast
  done


lemma seperatedBy_is_error[NER_simps]:
  "is_error (parse (seperatedBy sep elem sep_oracle)) i \<longleftrightarrow> False"
  by (simp add: seperatedBy_def seperatedByBase_def NER_simps)

lemma seperatedBy_has_result[NER_simps]:
  "has_result (parse (seperatedBy sep elem sep_oracle)) i r l \<longleftrightarrow> test"
  unfolding seperatedBy_def seperatedByBase_def
  apply (simp add: NER_simps)
  oops

lemma seperatedBy_has_result_safe_Nil[NER_simps]:
  "has_result (parse (seperatedBy sep elem sep_oracle)) i [] l \<longleftrightarrow> is_error (parse elem) i \<and> l = i"
  unfolding seperatedBy_def seperatedByBase_def
  by (auto simp add: NER_simps split: option.splits)
  
lemma seperatedBy_has_result_safe_Cons[NER_simps]:
  "has_result (parse (seperatedBy sep elem sep_oracle)) i (a#as) l \<longleftrightarrow> (
      \<exists>l'. has_result (parse elem) i a l' \<and>
            ((is_error (parse sep) l' \<and> as = []) \<or>
             (\<exists>l''. has_result (parse sep) l' s l'' \<and> has_result (parse (seperatedBy sep elem sep_oracle)) l'' as l)
))"
  apply (subst seperatedBy_def)
  apply (subst seperatedByBase_def)
  oops


\<comment> \<open>fp_NER\<close>
lemma seperatedBy_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (seperatedBy sep elem sep_oracle)) [] \<longleftrightarrow> False"
  "p_is_nonterm (print (seperatedBy sep elem sep_oracle)) (a#as) \<longleftrightarrow> 
    (p_is_nonterm (print elem) a \<or>
      \<not> p_is_error (print elem) a \<and>
      p_is_nonterm (print (many (b_then sep elem))) (map (Pair sep_oracle) as))"
  unfolding seperatedBy_def seperatedByBase_def
  by (clarsimp simp add: fp_NER)+

lemma seperatedBy_p_is_nonterm2[fp_NER]:
  assumes "\<not>(p_is_nonterm (print sep ) sep_oracle)"
  assumes "\<not>(\<exists>i \<in> set as. p_is_nonterm (print elem) i)"
  shows "p_is_nonterm (print (seperatedBy sep elem sep_oracle)) as \<longleftrightarrow> False"
  unfolding seperatedBy_def seperatedByBase_def
  using assms
  by (clarsimp simp add: fp_NER split: list.splits)


lemma seperatedBy_p_is_error[fp_NER]:
  "p_is_error (print (seperatedBy sep elem sep_oracle)) [] \<longleftrightarrow> False"
  "p_is_error (print (seperatedBy sep elem sep_oracle)) (a#as) \<longleftrightarrow> p_is_error (print elem) a \<or>
     \<not> p_is_nonterm (print elem) a \<and> p_is_error (print (many (b_then sep elem))) (map (Pair sep_oracle) as)"
  unfolding seperatedBy_def seperatedByBase_def
  by (clarsimp simp add: fp_NER)+

lemma seperatedBy_p_is_error2[fp_NER]:
  assumes "\<not>(p_is_error (print sep ) sep_oracle)"
  assumes "\<not>(\<exists>i \<in>set as. p_is_error (print elem) i)"
  shows "p_is_error (print (seperatedBy sep elem sep_oracle)) as \<longleftrightarrow> False"
  unfolding seperatedBy_def seperatedByBase_def
  using assms
  by (clarsimp simp add: fp_NER split: list.splits)


lemma seperatedBy_p_has_result[fp_NER]:
  "p_has_result (print (seperatedBy sep elem sep_oracle)) [] pr \<longleftrightarrow> pr = []"
  "p_has_result (print (seperatedBy sep elem sep_oracle)) [i] pr \<longleftrightarrow> p_has_result (print elem) i pr"
  "p_has_result (print (seperatedBy sep elem sep_oracle)) (i#is) pr \<longleftrightarrow> (\<exists>ta tb.
        pr = ta @ tb \<and>
        p_has_result (print elem) i ta \<and>
        p_has_result (print (many (b_then sep elem))) (map (Pair sep_oracle) is) tb)"
  unfolding seperatedBy_def seperatedByBase_def
  apply (clarsimp simp add: fp_NER)+
  by blast

lemma snd_comp_pair_id[simp]:
  "(snd \<circ> Pair a) = id"
  by fastforce

\<comment> \<open>Well formed\<close>
lemma seperatedBy_well_formed:
  assumes "good_seperatedBy_oracle sep sep_oracle"
  assumes "pa_does_not_eat_into_pb_nondep elem sep"
  assumes "pa_does_not_eat_into_pb_nondep sep elem"
  assumes "bidef_well_formed elem"
  assumes "bidef_well_formed sep"
  assumes "is_error (parse elem) []"
  assumes "pa_does_not_eat_into_pb_nondep elem (many (b_then sep elem))"
  assumes "parser_can_parse_print_result (parse (many (b_then sep elem))) (print (many (b_then sep elem)))" \<comment> \<open>Would be ideal to get this from WF elem, sep, and more.\<close>
  shows "bidef_well_formed (seperatedBy sep elem sep_oracle)"
  unfolding seperatedBy_def
  apply (rule transform_well_formed3)
  defer
  subgoal
    using assms(1,4,5,6)
    unfolding well_formed_transform_funcs3_def good_seperatedBy_oracle_def
              bidef_well_formed_def printer_can_print_parse_result_def
              seperatedByBase_def
    apply (auto simp add: fp_NER NER_simps split: option.splits)
    subgoal for x i a b xa l'
      unfolding optional_p_has_result(2) b_then_p_has_result
      apply (auto simp add: fp_NER NER_simps split: option.splits)
      apply (induction b arbitrary: x i a xa l')
      subgoal by (auto simp add: fp_NER)
      subgoal
        apply (auto simp add: fp_NER NER_simps split: option.splits)
        unfolding many_p_has_result_safe \<comment> \<open>Inside the Ex auto does not do these, so we force it\<close>
        by (metis b_then_p_has_result(1))
      done
    subgoal for _ t by (cases t; clarsimp; blast)
    subgoal for x t a b ta tb
      apply (cases t; clarsimp) \<comment> \<open>t = a # as\<close>
      subgoal for as
        using assms(7)[unfolded pa_does_not_eat_into_pb_nondep_def,
                       rule_format,
                       of a ta \<open>(map (Pair sep_oracle) as)\<close> tb]
        apply clarsimp
        using assms(8)[unfolded parser_can_parse_print_result_def,
                       rule_format,
                       of \<open>(map (Pair sep_oracle) as)\<close> tb]
        apply clarsimp
        apply (rule exI[of _ \<open>[]\<close>])
        apply (rule exI[of _ \<open>Some (a, (map (Pair sep_oracle) as))\<close>])
        by auto
      done
    done
  apply (rule optional_well_formed)
  subgoal by (clarsimp simp add: seperatedByBase_def NER_simps assms(6))
  unfolding seperatedByBase_def
  apply (rule b_then_well_formed)
  subgoal by (rule assms(4))
    defer
  subgoal by (rule assms(7))
  apply (rule well_formed_does_not_grow_by_printer)
    defer defer
  subgoal
    apply (clarsimp simp add: NER_simps assms(6))
    by (metis assms(8) b_then_is_error many_has_result_safe(1) many_p_has_result_safe(1) parser_can_parse_print_result_simp)
  subgoal 
    unfolding parse_result_cannot_be_grown_by_printer_def
    apply (clarsimp simp add: NER_simps assms(6))
    sorry \<comment> \<open>SORRY HERE, TODO!\<close>
  apply (rule b_then_well_formed)
  subgoal by (rule assms(5))
  subgoal by (rule assms(4))
  subgoal by (rule assms(3))
  oops
end
