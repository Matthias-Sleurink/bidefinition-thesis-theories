theory derived_separated_by
  imports basic_definitions
          derived_many
          derived_optional
begin

definition separated_byBase :: "'b bd \<Rightarrow> 'a bd \<Rightarrow> ('a \<times> ('b \<times> 'a) list) bd" where
  "separated_byBase sep elem = b_then elem (many (b_then sep elem))"

definition separated_by :: "'b bd \<Rightarrow> 'a bd \<Rightarrow> 'b \<Rightarrow> 'a list bd" where
  "separated_by sep elem sep_oracle =
      transform
         \<comment> \<open>('a \<times> ('b \<times> 'a) list) option \<Rightarrow> 'a list\<close>
        (\<lambda>m_al. case m_al of None \<Rightarrow> [] | Some (a, l) \<Rightarrow> a#(map snd l))
        \<comment> \<open>'a list \<Rightarrow> ('a \<times> ('b \<times> 'a) list) option\<close>
        (\<lambda>l. case l of [] \<Rightarrow> None | (a#as) \<Rightarrow> Some (a, map (Pair sep_oracle) as))
        \<comment> \<open>('a \<times> ('b \<times> 'a) list) option bd\<close>
        (optional (separated_byBase sep elem))
"



definition good_separated_by_oracle :: "'a bidef \<Rightarrow> 'a \<Rightarrow> bool" where
  "good_separated_by_oracle sep oracle \<longleftrightarrow> (\<exists>r. p_has_result (print sep) oracle r)"



\<comment> \<open>NER\<close>
\<comment> \<open>Unsatisfying, should create also sep ~= nonterm, elem ~= nonterm, and both ~= nonterm cases\<close>
lemma separated_by_is_nonterm[NER_simps]:
  "is_nonterm (parse (separated_by sep elem sep_oracle)) i \<longleftrightarrow> 
      (is_nonterm (parse elem) i \<or>
        (\<exists>r l. has_result (parse elem) i r l \<and>
              is_nonterm (parse (many (b_then sep elem))) l))"
  by (simp add: separated_by_def separated_byBase_def NER_simps)

lemma separated_by_is_nonterm_wf[NER_simps]:
  assumes "\<nexists>i'. is_nonterm (parse sep) i'"
  assumes "\<nexists>i'. is_nonterm (parse elem) i'"
  assumes "PASI (parse sep)"
  assumes "PASI (parse elem)"
  shows "is_nonterm (parse (separated_by sep elem sep_oracle)) i \<longleftrightarrow> False"
  using assms
  unfolding separated_by_def separated_byBase_def
  apply (simp add: NER_simps)
  apply (subst many_not_nonterm_when_base_not_nonterm)
  subgoal by (simp add: NER_simps)
  subgoal by (auto simp add: NER_simps then_PASI)
  subgoal by fast
  done


lemma separated_by_is_error[NER_simps]:
  "is_error (parse (separated_by sep elem sep_oracle)) i \<longleftrightarrow> False"
  by (simp add: separated_by_def separated_byBase_def NER_simps)

lemma separated_by_has_result[NER_simps]:
  "has_result (parse (separated_by sep elem sep_oracle)) i r l \<longleftrightarrow> test"
  unfolding separated_by_def separated_byBase_def
  apply (simp add: NER_simps)
  oops

lemma separated_by_has_result_safe_Nil[NER_simps]:
  "has_result (parse (separated_by sep elem sep_oracle)) i [] l \<longleftrightarrow> is_error (parse elem) i \<and> l = i"
  unfolding separated_by_def separated_byBase_def
  by (auto simp add: NER_simps split: option.splits)
  
lemma separated_by_has_result_safe_Cons[NER_simps]:
  "has_result (parse (separated_by sep elem sep_oracle)) i (a#as) l \<longleftrightarrow> (
      \<exists>l'. has_result (parse elem) i a l' \<and>
            ((is_error (parse sep) l' \<and> as = []) \<or>
             (\<exists>l''. has_result (parse sep) l' s l'' \<and> has_result (parse (separated_by sep elem sep_oracle)) l'' as l)
))"
  apply (subst separated_by_def)
  apply (subst separated_byBase_def)
  oops

lemma separated_by_has_result_safe_one[NER_simps]:
  "has_result (parse (separated_by sep elem sep_oracle)) i [r] l \<longleftrightarrow> (
      has_result (parse elem) i r l \<and> is_error (parse (b_then sep elem)) l)"
  unfolding separated_by_def separated_byBase_def
  apply (auto simp add: NER_simps split: option.splits)
  using b_then_is_error many_has_result_when_first_parse_fails
  by blast+



\<comment> \<open>fp_NER\<close>
lemma separated_by_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (separated_by sep elem sep_oracle)) [] \<longleftrightarrow> False"
  "p_is_nonterm (print (separated_by sep elem sep_oracle)) (a#as) \<longleftrightarrow> 
    (p_is_nonterm (print elem) a \<or>
      \<not> p_is_error (print elem) a \<and>
      p_is_nonterm (print (many (b_then sep elem))) (map (Pair sep_oracle) as))"
  unfolding separated_by_def separated_byBase_def
  by (clarsimp simp add: fp_NER)+

lemma separated_by_p_is_nonterm2[fp_NER]:
  assumes "\<not>(p_is_nonterm (print sep ) sep_oracle)"
  assumes "\<not>(\<exists>i \<in> set as. p_is_nonterm (print elem) i)"
  shows "p_is_nonterm (print (separated_by sep elem sep_oracle)) as \<longleftrightarrow> False"
  unfolding separated_by_def separated_byBase_def
  using assms
  by (clarsimp simp add: fp_NER split: list.splits)


lemma separated_by_p_is_error[fp_NER]:
  "p_is_error (print (separated_by sep elem sep_oracle)) [] \<longleftrightarrow> False"
  "p_is_error (print (separated_by sep elem sep_oracle)) (a#as) \<longleftrightarrow> p_is_error (print elem) a \<or>
     \<not> p_is_nonterm (print elem) a \<and> p_is_error (print (many (b_then sep elem))) (map (Pair sep_oracle) as)"
  unfolding separated_by_def separated_byBase_def
  by (clarsimp simp add: fp_NER)+

lemma separated_by_p_is_error2[fp_NER]:
  assumes "\<not>(p_is_error (print sep ) sep_oracle)"
  assumes "\<not>(\<exists>i \<in>set as. p_is_error (print elem) i)"
  shows "p_is_error (print (separated_by sep elem sep_oracle)) as \<longleftrightarrow> False"
  unfolding separated_by_def separated_byBase_def
  using assms
  by (clarsimp simp add: fp_NER split: list.splits)


lemma separated_by_p_has_result[fp_NER]:
  "p_has_result (print (separated_by sep elem sep_oracle)) [] pr \<longleftrightarrow> pr = []"
  "p_has_result (print (separated_by sep elem sep_oracle)) [i] pr \<longleftrightarrow> p_has_result (print elem) i pr"
  "p_has_result (print (separated_by sep elem sep_oracle)) (i#is) pr \<longleftrightarrow> (\<exists>ta tb.
        pr = ta @ tb \<and>
        p_has_result (print elem) i ta \<and>
        p_has_result (print (many (b_then sep elem))) (map (Pair sep_oracle) is) tb)"
  unfolding separated_by_def separated_byBase_def
  apply (clarsimp simp add: fp_NER)+
  by blast

lemma snd_comp_pair_id[simp]:
  "(snd \<circ> Pair a) = id"
  by fastforce

\<comment> \<open>Well formed\<close>
lemma separated_by_well_formed:
  assumes "good_separated_by_oracle sep sep_oracle"
  assumes "pa_does_not_eat_into_pb_nondep elem sep"
  assumes "pa_does_not_eat_into_pb_nondep sep elem"
  assumes "bidef_well_formed elem"
  assumes "bidef_well_formed sep"
  assumes "is_error (parse elem) []"
  assumes "pa_does_not_eat_into_pb_nondep elem (many (b_then sep elem))"
  assumes "parser_can_parse_print_result (parse (many (b_then sep elem))) (print (many (b_then sep elem)))" \<comment> \<open>Would be ideal to get this from WF elem, sep, and more.\<close>
  assumes "parse_result_cannot_be_grown_by_printer (parse (b_then sep elem)) (print (many (b_then sep elem)))"
  assumes "PASI (parse elem) \<or> PASI (parse sep)"
  shows "bidef_well_formed (separated_by sep elem sep_oracle)"
  unfolding separated_by_def
  apply (rule transform_well_formed3)
  defer
  subgoal
    using assms(1,4,6)
    unfolding well_formed_transform_funcs3_def good_separated_by_oracle_def
              bidef_well_formed_def printer_can_print_parse_result_def
              separated_byBase_def
    apply (auto simp add: fp_NER NER_simps split: option.splits)
    subgoal for x i a b xa l'
      unfolding optional_p_has_result(2) b_then_p_has_result
      apply (auto simp add: fp_NER NER_simps split: option.splits)
      apply (induction b arbitrary: i a l')
      subgoal by (auto simp add: fp_NER)
      subgoal
        apply (auto simp add: fp_NER NER_simps split: option.splits)
        unfolding many_p_has_result_safe \<comment> \<open>Inside the Ex auto does not do these, so we force it\<close>
        by (metis b_then_p_has_result(1))
      done
    subgoal for _ t by (cases t; clarsimp; blast)
    subgoal for x t a b ta tb
      apply (cases t; clarsimp) \<comment> \<open>t=[] removed by clarsimp, left: t = a # as\<close>
      subgoal for as
        using assms(7)[unfolded pa_does_not_eat_into_pb_nondep_def,
                       rule_format,
                       of a ta \<open>(map (Pair sep_oracle) as)\<close> tb]
              assms(8)[unfolded parser_can_parse_print_result_def,
                       rule_format,
                       of \<open>(map (Pair sep_oracle) as)\<close> tb]
        apply clarsimp
        apply (rule exI[of _ \<open>[]\<close>])
        apply (rule exI[of _ \<open>Some (a, (map (Pair sep_oracle) as))\<close>])
        by auto
      done
    done
  apply (rule optional_well_formed)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps assms(6))
  unfolding separated_byBase_def
  apply (rule b_then_well_formed)
  subgoal by (rule assms(4))
    defer
  subgoal by (rule assms(7))
  apply (rule well_formed_does_not_grow_by_printer)
    defer defer
  subgoal
    apply (clarsimp simp add: NER_simps assms(6)) \<comment> \<open>number 6 should not be needed here since sep is not []?\<close>
    by (metis assms(8) b_then_is_error many_has_result_safe(1) many_p_has_result_safe(1) parser_can_parse_print_result_simp)
  subgoal
    using assms(10)
          assms(4,5)[THEN get_pngi]
    using then_PASI_from_pasi_pngi then_PASI_from_pngi_pasi by blast
  subgoal by (rule assms(9))
  apply (rule b_then_well_formed)
  subgoal by (rule assms(5))
  subgoal by (rule assms(4))
  subgoal by (rule assms(3))
  done


\<comment> \<open>USE WRAPPER LEMMA BELOW!\<close>
lemma separated_by_well_formed_sub_lemma:
  assumes "good_separated_by_oracle sep sep_oracle"
  assumes "pa_does_not_eat_into_pb_nondep sep elem"
  assumes "bidef_well_formed elem"
  assumes "bidef_well_formed sep"
  assumes "is_error (parse elem) []"
  assumes "pa_does_not_eat_into_pb_nondep elem (many (b_then sep elem))"
  assumes "parse_result_cannot_be_grown_by_printer (parse (b_then sep elem)) (print (many (b_then sep elem)))"
  assumes "bidef_well_formed (b_then sep elem)" \<comment> \<open>can be proven from other requirements. Wrap this lemma in lemma that does that!\<close>
  assumes "is_error (parse (b_then sep elem)) []" \<comment> \<open>Same as above.\<close>
  assumes "PASI (parse elem) \<or> PASI (parse sep)"
  shows "bidef_well_formed (separated_by sep elem sep_oracle)"
  unfolding separated_by_def
  apply (rule transform_well_formed3)
  defer
  subgoal
    using assms(1,3,5)
    unfolding well_formed_transform_funcs3_def
    unfolding good_separated_by_oracle_def
              bidef_well_formed_def printer_can_print_parse_result_def
              separated_byBase_def
    apply (auto simp add: fp_NER NER_simps split: option.splits)
    subgoal for x i a b xa l'
      unfolding optional_p_has_result(2) b_then_p_has_result
      apply (auto simp add: fp_NER NER_simps split: option.splits)
      apply (induction b arbitrary: i a l')
      subgoal by (auto simp add: fp_NER)
      subgoal
        apply (auto simp add: fp_NER NER_simps split: option.splits)
        unfolding many_p_has_result_safe \<comment> \<open>Inside the Ex auto does not do these, so we force it\<close>
        by (metis b_then_p_has_result(1))
      done
    subgoal for _ t by (cases t; clarsimp; blast)
    subgoal for x t a b ta tb
      apply (cases t; clarsimp) \<comment> \<open>t=[] removed by clarsimp, left: t = a # as\<close>
      subgoal for as
        using assms(6)[unfolded pa_does_not_eat_into_pb_nondep_def,
                       rule_format,
                       of a ta \<open>(map (Pair sep_oracle) as)\<close> tb]
        using parser_can_parse_print_result_many[
                      unfolded parser_can_parse_print_result_def, rule_format,
                      of \<open>b_then sep elem\<close> \<open>map (Pair sep_oracle) as\<close> tb,
                      OF assms(7) assms(8) assms(9)]
        apply clarsimp
        apply (rule exI[of _ \<open>[]\<close>])
        apply (rule exI[of _ \<open>Some (a, (map (Pair sep_oracle) as))\<close>])
        by auto
      done
    done
  apply (rule optional_well_formed)
      \<comment> \<open>This rule makes us require \<^term>\<open>is_error (parse (separated_byBase sep elem)) []\<close>\<close>
      \<comment> \<open>This is good, since the empty list printer (prints []) must never be parsed into a nonempty list.\<close>
      \<comment> \<open>So, we need to ensure that the first element in the list cannot be parsed from empty.\<close>
      \<comment> \<open>Since if it could, we could print [] and get back [e]. Which is not allowed by WF.\<close>
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps assms(5))
  unfolding separated_byBase_def
  apply (rule b_then_well_formed)
  subgoal by (rule assms(3))
    defer
  subgoal by (rule assms(6))
  apply (rule well_formed_does_not_grow_by_printer) \<comment> \<open>rule for WF many\<close>
    defer defer
  subgoal by (rule assms(9))
  subgoal
    using assms(10)
          assms(3,4)[THEN get_pngi]
    using then_PASI_from_pasi_pngi then_PASI_from_pngi_pasi by blast
  subgoal by (rule assms(7))
  apply (rule b_then_well_formed)
  subgoal by (rule assms(4))
  subgoal by (rule assms(3))
  subgoal by (rule assms(2))
  done

lemma separated_by_well_formed2:
  assumes "good_separated_by_oracle sep sep_oracle"
  assumes "pa_does_not_eat_into_pb_nondep sep elem"
  assumes "bidef_well_formed elem"
  assumes "bidef_well_formed sep"
  assumes "is_error (parse elem) []"
  assumes "pa_does_not_eat_into_pb_nondep elem (many (b_then sep elem))"
  assumes "parse_result_cannot_be_grown_by_printer (parse (b_then sep elem)) (print (many (b_then sep elem)))"
  assumes "is_error (parse sep) []"
  assumes "PASI (parse elem) \<or> PASI (parse sep)"
  shows "bidef_well_formed (separated_by sep elem sep_oracle)"
  apply (rule separated_by_well_formed_sub_lemma)
  subgoal by (rule assms(1))
  subgoal by (rule assms(2))
  subgoal by (rule assms(3))
  subgoal by (rule assms(4))
  subgoal by (rule assms(5))
  subgoal by (rule assms(6))
  subgoal by (rule assms(7))
  subgoal by (rule b_then_well_formed; rule assms(2, 3, 4))
  subgoal
    apply (rule b_then_is_error[of sep elem \<open>[]\<close>, THEN iffD2])
    by (simp add: assms(5, 8))
  subgoal by (rule assms(9))
  done

lemma cannot_be_grown_to_many:
  assumes "parse_result_cannot_be_grown_by_printer (parse elem) (print sep)"
  assumes "pa_does_not_eat_into_pb_nondep elem (many (b_then sep elem))"
  \<comment> \<open>possibly need that sep will never print [] !! NOTE: this might be constrainable to sep only printing the oracle?\<close>
  shows "parse_result_cannot_be_grown_by_printer (parse (b_then sep elem)) (print (many (b_then sep elem)))"
  using assms
  unfolding parse_result_cannot_be_grown_by_printer_def pa_does_not_eat_into_pb_nondep_def
  apply (auto simp add: b_then_has_result)
  subgoal for i a b l pri prt l'
    apply (rule exI[of _ \<open>l' @ prt\<close>])
    apply auto
     apply (cases prt)
    subgoal \<comment> \<open>prt = []\<close> by fastforce
    subgoal for t ts\<comment> \<open>= prt\<close>
      apply clarsimp
      
      sorry
    \<comment> \<open>Here it would be nice to have something like the charset thing.\<close>
    \<comment> \<open>Basically the idea is that either prt =[] in which case this is trivial\<close>
    \<comment> \<open>Or \<open>hd prt\<close> is not in the set of chars that sep will consume.\<close>

    oops


end
