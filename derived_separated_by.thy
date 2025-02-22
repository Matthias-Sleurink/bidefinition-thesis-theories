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
lemma mono_separated_by[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "mono_bd B"
  shows "mono_bd (\<lambda>f. separated_by (A f) (B f) b)"
  unfolding separated_by_def separated_byBase_def using ma mb
  by pf_mono_prover




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
      \<exists>l'. has_result (parse elem) i a l' \<and> (\<exists>ss. length ss = length as \<and> has_result (parse (many (b_then sep elem))) l' (zip ss as) l))"
  apply (subst separated_by_def)
  apply (subst separated_byBase_def)
  apply (auto simp add: NER_simps split: option.splits)
  subgoal for rs l'
    apply (rule exI[of _ l'])
    apply clarsimp
    apply (rule exI[of _ \<open>map fst rs\<close>])
    by (clarsimp simp add: zip_map_fst_snd)
  subgoal for l' seps
    apply (rule exI[of _ \<open>Some (a, zip seps as)\<close>])
    by fastforce
  done

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

lemma separated_by_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (separated_by sep elem sep_oracle)) []     [] \<longleftrightarrow> True"
  "p_has_result (print (separated_by sep elem sep_oracle)) [i]    [] \<longleftrightarrow> p_has_result (print elem) i []"
  "p_has_result (print (separated_by sep elem sep_oracle)) (i#is) [] \<longleftrightarrow> (
        p_has_result (print elem) i [] \<and>
        p_has_result (print (many (b_then sep elem))) (map (Pair sep_oracle) is) [])"
  by (clarsimp simp add: fp_NER)+

lemma separated_by_print_empty:
  "p_has_result (print (separated_by sep elem sep_oracle)) i' [] \<longleftrightarrow> (
    case i' of [] \<Rightarrow> True
    | (i#is) \<Rightarrow>
        p_has_result (print elem) i [] \<and>
        p_has_result (print (many (b_then sep elem))) (map (Pair sep_oracle) is) [])"
  by (clarsimp simp add: print_empty split: list.splits)+

lemma replicate_tuples:
  assumes "length Es1 = length Es2"
  assumes "replicate (length Es2) (E1, E2) = zip Es1 Es2"
  shows "replicate (length Es2) E1 = Es1 \<and> replicate (length Es2) E2 = Es2"
  using assms
  apply (induction Es1 arbitrary: Es2)
  subgoal by clarsimp
  apply auto
  subgoal by (metis (no_types, lifting) length_Cons length_replicate length_zip map_fst_zip zip_replicate)
  subgoal by (metis (no_types, lifting) length_Cons length_replicate length_zip map_snd_zip zip_replicate)
  done

lemma separated_by_result_when_elem_result_always_same:
  assumes SE_pasi: "PASI (parse (b_then S E))"
  assumes E_rs_eq: "\<And> i r l. has_result (parse E) i r l \<Longrightarrow> r = E_r"
  assumes S_rs_eq: "\<And> i r l. has_result (parse S) i r l \<Longrightarrow> r = S_r"
  shows "has_result (parse (separated_by S E S_oracle)) i r l \<Longrightarrow> replicate (length r) E_r = r"
  apply (cases r; clarsimp simp add: NER_simps)
  subgoal for r' rs lE rsMS
    apply (rule conjI)
    subgoal using E_rs_eq[of i r' lE] by blast
    using many_has_result_when_result_always_same[OF SE_pasi, of \<open>(S_r, E_r)\<close> lE \<open>(zip rsMS rs)\<close> l]
    using then_result_always_same[of E E_r S S_r]
    using S_rs_eq E_rs_eq
    apply clarsimp
    using replicate_tuples[of rsMS rs S_r r'] by fastforce
  done

\<comment> \<open>PASI, PNGI\<close>
lemma separated_by_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  assumes PNGI_elem: "PNGI (parse elem)"
  assumes PASI_then: "PASI (parse (b_then sep elem))"
  shows "PNGI (parse (separated_by sep elem sep_oracle))"
  unfolding separated_by_def separated_byBase_def
  by (auto intro!: optional_PNGI then_PNGI
      intro: many_PNGI
      simp add: PNGI_elem PASI_then transform_PNGI[symmetric])



\<comment> \<open>Does not peek past end\<close>
lemma separated_by_does_peek_past_end[peek_past_end_simps]:
  assumes "\<exists> i r l. has_result (parse elem) i r l \<and> is_error (parse sep) l"
  assumes "\<exists> i r l re le. has_result (parse sep) i r l \<and> has_result (parse elem) l re le \<and> is_error (parse sep) le"
  assumes "PNGI (parse elem)"
  shows "\<not>does_not_peek_past_end (parse (separated_by sep elem oracle))"
  using assms unfolding does_not_peek_past_end_def PNGI_def
  apply (clarsimp simp add: NER_simps)
  subgoal for i ia r ra l la re x
    apply (rule exI[of _ \<open>list_upto i l\<close>])
    apply (rule exI[of _ \<open>[r]\<close>])
    apply (rule conjI)
    subgoal
      apply (rule exI[of _ l])
      using list_upto_cons_second[of i l]
      by (clarsimp simp add: NER_simps)
    subgoal
      apply (rule exI[of _ ia])
      apply (clarsimp simp add: NER_simps has_result_implies_not_is_error)
      by (metis (no_types, opaque_lifting) has_result_def is_error_implies_not_has_result option.inject snd_eqD)
    done
  done


\<comment> \<open>Does not consume past char3\<close>
lemma separated_by_no_consume_past_char:
  assumes E_error_empty: "is_error (parse E) []"
  assumes E_error_c: "\<And>l. is_error (parse E) (c # l)"
  assumes E_wf: "bidef_well_formed E"
  assumes MSTE_wf: "bidef_well_formed (many (b_then S E))"
  assumes E_dncpc_fpc_SE: "\<And>i c. fpc (parse (many (b_then S E))) i c \<longrightarrow> does_not_consume_past_char3 (parse E) c"
  assumes E_dncpc_c: "does_not_consume_past_char3 (parse E) c"
  assumes E_drop_leftover: "\<And>c c' l a. has_result (parse E) (c @ c' @ l) a (c' @ l) \<Longrightarrow> has_result (parse E) (c @ c') a c'"

  assumes S_error_empty: "\<forall>r l. has_result (parse S) [] r l \<longrightarrow> \<not> is_error (parse E) l \<Longrightarrow> is_error (parse S) []"
  assumes S_error_c: "\<And>l' r l. has_result (parse S) (c # l') r l \<longrightarrow> \<not> is_error (parse E) l \<Longrightarrow> is_error (parse S) (c # l')"
  assumes S_pngi: "PNGI (parse S)"

  assumes SE_pasi: "PASI (parse (b_then S E))"

  assumes S_drop_leftover_OR_E_no_parse_same_leftover: " \<And> cM l abs cS a b.
             \<lbrakk>has_result (parse (many (b_then S E))) (cM @ l) abs l; has_result (parse S) (cS @ cM @ l) a (cM @ l)\<rbrakk> \<Longrightarrow>
               ((has_result (parse E) (cM @ l) b (cM @ l) \<longrightarrow> False) \<or> (has_result (parse S) (cS @ cM) a cM))"

  assumes S_dncpc_fpc_E: "\<And>i c. fpc (parse E) i c \<Longrightarrow> does_not_consume_past_char3 (parse S) c"


  shows "does_not_consume_past_char3 (parse (separated_by S E oracle)) c"
  unfolding separated_by_def
  apply (rule transform_does_not_consume_past_char3)
  apply (rule optional_does_not_consume_past_char3)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps E_error_empty)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps E_error_c)
  unfolding separated_byBase_def
  apply (rule then_does_not_consume_past3_from_can_drop_leftover) \<comment> \<open>Others are possible here too.\<close>
  subgoal by (rule E_wf)
  subgoal by (rule MSTE_wf)
     defer \<comment> \<open>does_not_consume_past_char3 (parse (many (b_then S E))) c\<close>
  subgoal by (rule E_dncpc_fpc_SE)
  subgoal by (rule E_dncpc_c)
  subgoal by (rule E_drop_leftover)
  \<comment> \<open>does_not_consume_past_char3 (parse (many (b_then S E))) c\<close>
  unfolding does_not_consume_past_char3_def
  apply clarsimp
  subgoal for ca r l
    apply (induction r arbitrary: ca l; clarsimp?)
    subgoal for ca l \<comment> \<open>Empty\<close>
      apply (auto simp add: NER_simps)
      subgoal by (rule S_error_empty)
      subgoal using S_error_c by blast
      subgoal by (rule S_error_empty)
      subgoal using S_error_c by blast
      done
    subgoal for a b abs ca l \<comment> \<open>NonEmpty\<close>
      apply (auto simp add: NER_simps)
      subgoal for l' l''
        apply (insert S_pngi[unfolded PNGI_def, rule_format, of \<open>ca@l\<close> a l'']; clarsimp)
        subgoal for cS
          apply (insert E_wf[THEN get_pngi_unfold, rule_format, of l'' b l']; clarsimp)
          subgoal for cE
            apply (insert many_PNGI[OF SE_pasi, unfolded PNGI_def, rule_format, of l' abs l]; clarsimp)
            subgoal for cM
              apply (rule exI[of _ cM]; clarsimp)
              apply (rule exI[of _ \<open>cE @ cM\<close>]; rule conjI)
              subgoal
                apply (cases cE; clarsimp)
                subgoal \<comment> \<open>empty\<close> by (insert S_drop_leftover_OR_E_no_parse_same_leftover; clarsimp)
                subgoal for cE' cEs
                  by (insert S_dncpc_fpc_E[of b cE', unfolded fpc_def, OF exI[of _ cEs], OF exI[of _ \<open>cM@l\<close>],
                                           unfolded does_not_consume_past_char3_def, rule_format,
                                           of cS \<open>cE' # cEs @ cM @ l\<close> a \<open>cEs @ cM\<close>]; clarsimp)
                done
              subgoal
                apply (cases cM; clarsimp)
                subgoal \<comment> \<open>empty\<close>
                  using E_dncpc_c[unfolded does_not_consume_past_char3_def] by fast
                subgoal for cM' cMs
                  using E_dncpc_fpc_SE[unfolded does_not_consume_past_char3_def fpc_def] by blast
                done
              done
            done
          done
        done
      subgoal for l' l'' l'''
        apply (insert S_pngi[unfolded PNGI_def, rule_format, of \<open>ca@l\<close> a l'']; clarsimp)
        subgoal for cS
          apply (insert E_wf[THEN get_pngi_unfold, rule_format, of l'' b l']; clarsimp)
          subgoal for cE
            apply (insert many_PNGI[OF SE_pasi, unfolded PNGI_def, rule_format, of l' abs l]; clarsimp)
            subgoal for cM
              apply (rule exI[of _ \<open>cM @ c # l'''\<close>]; clarsimp)
              apply (rule exI[of _ \<open>cE @ cM @ c # l'''\<close>]; rule conjI)
              subgoal
                apply (cases cE; clarsimp)
                subgoal \<comment> \<open>Empty\<close>
                  apply (insert S_drop_leftover_OR_E_no_parse_same_leftover[of cM l abs cS a b]; clarsimp)
                  apply (insert E_dncpc_c[unfolded does_not_consume_past_char3_def, rule_format, of \<open>[]\<close> \<open>cM@l\<close> b, simplified]
                                has_result_implies_not_is_error[of \<open>parse E\<close> \<open>[]\<close> b \<open>[]\<close>]
                                E_error_empty)
                  by clarsimp
                subgoal for cE' cEs
                  using S_dncpc_fpc_E[unfolded does_not_consume_past_char3_def fpc_def] by fast
                done
              subgoal
                apply (cases cM; clarsimp)
                subgoal \<comment> \<open>Empty\<close>
                  using E_dncpc_c[unfolded does_not_consume_past_char3_def] by fast
                subgoal for cM' cMs
                  using E_dncpc_fpc_SE[unfolded does_not_consume_past_char3_def fpc_def] by blast
                done
              done
            done
          done
        done
      done
    done
  done


lemma separated_by_drop_past_leftover:
  assumes E_pngi: "PNGI (parse E)"
  assumes S_pngi: "PNGI (parse S)"
  assumes SE_pasi: "PASI (parse (b_then S E))"

  assumes E_drop_leftover_error: "\<And>l l'. is_error (parse E) (l @ l') \<Longrightarrow> is_error (parse E) l"
  assumes E_drop_leftover: "\<And> c l l' r. has_result (parse E) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse E) (c @ l) r l"

  assumes S_drop_leftover_error: "\<And>l l'. is_error (parse S) (l @ l') \<Longrightarrow> is_error (parse S) l"
  assumes S_drop_leftover: "\<And> c l l' r. has_result (parse S) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse S) (c @ l) r l"

  assumes SE_error_no_S_nonterm: "\<And>i i'. is_error (parse (b_then S E)) (i @ i') \<Longrightarrow> \<not> is_nonterm (parse S) i"

  assumes remove_into_S_means_error_S_or_error_E: "\<And>i i' r l. \<lbrakk>i'\<noteq> []; has_result (parse S) (i @ i' @ l) r l; is_error (parse E) l\<rbrakk> \<Longrightarrow> (is_error (parse S) i \<or> (\<exists>r l. has_result (parse S) i r l \<and> is_error (parse E) l))"

  shows "has_result (parse (separated_by S E oracle)) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse (separated_by S E oracle)) (c @ l) r l"
  apply (cases r; clarsimp)
  subgoal by (clarsimp simp add: NER_simps E_drop_leftover_error)
  subgoal for r' rs
    apply (clarsimp simp add: NER_simps)
    subgoal for lE s_rs
      apply (insert E_pngi[unfolded PNGI_def, rule_format, of \<open>c@l@l'\<close> r' lE]; clarsimp)
      apply (insert many_PNGI[OF SE_pasi, unfolded PNGI_def, rule_format, of lE \<open>(zip s_rs rs)\<close> \<open>l@l'\<close>]; clarsimp)
      subgoal for cE cMSE
        apply (rule exI[of _ \<open>cMSE @ l\<close>]; rule conjI)
        subgoal by (clarsimp simp add: E_drop_leftover)
        subgoal
          apply (rule exI[of _ s_rs]; clarsimp)
          apply (rule many_can_drop_leftover[of \<open>b_then S E\<close> cMSE l l' \<open>zip s_rs rs\<close>]; assumption?)
          subgoal for c2 l2 l2' r2
            apply (rule then_can_drop_leftover[of S E c2 l2 l2' r2]; assumption?)
            subgoal by (rule S_drop_leftover)
            subgoal by (rule S_pngi)
            subgoal by (rule E_drop_leftover)
            subgoal by (rule E_pngi)
            done
          subgoal for l2 l2'
            apply (rule then_can_drop_leftover_on_error; assumption?)
            subgoal by (rule S_drop_leftover_error)
            subgoal by (rule S_pngi)
            subgoal by (rule SE_error_no_S_nonterm)
            subgoal by (rule remove_into_S_means_error_S_or_error_E)
            subgoal by (rule S_drop_leftover)
            subgoal by (rule E_drop_leftover_error)
            done
          subgoal by (rule SE_pasi)
          done
        done
      done
    done
  done


\<comment> \<open>First printed char\<close>
lemma serparated_by_fpci[fpci_simps]:
  "first_printed_chari (print (separated_by sep elem oracle)) i c \<longleftrightarrow>(
    case i of
      [] \<Rightarrow> False
    | (x#xs) \<Rightarrow>(
      if p_has_result (print elem) x [] then
        (first_printed_chari (print (many (b_then sep elem))) (map (Pair oracle) xs) c)
      else
        (first_printed_chari (print elem) x c \<and>
         (\<exists>t. p_has_result (print (many (b_then sep elem))) (map (Pair oracle) xs) t))
      ))"
  by (clarsimp simp add: separated_by_def separated_byBase_def fpci_simps split: list.splits)



\<comment> \<open>Well formed\<close>
lemma snd_comp_pair_id[simp]:
  "(snd \<circ> Pair a) = id"
  by fastforce


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



lemma separated_by_well_formed_does_not_peek_past:
  assumes "good_separated_by_oracle sep sep_oracle"
  assumes "does_not_peek_past_end (parse elem)"
  assumes "does_not_peek_past_end (parse sep)"
  assumes "bidef_well_formed elem"
  assumes "bidef_well_formed sep"
  assumes "is_error (parse elem) []"
  assumes "is_error (parse sep) []"
  assumes "PASI (parse elem) \<or> PASI (parse sep)"
  shows "bidef_well_formed (separated_by sep elem sep_oracle)"
  apply (rule separated_by_well_formed2)
  subgoal by (rule assms(1))
  subgoal by (clarsimp simp add: does_not_peek_past_end_implies_does_not_eat_into assms(3,5))
  subgoal by (rule assms(4))
  subgoal by (rule assms(5))
  subgoal by (rule assms(6))
  subgoal by (clarsimp simp add: does_not_peek_past_end_implies_does_not_eat_into assms(2,4))
  subgoal
    using cannot_be_grown_by_when_no_peek_past[of \<open>b_then sep elem\<close>]
          then_does_not_peek_past_end[OF assms(3) assms(5)[THEN get_pngi]
                                         assms(2) assms(4)[THEN get_pngi]]
          b_then_well_formed_does_not_peek_past[OF assms(5, 4, 3)]
    by blast
  subgoal by (rule assms(7))
  subgoal by (rule assms(8))
  done


lemma wf_many_then:
  assumes wf_elem: "bidef_well_formed elem"
  assumes wf_sep:  "bidef_well_formed sep"
  assumes error_elem_empty: "is_error (parse elem) []"
  assumes error_sep_empty: "is_error (parse sep) []"
  assumes pasi_elem_or_sep: "PASI (parse elem) \<or> PASI (parse sep)"
  assumes sep_no_consume_fpc_elem: "\<forall>i c. first_printed_chari (print elem) i c \<longrightarrow> does_not_consume_past_char3 (parse sep) c"
  \<comment> \<open>We definitely want to remove everything below this at some point.\<close>
  assumes sep_elem_no_consume_sep_elem: "\<forall>i c. first_printed_chari (print (b_then sep elem)) i c \<longrightarrow> does_not_consume_past_char3 (parse (b_then sep elem)) c"
  shows "bidef_well_formed (many (b_then sep elem))"
  apply (rule no_consume_past_own_first_char_wf_many)
  subgoal
    using pasi_elem_or_sep wf_elem[THEN get_pngi] wf_sep[THEN get_pngi]
    by (auto simp add: then_PASI_from_pasi_pngi then_PASI_from_pngi_pasi)
  subgoal
    using \<open>PASI (parse (b_then sep elem))\<close> \<comment> \<open>Literal fact of previous subgoal\<close>
          error_elem_empty error_sep_empty
          wf_sep[THEN get_pngi, unfolded PNGI_def]
    by (clarsimp simp add: NER_simps)
  subgoal
    apply (rule b_then_well_formed)
    subgoal by (rule wf_sep)
    subgoal by (rule wf_elem)
    subgoal
      apply (rule first_printed_does_not_eat_into3)
      subgoal by (rule wf_sep)
      subgoal by (rule sep_no_consume_fpc_elem)
      done
    done
  subgoal by (rule sep_elem_no_consume_sep_elem)
  done

lemma separated_by_well_formed_no_consume_past_char_inner:
  assumes good_sep_oracle: "good_separated_by_oracle sep sep_oracle"
  assumes wf_elem: "bidef_well_formed elem"
  assumes wf_sep:  "bidef_well_formed sep"
  assumes error_elem_empty: "is_error (parse elem) []"
  assumes error_sep_empty: "is_error (parse sep) []"
  assumes pasi_elem_or_sep: "PASI (parse elem) \<or> PASI (parse sep)"
  assumes sep_no_consume_fpc_elem: "\<forall>i c. first_printed_chari (print elem) i c \<longrightarrow> does_not_consume_past_char3 (parse sep) c"
  assumes elem_no_consume_fpc_sep: "\<forall>i c. first_printed_chari (print sep) i c \<longrightarrow> does_not_consume_past_char3 (parse elem) c"
  \<comment> \<open>We definitely want to remove everything below this at some point.\<close>
  assumes sep_elem_no_consume_sep_elem: "\<forall>i c. first_printed_chari (print (b_then sep elem)) i c \<longrightarrow> does_not_consume_past_char3 (parse (b_then sep elem)) c"
  shows "bidef_well_formed (separated_by sep elem sep_oracle)"
  unfolding separated_by_def separated_byBase_def
  apply (rule transform_well_formed3)
  subgoal
    apply (rule optional_well_formed)
    subgoal by (clarsimp simp add: NER_simps error_elem_empty)
    subgoal
      apply (rule b_then_well_formed)
      subgoal by (rule wf_elem)
      subgoal by (clarsimp simp add: wf_many_then assms)
      subgoal
        apply (rule first_printed_does_not_eat_into3)
        subgoal by (rule wf_elem)
        subgoal
          apply (subst many_fpci)
          apply clarsimp
          subgoal for i c
            apply (cases i)
            using wf_no_empty_parse_means_no_empty_print[OF error_sep_empty wf_sep]
                  elem_no_consume_fpc_sep
            by (clarsimp simp add: fpci_simps print_empty)+
          done
        done
      done
    done
  subgoal
    unfolding well_formed_transform_funcs3_def
    \<comment> \<open>A lot of this is basically well formed over said change. Maybe this can be generalised?\<close>
    apply (auto simp add: NER_simps fp_NER split: option.splits list.splits)
    subgoal for i r rs l l'
      unfolding optional_p_has_result
      using wf_elem[THEN get_printer_can_print_unfold,
                    rule_format, of i r l']
      apply (clarsimp simp add: fp_NER)
      apply (induction rs arbitrary: i r l l'; clarsimp simp add: fp_NER NER_simps)
      subgoal for r_a r_b rs' r_pr l l'' l'''
        unfolding many_p_has_result_safe(2)
        apply (auto simp add: fp_NER)
        subgoal by (rule good_sep_oracle[unfolded good_separated_by_oracle_def])
        subgoal using wf_elem[THEN get_printer_can_print_unfold] by blast
        subgoal using wf_elem[THEN get_printer_can_print_unfold] by blast
        done
      done
    subgoal using error_elem_empty by blast
    subgoal for i bs i_pr bs_map_pr
      apply (rule exI[of _ \<open>[]\<close>])
      apply (rule exI[of _ \<open>Some (i, map (Pair sep_oracle) bs)\<close>])
      apply clarsimp
      apply (rule exI[of _ bs_map_pr])
      using wf_elem[THEN get_parser_can_parse_unfold, rule_format, of i i_pr]
      apply auto
      subgoal
        apply (cases bs_map_pr; clarsimp) \<comment> \<open>[] case is easily dispatched\<close>
        subgoal for hd_bs_map_pr tl_bs_map_pr
          apply (cases \<open>map (Pair sep_oracle) bs\<close>)
          subgoal by (clarsimp simp add: fp_NER) \<comment> \<open>Empty case dispatched because we know at least one char in print result\<close>
          subgoal
            apply (clarsimp simp add: fp_NER)
            using elem_no_consume_fpc_sep[rule_format, of sep_oracle hd_bs_map_pr, unfolded first_printed_chari_def]
                  no_consume_past3_wf_stronger[OF _ wf_elem, of hd_bs_map_pr]
                  wf_no_empty_parse_means_no_empty_print[OF error_sep_empty wf_sep]
            by (metis hd_append list.sel(1))
          done
        done
      subgoal
        using wf_many_then[OF wf_elem wf_sep error_elem_empty
                              error_sep_empty pasi_elem_or_sep
                              sep_no_consume_fpc_elem
                              sep_elem_no_consume_sep_elem,
                           THEN wf_parser_can_parse_print_result_apply]
        by blast
      done
    done
  done



\<comment> \<open>This is just built up here to ensure that we can more easily remove that last assms when we can.\<close>
lemma separated_by_well_formed_no_consume_past_char:
  assumes good_sep_oracle: "good_separated_by_oracle sep sep_oracle"
  assumes wf_elem: "bidef_well_formed elem"
  assumes wf_sep:  "bidef_well_formed sep"
  assumes error_elem_empty: "is_error (parse elem) []"
  assumes error_sep_empty: "is_error (parse sep) []"
  assumes pasi_elem_or_sep: "PASI (parse elem) \<or> PASI (parse sep)"
  assumes sep_no_consume_fpc_elem: "\<forall>i c. first_printed_chari (print elem) i c \<longrightarrow> does_not_consume_past_char3 (parse sep) c"
  assumes elem_no_consume_fpc_sep: "\<forall>i c. first_printed_chari (print sep) i c \<longrightarrow> does_not_consume_past_char3 (parse elem) c"
  \<comment> \<open>We definitely want to remove everything below this at some point.\<close>
  assumes sep_elem_no_consume_sep_elem: "\<forall>i c. first_printed_chari (print (b_then sep elem)) i c \<longrightarrow> does_not_consume_past_char3 (parse (b_then sep elem)) c"
  shows "bidef_well_formed (separated_by sep elem sep_oracle)"
  by (rule separated_by_well_formed_no_consume_past_char_inner[OF assms])



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
