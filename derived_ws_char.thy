theory derived_ws_char
  imports basic_definitions
          derived_this_char
          derived_then
          derived_many
          derived_whitespace_char
          derived_drop
begin

definition ws_char :: "char \<Rightarrow> unit bidef" where
  "ws_char c = drop (b_then (many whitespace_char) (this_char c)) ([], c)"



section NER
lemma ws_char_is_nonterm[NER_simps]:
  "is_nonterm (parse (ws_char c)) i \<longleftrightarrow> False"
  unfolding ws_char_def
  by (auto simp add: NER_simps whitespace_char_PASI)

lemma ws_char_is_error[NER_simps]:
  "is_error (parse (ws_char c)) i \<longleftrightarrow> c\<in>whitespace_chars \<or> (\<nexists>tl. dropWhile (\<lambda>x. x \<in>whitespace_chars) i = (c #tl))"
  apply (auto simp add: ws_char_def NER_simps whitespace_char_def any_from_set_def)
  subgoal by (metis dropWhile_eq_Nil_conv list.distinct(1))
  subgoal by (meson dropWhile_eq_Nil_conv hd_dropWhile)
  subgoal by (metis dropWhile_eq_Nil_conv list.collapse)
  done

lemma ws_char_has_result[NER_simps]:
  "has_result (parse (ws_char c)) i r l \<longleftrightarrow>
        r = ()
      \<and> l = tl (dropWhile (\<lambda>x. x \<in>whitespace_chars) i)
      \<and> (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) \<noteq> []
      \<and> hd (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) = c"
  apply (auto simp add: ws_char_def NER_simps whitespace_char_def any_from_set_def)
  by (metis dropWhile_eq_Nil_conv hd_Cons_tl)

lemma ws_char_no_result_same_leftover[NER_simps]:
  "has_result (parse (ws_char c)) i r i \<longleftrightarrow> False"
  apply (clarsimp simp add: NER_simps)
  by (metis hd_Cons_tl impossible_Cons length_dropWhile_le length_greater_0_conv length_pos_if_in_set list.sel(2))

lemma ws_char_first_char_result:
  "has_result (parse (ws_char c)) (i#is) r l \<Longrightarrow> i \<in> whitespace_chars \<or> i = c"
  by (clarsimp simp add: NER_simps split: if_splits)


lemma ws_char_has_result_c[NER_simps]:
  "has_result_c (parse (ws_char c)) i r l \<longleftrightarrow>
      r = ()
    \<and> [] = tl (dropWhile (\<lambda>x. x \<in>whitespace_chars) i)
    \<and> (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) \<noteq> []
    \<and> hd (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) = c
"
  apply (auto simp add: ws_char_def has_result_c_def NER_simps whitespace_char_def any_from_set_def)
  subgoal by (metis (no_types, lifting) Cons_eq_appendI append.right_neutral append_eq_append_conv2 append_same_eq dropWhile_append1 dropWhile_eq_Nil_conv same_append_eq tl_Nil)
  subgoal by (metis Cons_eq_appendI dropWhile_append list.simps(3) self_append_conv2 takeWhile_dropWhile_id)
  subgoal using \<open>\<And>x. \<lbrakk>dropWhile (\<lambda>found. found \<in> whitespace_chars) (i @ l) = c # l; x \<notin> whitespace_chars; x \<in> set l\<rbrakk> \<Longrightarrow> \<exists>x\<in>set i. x \<notin> whitespace_chars\<close>
    by fastforce
  subgoal by (metis dropWhile_eq_Nil_conv hd_Cons_tl)
  done



section \<open>fp NER\<close>
lemma ws_char_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (ws_char c)) i \<longleftrightarrow> False"
  by (clarsimp simp add: ws_char_def fp_NER)

lemma ws_char_p_is_error[fp_NER]:
  "p_is_error (print (ws_char c)) i \<longleftrightarrow> False"
  by (clarsimp simp add: ws_char_def fp_NER)

lemma ws_char_p_has_result[fp_NER]:
  "p_has_result (print (ws_char c)) i r \<longleftrightarrow> r = [c]"
  by (auto simp add: ws_char_def fp_NER)

lemma ws_char_print_empty[print_empty, fp_NER]:
  "p_has_result (print (ws_char c)) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: ws_char_p_has_result)



section \<open>PNGI, PASI\<close>
lemma ws_char_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse (ws_char c))"
  unfolding ws_char_def
  thm drop_PNGI
  by (simp add: ws_char_def drop_PNGI then_PNGI many_PNGI whitespace_char_PASI this_char_PNGI)

lemma ws_char_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse (ws_char c))"
  apply (subst ws_char_def)
  by pasi_pngi



section \<open>Does not peek past end\<close>
lemma ws_char_does_not_peek_past_end[peek_past_end_simps]:
  assumes "c \<notin> whitespace_chars"
  shows "does_not_peek_past_end (parse (ws_char c))"
  apply (clarsimp simp add: does_not_peek_past_end_def)
  subgoal for c' l l'
    apply (induction l'; clarsimp)
    subgoal
      apply (auto simp add: NER_simps)
      subgoal by (metis self_append_conv2 tl_Nil tl_append2)
      subgoal by (metis dropWhile_eq_Nil_conv hd_append)
      subgoal by (metis append_Nil2 has_result_c_def tl_Nil ws_char_has_result ws_char_has_result_c)
      subgoal by (metis (no_types, lifting) dropWhile_append2 dropWhile_eq_Nil_conv has_result_c_def ws_char_has_result ws_char_has_result_c)
      subgoal for x by (metis dropWhile_append1
                  \<open>\<And>x. \<lbrakk>l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) (c' @ l)); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) (c' @ l)); x \<notin> whitespace_chars; x \<in> set l\<rbrakk> \<Longrightarrow> \<exists>x\<in>set c'. x \<notin> whitespace_chars\<close> \<open>\<And>x. \<lbrakk>l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); x \<notin> whitespace_chars; x \<in> set c'\<rbrakk> \<Longrightarrow> hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c') = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l)\<close>)
      done
    subgoal for l'hd l'
      apply (auto simp add: NER_simps)
      subgoal by (metis dropWhile_eq_Nil_conv self_append_conv2 tl_append2)
      subgoal by (metis dropWhile_eq_Nil_conv hd_append2)
      subgoal using \<open>\<And>xa x. \<lbrakk>l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); x \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); xa \<notin> whitespace_chars; x \<in> set c'; xa \<in> set c'\<rbrakk> \<Longrightarrow> l'hd # l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'hd # l')\<close>
        by blast
      subgoal using \<open>\<And>xa x. \<lbrakk>l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); x \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); xa \<notin> whitespace_chars; x \<in> set c'; xa \<in> set c'\<rbrakk> \<Longrightarrow> hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'hd # l') = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l')\<close>
        by blast
      subgoal using \<open>\<And>xa x. \<lbrakk>l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); x \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); xa \<notin> whitespace_chars; x \<in> set c'; xa \<in> set c'\<rbrakk> \<Longrightarrow> l'hd # l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'hd # l')\<close>
        by blast
      subgoal using \<open>\<And>xa x. \<lbrakk>l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); x \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); xa \<notin> whitespace_chars; x \<in> set c'; xa \<in> set c'\<rbrakk> \<Longrightarrow> hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'hd # l') = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l')\<close>
        by blast
      subgoal using \<open>\<And>xa x. \<lbrakk>l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l); c = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); x \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'); xa \<notin> whitespace_chars; x \<in> set l'; xa \<in> set c'\<rbrakk> \<Longrightarrow> l'hd # l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) c' @ l'hd # l')\<close>
                    \<open>has_result (parse (ws_char c)) (c' @ l) () l \<Longrightarrow> has_result (parse (ws_char c)) c' () []\<close>
                    ws_char_has_result
        by force
      subgoal
        by (smt (verit, ccfv_SIG) \<open>has_result (parse (ws_char c)) (c' @ l) () l \<Longrightarrow> has_result (parse (ws_char c)) c' () []\<close> dropWhile_append dropWhile_eq_Nil_conv hd_append2 ws_char_has_result)
      done
    done
  done



section \<open>Does not consume past char\<close>
lemma ws_char_does_not_consume_past_char3:
  assumes "c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3 (parse (ws_char c)) ch"
  using ws_char_does_not_peek_past_end[OF assms]
        does_not_consume_past_any_char3_eq_not_peek_past_end
  by blast



section \<open>First printed/parsed char\<close>
lemma ws_char_fpci[fpci_simps]:
  shows "first_printed_chari (print (ws_char c)) i c' \<longleftrightarrow> c' = c"
  unfolding first_printed_chari_def
  by (auto simp add: ws_char_p_has_result)

lemma ws_char_fpc[fpc_simps]:
  "fpc (parse (ws_char c)) i c' \<longleftrightarrow> c\<notin>whitespace_chars \<and> c' \<in> ({c} \<union> whitespace_chars)"
  unfolding fpc_def
  apply (cases \<open>c \<in> whitespace_chars\<close>)
  subgoal \<comment> \<open>c \<in> whitespace_chars means that there is never a result.\<close>
    using ws_char_is_error[of c]
    apply clarsimp
    using has_result_implies_not_is_error by fast
  subgoal \<comment> \<open>c \<notin> whitespace_chars means that there can be a result.\<close>
    apply (cases \<open>c' \<in> whitespace_chars\<close>)
    subgoal
      apply clarsimp
      apply (rule exI[of _ \<open>[c]\<close>])
      apply (rule exI[of _ \<open>[c]\<close>]) \<comment> \<open>Using c as char that is not ws\<close>
      by (clarsimp simp add: NER_simps)
    subgoal by (auto simp add: NER_simps)
    done
  done



section \<open>chars_can_be_dropped\<close>
lemma ws_char_chars_can_be_dropped:
  "chars_can_be_dropped (parse (ws_char c)) whitespace_chars"
  unfolding chars_can_be_dropped_def
  by (clarsimp simp add: NER_simps)


\<comment> \<open>Pretty sure this can be strengthened to can change leftover.\<close>
section \<open>can drop past leftover\<close>
lemma ws_char_can_drop_past_leftover:
  assumes "has_result (parse (ws_char C)) (c @ l @ l') () (l @ l')"
  shows "has_result (parse (ws_char C)) (c @ l) () (l)"
  using assms
  apply (induction l; clarsimp)
  subgoal
    apply (clarsimp simp add: NER_simps)
    by (metis assms dropWhile_eq_Nil_conv has_result_c_def ws_char_has_result_c)
  subgoal for a l
    apply (clarsimp simp add: NER_simps)
    by (metis (mono_tags, lifting) assms does_not_peek_past_end_def hd_dropWhile ws_char_does_not_peek_past_end ws_char_has_result)
  done



section \<open>Well formed\<close>
lemma many_ws_wf:
  "bidef_well_formed (many whitespace_char)"
  unfolding whitespace_char_def any_from_set_def
  by (auto simp add: many_char_for_pred_well_formed)
lemma many_ws_no_consume_past:
  "does_not_consume_past_char3 (parse (many whitespace_char)) c \<longleftrightarrow> c \<notin> whitespace_chars"
  unfolding whitespace_char_def any_from_set_def
            many_char_for_predicate_does_not_consume_past_char3
  by blast


lemma ws_char_well_formed:
  assumes "c \<notin> whitespace_chars"
  shows "bidef_well_formed (ws_char c)"
  unfolding ws_char_def
  apply (rule drop_well_formed)
  subgoal
    apply (rule b_then_well_formed)
    subgoal by (rule many_ws_wf)
    subgoal by (rule this_char_well_formed)
    subgoal
      apply (rule first_printed_does_not_eat_into3)
      subgoal by (rule many_ws_wf)
      by (clarsimp simp add: this_char_fpci assms many_ws_no_consume_past)
    done
  by (clarsimp simp add: fp_NER)


end
