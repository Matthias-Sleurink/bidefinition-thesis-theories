theory derived_ws_char_ws
  imports basic_definitions
          derived_this_char
          derived_then
          derived_many
          derived_whitespace_char
          derived_drop
begin

definition ws_char_ws :: "char \<Rightarrow> unit bidef" where
  "ws_char_ws c = drop (b_then (many whitespace_char) (b_then (this_char c) (many whitespace_char))) ([], c, [])"



section NER
lemma ws_char_ws_is_nonterm[NER_simps]:
  "is_nonterm (parse (ws_char_ws c)) i \<longleftrightarrow> False"
  unfolding ws_char_ws_def
  by (auto simp add: NER_simps whitespace_char_PASI)

lemma ws_char_ws_is_error[NER_simps]:
  "is_error (parse (ws_char_ws c)) i \<longleftrightarrow> c\<in>whitespace_chars \<or> (\<nexists>tl. dropWhile (\<lambda>x. x \<in>whitespace_chars) i = (c #tl))"
  apply (auto simp add: ws_char_ws_def NER_simps whitespace_char_def any_from_set_def)
  subgoal by (metis dropWhile_eq_Nil_conv list.distinct(1))
  subgoal by (meson dropWhile_eq_Nil_conv hd_dropWhile)
  subgoal by (metis dropWhile_eq_Nil_conv list.collapse)
  done

lemma ws_char_ws_has_result[NER_simps]:
  "has_result (parse (ws_char_ws c)) i r l \<longleftrightarrow>
        r = ()
      \<and> l = dropWhile (\<lambda>x. x \<in>whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in>whitespace_chars) i))
      \<and> (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) \<noteq> []
      \<and> hd (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) = c"
  apply (auto simp add: ws_char_ws_def NER_simps whitespace_char_def any_from_set_def)
  by (metis dropWhile_eq_Nil_conv hd_Cons_tl)

lemma ws_char_ws_has_result_implies_leftover_head:
  assumes "has_result (parse (ws_char_ws c)) i r l"
  shows "case l of [] \<Rightarrow> True | (l'#ls) \<Rightarrow> l' \<notin> whitespace_chars"
  using assms[unfolded ws_char_ws_has_result]
  apply (clarsimp split: list.splits)
  by (metis hd_dropWhile list.discI list.sel(1))



lemma ws_char_ws_has_result_c[NER_simps]:
  "has_result_c (parse (ws_char_ws c)) i r l \<longleftrightarrow>
      r = ()
    \<and> [] = dropWhile (\<lambda>x. x \<in>whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in>whitespace_chars) i))
    \<and> (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) \<noteq> []
    \<and> hd (dropWhile (\<lambda>x. x \<in>whitespace_chars) i) = c
    \<and> (l \<noteq> [] \<longrightarrow> hd l \<notin> whitespace_chars)
"
  apply (auto simp add: ws_char_ws_def has_result_c_def NER_simps whitespace_char_def any_from_set_def)
  subgoal by (metis (no_types, lifting) append_eq_Cons_conv append_same_eq dropWhile_eq_Nil_conv list.sel(3) set_takeWhileD takeWhile_dropWhile_id)
  subgoal by (metis dropWhile_eq_Nil_conv hd_append2 list.sel(1))
  subgoal by (meson dropWhile_eq_Nil_conv hd_dropWhile)
  subgoal by (smt (verit) Nil_tl append_eq_Cons_conv append_same_eq dropWhile_append dropWhile_eq_Nil_conv list.sel(3) set_takeWhileD takeWhile_dropWhile_id)
  subgoal by (metis dropWhile_append2 dropWhile_idem length_Cons length_dropWhile_le lessI linorder_not_less)
  subgoal by (metis (mono_tags, lifting) \<open>\<And>x l'. \<lbrakk>x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) (i @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = c # l'; l = dropWhile (\<lambda>found. found \<in> whitespace_chars) l'; x \<in> set (dropWhile (\<lambda>found. found \<in> whitespace_chars) l')\<rbrakk> \<Longrightarrow> \<exists>x\<in>set i. x \<notin> whitespace_chars\<close> \<open>\<And>x l'. \<lbrakk>x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) i @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l' = c # l'; l = dropWhile (\<lambda>found. found \<in> whitespace_chars) l'; x \<in> set i\<rbrakk> \<Longrightarrow> hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i) = c\<close>
                    dropWhile_append)
  subgoal by (metis hd_dropWhile length_greater_0_conv length_pos_if_in_set)
  subgoal by (metis dropWhile_eq_Nil_conv hd_Cons_tl)
  subgoal
    apply (rule exI[of _ \<open>(takeWhile (\<lambda>x. x\<in>whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i))) @l\<close>])
    apply auto
    subgoal by (metis dropWhile_eq_Nil_conv list.collapse takeWhile_eq_all_conv)
    subgoal by (metis dropWhile_append2 dropWhile_hd_no_match set_takeWhileD)
    done
  done



section \<open>fp NER\<close>
lemma ws_char_ws_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (ws_char_ws c)) i \<longleftrightarrow> False"
  by (clarsimp simp add: ws_char_ws_def fp_NER)

lemma ws_char_ws_p_is_error[fp_NER]:
  "p_is_error (print (ws_char_ws c)) i \<longleftrightarrow> False"
  by (clarsimp simp add: ws_char_ws_def fp_NER)

lemma ws_char_ws_p_has_result[fp_NER]:
  "p_has_result (print (ws_char_ws c)) i r \<longleftrightarrow> r = [c]"
  "\<exists>r. p_has_result (print (ws_char_ws c)) () r"
  by (auto simp add: ws_char_ws_def fp_NER)

lemma ws_char_ws_print_empty[print_empty, fp_NER]:
  "p_has_result (print (ws_char_ws c)) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: ws_char_ws_p_has_result)



section \<open>PNGI, PASI\<close>
lemma ws_char_ws_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse (ws_char_ws c))"
  unfolding ws_char_ws_def
  thm drop_PNGI
  by (simp add: ws_char_ws_def drop_PNGI then_PNGI many_PNGI whitespace_char_PASI this_char_PNGI)

lemma ws_char_ws_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse (ws_char_ws c))"
  apply (subst ws_char_ws_def)
  apply (subst drop_PASI)
  apply (rule then_PASI_from_pngi_pasi)
  subgoal by (clarsimp simp add: many_PNGI whitespace_char_PASI)
  apply (rule then_PASI_from_pasi_pngi)
  subgoal by (rule this_char_PASI)
  subgoal by (clarsimp simp add: many_PNGI whitespace_char_PASI)
  done



section \<open>Does not peek past end\<close>
lemma ws_char_ws_does_not_peek_past_end[peek_past_end_simps]:
  assumes "c \<notin> whitespace_chars"
  shows "\<not>does_not_peek_past_end (parse (ws_char_ws c))"
  unfolding does_not_peek_past_end_def
  apply clarsimp
  apply (rule exI[of _ \<open>[c]\<close>])
  apply clarsimp
  apply (rule conjI)
  subgoal
    apply (rule exI[of _ \<open>[]\<close>])
    by (clarsimp simp add: NER_simps assms)
  subgoal
    apply (rule exI[of _ \<open>'' ''\<close>])
    by (clarsimp simp add: NER_simps whitespace_chars_def)
  done



section \<open>Does not consume past char\<close>
lemma ws_char_ws_does_not_consume_past_char3:
  assumes "c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3 (parse (ws_char_ws c)) ch \<longleftrightarrow> ch \<notin> whitespace_chars"
  unfolding does_not_consume_past_char3_def
  apply auto
  subgoal by (metis assms does_not_peek_past_end_def has_result_c_def list.sel(1) list.simps(3) ws_char_ws_does_not_peek_past_end ws_char_ws_has_result_c)
  subgoal for cs l
    apply (clarsimp simp add: NER_simps)
    subgoal for c
      apply auto
      subgoal by (smt (verit, best) append_same_eq append_self_conv dropWhile_eq_Nil_conv takeWhile_append1 takeWhile_dropWhile_id tl_append2)
      subgoal by (metis dropWhile_eq_Nil_conv hd_append2)
      subgoal by (smt (verit, best) append_same_eq append_self_conv dropWhile_append dropWhile_eq_Nil_conv list.sel(2) takeWhile_append1 takeWhile_dropWhile_id tl_append2)
      subgoal by (metis Nitpick.size_list_simp(2) dropWhile_append dropWhile_idem length_dropWhile_le length_pos_if_in_set lessI linorder_not_less)
      subgoal by (smt (verit, ccfv_threshold) Nitpick.size_list_simp(2) dropWhile_append dropWhile_idem hd_append2 length_dropWhile_le length_pos_if_in_set lessI linorder_not_less)
      done
    done
  subgoal for cs l l'
    apply (clarsimp simp add: NER_simps)
    subgoal for c'
      apply auto
      subgoal by (smt (verit, ccfv_threshold) Nil_is_append_conv append_self_conv2 dropWhile_append1 dropWhile_append2 dropWhile_hd_no_match list.distinct(1) list.sel(1) split_list_first tl_append2)
      subgoal by (metis dropWhile_eq_Nil_conv hd_append)
      subgoal by (metis \<open>\<And>l cs. \<lbrakk>ch \<notin> whitespace_chars; has_result (parse (ws_char_ws c)) (cs @ l) () l\<rbrakk> \<Longrightarrow> has_result (parse (ws_char_ws c)) cs () []\<close>
                        append_self_conv2 dropWhile.simps(1) dropWhile_append3 length_greater_0_conv length_pos_if_in_set list.sel(2) tl_append2 ws_char_ws_has_result)
      subgoal by (metis \<open>\<And>l cs. \<lbrakk>ch \<notin> whitespace_chars; has_result (parse (ws_char_ws c)) (cs @ l) () l\<rbrakk> \<Longrightarrow> has_result (parse (ws_char_ws c)) cs () []\<close>
                        dropWhile.simps(1) dropWhile_append3 hd_append2 length_greater_0_conv length_pos_if_in_set list.sel(2) ws_char_ws_has_result)
      done
    done
  done


section \<open>First printed/parsed char\<close>
lemma ws_char_ws_fpci[fpci_simps]:
  shows "first_printed_chari (print (ws_char_ws c)) i c' \<longleftrightarrow> c' = c"
  unfolding first_printed_chari_def
  by (auto simp add: ws_char_ws_p_has_result)

lemma ws_char_ws_fpc[fpc_simps]:
  "fpc (parse (ws_char_ws c)) i c' \<longleftrightarrow> c\<notin>whitespace_chars \<and> c' \<in> ({c} \<union> whitespace_chars)"
  unfolding fpc_def
  apply (cases \<open>c \<in> whitespace_chars\<close>)
  subgoal \<comment> \<open>c \<in> whitespace_chars means that there is never a result.\<close>
    using ws_char_ws_is_error[of c]
    apply clarsimp
    using has_result_implies_not_is_error by fast
  subgoal \<comment> \<open>c \<notin> whitespace_chars means that there can be a result.\<close>
    apply (cases \<open>c' \<in> whitespace_chars\<close>)
    subgoal
      apply clarsimp
      apply (rule exI[of _ \<open>[c]\<close>])
      apply (rule exI[of _ \<open>[c]\<close>]) \<comment> \<open>Using c as char that is not ws\<close>
      by (clarsimp simp add: NER_simps)
    subgoal
      apply (auto simp add: NER_simps)
      subgoal
        apply (rule exI[of _ \<open>'' ''\<close>])
        apply (rule exI[of _ \<open>[c]\<close>]) \<comment> \<open>Using c as char that is not ws\<close>
        by simp
      done
    done
  done



section \<open>chars_can_be_dropped\<close>
lemma ws_char_ws_chars_can_be_dropped:
  "chars_can_be_dropped (parse (ws_char_ws c)) whitespace_chars"
  unfolding chars_can_be_dropped_def
  by (clarsimp simp add: NER_simps)


section \<open>can drop past leftover\<close>
lemma ws_char_ws_can_drop_past_leftover:
  assumes "has_result (parse (ws_char_ws C)) (c @ l @ l') r (l @ l')"
  shows "has_result (parse (ws_char_ws C)) (c @ l) r (l)"
  using assms
  apply (cases l; clarsimp)
  subgoal
    apply (insert ws_char_ws_has_result_implies_leftover_head[of C \<open>c @ l'\<close> \<open>()\<close> l', simplified]; clarsimp split: list.splits)
    apply (clarsimp simp add: NER_simps; rule conjI)
    subgoal by (metis assms has_result_c_def ws_char_ws_has_result_c)
    subgoal
      apply (rule conjI)
      subgoal by (metis assms has_result_c_def ws_char_ws_has_result_c dropWhile_eq_Nil_conv)
      subgoal by (metis assms has_result_c_def ws_char_ws_has_result_c)
      done
    done
  subgoal for a l
    \<comment> \<open>now we know that a is not in whitespace so we anything after it is not affected by the dropwhile.\<close>
    apply (insert ws_char_ws_has_result_implies_leftover_head[of C \<open>c @ a # l @ l'\<close> \<open>()\<close> \<open>a # l @ l'\<close>, simplified]; clarsimp)
    apply (clarsimp simp add: NER_simps; rule conjI)
    subgoal by (metis assms does_not_consume_past_char3_def hd_dropWhile ws_char_ws_does_not_consume_past_char3 ws_char_ws_has_result)
    subgoal by (metis dropWhile_append3 hd_append2 list.sel(1) self_append_conv2)
    done
  done


lemma ws_char_ws_drop_input_on_error:
  assumes "is_error (parse (ws_char_ws C)) (i @ i')"
  shows " is_error (parse (ws_char_ws C)) i"
  using assms
  apply (clarsimp simp add: NER_simps)
  by (metis Cons_eq_appendI dropWhile_append dropWhile_eq_Nil_conv list.distinct(1))



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


lemma ws_char_ws_well_formed:
  assumes "c \<notin> whitespace_chars"
  shows "bidef_well_formed (ws_char_ws c)"
  unfolding ws_char_ws_def
  apply (auto intro!: b_then_well_formed first_printed_does_not_eat_into3
               intro: drop_well_formed
            simp add: assms 
                      fp_NER
                      many_ws_wf this_char_well_formed
                      this_char_does_not_consume_past_char3 then_fpci this_char_fpci
                      many_ws_no_consume_past)
  done


end
