theory example_numberlist_comma
  imports all_definitions
begin

\<comment> \<open>If this is unit bd, which proofs become easuer?\<close>
definition separator where
  "separator = b_then (many whitespace_char) (b_then (this_char CHR '','') (many whitespace_char))"

lemma comma_not_whitespace[simp]:
  "CHR '','' \<notin> whitespace_chars"
  by (simp add: whitespace_chars_def)

lemma many_ws_wf:
  "bidef_well_formed (many whitespace_char)"
  by (clarsimp simp add: whitespace_char_def any_from_set_def many_char_for_predicate_well_formed)
lemma many_ws_no_consume_past:
  "does_not_consume_past_char2 (parse (many whitespace_char)) c \<longleftrightarrow> c \<notin> whitespace_chars"
  by (clarsimp simp add: whitespace_char_def any_from_set_def
                         many_char_for_predicate_does_not_consume_past_char)

lemma separator_wf:
  "bidef_well_formed separator"
  unfolding separator_def
  by (auto intro!: b_then_well_formed first_printed_does_not_eat_into
           simp add: many_ws_wf this_char_well_formed
                     this_char_does_not_consume_past_char2
                     fpci_simps print_empty
                     many_ws_no_consume_past)

lemma separator_fpci[fpci_simps]:
  assumes "first_printed_chari (print separator) i c"
  shows "c\<in>({CHR '',''} \<union> whitespace_chars)"
  using assms
  unfolding separator_def
  apply (clarsimp simp add: fpci_simps print_empty split: if_splits)
  subgoal for t
    unfolding whitespace_char_def any_from_set_def
    apply (subst (asm) many_char_for_predicate_fpci[of _ \<open>fst i\<close> c])
    by (clarsimp split: list.splits)
  done

lemma separator_print_empty[print_empty, fp_NER]:
  "p_has_result (print separator) i [] \<longleftrightarrow> False"
  unfolding separator_def
  by (clarsimp simp add: fp_NER)


\<comment> \<open>Note how the proof here would be easier if we had some specialised version for is_error P []\<close>
lemma separator_empty_input:
  "is_error (parse (separator)) []"
  unfolding separator_def
  by (clarsimp simp add: NER_simps whitespace_char_def any_from_set_def)
  
lemma PASI_separator:
  "PASI (parse separator)"
  unfolding separator_def
  apply (rule then_PASI_from_pngi_pasi)
  subgoal by (clarsimp simp add: many_PNGI whitespace_char_PASI)
  apply (rule then_PASI_from_pasi_pngi)
  subgoal by (rule this_char_PASI)
  subgoal by (clarsimp simp add: many_PNGI whitespace_char_PASI)
  done

lemma dropWhile_never_grows:
  "dropWhile P l'a = c # l'a \<longleftrightarrow> False"
  by (metis length_Cons length_dropWhile_le lessI linorder_not_less)

lemma hd_in_set_cannot_create_from_dropWhile:
  assumes "l \<noteq> []"
  assumes "hd l \<in> s"
  shows "\<nexists>l'. l = dropWhile (\<lambda>found. found \<in> s) l'"
  using assms
  apply (induction l; clarsimp)
  by (metis hd_dropWhile list.discI list.sel(1))

\<comment> \<open>We clearly need better combinators for dncpc\<close>
lemma separator_no_consume_past3:
  "does_not_consume_past_char3 (parse separator) c \<longleftrightarrow> c \<notin> whitespace_chars"
  unfolding does_not_consume_past_char3_def
            separator_def
  apply (auto simp add: NER_simps whitespace_char_def any_from_set_def)
  subgoal
    using hd_in_set_cannot_create_from_dropWhile[of _ whitespace_chars]
    apply clarsimp
    by (metis append.right_neutral comma_not_whitespace dropWhile_eq_self_iff dropWhile_never_grows list.sel(1) list.set_sel(1) set_append)
  subgoal by (metis (no_types, lifting) Cons_eq_appendI append_Nil2 append_same_eq dropWhile_takeWhile_same_predicate takeWhile_dropWhile_id)
  subgoal for cs x l l'
    apply (rule exI[of _ \<open>tl (dropWhile (\<lambda>found. found \<in> whitespace_chars) cs @ c # l')\<close>])
    apply auto
    subgoal
      by (metis (no_types, lifting) append_is_Nil_conv dropWhile_never_grows hd_append2 list.collapse list.sel(1) self_append_conv2)
    subgoal
      by (metis (no_types, lifting) append_same_eq dropWhile_never_grows list.sel(3) self_append_conv2 takeWhile_dropWhile_id takeWhile_idem takeWhile_tail tl_append2)
    subgoal
      by (metis (no_types, lifting) \<open>\<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) cs @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l = CHR '','' # l; x \<in> set cs\<rbrakk> \<Longrightarrow> takeWhile (\<lambda>found. found \<in> whitespace_chars) l = takeWhile (\<lambda>found. found \<in> whitespace_chars) (tl (dropWhile (\<lambda>found. found \<in> whitespace_chars) cs @ c # l'))\<close>
              append_same_eq dropWhile_never_grows list.sel(3) same_append_eq self_append_conv2 takeWhile_dropWhile_id tl_append2)
    done
  subgoal by (metis dropWhile_append2 dropWhile_idem dropWhile_never_grows takeWhile_append)
  subgoal by (metis (no_types, lifting) dropWhile_append2 dropWhile_never_grows set_takeWhileD takeWhile_dropWhile_id)
  subgoal by (metis (full_types, lifting) \<open>\<And>x l' ca. \<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) (ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = CHR '','' # l'; x \<in> set (dropWhile (\<lambda>found. found \<in> whitespace_chars) l')\<rbrakk> \<Longrightarrow> \<exists>x\<in>set ca. x \<notin> whitespace_chars\<close> \<open>\<And>x l' ca. \<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l' = CHR '','' # l'; x \<in> set ca\<rbrakk> \<Longrightarrow> \<exists>l'a. dropWhile (\<lambda>found. found \<in> whitespace_chars) ca = CHR '','' # l'a \<and> takeWhile (\<lambda>found. found \<in> whitespace_chars) l' = takeWhile (\<lambda>found. found \<in> whitespace_chars) l'a \<and> [] = dropWhile (\<lambda>found. found \<in> whitespace_chars) l'a\<close>
                                          dropWhile_append1)
  subgoal by (simp add: \<open>\<And>x l' ca. \<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) (ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = CHR '','' # l'; x \<in> set (dropWhile (\<lambda>found. found \<in> whitespace_chars) l')\<rbrakk> \<Longrightarrow> takeWhile (\<lambda>found. found \<in> whitespace_chars) (ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = takeWhile (\<lambda>found. found \<in> whitespace_chars) ca\<close>
                        takeWhile_tail)
  subgoal for cs x l l'
    apply (rule exI[of _ \<open>tl (dropWhile (\<lambda>found. found \<in> whitespace_chars) (cs @ c # l'))\<close>])
    apply auto
    subgoal
      by (metis \<open>\<And>x l' ca. \<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) (ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = CHR '','' # l'; x \<in> set (dropWhile (\<lambda>found. found \<in> whitespace_chars) l')\<rbrakk> \<Longrightarrow> \<exists>l'a. dropWhile (\<lambda>found. found \<in> whitespace_chars) ca = CHR '','' # l'a \<and> takeWhile (\<lambda>found. found \<in> whitespace_chars) l' = takeWhile (\<lambda>found. found \<in> whitespace_chars) l'a \<and> [] = dropWhile (\<lambda>found. found \<in> whitespace_chars) l'a\<close>
                Cons_eq_appendI dropWhile_append3 list.sel(3))
    subgoal
      by (metis \<open>\<And>x l' ca. \<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) (ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = CHR '','' # l'; x \<in> set (dropWhile (\<lambda>found. found \<in> whitespace_chars) l')\<rbrakk> \<Longrightarrow> \<exists>l'a. dropWhile (\<lambda>found. found \<in> whitespace_chars) ca = CHR '','' # l'a \<and> takeWhile (\<lambda>found. found \<in> whitespace_chars) l' = takeWhile (\<lambda>found. found \<in> whitespace_chars) l'a \<and> [] = dropWhile (\<lambda>found. found \<in> whitespace_chars) l'a\<close>
                Cons_eq_appendI dropWhile_append3 list.sel(3) takeWhile_tail)
    subgoal
      by (smt (verit, ccfv_threshold) \<open>\<And>x l' ca. \<lbrakk>c \<notin> whitespace_chars; x \<notin> whitespace_chars; dropWhile (\<lambda>found. found \<in> whitespace_chars) (ca @ dropWhile (\<lambda>found. found \<in> whitespace_chars) l') = CHR '','' # l'; x \<in> set (dropWhile (\<lambda>found. found \<in> whitespace_chars) l')\<rbrakk> \<Longrightarrow> \<exists>l'a. dropWhile (\<lambda>found. found \<in> whitespace_chars) ca = CHR '','' # l'a \<and> takeWhile (\<lambda>found. found \<in> whitespace_chars) l' = takeWhile (\<lambda>found. found \<in> whitespace_chars) l'a \<and> [] = dropWhile (\<lambda>found. found \<in> whitespace_chars) l'a\<close>
              dropWhile_append dropWhile_eq_Nil_conv dropWhile_eq_self_iff dropWhile_never_grows list.sel(1) list.sel(3) tl_append2)
    done
  done


lemma many_ws_has_result:
  "has_result (parse (many whitespace_char)) i r l \<longleftrightarrow> r = takeWhile (\<lambda>c. c\<in>whitespace_chars) i \<and> l = dropWhile (\<lambda>c. c\<in>whitespace_chars) i"
  unfolding whitespace_char_def any_from_set_def
  by (rule many_char_for_predicate_has_result)

lemma separator_has_result[NER_simps]:
  "has_result (parse separator) i (w1, s, w2) l \<longleftrightarrow> 
    w1 = takeWhile (\<lambda>c. c\<in>whitespace_chars) i \<and>
    dropWhile (\<lambda>c. c\<in>whitespace_chars) i = CHR '','' # (tl (dropWhile (\<lambda>c. c\<in>whitespace_chars) i)) \<and>
    s  = CHR '','' \<and>
    w2 = takeWhile (\<lambda>c. c\<in>whitespace_chars) (tl (dropWhile (\<lambda>c. c\<in>whitespace_chars) i)) \<and>
    i \<noteq> [] \<and>
    l = dropWhile (\<lambda>c. c\<in>whitespace_chars) (tl (dropWhile (\<lambda>c. c\<in>whitespace_chars) i))"
  unfolding separator_def
  apply (auto simp add: NER_simps many_ws_has_result)
  using list.discI by fastforce



definition numberlist :: "nat list bidef" where
  "numberlist = separated_by separator nat_b ([], CHR '','', [])"

lemma numberlist_results:
  "has_result (parse numberlist) ''''       []       ''''"
  "has_result (parse numberlist) '' ''      []       '' ''"
  "has_result (parse numberlist) ''1''      [1]      ''''"
  "has_result (parse numberlist) ''1 ''     [1]      '' ''"
  "has_result (parse numberlist) ''1,2''    [1, 2]   ''''"
  "has_result (parse numberlist) ''1 ,2''   [1, 2]   ''''"
  "has_result (parse numberlist) ''1 , 2''  [1, 2]   ''''"
  "has_result (parse numberlist) ''1, 12''  [1, 12]  ''''"
  "has_result (parse numberlist) ''13, 12'' [13, 12] ''''"
  by eval+

lemma good_oracle:
  "good_separated_by_oracle separator ([], CHR '','', [])"
  unfolding good_separated_by_oracle_def
  by (auto simp add: fp_NER separator_def)

lemma ws_not_digit:
  assumes "c \<in> whitespace_chars"
  shows "c \<notin> derived_digit_char.digit_chars"
        "c \<notin> digit_chars"
  using assms
  unfolding whitespace_chars_def derived_digit_char.digit_chars_def
  by fast+

lemma comma_not_digit:
  "CHR '','' \<notin> derived_digit_char.digit_chars"
  "CHR '','' \<notin> meta_digit_to_nat_and_back.digit_chars"
  unfolding derived_digit_char.digit_chars_def
  by fastforce+


lemma takeWhileAllNot:
  assumes "\<forall>a \<in> set as. \<not>P a"
  shows "takeWhile P as = []"
  using assms
  by (metis list.set_sel(1) takeWhile_eq_Nil_iff)

lemma no_space_in_nat:
  "\<forall>a\<in>set (print_nat n). a \<notin> whitespace_chars"
  using digit_char_p_is_error digit_char_p_no_error ws_not_digit(1)
  by blast

lemma no_space_hd_nat:
  "hd (print_nat n) \<notin> whitespace_chars"
  using ws_not_digit(2) by fastforce

lemma lst_eq_c_tl_lst:
  "l = c#(tl l) \<Longrightarrow> hd l = c"
  by (metis list.sel(1))

lemma takeWhile_not_empty:
  assumes "takeWhile P l \<noteq> []"
  shows "P (hd l)"
  using assms
  by (induction l; clarsimp split: if_splits)




lemma numberlist_comma_well_formed:
  "bidef_well_formed numberlist"
  unfolding numberlist_def 
  apply (auto intro!: separated_by_well_formed_no_consume_past_char
              simp add: good_oracle nat_b_well_formed separator_wf
                        nat_is_error separator_empty_input
                        nat_b_PASI)
  subgoal for i c
    using separator_no_consume_past3 nat_fpci ws_not_digit(1)
    by force
  subgoal for w1 s w2 c
    using separator_fpci nat_does_not_consume_past3
          comma_not_digit(1) ws_not_digit(1)
    by fastforce
  subgoal for w1 s w2 n c
    \<comment> \<open>Why does this not unfold separator_fpci?\<close>
    apply (clarsimp simp add: fpci_simps print_empty)
    using separator_fpci[of \<open>(w1, s, w2)\<close> c]
    apply (auto intro!: then_does_not_consume_past3
                simp add: separator_wf nat_b_well_formed
                          nat_does_not_consume_past3
                          comma_not_digit(1) ws_not_digit(1)
                          separator_no_consume_past3
                          fpc_def NER_simps)
    done
  done


end
