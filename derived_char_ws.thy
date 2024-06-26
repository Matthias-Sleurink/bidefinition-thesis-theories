theory derived_char_ws
  imports basic_definitions
          derived_this_char
          derived_then
          derived_many
          derived_whitespace_char
          derived_drop
begin

definition char_ws :: "char \<Rightarrow> unit bidef" where
  "char_ws c = drop (b_then (this_char c) (many whitespace_char)) (c, [])"



section NER
lemma char_ws_is_nonterm[NER_simps]:
  "is_nonterm (parse (char_ws c)) i \<longleftrightarrow> False"
  unfolding char_ws_def
  by (auto simp add: NER_simps whitespace_char_PASI)

lemma char_ws_is_error[NER_simps]:
  "is_error (parse (char_ws c)) i \<longleftrightarrow> (\<nexists>tl. i = c#tl)"
  apply (auto simp add: char_ws_def NER_simps)
  by (metis hd_Cons_tl)

lemma char_ws_has_result[NER_simps]:
  "has_result (parse (char_ws c)) i r l \<longleftrightarrow>
        r = ()
      \<and> (\<exists>ws. i = c#ws@l \<and> (\<forall>f\<in>set ws. f \<in> whitespace_chars))
      \<and> (case l of [] \<Rightarrow> True | (l'#ls) \<Rightarrow> l' \<notin> whitespace_chars)"
  apply (auto simp add: char_ws_def NER_simps whitespace_char_def any_from_set_def dropWhile_hd_no_match split: list.splits)
  subgoal by (metis dropWhile_eq_Nil_conv)
  subgoal by (metis dropWhile_eq_Nil_conv)
  subgoal by (metis set_takeWhileD takeWhile_dropWhile_id)
  subgoal by (metis dropWhile_eq_Cons_conv)
  done


lemma char_ws_has_result_implies_leftover_head:
  assumes "has_result (parse (char_ws c)) i r l"
  shows "case l of [] \<Rightarrow> True | (l'#ls) \<Rightarrow> l' \<notin> whitespace_chars"
  using assms[unfolded char_ws_has_result]
  by (clarsimp split: list.splits)

lemma char_ws_has_result_c[NER_simps]:
  "has_result_c (parse (char_ws c)) i r l \<longleftrightarrow>
        r = ()
      \<and> (\<exists>ws. i = c#ws \<and> (\<forall>f\<in>set ws. f \<in> whitespace_chars))
      \<and> (case l of [] \<Rightarrow> True | (l'#ls) \<Rightarrow> l' \<notin> whitespace_chars)"
  apply (auto simp add: char_ws_def has_result_c_def NER_simps whitespace_char_def any_from_set_def dropWhile_hd_no_match split: list.splits)
  subgoal by (metis dropWhile_eq_Nil_conv)
  subgoal by (metis dropWhile_eq_Nil_conv)
  subgoal by (metis append_Cons append_same_eq set_takeWhileD takeWhile_dropWhile_id)
  subgoal by (metis dropWhile_eq_self_iff dropWhile_idem list.distinct(1) list.sel(1))
  done



section \<open>fp NER\<close>
lemma char_ws_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (char_ws c)) i \<longleftrightarrow> False"
  by (clarsimp simp add: char_ws_def fp_NER)

lemma char_ws_p_is_error[fp_NER]:
  "p_is_error (print (char_ws c)) i \<longleftrightarrow> False"
  by (clarsimp simp add: char_ws_def fp_NER)

lemma char_ws_p_has_result[fp_NER]:
  "p_has_result (print (char_ws c)) i r \<longleftrightarrow> r = [c]"
  by (auto simp add: char_ws_def fp_NER)

lemma char_ws_print_empty[print_empty, fp_NER]:
  "p_has_result (print (char_ws c)) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: char_ws_p_has_result)



section \<open>PNGI, PASI\<close>
lemma char_ws_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse (char_ws c))"
  unfolding char_ws_def
  thm drop_PNGI
  by (simp add: char_ws_def drop_PNGI then_PNGI many_PNGI whitespace_char_PASI this_char_PNGI)

lemma char_ws_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse (char_ws c))"
  apply (subst char_ws_def)
  by pasi_pngi



section \<open>Does not peek past end\<close>
lemma char_ws_does_not_peek_past_end[peek_past_end_simps]:
  assumes "c \<notin> whitespace_chars"
  shows "\<not>does_not_peek_past_end (parse (char_ws c))"
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
lemma char_ws_does_not_consume_past_char3:
  assumes "c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3 (parse (char_ws c)) ch \<longleftrightarrow> ch \<notin> whitespace_chars"
  unfolding does_not_consume_past_char3_def
  apply (auto simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>'' ''\<close>]; clarsimp)
  subgoal by (rule exI[of _ \<open>''''\<close>]; clarsimp)
  done



section \<open>First printed/parsed char\<close>
lemma char_ws_fpci[fpci_simps]:
  shows "first_printed_chari (print (char_ws c)) i c' \<longleftrightarrow> c' = c"
  unfolding first_printed_chari_def
  by (auto simp add: char_ws_p_has_result)

lemma char_ws_fpc[fpc_simps]:
  "fpc (parse (char_ws c)) i c' \<longleftrightarrow> c' = c"
  unfolding fpc_def
  apply (auto simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>'' ''\<close>]; clarsimp)
  subgoal by (rule exI[of _ \<open>''''\<close>]; clarsimp)
  done



section \<open>chars_can_be_dropped\<close>
lemma char_ws_chars_can_be_dropped:
  "chars_can_be_dropped (parse (char_ws c)) S"
  unfolding chars_can_be_dropped_def
  oops \<comment> \<open>Not sure right now, but I believe that this can never be true.\<close>



section \<open>can drop past leftover\<close>
lemma char_ws_can_drop_past_lefover:
  assumes "has_result (parse (char_ws C)) (c @ l @ l') () (l @ l')"
  shows "has_result (parse (char_ws C)) (c @ l) () (l)"
  using assms
  apply (cases l; clarsimp)
  subgoal
    apply (insert char_ws_has_result_implies_leftover_head[of C \<open>c @ l'\<close> \<open>()\<close> l', simplified]; clarsimp split: list.splits)
    by (clarsimp simp add: NER_simps)
  subgoal for a l
    apply (insert char_ws_has_result_implies_leftover_head[of C \<open>c @ a # l @ l'\<close> \<open>()\<close> \<open>a # l @ l'\<close>, simplified]; clarsimp)
    by (clarsimp simp add: NER_simps)
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


lemma char_ws_well_formed:
  assumes "c \<notin> whitespace_chars"
  shows "bidef_well_formed (char_ws c)"
  unfolding char_ws_def
  apply (auto intro!: b_then_well_formed first_printed_does_not_eat_into3
               intro: drop_well_formed
            simp add: assms
                      fp_NER
                      many_ws_wf this_char_well_formed
                      this_char_does_not_consume_past_char3 this_char_fpci)
  done


end
