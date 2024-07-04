theory derived_this_string
  imports basic_definitions
          derived_this_char
begin

definition this_string :: "char list \<Rightarrow> char list bidef" where
  "this_string = m_map this_char"


\<comment> \<open>NER\<close>
lemma this_string_is_nonterm[NER_simps]:
  "is_nonterm (parse (this_string s)) i \<longleftrightarrow> False"
  unfolding this_string_def m_map_def
  by (simp add: this_char_is_nonterm mmap_not_nonterm_if_param_never_nonterm)

lemma this_string_is_error[NER_simps]:
  "is_error (parse (this_string [])) i \<longleftrightarrow> False"
  "is_error (parse (this_string (c#cs))) i \<longleftrightarrow> i = [] \<or> (hd i \<noteq> c \<or> is_error (parse (this_string cs)) (tl i))"
  unfolding this_string_def
  subgoal by (simp add: NER_simps)
  apply (subst m_map_is_error)
  using this_char_has_result this_char_is_error by fastforce

lemma this_string_has_result[NER_simps]:
  "has_result (parse (this_string s)) i r l \<longleftrightarrow> s = r \<and> i = r@l"
  unfolding this_string_def
  apply (induction s arbitrary: i r l)
  by (auto simp add: NER_simps)

lemma this_string_has_result_ci[NER_simps]:
  "has_result_ci (parse (this_string s)) i c r l \<longleftrightarrow> r=s \<and> r@l=i \<and> c=s"
  unfolding has_result_ci_def has_result_c_def
  by (auto simp add: NER_simps)



\<comment> \<open>FP ner\<close>
lemma this_string_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (this_string s)) i \<longleftrightarrow> False"
  unfolding this_string_def
  apply (induction s arbitrary: i)
  by (auto simp add: fp_NER)

lemma this_string_p_is_error[fp_NER]:
  "p_is_error (print (this_string s)) i \<longleftrightarrow> s \<noteq> i"
  unfolding this_string_def
  apply (induction s arbitrary: i)
  subgoal by (auto simp add: fp_NER)
  apply (auto simp add: fp_NER)
  by (metis one_char_parser.cases)

lemma this_string_p_has_result[fp_NER]:
  "p_has_result (print (this_string s)) i r \<longleftrightarrow> r = s \<and> i = s"
  unfolding this_string_def
  apply (induction s arbitrary: i r)
  by (auto simp add: fp_NER)

lemma this_string_print_empty[print_empty, fp_NER]:
  "p_has_result (print (this_string c)) i [] \<longleftrightarrow> c = [] \<and> i = []"
  by (cases c; clarsimp simp add: this_string_def fp_NER)



\<comment> \<open>PASI, PNGI\<close>
lemma this_string_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse (this_string s))"
  by (simp add: this_string_def this_char_PNGI PNGI_m_map)

lemma this_string_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "s \<noteq> [] \<Longrightarrow> PASI (parse (this_string s))"
  by (simp add: this_string_def this_char_PASI PASI_m_map)



\<comment> \<open>Does not peek past end\<close>
lemma this_string_does_not_peek_past_end[peek_past_end_simps]:
  "does_not_peek_past_end (parse (this_string s))"
  unfolding this_string_def
  by (clarsimp simp add: peek_past_end_simps this_char_PNGI)



\<comment> \<open>Drop leftover\<close>
lemma this_string_drop_leftover:
  shows "has_result (parse (this_string s)) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse (this_string s)) (c @ l) r l"
  using this_string_does_not_peek_past_end[unfolded does_not_peek_past_end_def]
  by blast


lemma this_string_drop_leftover_on_error:
  shows "is_error (parse (this_string s)) (c @ l @ l')
            \<Longrightarrow> is_error (parse (this_string s)) (c @ l)"
  apply (induction s; auto simp add: NER_simps)
  subgoal by (cases c; cases l; clarsimp)
  subgoal by (cases c; cases l; clarsimp)
  subgoal for s
    apply (cases c; clarsimp)
    subgoal for c' cs
      apply (insert has_result_exhaust(1)[of \<open>parse (this_string s)\<close> \<open>cs@l\<close>]
                    this_string_is_nonterm[of s \<open>cs@l\<close>, simplified]; clarsimp)
      subgoal for r x
        apply (insert this_string_PNGI[of s, unfolded PNGI_def, rule_format, of \<open>cs@l\<close> r x]; clarsimp)
        subgoal for cr
          apply (insert this_string_does_not_peek_past_end[of s, unfolded does_not_peek_past_end_def, rule_format, of cr x r \<open>x@l'\<close>]; clarsimp)
          apply (insert has_result_implies_not_is_error[of \<open>parse (this_string s)\<close> \<open>cr@x@l'\<close> r \<open>x@l'\<close>]; clarsimp)
          by (metis append.assoc)
        done
      done
    done
  subgoal for s
    apply (cases c; cases l; clarsimp)
    subgoal for l'' ls
      apply (insert has_result_exhaust(1)[of \<open>parse (this_string s)\<close> ls]
                    this_string_is_nonterm[of s ls, simplified]; clarsimp)
      subgoal for rs lls
        apply (insert this_string_PNGI[of s, unfolded PNGI_def, rule_format, of ls rs lls]; clarsimp)
        subgoal for cs
          apply (insert this_string_does_not_peek_past_end[of s, unfolded does_not_peek_past_end_def, rule_format, of cs lls rs \<open>lls@l'\<close>]; clarsimp)
          by (insert has_result_implies_not_is_error[of \<open>parse (this_string s)\<close> \<open>cs@lls@l'\<close> rs \<open>lls@l'\<close>]; clarsimp)
        done
      done
    subgoal for c' cs l'' ls
      apply (insert has_result_exhaust(1)[of \<open>parse (this_string s)\<close> \<open>cs @ l'' # ls\<close>]
                    this_string_is_nonterm[of s \<open>cs @ l'' # ls\<close>, simplified]; clarsimp)
      subgoal for rs lls
        apply (insert this_string_PNGI[of s, unfolded PNGI_def, rule_format, of \<open>cs@l''#ls\<close> rs lls]; clarsimp)
        subgoal for conss
          apply (insert this_string_does_not_peek_past_end[of s, unfolded does_not_peek_past_end_def, rule_format, of conss lls rs \<open>lls@l'\<close>]; clarsimp)
          apply (insert has_result_implies_not_is_error[of \<open>parse (this_string s)\<close> \<open>conss@lls@l'\<close> rs \<open>lls@l'\<close>]; clarsimp)
          by (metis append.assoc append_Cons)
        done
      done
    done
  done



\<comment> \<open>First printed char\<close>
lemma this_string_fpci[fpci_simps]:
  "first_printed_chari (print (this_string s)) i c \<longleftrightarrow> s\<noteq>[] \<and> i = s \<and> c = (hd s)"
  apply (cases s; auto simp add: this_string_def fpci_simps fp_NER)
  subgoal by (metis first_printed_chari_def this_string_def this_string_p_has_result)
  subgoal by (metis first_printed_chari_def this_string_def this_string_p_has_result list.sel(1))
  subgoal using this_string_def this_string_p_has_result by presburger
  done



\<comment> \<open>First Parsed Char\<close>
lemma fpc_this_string[fpc_simps]:
  "fpc (parse (this_string (sc#s))) i c \<Longrightarrow> c = sc"
  by (clarsimp simp add: fpc_def NER_simps)



\<comment> \<open>Well formed\<close>
lemma this_string_wf:
  "bidef_well_formed (this_string s)"
  apply wf_init
  subgoal by (rule this_string_PNGI)
  subgoal by (auto simp add: parser_can_parse_print_result_def fp_NER NER_simps)
  subgoal by (auto simp add: printer_can_print_parse_result_def fp_NER NER_simps)
  done



end
