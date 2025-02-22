theory example_dimacs
  imports all_definitions
begin

text \<open>
The Dimacs file for SAT solvers.
No support for comments. (Which are lines starting with c).
\<close>

definition DIMACS_header :: "(nat \<times> nat) bidef" where
  "DIMACS_header = then_drop_first (this_string ''p cnf '') (b_then nat_b (then_drop_first (this_char CHR '' '') nat_b (CHR '' ''))) ''p cnf ''"

lemma header_example:
  "has_result (parse DIMACS_header) ''p cnf 12 13'' (12, 13) []"
  apply (auto simp add: NER_simps DIMACS_header_def)
  subgoal by (rule parse_nat_s2[of \<open>''1''\<close> \<open>CHR ''2''\<close>, simplified])
  subgoal by (rule parse_nat_s2[of \<open>''1''\<close> \<open>CHR ''3''\<close>, simplified])
  done

lemma header_example_print:
  "p_has_result (print DIMACS_header) (12, 13) ''p cnf 12 13''"
  by (auto simp add: fp_NER DIMACS_header_def print_nat_def numeral_2_eq_2)


lemma header_pngi[PASI_PNGI_intros]:
  "PNGI (parse DIMACS_header)"
  unfolding DIMACS_header_def
  by pasi_pngi

lemma header_WF:
  "bidef_well_formed DIMACS_header"
  unfolding DIMACS_header_def
  by (auto intro!: then_drop_first_well_formed b_then_well_formed
         simp add: this_string_wf nat_b_well_formed this_char_well_formed NER_simps
                   pa_does_not_eat_into_pb_nondep_def fp_NER takeWhile_tail)

lemma header_wf_proof_for_thesis:
  "bidef_well_formed DIMACS_header"
  unfolding DIMACS_header_def
  apply (rule then_drop_first_well_formed)
  subgoal by (rule this_string_wf)
  subgoal
    apply (rule b_then_well_formed)
    subgoal by (rule nat_b_well_formed)
    subgoal
      apply (rule then_drop_first_well_formed)
      subgoal by (rule this_char_well_formed)
      subgoal by (rule nat_b_well_formed)
      subgoal
        unfolding pa_does_not_eat_into_pb_nondep_def
        apply (clarsimp simp add: fp_NER)
        by (clarsimp simp add: NER_simps)
      subgoal by (clarsimp simp add: NER_simps)
      done
    subgoal
      apply (rule first_printed_does_not_eat_into3)
      subgoal by (rule nat_b_well_formed)
      by (clarsimp simp add: fpci_simps print_empty nat_does_not_consume_past3)
    done
  subgoal
    apply (rule does_not_peek_past_end_implies_does_not_eat_into)
    subgoal by (rule this_string_does_not_peek_past_end)
    subgoal by (rule this_string_wf)
    done
  subgoal by (clarsimp simp add: NER_simps)
  done


lemma mono_header[partial_function_mono]:
  shows "mono_bd (\<lambda>f. DIMACS_header)"
  unfolding DIMACS_header_def
  by pf_mono_prover

lemma header_no_eat_into_newline:
  "pa_does_not_eat_into_pb_nondep DIMACS_header (this_char CHR ''\<newline>'')"
  unfolding pa_does_not_eat_into_pb_nondep_def
  by (auto simp add: NER_simps fp_NER DIMACS_header_def takeWhile_tail)

lemma header_does_not_consume_past_newline:
  "does_not_consume_past_char3 (parse DIMACS_header) CHR ''\<newline>''"
  unfolding DIMACS_header_def then_drop_first_def
  apply (rule transform_does_not_consume_past_char3)
  apply (rule then_does_not_consume_past3)
  subgoal by (rule this_string_wf)
  subgoal
    apply (auto intro!: b_then_well_formed transform_well_formed4
              simp add: nat_b_well_formed this_char_well_formed)
    subgoal by (clarsimp simp add: NER_simps well_formed_transform_funcs4_def)
    subgoal
      using does_not_peek_past_end_implies_does_not_eat_into[OF this_char_does_not_peek_past_end this_char_well_formed]
      by blast
    subgoal
      apply (rule first_printed_does_not_eat_into3; clarsimp?)
      subgoal by (rule nat_b_well_formed)
      subgoal by (clarsimp simp add: fpci_simps print_empty nat_does_not_consume_past3)
      done
    done
  subgoal
    apply (rule then_does_not_consume_past3)
    subgoal by (rule nat_b_well_formed)
    subgoal
      by (auto intro!: transform_well_formed4 b_then_well_formed
             simp add: nat_b_well_formed this_char_well_formed well_formed_transform_funcs4_def NER_simps
                       does_not_peek_past_end_implies_does_not_eat_into[OF this_char_does_not_peek_past_end])
    subgoal
      apply (rule transform_does_not_consume_past_char3)
      apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
      subgoal by (rule this_char_does_not_peek_past_end)
      subgoal by pasi_pngi
      subgoal using nat_does_not_consume_past3 by force
      subgoal by pasi_pngi
      done
    subgoal by (clarsimp simp add: fpc_def NER_simps nat_does_not_consume_past3)
    subgoal by (clarsimp simp add: NER_simps)
    done
  subgoal using this_string_no_consume_past_char3 by blast
  subgoal by (clarsimp simp add: NER_simps)
  done


definition DIMACS_line :: "int list bidef" where
  "DIMACS_line = separated_by1 int_b (this_char CHR '' '') (CHR '' '')"

lemma PNGI_line:
  "PNGI (parse DIMACS_line)"
  unfolding DIMACS_line_def
  by (auto intro!: separated_by1_PNGI then_PASI simp add: PASI_PNGI)

lemma fpci_DIMACS_line:
  "first_printed_chari (print DIMACS_line) i c \<Longrightarrow> c \<in> digit_chars \<or> c = CHR ''-''"
  by (clarsimp simp add: fpci_simps fp_NER separated_by1_def DIMACS_line_def split: if_splits list.splits)


lemma ex_result:
  "\<exists>ar al. (has_result (parse (this_char c)) i ar al \<and> P ar al)
    \<equiv>
   \<exists>al. (has_result (parse (this_char c)) i c al \<and> P c al)"
  by (clarsimp simp add: NER_simps)

lemma first_printed_char_of_many_this_char:
  assumes "p_has_result (print (many (b_then (this_char c) int_b))) pri (prt # prts)"
  shows "prt = c"
  using assms by (cases pri; clarsimp simp add: fp_NER)


lemma this_char_int_no_grown_by_many_this_char_int:
  "parse_result_cannot_be_grown_by_printer (parse (b_then (this_char CHR '' '') int_b)) (print (many (b_then (this_char CHR '' '') int_b)))"
  unfolding parse_result_cannot_be_grown_by_printer_def
  apply (auto simp add: NER_simps)
  subgoal for r l pri prt i
    apply (cases prt; clarsimp)
    subgoal for prt prts
      using first_printed_char_of_many_this_char[of \<open>CHR '' ''\<close> pri prt prts]
      apply (clarsimp simp add: NER_simps)
      apply (cases l; clarsimp simp add: NER_simps)
      subgoal by (metis append.right_neutral char_not_in_digit_chars(1) digit_chars_def
                        does_not_consume_past_char3_def int_b_does_not_consume_past_char3)

      subgoal for l' ls
        using int_b_leftover_no_start_with_digit[rule_format, of i r \<open>l'#ls\<close>]
        by (cases i; clarsimp simp add: NER_simps dropWhile_append3 takeWhile_tail split: if_splits)
      done
    done
  done


lemma line_WF_for_thesis:
  "bidef_well_formed DIMACS_line"
  unfolding DIMACS_line_def
  apply (rule separated_by1_well_formed)
  subgoal by (clarsimp simp add: fp_NER)
  subgoal by (rule int_b_well_formed)
  apply (rule b_then_well_formed)
  subgoal by (rule int_b_well_formed)
   apply (rule well_formed_does_not_grow_by_printer)
  subgoal by (rule this_char_int_no_grown_by_many_this_char_int)
     apply (rule b_then_well_formed)
  subgoal by (rule this_char_well_formed)
  subgoal by (rule int_b_well_formed)
  subgoal by (clarsimp simp add: fp_NER NER_simps pa_does_not_eat_into_pb_nondep_def)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by pasi_pngi
  apply (rule int_does_not_eat_into_if_first_char_not_digit)
  apply (clarsimp simp add: fpci_simps many_fpci fp_NER split: list.splits)
  done

\<comment> \<open>We're setting this up to create some example proof states.\<close>
lemma line_WF_section:
  "bidef_well_formed (many (b_then (this_char CHR '' '') int_b))"
  apply (rule wf_many_then)
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  subgoal sorry
  apply (clarsimp simp add: fpci_simps print_empty)
  apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
  
  oops

lemma line_WF_for_thesis_2:
  "bidef_well_formed DIMACS_line"
  unfolding DIMACS_line_def
  by (auto intro!: separated_by1_well_formed b_then_well_formed wf_many_then
                   int_does_not_eat_into_if_first_char_not_digit
                   then_does_not_consume_past_char_from_first_no_peek_past_end
         simp add: fp_NER NER_simps
                   int_b_well_formed this_char_well_formed
                   fpci_simps many_fpci
                   PASI_PNGI
                   this_char_does_not_consume_past_char3
                   this_char_does_not_peek_past_end
                   int_b_does_not_consume_past_char3
            split: list.splits if_splits)

lemma line_WF:
  "bidef_well_formed DIMACS_line"
  unfolding DIMACS_line_def
  apply (auto intro!: separated_by1_well_formed b_then_well_formed well_formed_does_not_grow_by_printer
                      int_does_not_eat_into_if_first_char_not_digit
            simp add: fp_NER NER_simps
                      int_b_well_formed this_char_well_formed
                      PASI_PNGI then_PASI
                      pa_does_not_eat_into_pb_nondep_def[of \<open>this_char CHR '' ''\<close>]
                      fpci_simps many_fpci
                      this_char_int_no_grown_by_many_this_char_int
               split: list.splits)
  done

lemma line_error_empty:
  "is_error (parse DIMACS_line) []"
  unfolding DIMACS_line_def by (clarsimp simp add: NER_simps)


lemma fpci_line[fpci_simps]:
  "first_printed_chari (print DIMACS_line) [] c \<longleftrightarrow> False"
  "first_printed_chari (print DIMACS_line) [e] c \<longleftrightarrow> first_printed_chari (print int_b) e c"
  "first_printed_chari (print DIMACS_line) (e#es) c \<longleftrightarrow> first_printed_chari (print int_b) e c"
  subgoal by (clarsimp simp add: DIMACS_line_def fpci_simps)
  subgoal by (auto simp add: DIMACS_line_def fpci_simps fp_NER)
  subgoal
    apply (auto simp add: DIMACS_line_def fpci_simps fp_NER)
    subgoal
      apply (induction es; clarsimp simp add: fp_NER)
      subgoal for n es es_pr
        apply (rule exI[of _ \<open>(THE t. p_has_result (print (b_then (this_char CHR '' '') int_b)) (CHR '' '', n) t)@es_pr\<close>])
        by (cases \<open>n < 0\<close>; clarsimp simp add: fp_NER)
      done
    subgoal
      apply (induction es; clarsimp simp add: fp_NER)
      subgoal for n es es_pr
        apply (rule exI[of _ \<open>(THE t. p_has_result (print (b_then (this_char CHR '' '') int_b)) (CHR '' '', n) t)@es_pr\<close>])
        by (cases \<open>n < 0\<close>; clarsimp simp add: fp_NER)
      done
    done
  done
    
lemma line_no_consume_past_newline:
  "does_not_consume_past_char3 (parse DIMACS_line) CHR ''\<newline>''"
  unfolding DIMACS_line_def does_not_consume_past_char3_def
  apply clarsimp
  subgoal for c r l
    apply (cases r) subgoal by (clarsimp simp add: NER_simps)
    subgoal for r1 rs
      apply (rule conjI)
      subgoal
        apply (clarsimp simp add: NER_simps)
        subgoal for l' spaces
          apply (rule exI[of _ \<open>list_upto l' l\<close>]; rule conjI)
          subgoal
            apply (insert many_PNGI[OF then_PASI, OF this_char_PASI, OF int_b_PASI, of \<open>CHR '' ''\<close>, unfolded PNGI_def, rule_format, of l' \<open>(zip spaces rs)\<close> l])
            apply clarsimp
            apply (subst list_upto_self[of _ l])
            using int_b_leftover_can_be_dropped_gen[of c l r1] by blast
          subgoal
            apply (rule exI[of _ spaces]; clarsimp)
            using many0_induct[of \<open>b_then (this_char CHR '' '') int_b\<close>, OF then_PASI, OF this_char_PASI, OF int_b_PASI,
                    of _ l' \<open>zip spaces rs\<close> l]

            apply (induction rs arbitrary: l' l spaces; clarsimp)
            subgoal by (clarsimp simp add: NER_simps)
            subgoal for r2 rs l' l spaces
              
            sorry
          done
        done
    oops


lemma line_no_consume_past_newline:
  "does_not_consume_past_char3 (parse DIMACS_line) CHR ''\<newline>''"
  unfolding DIMACS_line_def separated_by1_def
  apply (rule ftransform_does_not_consume_past_char3)
  apply (rule then_does_not_consume_past3_from_can_drop_leftover)
  subgoal by (rule int_b_well_formed)
  subgoal
    apply (rule wf_many_then; clarsimp?)
    subgoal by (rule int_b_well_formed)
    subgoal by (rule this_char_well_formed)
    subgoal using int_b_is_error(1) by blast
    subgoal using this_char_is_error(1) by blast
    subgoal by pasi_pngi
    subgoal by (rule this_char_does_not_consume_past_char3)
    subgoal for i i' c
      apply (clarsimp simp add: fpci_simps print_empty split: if_splits)
      apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
      subgoal by (rule this_char_does_not_peek_past_end)
      subgoal by pasi_pngi
      subgoal using int_b_does_not_consume_past_char3 by force
      subgoal by pasi_pngi
      done
    done
  subgoal
    apply (rule many_does_not_consume_past_char3)
    subgoal by pasi_pngi
    subgoal by pasi_pngi
    subgoal by (simp add: b_then_is_error_from_first this_char_is_error)
    subgoal by (simp add: b_then_is_error_from_first this_char_is_error)
    subgoal for c l l' r
      apply (rule then_can_drop_leftover[of _ _ c l l' r]; clarsimp?)
      subgoal by (rule this_char_drop_leftover)
      subgoal by pasi_pngi
      subgoal for c l l' r by (rule int_b_leftover_can_be_dropped_gen[of \<open>c@l\<close> l' r l, simplified])
      subgoal by pasi_pngi
      done
    subgoal
      apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
      subgoal by (rule this_char_does_not_peek_past_end)
      subgoal by pasi_pngi
      subgoal by (simp add: int_b_does_not_consume_past_char3)
      subgoal by pasi_pngi
      done
    subgoal for i c
      unfolding fpc_def
      apply (clarsimp simp add: NER_simps)
      subgoal premises prems \<comment> \<open>Ugly but it's the result of the NER rule\<close>
        apply (insert prems(2)[THEN sym]; clarsimp)
        apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
        subgoal by (rule this_char_does_not_peek_past_end)
        subgoal by pasi_pngi
        subgoal using int_b_does_not_consume_past_char3 by force
        subgoal by pasi_pngi
        done
      done
    done
  subgoal for i c
    apply (induction i; clarsimp simp add: fpc_def NER_simps)
    by (simp add: int_b_does_not_consume_past_char3)
  subgoal by (simp add: int_b_does_not_consume_past_char3)
  subgoal for c l l' r using int_b_leftover_can_be_dropped_gen[of \<open>c@l\<close> l' r l, simplified] by blast
  done


lemma line_no_consume_past_to_newline_then_line_no_consume_past:
  assumes "does_not_consume_past_char3 (parse DIMACS_line) CHR ''\<newline>''"
  shows "does_not_consume_past_char3 (parse (b_then (this_char CHR ''\<newline>'') DIMACS_line)) CHR ''\<newline>''"
  by (auto intro!: then_does_not_consume_past_char_from_first_no_peek_past_end
            simp add: this_char_does_not_peek_past_end this_char_PNGI PNGI_line assms)


\<comment> \<open>this gives us nvars, nclauses, clauses\<close>
definition DIMACS :: "((nat \<times> nat) \<times> int list list) bidef" where
  "DIMACS = b_then (then_drop_second DIMACS_header (this_char CHR ''\<newline>'') CHR ''\<newline>'')
                   (separated_by (this_char CHR ''\<newline>'') DIMACS_line CHR ''\<newline>'')"

lemma this_char_does_not_eat_into:
  "pa_does_not_eat_into_pb_nondep (this_char C) A"
  unfolding pa_does_not_eat_into_pb_nondep_def
  by (clarsimp simp add: NER_simps fp_NER)

lemma header_newline_no_eat_into_line:
  "pa_does_not_eat_into_pb_nondep
    (then_drop_second DIMACS_header (this_char CHR ''\<newline>'') CHR ''\<newline>'')
    (separated_by (this_char CHR ''\<newline>'') DIMACS_line CHR ''\<newline>'')"
  apply (rule does_not_peek_past_end_implies_does_not_eat_into)
  subgoal
    unfolding then_drop_second_def
    apply (rule transform_does_not_peek_past_end)
    apply (rule then_does_not_peek_past_end_from_fpc; clarsimp?)
    subgoal by (clarsimp simp add: this_char_fpc header_does_not_consume_past_newline)
    subgoal using this_char_no_result_consume_nothing by blast
    subgoal by pasi_pngi
    subgoal by (rule this_char_does_not_peek_past_end)
    subgoal by pasi_pngi
    done
  apply (rule then_drop_second_well_formed)
  subgoal by (rule header_WF)
  subgoal by (rule this_char_well_formed)
  subgoal by (rule header_no_eat_into_newline)
  subgoal by (clarsimp simp add: NER_simps)
  done



lemma DIMACS_wf_for_thesis:
  shows  "bidef_well_formed DIMACS"
  unfolding DIMACS_def
  supply [[goals_limit=20]]
  apply (auto intro!: b_then_well_formed then_drop_second_well_formed
                      separated_by_well_formed_no_consume_past_char
            simp add: NER_simps line_error_empty
                      header_WF this_char_well_formed line_WF
                      PASI_PNGI
                      good_separated_by_oracle_def
                      fpci_simps fp_NER
                      line_no_consume_past_newline                      
                      this_char_does_not_consume_past_char3
                      header_no_eat_into_newline
                      header_newline_no_eat_into_line
                      line_no_consume_past_to_newline_then_line_no_consume_past
               split: if_splits
  )
  
  oops


lemma DIMACS_wf:
  shows  "bidef_well_formed DIMACS"
  unfolding DIMACS_def
  apply (auto intro!: b_then_well_formed then_drop_second_well_formed separated_by_well_formed_no_consume_past_char
            simp add: header_WF this_char_well_formed NER_simps
                      header_no_eat_into_newline
                      good_separated_by_oracle_def fp_NER
                      line_WF
                      line_error_empty
                      this_char_PASI
                      this_char_does_not_consume_past_char3
                      fpci_simps
                      line_no_consume_past_newline
                      line_no_consume_past_to_newline_then_line_no_consume_past
                      header_newline_no_eat_into_line
                      )
  done




end