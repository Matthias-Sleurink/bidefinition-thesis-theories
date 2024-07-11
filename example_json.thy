theory example_json
  imports
    all_definitions
begin


\<comment> \<open>Try s, if fail, do a.
           if succeed, stop\<close>
definition until :: "'a bidef \<Rightarrow> 'b bidef \<Rightarrow> 'a list bidef" where
  "until a s = many (ftransform (\<lambda>Inl l \<Rightarrow> None | Inr r \<Rightarrow> Some r) (Some o Inr) (or s a))"

lemma PNGI_until[PASI_PNGI_intros]:
  assumes "PASI (parse A)"
  assumes "PASI (parse B)"
  shows "PNGI (parse (until A B))"
  unfolding until_def apply (insert assms)
  by pasi_pngi


abbreviation "quot_chr \<equiv> CHR ''\"''"
definition quot :: "char bidef" where
  "quot = this_char quot_chr"
lemma quot_PASI_PNGI[PASI_PNGI_intros]:
  "PNGI (parse quot)"
  "PASI (parse quot)"
  unfolding quot_def by pasi_pngi+


definition end_str where "end_str = until one_char (quot)"
lemma until_examples:
  "has_result (parse end_str) ''apples'' ''apples'' []" \<comment> \<open>Perhaps somewhat unfortunate, could be solvable if we choose to also consume the stopper.\<close>
  "has_result (parse end_str) ''\"apples'' '''' ''\"apples''"
  "has_result (parse end_str) ''apple\"s'' ''apple'' ''\"s''"
  by eval+

definition takeMiddle :: "'a bidef \<Rightarrow> 'b bidef \<Rightarrow> 'c bidef \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'b bidef" where
  "takeMiddle ab bb cb a c = transform
                              (fst o snd)
                              (\<lambda>b. (a, b, c))
                              (b_then ab (b_then bb cb))"

lemma PNGI_takeMiddle[PASI_PNGI_intros]:
  assumes "PNGI (parse A)"
  assumes "PNGI (parse B)"
  assumes "PNGI (parse C)"
  shows "PNGI (parse (takeMiddle A B C a c))"
  unfolding takeMiddle_def apply (insert assms)
  by pasi_pngi

lemma PASI_takeMiddle[PASI_PNGI_intros]: \<comment> \<open>Probably the most common usage, where the outer ones are a mandatory character.\<close>
  assumes "PASI (parse A)"
  assumes "PNGI (parse B)"
  assumes "PNGI (parse C)"
  shows "PASI (parse (takeMiddle A B C a c))"
  unfolding takeMiddle_def apply (insert assms)
  by pasi_pngi



lemma mono_takeMiddle[partial_function_mono]:
  assumes ma: "mono_bd A"
  assumes mb: "mono_bd B"
  assumes mc: "mono_bd C"
  shows "mono_bd (\<lambda>f. takeMiddle (A f) (B f) (C f) a c)"
  unfolding takeMiddle_def using ma mb mc
  by pf_mono_prover


datatype JSON
  = String "string"
  | Number "int"
  | Object "(string \<times> JSON) list"
  | List "JSON list"
  | JTrue
  | JFalse
  | JNull


definition str_literal :: "string bidef" where
  "str_literal = takeMiddle quot ((many (char_not_in_set {quot_chr}))) quot quot_chr quot_chr"
value "has_result (parse str_literal) ''\"apples\"'' ''apples'' []"
value "is_error (parse str_literal) ''apples\"''"
value "is_error (parse str_literal) ''\"apples''"
value "is_error (parse str_literal) ''\"''"


lemma str_literal_has_result[NER_simps]:
  "has_result (parse str_literal) [] r l \<longleftrightarrow> False"
  "has_result (parse str_literal) i r i \<longleftrightarrow> False"
  apply (auto simp add: NER_simps str_literal_def takeMiddle_def quot_def char_not_in_set_def)
  by (metis Cons_eq_appendI list.simps(3) self_append_conv2 takeWhile_dropWhile_id)

lemma str_literal_first_char:
  "has_result (parse str_literal) (c # cs) r l \<Longrightarrow> c = quot_chr"
  by (clarsimp simp add: NER_simps str_literal_def takeMiddle_def quot_def)

lemma is_error_str_literal[NER_simps]:
  "is_error (parse str_literal) []"
  "c \<noteq> quot_chr \<Longrightarrow> is_error (parse str_literal) (c # l)"
  by (clarsimp simp add: str_literal_def NER_simps takeMiddle_def quot_def)+

lemma is_error_str_literal2[NER_simps]:
  "is_error (parse str_literal) (i#is) \<longleftrightarrow> i \<noteq> quot_chr \<or> is = [] \<or> (is \<noteq> [] \<and> dropWhile (\<lambda>c. c \<noteq> quot_chr) is = [])"
  apply (auto simp add: str_literal_def NER_simps takeMiddle_def quot_def char_not_in_set_def)
  apply (induction \<open>is\<close>; clarsimp)
  apply (auto split: if_splits)
  by fastforce

lemma str_literal_is_nonterm[NER_simps]:
  "is_nonterm (parse str_literal) i \<longleftrightarrow> False"
  by (clarsimp simp add: str_literal_def takeMiddle_def quot_def NER_simps char_not_in_set_PASI)


lemma str_literal_print_empty[fp_NER, print_empty]:
  "p_has_result (print (str_literal)) i [] \<longleftrightarrow> False"
  unfolding str_literal_def
  by (clarsimp simp add: print_empty takeMiddle_def quot_def)

lemma PNGI_str_literal[PASI_PNGI_intros]:
  shows "PNGI (parse str_literal)"
  unfolding str_literal_def
  by pasi_pngi
lemma PASI_str_literal[PASI_PNGI_intros]:
  shows "PASI (parse str_literal)"
  unfolding str_literal_def takeMiddle_def
  by pasi_pngi

lemma fpci_str_literal[fpci_simps]:
  "first_printed_chari (print str_literal) t c \<Longrightarrow> c = quot_chr"
  by (clarsimp simp add: str_literal_def fpci_simps takeMiddle_def print_empty quot_def split: if_splits)

lemma fpc_str_literal[fpc_simps]:
  "fpc (parse str_literal) a c \<Longrightarrow> c = quot_chr"
  apply (clarsimp simp add: str_literal_def fpc_simps takeMiddle_def)
  by (clarsimp simp add: fpc_def NER_simps quot_def)

lemma str_literal_drop_input_on_error:
  "is_error (parse str_literal) (i @ i') \<Longrightarrow> is_error (parse str_literal) i"
  apply (clarsimp simp add: str_literal_def takeMiddle_def)
  apply (rule transform_drop_input_leftover_on_error; assumption?)
  apply (rule then_can_drop_leftover_on_error; assumption?; clarsimp?)
  subgoal
    apply (clarsimp simp add: quot_def)
    by (rule this_char_drop_leftover_on_error)
  subgoal by pasi_pngi
  subgoal by (clarsimp simp add: NER_simps quot_def)
  subgoal by (cases \<open>i\<close>; clarsimp simp add: NER_simps quot_def)
  subgoal unfolding quot_def by (rule this_char_drop_leftover)
  subgoal for i2 i2'
    apply (rule then_can_drop_leftover_on_error; assumption?; clarsimp?)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by pasi_pngi
    subgoal
      using many_not_nonterm_when_base_not_nonterm[of \<open>char_not_in_set {quot_chr}\<close> i2, OF _ char_not_in_set_PASI]
            char_not_in_set_is_nonterm
      by blast
    subgoal by (clarsimp simp add: NER_simps char_not_in_set_def quot_def)
    subgoal for c2 l2 l2' r2
      apply (clarsimp simp add: NER_simps char_not_in_set_def quot_def; rule conjI)
      subgoal by (smt (verit, best) append_is_Nil_conv hd_dropWhile takeWhile_append takeWhile_eq_all_conv takeWhile_hd_no_match)
      subgoal by (smt (verit, best) append_is_Nil_conv dropWhile_append dropWhile_eq_self_iff hd_append2 self_append_conv2)
      done
    subgoal unfolding quot_def by (rule this_char_drop_leftover_on_error)
    done
  done

lemma str_literal_error_if_take_from_c:
  assumes take_no_empty: "i' \<noteq> []"
  assumes result: "has_result (parse str_literal) (i @ i' @ l) r l"
  shows "is_error (parse str_literal) i"
  using assms
  apply (clarsimp simp add: NER_simps str_literal_def takeMiddle_def quot_def char_not_in_set_def)
  subgoal for l'
    apply (rule exI[of _ \<open>tl i\<close>]; rule conjI; clarsimp?)
    subgoal using list.collapse by force
    subgoal by (smt (verit, ccfv_SIG) append.assoc append_is_Nil_conv dropWhile_append1 dropWhile_eq_Nil_conv list.sel(3) self_append_conv2 tl_append2)
    done
  done


lemma str_literal_well_formed:
  "bidef_well_formed str_literal"
  unfolding str_literal_def takeMiddle_def
  apply (rule transform_well_formed4)
  subgoal by (clarsimp simp add: well_formed_transform_funcs4_def NER_simps quot_def)
  apply (rule b_then_well_formed_does_not_peek_past)
  subgoal by (clarsimp simp add: quot_def this_char_well_formed)
  subgoal
    apply (rule b_then_well_formed)
    subgoal unfolding char_not_in_set_def by (rule many_char_for_predicate_well_formed)
    subgoal by (clarsimp simp add: quot_def this_char_well_formed)
    subgoal
      apply (rule first_printed_does_not_eat_into3; clarsimp?)
      subgoal
        unfolding char_not_in_set_def
        by (rule many_char_for_predicate_well_formed)
      subgoal
        by (clarsimp simp add: fpci_simps quot_def char_not_in_set_def many_char_for_predicate_does_not_consume_past_char3)
      done
    done
  subgoal unfolding quot_def by (rule this_char_does_not_peek_past_end)
  done

lemma t:
  assumes A_pngi: "PNGI (parse A)"
  assumes B_pngi: "PNGI (parse B)"
  assumes B_fpc_dncpcA: "\<And>i c. fpc (parse B) i c \<Longrightarrow> does_not_consume_past_char3 (parse A) c"
  assumes B_dncpc: "does_not_peek_past_end (parse B)"
  shows "does_not_peek_past_end (parse (b_then A B))"
  apply (clarsimp simp add: does_not_peek_past_end_def NER_simps)
  \<comment> \<open>Worth a try in the future\<close>
  oops

lemma dropWhile_cons_l_eq_char_cons_l:
  "dropWhile (\<lambda>found. found \<noteq> chr) (l @ l') = chr # l' \<Longrightarrow> (\<exists>ls. l = ls@[chr])"
  apply (induction l; clarsimp)
  subgoal by (clarsimp simp add: length_dropWhile_le[of _ l'] impossible_Cons)
  subgoal by (clarsimp split: if_splits)
  done

lemma str_literal_no_peek_past_end:
  "does_not_peek_past_end (parse str_literal)"
  unfolding str_literal_def takeMiddle_def
  apply (rule transform_does_not_peek_past_end)
  apply (rule then_does_not_peek_past_end)
  subgoal by (clarsimp simp add: quot_def this_char_does_not_peek_past_end)
  subgoal by pasi_pngi
  subgoal
    apply (clarsimp simp add: does_not_peek_past_end_def)
    subgoal for c a b l l'
      apply (insert dropWhile_cons_l_eq_char_cons_l[of quot_chr c l])
      by (auto simp add: NER_simps char_not_in_set_def quot_def takeWhile_tail dropWhile_append3)
    done
  subgoal by pasi_pngi
  done

lemma str_literal_can_drop_leftover:
  assumes "has_result (parse str_literal) (c @ l @ l') r (l @ l')"
  shows "has_result (parse str_literal) (c @ l) r l"
  apply (insert assms)
  using str_literal_no_peek_past_end[unfolded does_not_peek_past_end_def]
  by fast



definition JsonString :: "JSON bidef" where
  "JsonString = ftransform
                 (Some o String)
                 (\<lambda>String s \<Rightarrow> Some s
                  | _ \<Rightarrow> None)
                 str_literal"

lemma has_result_JsonString[NER_simps]:
  "has_result (parse (JsonString)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i (String str) l \<longleftrightarrow> has_result (parse str_literal) i str l"
  "has_result (parse (JsonString)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i JNull l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i r i \<longleftrightarrow> False"
  by (clarsimp simp add: JsonString_def NER_simps)+

lemma JsonString_first_char_result:
  "has_result (parse (JsonString)) (c # cs) r l \<Longrightarrow> c = quot_chr"
  by (clarsimp simp add: NER_simps JsonString_def str_literal_first_char)

lemma is_error_JsonString[NER_simps]:
  "is_error (parse (JsonString)) []"
  "c \<noteq> quot_chr \<Longrightarrow> is_error (parse JsonString) (c # i)"
  by (clarsimp simp add: JsonString_def NER_simps str_literal_def takeMiddle_def quot_def)+


lemma JsonString_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonString)) i [] \<longleftrightarrow> False"
  unfolding JsonString_def
  by (clarsimp simp add: print_empty)

lemma PASI_PNGI_JsonString[PASI_PNGI_intros]:
  shows "PASI (parse JsonString)"
        "PNGI (parse JsonString)"
  unfolding JsonString_def
  by pasi_pngi+

lemma fpc_JsonString[fpc_simps]:
  "fpc (parse JsonString) a c \<Longrightarrow> c = quot_chr"
  by (clarsimp simp add: JsonString_def fpc_simps)

lemma JsonString_drop_leftover_on_error:
  assumes "is_error (parse JsonString) (c @ l)"
  shows "is_error (parse JsonString) c"
  by (cases c; insert assms; auto simp add: NER_simps JsonString_def)

lemma JsonString_drop_leftover_on_error2:
  assumes "is_error (parse JsonString) (c @ l @ l')"
  shows "is_error (parse JsonString) (c @ l)"
  by (cases c; insert assms; auto simp add: NER_simps JsonString_def; cases l; auto simp add: NER_simps)

lemma JsonString_no_peek_past_end:
  "does_not_peek_past_end (parse JsonString)"
  unfolding JsonString_def
  apply (rule ftrans_does_not_peek_past_end)
  by (rule str_literal_no_peek_past_end)

lemma JsonString_no_consume_past_any_char:
  "does_not_consume_past_char3 (parse JsonString) c"
  using does_not_consume_past_any_char3_eq_not_peek_past_end[of \<open>parse JsonString\<close>]
        JsonString_no_peek_past_end
  by blast

lemma JsonString_drop_leftover:
  shows "has_result (parse JsonString) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse JsonString) (c @ l) r l"
  using JsonString_no_peek_past_end[unfolded does_not_peek_past_end_def] by blast


lemma JsonString_well_formed:
  "bidef_well_formed JsonString"
  unfolding JsonString_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def ftransform_p_has_result split: JSON.splits)
  subgoal by (rule str_literal_well_formed)
  done



definition JsonNumber :: "JSON bidef" where
  "JsonNumber = ftransform
                 (Some o Number)
                 (\<lambda>Number n \<Rightarrow> Some n
                  | _ \<Rightarrow> None)
                 int_b"

lemma has_result_JsonNumber[NER_simps]:
  "has_result (parse (JsonNumber)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i (Number n) l \<longleftrightarrow> has_result (parse int_b) i n l"
  "has_result (parse (JsonNumber)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i JNull l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i r i \<longleftrightarrow> False"
  by (clarsimp simp add: JsonNumber_def NER_simps)+

lemma JsonNumber_first_char_result:
  "has_result (parse (JsonNumber)) (c # cs) r l \<Longrightarrow> c = CHR ''-'' \<or> c \<in> digit_chars"
  by (cases r; clarsimp simp add: NER_simps split: if_splits)

lemma is_error_JsonNumber[NER_simps]:
  "is_error (parse (JsonNumber)) []"
  "c \<notin> ({CHR ''-''} \<union> digit_chars) \<Longrightarrow> is_error (parse JsonNumber) (c # i)"
  by (clarsimp simp add: JsonNumber_def NER_simps)+

lemma JsonNumber_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonNumber)) i [] \<longleftrightarrow> False"
  unfolding JsonNumber_def
  by (clarsimp simp add: print_empty)

lemma PASI_PNGI_JsonNumber[PASI_PNGI_intros]:
  shows "PASI (parse JsonNumber)"
        "PNGI (parse JsonNumber)"
  unfolding JsonNumber_def
  by pasi_pngi+

lemma fpci_JsonNumber[fpci_simps]:
  "first_printed_chari (print JsonNumber) i c \<Longrightarrow> c \<in> digit_chars \<or> c = CHR ''-''"
  unfolding JsonNumber_def
  by (clarsimp simp add: fpci_simps split: JSON.splits if_splits)

lemma fpc_JsonNumber[fpc_simps]:
  "fpc (parse JsonNumber) a c \<Longrightarrow> c \<in> digit_chars \<or> c = CHR ''-''"
  by (auto simp add: JsonNumber_def fpc_simps split: if_splits)

lemma JsonNumber_can_drop_leftover_on_error:
  assumes "is_error (parse JsonNumber) (c @ l)"
  shows "is_error (parse JsonNumber) c"
  using assms
  by (clarsimp simp add: NER_simps JsonNumber_def int_b_can_drop_leftover_on_error)

lemma JsonNumber_can_drop_leftover_on_error2:
  assumes "is_error (parse JsonNumber) (c @ l @ l')"
  shows "is_error (parse JsonNumber) (c @ l)"
  using assms
  by (clarsimp simp add: NER_simps JsonNumber_def int_b_can_drop_leftover_on_error)

lemma JsonNumber_drop_leftover:
  shows "has_result (parse JsonNumber) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse JsonNumber) (c @ l) r l"
  by (clarsimp simp add: NER_simps JsonNumber_def int_b_leftover_can_be_dropped_gen)


lemma JsonNumber_stays_error_with_injected_char:
  assumes "is_error (parse JsonNumber) (c @ l)"
  assumes "c' \<noteq> CHR ''-'' \<and> c' \<notin> digit_chars" \<comment> \<open>Too strong but good for our uses here.\<close>
  shows "is_error (parse JsonNumber) (c @ c' # l')"
  using assms
  by (clarsimp simp add: NER_simps JsonNumber_def int_b_stays_error_with_injected_char)

lemma JsonNumber_no_consume_past_non_digit_chars:
  assumes "c \<notin> digit_chars"
  shows "does_not_consume_past_char3 (parse JsonNumber) c"
  unfolding JsonNumber_def
  apply (rule ftransform_does_not_consume_past_char3)
  using assms by (rule int_b_does_not_consume_past_char3)


lemma wf_JsonNumber:
  "bidef_well_formed JsonNumber"
  unfolding JsonNumber_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def fp_NER split: JSON.splits)
  subgoal by (rule int_b_well_formed)
  done



definition JsonNameColonObject :: "JSON bidef \<Rightarrow> (string \<times> JSON) bidef" where
  "JsonNameColonObject i = b_then str_literal (then_drop_first (ws_char_ws CHR '':'') i ())"

lemma PASI_PNGI_JsonNameColonObject[PASI_PNGI_intros]:
  assumes "PNGI (parse I)"
  shows "PASI (parse (JsonNameColonObject I))"
        "PNGI (parse (JsonNameColonObject I))"
  unfolding JsonNameColonObject_def apply (insert assms)
  by pasi_pngi+

lemma mono_JsonNameColonObject[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. JsonNameColonObject (A f))"
  unfolding JsonNameColonObject_def using ma
  by pf_mono_prover

lemma p_has_result_JsonNameColonObject[print_empty, fp_NER]:
  "p_has_result (print (JsonNameColonObject J)) t [] \<longleftrightarrow> False"
  by (clarsimp simp add: JsonNameColonObject_def print_empty)

lemma fpci_JsonNameColonObject[fpci_simps]:
  "first_printed_chari (print (JsonNameColonObject J)) t c \<Longrightarrow> c = quot_chr"
  by (clarsimp simp add: JsonNameColonObject_def fpci_simps print_empty split: if_splits)

lemma is_error_JsonNameColonObject[NER_simps]:
  "is_error (parse (JsonNameColonObject J)) []"
  "c \<noteq> quot_chr \<Longrightarrow> is_error (parse (JsonNameColonObject J)) (c # l)"
  by (clarsimp simp add: JsonNameColonObject_def NER_simps)+

lemma has_result_JsonNameColonObject[NER_simps]:
  assumes J_pngi: "PNGI (parse J)"
  shows "has_result (parse (JsonNameColonObject J)) i r i \<longleftrightarrow> False"
  using PASI_PNGI_JsonNameColonObject(1)[OF J_pngi, unfolded PASI_def, rule_format]
  by blast
lemma has_result_JsonNameColonObject_first_char:
  shows "has_result (parse (JsonNameColonObject J)) (i#is) r l \<Longrightarrow> i = quot_chr"
  apply (clarsimp simp add: NER_simps JsonNameColonObject_def str_literal_def takeMiddle_def quot_def)
  done

lemma fpc_JsonNameColonObject[fpc_simps]:
  "fpc (parse (JsonNameColonObject I)) a c \<Longrightarrow> c = quot_chr"
  apply (clarsimp simp add: JsonNameColonObject_def fpc_simps)
  by (clarsimp simp add: fpc_def NER_simps str_literal_def takeMiddle_def quot_def)


lemma JsonNameColonObject_no_consume_past_closing_brace:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse J) CHR ''}''"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  shows "does_not_consume_past_char3 (parse (JsonNameColonObject J)) CHR ''}''"
  unfolding JsonNameColonObject_def
  apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
  subgoal by (rule str_literal_no_peek_past_end)
  subgoal by pasi_pngi
  subgoal
    unfolding then_drop_first_def
    apply (rule transform_does_not_consume_past_char3)
    apply (rule then_does_not_consume_past3) \<comment> \<open>or do: then_does_not_consume_past3_from_can_drop_leftover\<close>
    subgoal by (clarsimp simp add: ws_char_ws_well_formed)
    subgoal by (rule J_wf)
    subgoal by (rule J_no_consume_past_closing_brace)
    subgoal by (clarsimp simp add: J_fpc_no_ws ws_char_ws_does_not_consume_past_char3)
    subgoal by (rule J_no_parse_empty)
    done
  subgoal using J_pngi by pasi_pngi
  done

lemma JsonNameColonObject_no_consume_past_closing_bracket:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_no_consume_past_closing_bracket: "does_not_consume_past_char3 (parse J) CHR '']''"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  shows "does_not_consume_past_char3 (parse (JsonNameColonObject J)) CHR '']''"
  unfolding JsonNameColonObject_def
  apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
  subgoal by (rule str_literal_no_peek_past_end)
  subgoal by pasi_pngi
  subgoal
    unfolding then_drop_first_def
    apply (rule transform_does_not_consume_past_char3)
    apply (rule then_does_not_consume_past3) \<comment> \<open>or do: then_does_not_consume_past3_from_can_drop_leftover\<close>
    subgoal by (clarsimp simp add: ws_char_ws_well_formed)
    subgoal by (rule J_wf)
    subgoal by (rule J_no_consume_past_closing_bracket)
    subgoal by (clarsimp simp add: J_fpc_no_ws ws_char_ws_does_not_consume_past_char3)
    subgoal by (rule J_no_parse_empty)
    done
  subgoal using J_pngi by pasi_pngi
  done

lemma JsonNameColonObject_no_consume_past_comma:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_no_consume_past_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  shows "does_not_consume_past_char3 (parse (JsonNameColonObject J)) CHR '',''"
  unfolding JsonNameColonObject_def
  apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
  subgoal by (rule str_literal_no_peek_past_end)
  subgoal by pasi_pngi
  subgoal
    unfolding then_drop_first_def
    apply (rule transform_does_not_consume_past_char3)
    apply (rule then_does_not_consume_past3) \<comment> \<open>or do: then_does_not_consume_past3_from_can_drop_leftover\<close>
    subgoal by (clarsimp simp add: ws_char_ws_well_formed)
    subgoal by (rule J_wf)
    subgoal by (rule J_no_consume_past_comma)
    subgoal by (clarsimp simp add: J_fpc_no_ws ws_char_ws_does_not_consume_past_char3)
    subgoal by (rule J_no_parse_empty)
    done
  subgoal using J_pngi by pasi_pngi
  done

lemma JsonNameColonObject_no_consume_past_ws:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_no_consume_past_ws: "\<And>c . c\<in>whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse J) c"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  assumes c_in_ws: "c \<in> whitespace_chars"
  shows "does_not_consume_past_char3 (parse (JsonNameColonObject J)) c"
  unfolding JsonNameColonObject_def
  apply (rule then_does_not_consume_past_char_from_first_no_peek_past_end)
  subgoal by (rule str_literal_no_peek_past_end)
  subgoal by pasi_pngi
  subgoal
    unfolding then_drop_first_def
    apply (rule transform_does_not_consume_past_char3)
    apply (rule then_does_not_consume_past3) \<comment> \<open>or do: then_does_not_consume_past3_from_can_drop_leftover\<close>
    subgoal by (clarsimp simp add: ws_char_ws_well_formed)
    subgoal by (rule J_wf)
    subgoal by (rule J_no_consume_past_ws[OF c_in_ws])
    subgoal by (clarsimp simp add: J_fpc_no_ws ws_char_ws_does_not_consume_past_char3)
    subgoal by (rule J_no_parse_empty)
    done
  subgoal using J_pngi by pasi_pngi
  done


lemma JsonNameColonObject_drop_leftover:
  assumes I_pngi: "PNGI (parse I)"
  assumes I_drop_leftover: "\<And>c l l' r. has_result (parse I) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse I) (c @ l) r l"
  shows "has_result (parse (JsonNameColonObject I)) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse (JsonNameColonObject I)) (c @ l) r l"
  unfolding JsonNameColonObject_def
  apply (rule then_can_drop_leftover; assumption?)
  subgoal for cs ls ls' rs
    using str_literal_no_peek_past_end[unfolded does_not_peek_past_end_def, rule_format, of cs \<open>ls@ls'\<close> rs ls] by blast
  subgoal by pasi_pngi
  subgoal for ctt ltt ltt' rtt
    unfolding then_drop_first_def
    apply (rule transform_can_drop_leftover[of \<open>b_then (ws_char_ws CHR '':'') I\<close> snd \<open>Pair ()\<close> ctt ltt ltt' rtt]; assumption?)
    subgoal for ct lt lt' rt
      apply (rule then_can_drop_leftover; assumption?)
      subgoal for cw lw lw' rw
        by (rule ws_char_ws_can_drop_past_leftover[of \<open>CHR '':''\<close> cw lw lw' rw])
      subgoal by pasi_pngi
      subgoal by (rule I_drop_leftover)
      subgoal by (rule I_pngi)
      done
    done
  subgoal using I_pngi by pasi_pngi
  done

lemma result_of_ws_char_ws_from_c_must_be_empty:
  assumes "i' \<noteq> []"
  assumes "has_result (parse (ws_char_ws C)) (i @ i' @ l) r l"
	assumes "has_result (parse (ws_char_ws C)) i r l'"
	shows "l' = []"
  using assms
  apply (auto simp add: NER_simps)
  subgoal by (metis (no_types, lifting) Nil_is_append_conv append.assoc append_self_conv2 assms(3) dropWhile_append1 tl_append2 ws_char_ws_has_result)
  subgoal using \<open>\<And>xb xa x. \<lbrakk>i' \<noteq> []; x \<in> set (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i)); l = dropWhile (\<lambda>x. x \<in> whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i @ i' @ l)); l' = dropWhile (\<lambda>x. x \<in> whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i)); C = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i @ i' @ l); xa \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i @ i' @ l); xb \<in> set i; xb \<notin> whitespace_chars; xa \<in> set i\<rbrakk> \<Longrightarrow> x \<in> whitespace_chars\<close>
    by blast
  subgoal using \<open>\<And>xb xa x. \<lbrakk>i' \<noteq> []; x \<in> set (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i)); l = dropWhile (\<lambda>x. x \<in> whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i @ i' @ l)); l' = dropWhile (\<lambda>x. x \<in> whitespace_chars) (tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) i)); C = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i @ i' @ l); xa \<notin> whitespace_chars; hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i) = hd (dropWhile (\<lambda>x. x \<in> whitespace_chars) i @ i' @ l); xb \<in> set i; xb \<notin> whitespace_chars; xa \<in> set i\<rbrakk> \<Longrightarrow> x \<in> whitespace_chars\<close>
    by blast
  done


lemma JsonNameColonObject_drop_leftover_on_error:
  assumes I_error_empty: "is_error (parse I) []"
  assumes I_drop_leftover_on_error: "\<And>i i'. is_error (parse I) (i @ i') \<Longrightarrow> is_error (parse I) i"
  assumes e1: "is_error (parse (JsonNameColonObject I)) (i @ i')"
  shows "is_error (parse (JsonNameColonObject I)) i"
  apply (insert e1)
  unfolding JsonNameColonObject_def
  apply (rule then_can_drop_leftover_on_error; assumption?; clarsimp?)
  subgoal by (rule str_literal_drop_input_on_error)
  subgoal by pasi_pngi
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (rule str_literal_error_if_take_from_c)
  subgoal by (rule str_literal_can_drop_leftover)
  subgoal for i2 i2'
    unfolding then_drop_first_def
    apply (rule transform_drop_input_leftover_on_error; assumption?)
    apply (rule then_can_drop_leftover_on_error; assumption?; clarsimp?)
    subgoal by (rule ws_char_ws_drop_input_on_error)
    subgoal by pasi_pngi
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for i3' l3
      apply (insert result_of_ws_char_ws_from_c_must_be_empty[of i3' \<open>CHR '':''\<close> i2 l3 \<open>()\<close>]; clarsimp)
      using I_error_empty
      by (metis (full_types) has_result_exhaust(2) old.unit.exhaust ws_char_ws_is_nonterm)
    subgoal by (rule ws_char_ws_can_drop_past_leftover)
    subgoal by (rule I_drop_leftover_on_error)
    done
  done


lemma wf_JsonNameColonObject:
  assumes J_wf: "bidef_well_formed J"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  shows "bidef_well_formed (JsonNameColonObject J)"
  unfolding JsonNameColonObject_def
  apply (rule b_then_well_formed_does_not_peek_past)
  subgoal by (rule str_literal_well_formed)
   defer \<comment> \<open>bidef_well_formed (then_drop_first (ws_char_ws CHR '':'') J ())\<close>
  subgoal by (rule str_literal_no_peek_past_end)
  unfolding then_drop_first_def
  apply (rule transform_well_formed4)
  subgoal by (clarsimp simp add: well_formed_transform_funcs4_def)
  apply (rule b_then_well_formed)
  subgoal by (rule ws_char_ws_well_formed; clarsimp)
  subgoal by (rule J_wf)
  apply (rule first_printed_does_not_eat_into3; clarsimp?)
  subgoal by (rule ws_char_ws_well_formed; clarsimp)
  subgoal for i c
    apply (subst ws_char_ws_does_not_consume_past_char3[of \<open>CHR '':''\<close> c, simplified])
    by (rule J_fpci_no_ws)
  done



lemma ws_char_ws_then_JNCO_no_consume_past_char:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  assumes J_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse J) c"

  assumes c_val: "c = CHR ''}'' \<or> c = CHR '','' \<or> c \<in> whitespace_chars"

  assumes J_no_consume_past_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse J) c"

  shows "does_not_consume_past_char3 (parse (b_then (ws_char_ws CHR '','') (JsonNameColonObject J))) c"
  apply (rule then_does_not_consume_past3)
  subgoal by (rule ws_char_ws_well_formed; clarsimp)
  subgoal by (rule wf_JsonNameColonObject; clarsimp simp add: J_fpci_no_ws J_wf)
  subgoal
    using c_val
    apply auto
    subgoal
      apply (rule JsonNameColonObject_no_consume_past_closing_brace[OF J_pngi J_wf])
      subgoal using J_no_consume_past_closing_brace by blast
      subgoal by (clarsimp simp add: J_fpc_no_ws)
      subgoal by (clarsimp simp add: J_no_parse_empty)
      done
    subgoal
      apply (rule JsonNameColonObject_no_consume_past_comma[OF J_pngi J_wf])
      subgoal using J_no_consume_past_closing_brace by blast
      subgoal by (clarsimp simp add: J_fpc_no_ws)
      subgoal by (clarsimp simp add: J_no_parse_empty)
      done
    subgoal
      apply (rule JsonNameColonObject_no_consume_past_ws[OF J_pngi J_wf])
      subgoal using J_no_consume_past_ws by blast
      subgoal by (clarsimp simp add: J_fpc_no_ws)
      subgoal by (clarsimp simp add: J_no_parse_empty)
      subgoal by clarsimp
      done
    done
  subgoal for i c
    by (insert fpc_JsonNameColonObject[of J i c]; clarsimp simp add: ws_char_ws_does_not_consume_past_char3)
  subgoal
    using is_error_JsonNameColonObject(1) is_error_implies_not_has_result by blast
  done

lemma JsonNameColonObject_sepByComma_no_consume_past_chars_ws:
  assumes JNCO_wf: "bidef_well_formed (JsonNameColonObject I)"
  assumes I_pngi: "PNGI (parse I)"
  assumes I_wf: "bidef_well_formed I"
  assumes I_dncp_comma: "does_not_consume_past_char3 (parse I) CHR '',''"
  assumes I_dncp_closing_brace: "does_not_consume_past_char3 (parse I) CHR ''}''"
  assumes I_dncp_closing_bracket: "does_not_consume_past_char3 (parse I) CHR '']''"
  assumes I_dncp_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse I) c"
  assumes I_fpc_no_ws: "\<And>i c. fpc (parse I) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes I_no_result_from_empty: "\<And>r x. has_result (parse I) [] r x \<Longrightarrow> False"
  assumes I_drop_leftover: "\<And>c l l' r. has_result (parse I) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse I) (c @ l) r l"

  \<comment> \<open>Might also like to add comma later?\<close>
  \<comment> \<open>Sadly had to drop the ws_chars from here because the separated_by_no_consume_past_char rule breaks that.\<close>
  assumes c_val: "c \<in> whitespace_chars"
  shows "does_not_consume_past_char3 (parse (separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ())) c"
  apply (rule separated_by_no_consume_past_char)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal for l
    apply (insert c_val)
    by (rule is_error_JsonNameColonObject(2)[of c I l]; clarsimp)
  subgoal by (rule JNCO_wf)
  subgoal
    apply (rule WF_many_then; clarsimp?)
    subgoal by (rule ws_char_ws_well_formed; clarsimp)
    subgoal by pasi_pngi
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by (rule JNCO_wf)
    subgoal using I_pngi by pasi_pngi
    subgoal for a b c
      apply (insert fpci_JsonNameColonObject[of I \<open>(a,b)\<close> c]; clarsimp)
      by (rule ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> quot_chr, simplified])
    subgoal for c
      apply (clarsimp simp add: fpci_simps)
      apply (rule JsonNameColonObject_no_consume_past_comma)
      subgoal by (rule I_pngi)
      subgoal by (rule I_wf)
      subgoal by (rule I_dncp_comma)
      subgoal by (rule I_fpc_no_ws)
      subgoal using I_no_result_from_empty by blast
      done
    done
  subgoal for i c
    apply (cases i; clarsimp simp add: fpc_simps) \<comment> \<open>Empty case dispatched\<close>
    apply (auto simp add: NER_simps fpc_def split: if_splits)
    subgoal
      apply (insert I_fpc_no_ws)
      apply (rule JsonNameColonObject_no_consume_past_ws[of _ c, OF I_pngi I_wf I_dncp_ws, simplified]; assumption?)
      using I_no_result_from_empty by blast
    subgoal
      apply (insert I_fpc_no_ws)
      apply (rule JsonNameColonObject_no_consume_past_ws[of _ c, OF I_pngi I_wf I_dncp_ws, simplified]; assumption?)
      using I_no_result_from_empty by blast
    subgoal by (rule JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_dncp_comma]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    subgoal by (rule JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_dncp_comma]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    subgoal by (rule JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_dncp_comma]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    done
  subgoal
    apply (insert c_val)
    apply (rule JsonNameColonObject_no_consume_past_ws)
         apply (auto simp add: I_pngi I_wf I_dncp_ws I_fpc_no_ws)
    using I_no_result_from_empty by blast
  subgoal for c l l' r
    apply (rule JsonNameColonObject_drop_leftover[OF I_pngi]; assumption?)
    by (rule I_drop_leftover)
  subgoal
    by (clarsimp simp add: NER_simps)
  subgoal for i r l
    \<comment> \<open>Problem here! We find that ws_char_ws does not actually error on ws.\<close>
    \<comment> \<open>So we do look past ws\<close>

    oops


lemma a_imp_conj2:
  "(A1 \<Longrightarrow> A2 \<Longrightarrow> A3 \<Longrightarrow> A4 \<Longrightarrow> A5 \<Longrightarrow> A6 \<Longrightarrow> A7 \<Longrightarrow> (B \<and> C)) \<Longrightarrow> (A1 \<longrightarrow> A2 \<longrightarrow> A3 \<longrightarrow> A4 \<longrightarrow> A5 \<longrightarrow> A6 \<longrightarrow> A7 \<longrightarrow> C)"
  by blast

lemma sublemma_1:
  assumes I_pngi: "PNGI (parse I)"
  shows "does_not_conusme_past_parse_consume_or_if_empty (parse (ws_char_ws CHR '','')) (parse (JsonNameColonObject I)) (parse (b_then (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject I))) (ws_char CHR ''}'')))"
  apply (clarsimp simp add: does_not_conusme_past_parse_consume_or_if_empty_def; rule conjI)
  subgoal for c l by (rule ws_char_ws_can_drop_past_leftover[of \<open>CHR '',''\<close> c \<open>[]\<close> l \<open>()\<close>, simplified])
  subgoal for c l c2 a b l2 c3 c3r l3
    apply (cases c2; clarsimp)
    subgoal using has_result_JsonNameColonObject[OF I_pngi] by blast
    subgoal for c2' c2s l''
      apply (insert has_result_JsonNameColonObject_first_char[of I c2' \<open>c2s@l2\<close> \<open>(a,b)\<close> l2]; clarsimp)
      using ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> quot_chr, simplified,
            unfolded does_not_consume_past_char3_def, rule_format, of c l \<open>()\<close>] by fast
    done
  done

lemma sublemma_2:
  assumes I_pngi: "PNGI (parse I)"
  assumes I_wf: "bidef_well_formed I"
  assumes I_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse I) CHR ''}''"
  assumes I_no_consume_past_ws: "\<And>c . c\<in>whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse I) c"
  assumes I_no_consume_past_comma: "does_not_consume_past_char3 (parse I) CHR '',''"
  assumes I_fpc_no_ws: "\<And> i c. fpc (parse I) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes I_no_parse_empty: "\<nexists>r l. has_result (parse I) [] r l"
  assumes I_drop_leftover: "\<And>c l l' r. has_result (parse I) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse I) (c @ l) r l"
  shows "does_not_consume_past_parse_consume (parse (JsonNameColonObject I)) (parse (b_then (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject I))) (ws_char CHR ''}'')))"
  apply (clarsimp simp add: does_not_consume_past_parse_consume_def)
  subgoal for c a b l l' c2 aa l2
    apply (rule conjI)
    subgoal
      using JsonNameColonObject_drop_leftover[OF I_pngi, of c \<open>[]\<close> l \<open>(a,b)\<close>, simplified] I_drop_leftover
      by blast
    subgoal
      apply (cases c2; clarsimp)
      subgoal
        using then_PASI_from_pngi_pasi[OF many_PNGI, OF then_PASI_from_pasi_pngi, OF ws_char_ws_PASI
                      PASI_PNGI_JsonNameColonObject(2), OF I_pngi ws_char_PASI,
                      unfolded PASI_def, rule_format, of _ _ l2 \<open>(aa, ())\<close> l2]
        by fast
      subgoal for c2' c2s
        apply (cases aa; clarsimp)
        subgoal
          apply (clarsimp simp add: b_then_has_result many_has_result)
          apply (insert ws_char_fpc[of \<open>CHR ''}''\<close> \<open>()\<close> c2', unfolded fpc_def]; auto)
          subgoal
            using I_fpc_no_ws I_no_parse_empty
                  JsonNameColonObject_no_consume_past_closing_brace[OF I_pngi I_wf I_no_consume_past_closing_brace,
                        unfolded does_not_consume_past_char3_def, rule_format, of c l \<open>(a,b)\<close> \<open>c2s @ l'\<close>]
            by fast
          subgoal
            using I_fpc_no_ws I_no_parse_empty
                  JsonNameColonObject_no_consume_past_ws[OF I_pngi I_wf I_no_consume_past_ws,
                        unfolded does_not_consume_past_char3_def, rule_format, of c2' c l \<open>(a,b)\<close> \<open>c2s @ l'\<close>]
            by fast
          done
        subgoal for aa' aas
          apply (clarsimp simp add: b_then_has_result many_has_result)
          apply (insert ws_char_ws_fpc[of \<open>CHR '',''\<close> \<open>()\<close> c2', unfolded fpc_def]; auto)
          subgoal
            using I_fpc_no_ws I_no_parse_empty
                  JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_no_consume_past_comma,
                        unfolded does_not_consume_past_char3_def, rule_format, of c l \<open>(a,b)\<close> \<open>c2s @ l'\<close>]
            by fast
          subgoal
            using I_fpc_no_ws I_no_parse_empty
                  JsonNameColonObject_no_consume_past_ws[OF I_pngi I_wf I_no_consume_past_ws,
                        unfolded does_not_consume_past_char3_def, rule_format, of c2' c l \<open>(a,b)\<close> \<open>c2s @ l'\<close>]
            by fast
          subgoal by (clarsimp simp add: NER_simps)
          done
        done
      done
    done
  done

lemma JNCO_sepBy_ws_comma_ws_no_consume_past_ws_closing_brace:
  assumes I_pngi: "PNGI (parse I)"
  assumes I_drop_leftover: "\<And>c l l' r. has_result (parse I) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse I) (c @ l) r l"

  assumes I_wf: "bidef_well_formed I"
  assumes I_no_consume_past_ws: "\<And>c . c\<in>whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse I) c"
  assumes I_no_consume_past_comma: "does_not_consume_past_char3 (parse I) CHR '',''"
  assumes I_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse I) CHR ''}''"
  assumes I_fpc_no_ws: "\<And> i c. fpc (parse I) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes I_no_parse_empty: "\<nexists>r l. has_result (parse I) [] r l"
  assumes I_error_empty: "is_error (parse I) []"
  assumes I_drop_leftover_on_error: "\<And>i i'. is_error (parse I) (i @ i') \<Longrightarrow> is_error (parse I) i"

  shows "does_not_consume_past_parse_consume (parse (separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ())) (parse (ws_char CHR ''}''))"
  unfolding separated_by_def
  apply (rule transform_does_not_consume_past_parser_result)
  apply (rule optional_does_not_consume_past_parse_consume)
  subgoal by (clarsimp simp add: NER_simps separated_byBase_def)
  subgoal for ea cws lws rws l'
    apply (cases cws; clarsimp)
    subgoal
      using ws_char_no_result_same_leftover[of \<open>CHR ''}''\<close> lws \<open>()\<close>] by blast
    by (clarsimp simp add: NER_simps separated_byBase_def JsonNameColonObject_def)
  unfolding separated_byBase_def
  apply (rule then_does_not_consume_past_parse_consume_or_if_empty_B)
  subgoal for c l l' r
    by (rule JsonNameColonObject_drop_leftover[OF I_pngi, of c l l' r]; clarsimp simp add: I_drop_leftover)
  subgoal for c l l' r
    apply (rule many_can_drop_leftover[of _ c l l' r]; clarsimp?)
    subgoal for ca la la' on oc
      apply (rule then_can_drop_leftover[of _ _ ca la la' \<open>((), on, oc)\<close>]; clarsimp?)
      subgoal using ws_char_ws_can_drop_past_leftover by blast
      subgoal by pasi_pngi
      subgoal using JsonNameColonObject_drop_leftover[OF I_pngi] I_drop_leftover by blast
      subgoal using I_pngi by pasi_pngi
      done
    subgoal for i i'
      apply (rule then_can_drop_leftover_on_error[of \<open>ws_char_ws CHR '',''\<close> i \<open>JsonNameColonObject I\<close> i']; assumption?; clarsimp?)
      subgoal by (rule ws_char_ws_drop_input_on_error)
      subgoal by pasi_pngi
      subgoal by (clarsimp simp add: NER_simps)
      subgoal for i'' l''
        apply (clarsimp simp add: ws_char_ws_has_result JsonNameColonObject_def)
        by (smt (verit) \<open>\<lbrakk>has_result (parse (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject I)))) (c @ l @ l') r (l @ l'); is_error (parse (b_then (ws_char_ws CHR '','') (JsonNameColonObject I))) (i @ i'); is_nonterm (parse (ws_char_ws CHR '','')) i\<rbrakk> \<Longrightarrow> False\<close>
                        JsonNameColonObject_def
                        append.assoc append_is_Nil_conv append_same_eq b_then_is_error_from_first
                        dropWhile_append dropWhile_eq_Nil_conv has_result_exhaust(1) is_error_str_literal(1)
                        self_append_conv tl_append2 ws_char_ws_has_result)
      subgoal using ws_char_ws_can_drop_past_leftover by blast
      subgoal for i2 i2'
        apply (rule JsonNameColonObject_drop_leftover_on_error[OF I_error_empty]; assumption?)
        by (rule I_drop_leftover_on_error)
      done
    subgoal using I_pngi by pasi_pngi
    done
  subgoal using I_pngi by pasi_pngi
  subgoal using I_pngi by pasi_pngi
  subgoal
    apply (clarsimp simp add: does_not_conusme_past_parse_consume_or_if_empty_def)
    subgoal for c a b l c2 r2 l2 c3 l3
      apply auto \<comment> \<open>Split up conjunctions and the implication\<close>
      subgoal
        apply (rule JsonNameColonObject_drop_leftover[OF I_pngi, of c \<open>[]\<close> l \<open>(a,b)\<close>, simplified]; assumption?)
        by (rule I_drop_leftover)
      subgoal for l'
        apply (cases c3; clarsimp)
        subgoal by (subst (asm) ws_char_no_result_same_leftover; clarsimp)
        subgoal for c3' c3s
          apply (insert ws_char_fpc[of \<open>CHR ''}''\<close> \<open>()\<close> c3', unfolded fpc_def]; auto)
          subgoal for cs la
            using JsonNameColonObject_no_consume_past_closing_brace[OF I_pngi I_wf I_no_consume_past_closing_brace,
                    unfolded does_not_consume_past_char3_def, rule_format, of c l \<open>(a,b)\<close> \<open>c3s@l'\<close>]
                  I_fpc_no_ws I_no_parse_empty
            by fast
          subgoal for cs la
            using JsonNameColonObject_no_consume_past_ws[OF I_pngi I_wf I_no_consume_past_ws,
                    unfolded does_not_consume_past_char3_def, rule_format, of c3' c l \<open>(a,b)\<close> \<open>c3s@l'\<close>]
                  I_fpc_no_ws I_no_parse_empty
            by fastforce
          done
        done
      subgoal for l''
        apply (cases c2; clarsimp) \<comment> \<open>Empty case dispatched because handled via c3 above.\<close>
        apply (cases r2; clarsimp)
        subgoal by (clarsimp simp add: NER_simps) \<comment> \<open>Many cannot parse empty with a nonempty consumed\<close>
        subgoal for c2' c2s a' b' ab's
          apply (clarsimp simp add: many_has_result b_then_has_result)
          apply (insert ws_char_ws_fpc[of \<open>CHR '',''\<close> \<open>()\<close> c2', unfolded fpc_def]; auto)
          subgoal
            using JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_no_consume_past_comma,
                    unfolded does_not_consume_past_char3_def, rule_format, of c l \<open>(a,b)\<close> \<open>c2s@l''\<close>]
                  I_fpc_no_ws I_no_parse_empty
            by fast
          subgoal
            using JsonNameColonObject_no_consume_past_ws[OF I_pngi I_wf I_no_consume_past_ws,
                    unfolded does_not_consume_past_char3_def, rule_format, of c2' c l \<open>(a,b)\<close> \<open>c2s@l''\<close>]
                  I_fpc_no_ws I_no_parse_empty
            by fastforce
          subgoal for l2' l2''
            apply (insert ws_char_ws_PASI[of \<open>CHR '',''\<close>, unfolded PASI_def, rule_format, of \<open>c2'#c2s@l2\<close> \<open>()\<close> l2'']; clarsimp)
            by (metis (no_types, lifting) dropWhile_eq_self_iff list.sel(1) ws_char_ws_has_result)
          done
        done
      done
    done
  subgoal
    apply (clarsimp simp add: does_not_consume_past_parse_consume_def)
    subgoal for c r l l' c2 l2
      apply (rule conjI)
      subgoal
        apply (rule many_can_drop_leftover[of _ c \<open>[]\<close> l r, simplified]; clarsimp?)
        subgoal for c3 l3 l3' ra rb
          apply (rule then_can_drop_leftover[of _ _ c3 l3 l3' \<open>((), ra, rb)\<close>]; clarsimp?)
          subgoal using ws_char_ws_can_drop_past_leftover by blast
          subgoal by pasi_pngi
          subgoal for c4 l4 l4'
            apply (rule JsonNameColonObject_drop_leftover[OF I_pngi, of c4 l4 l4']; clarsimp?)
            by (rule I_drop_leftover)
          subgoal using I_pngi by pasi_pngi
          done
        subgoal for l3 l3'
          apply (rule then_can_drop_leftover_on_error[of _ l3 _ l3']; clarsimp?)
          subgoal by (rule ws_char_ws_drop_input_on_error)
          subgoal by pasi_pngi
          subgoal by (clarsimp simp add: NER_simps)
          subgoal for i3' l3'
            apply (cases \<open>\<forall>b \<in> set l3. b \<in> whitespace_chars\<close>)
            subgoal
              apply (insert ws_char_ws_is_error[of \<open>CHR '',''\<close> l3, simplified]; clarsimp)
              by (metis chars_that_are_not_whitespace list.set_intros(1) set_dropWhileD)
            subgoal
              apply (insert ws_char_ws_has_result[of \<open>CHR '',''\<close> \<open>l3 @ i3' @ l3'\<close> \<open>()\<close> l3']
                            ws_char_ws_has_result[of \<open>CHR '',''\<close> \<open>l3\<close> \<open>()\<close>])
              apply clarsimp
              by (metis is_error_JsonNameColonObject(1) list.sel(1) result_of_ws_char_ws_from_c_must_be_empty ws_char_ws_is_error)
            done
          subgoal using ws_char_ws_can_drop_past_leftover by blast
          subgoal
            apply (rule JsonNameColonObject_drop_leftover_on_error[OF I_error_empty]; assumption?)
            by (rule I_drop_leftover_on_error)
          done
        subgoal using I_pngi by pasi_pngi
        done
      subgoal
        apply (induction r arbitrary: c; clarsimp?)
        subgoal for c
          apply (cases c; clarsimp)
          subgoal
            apply (insert ws_char_can_drop_past_leftover[of \<open>CHR ''}''\<close> c2 \<open>[]\<close> l2, simplified]; clarsimp)
            apply (clarsimp simp add: many_has_result)
            apply (rule b_then_is_error_from_first)
            apply (clarsimp simp add: ws_char_ws_is_error)
            apply (clarsimp simp add: ws_char_has_result[of \<open>CHR ''}''\<close> c2])
            by (smt (z3) char.inject dropWhile_eq_Nil_conv hd_append2 list.sel(1))
          subgoal by (clarsimp simp add: NER_simps)
          done
        subgoal for a b abs c
          apply (insert ws_char_can_drop_past_leftover[of \<open>CHR ''}''\<close> c2 \<open>[]\<close> l2, simplified]; clarsimp)
          apply (clarsimp simp add: many_has_result_safe)
          subgoal for l3
            apply (insert many_PNGI[of \<open>b_then (ws_char_ws CHR '','') (JsonNameColonObject I)\<close>,
                            OF then_PASI_from_pasi_pngi,
                            OF ws_char_ws_PASI PASI_PNGI_JsonNameColonObject(2),
                            OF I_pngi, unfolded PNGI_def, rule_format,
                            of l3 abs l]; clarsimp)
            subgoal for c_laters
              apply (insert then_PNGI[OF ws_char_ws_PNGI PASI_PNGI_JsonNameColonObject(2), OF I_pngi,
                              unfolded PNGI_def, rule_format,
                              of \<open>CHR '',''\<close> \<open>c@l\<close> \<open>((), a, b)\<close> \<open>c_laters@l\<close>]; clarsimp)
              subgoal for c_first
                apply (rule exI[of _ \<open>c_laters @ c2 @ l'\<close>]; clarsimp) \<comment> \<open>induction end removed, now just need the first.\<close>
                apply (insert then_does_not_consume_past_parse_consume_or_if_empty_B[
                        of \<open>ws_char_ws CHR '',''\<close>
                           \<open>JsonNameColonObject I\<close>
                           \<open>b_then (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject I))) (ws_char CHR ''}'')\<close>,
                        unfolded does_not_consume_past_parse_consume_def[of \<open>parse (b_then (ws_char_ws CHR '','') (JsonNameColonObject I))\<close>],
                        rule_format, of c_first \<open>c_laters @ l\<close> \<open>((), a, b)\<close> \<open>c_laters@c2\<close> l \<open>(abs, ())\<close> l',
                        OF _ _ ws_char_ws_PNGI PASI_PNGI_JsonNameColonObject(2)[OF I_pngi]
                        ]; clarsimp)
                apply (insert ws_char_ws_can_drop_past_leftover[of \<open>CHR '',''\<close>]; clarsimp)
                apply (insert I_drop_leftover)
                apply (insert JsonNameColonObject_drop_leftover[OF I_pngi])
                apply clarsimp
                apply (insert sublemma_1[OF I_pngi]; clarsimp)
                
                
                sorry
              done
            done
          done
        done
      done
    done
  oops


lemma JsonNameColonObject_sepByComma_no_consume_past_chars:
  assumes JNCO_wf: "bidef_well_formed (JsonNameColonObject I)"
  assumes I_pngi: "PNGI (parse I)"
  assumes I_wf: "bidef_well_formed I"
  assumes I_dncp_comma: "does_not_consume_past_char3 (parse I) CHR '',''"
  assumes I_dncp_closing_brace: "does_not_consume_past_char3 (parse I) CHR ''}''"
  assumes I_dncp_closing_bracket: "does_not_consume_past_char3 (parse I) CHR '']''"
  assumes I_dncp_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse I) c"
  assumes I_fpc_no_ws: "\<And>i c. fpc (parse I) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes I_no_result_from_empty: "\<And>r x. has_result (parse I) [] r x \<Longrightarrow> False"
  assumes I_drop_leftover: "\<And>c l l' r. has_result (parse I) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse I) (c @ l) r l"

  \<comment> \<open>Might also like to add comma later?\<close>
  \<comment> \<open>Sadly had to drop the ws_chars from here because the separated_by_no_consume_past_char rule breaks that.\<close>
  assumes c_val: "c = CHR ''}'' \<or> c = CHR '']''"
  shows "does_not_consume_past_char3 (parse (separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ())) c"
  apply (rule separated_by_no_consume_past_char)
  subgoal by (rule is_error_JsonNameColonObject)
  subgoal
    apply (rule is_error_JsonNameColonObject)
    using c_val by force
  subgoal by (rule JNCO_wf)
  subgoal
    apply (rule WF_many_then; clarsimp?)
    subgoal by (rule ws_char_ws_well_formed; clarsimp)
    subgoal by pasi_pngi
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by (rule JNCO_wf)
    subgoal using I_pngi by pasi_pngi
    subgoal for a b c
      apply (insert fpci_JsonNameColonObject[of I \<open>(a,b)\<close> c]; clarsimp)
      by (rule ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> quot_chr, simplified])
    subgoal for c
      apply (clarsimp simp add: fpci_simps)
      apply (rule JsonNameColonObject_no_consume_past_comma)
      subgoal by (rule I_pngi)
      subgoal by (rule I_wf)
      subgoal by (rule I_dncp_comma)
      subgoal by (rule I_fpc_no_ws)
      subgoal using I_no_result_from_empty by blast
      done
    done
  subgoal for i c
    apply (cases i; clarsimp)
    subgoal by (clarsimp simp add: fpc_simps)
    apply (auto simp add: fpc_def NER_simps split: if_splits)
    subgoal
      apply (insert I_fpc_no_ws)
      apply (rule JsonNameColonObject_no_consume_past_ws[of _ c, OF I_pngi I_wf I_dncp_ws, simplified]; assumption?)
      using I_no_result_from_empty by blast
    subgoal
      apply (insert I_fpc_no_ws)
      apply (rule JsonNameColonObject_no_consume_past_ws[of _ c, OF I_pngi I_wf I_dncp_ws, simplified]; assumption?)
      using I_no_result_from_empty by blast
    subgoal by (rule JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_dncp_comma]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    subgoal by (rule JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_dncp_comma]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    subgoal by (rule JsonNameColonObject_no_consume_past_comma[OF I_pngi I_wf I_dncp_comma]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    done
  subgoal
    apply (insert c_val; auto)
    subgoal by (rule JsonNameColonObject_no_consume_past_closing_brace[OF I_pngi I_wf I_dncp_closing_brace]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    subgoal by (rule JsonNameColonObject_no_consume_past_closing_bracket[OF I_pngi I_wf I_dncp_closing_bracket]; insert I_fpc_no_ws I_no_result_from_empty; blast)
    done
  subgoal
    apply (rule JsonNameColonObject_drop_leftover[OF I_pngi]; assumption?)
    by (rule I_drop_leftover)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal for cs r l
    apply (insert c_val; auto)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by (clarsimp simp add: NER_simps)
    done
  subgoal by pasi_pngi
  subgoal using I_pngi by pasi_pngi
  subgoal for cM l abs cS a b
    using has_result_JsonNameColonObject[OF I_pngi, of \<open>cM@l\<close> b] by fastforce
  subgoal for i c
    apply (insert fpc_JsonNameColonObject[of I i c]; clarsimp)
    by (rule ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> quot_chr, simplified])
  done

lemma wf_many_then_ws_char_ws_comma_JNCO:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_dncp_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  shows "bidef_well_formed (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject J)))"
  apply (rule WF_many_then; clarsimp?) \<comment> \<open>Slightly different alternative: wf_many_then\<close>
  subgoal by (rule ws_char_ws_well_formed; clarsimp)
  subgoal by pasi_pngi
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (rule wf_JsonNameColonObject; clarsimp simp add: J_wf J_fpci_no_ws)
  subgoal using J_pngi by pasi_pngi
  subgoal for a b c
    apply (insert fpci_JsonNameColonObject[of J \<open>(a,b)\<close> c]; clarsimp)
    by (rule ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> quot_chr, simplified])
  subgoal for c
    apply (insert ws_char_ws_fpci[of \<open>CHR '',''\<close> \<open>()\<close> c]; clarsimp)
    apply (rule JsonNameColonObject_no_consume_past_comma)
    by (auto simp add: J_pngi J_wf J_dncp_comma J_fpc_no_ws J_no_parse_empty)
  done

lemma map_pair_snd:
  shows "map (Pair () \<circ> snd) l = l"
  by (induction l; clarsimp)

lemma wf_JNCO_sepBy_ws_char_ws_comma:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_dncp_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  shows "bidef_well_formed (separated_by (ws_char_ws CHR '','') (JsonNameColonObject J) ())"
  \<comment> \<open>There are a few rules we can use here, but I think that from the above it'll be easier\<close>
  unfolding separated_by_def
  apply (rule transform_well_formed4)
  subgoal
    apply (auto simp add: well_formed_transform_funcs4_def split: list.splits sum.splits)
    subgoal for i r l by (cases r; clarsimp)
    subgoal for i r r'a r'b rs l by (cases r; clarsimp simp add: map_pair_snd)
    done
  apply (rule optional_well_formed)
  subgoal by (clarsimp simp add: NER_simps separated_byBase_def)
  unfolding separated_byBase_def
  apply (rule b_then_well_formed)
  subgoal
    apply (rule wf_JsonNameColonObject)
    by (auto simp add: J_wf J_fpci_no_ws)
  subgoal
    apply (rule wf_many_then_ws_char_ws_comma_JNCO)
    by (auto simp add: J_pngi J_wf J_fpci_no_ws J_dncp_comma J_fpc_no_ws J_no_parse_empty)
  subgoal
    apply (rule first_printed_does_not_eat_into3; clarsimp?)
    subgoal
      apply (rule wf_JsonNameColonObject)
      by (auto simp add: J_wf J_fpci_no_ws)
    subgoal for i c
      apply (cases i; clarsimp simp add: fpci_simps print_empty)
      apply (rule JsonNameColonObject_no_consume_past_comma)
      by (auto simp add: J_pngi J_wf J_dncp_comma J_fpc_no_ws J_no_parse_empty)
    done
  done



abbreviation "betweenBraces bd \<equiv> takeMiddle (char_ws CHR ''{'') bd (ws_char CHR ''}'') () ()"
definition JsonObject :: "JSON bidef \<Rightarrow> JSON bidef" where
  "JsonObject i = ftransform
                    (Some o Object)
                    (\<lambda>Object ob \<Rightarrow> Some ob
                     | _ \<Rightarrow> None)
                    (betweenBraces (separated_by (ws_char_ws CHR '','') (JsonNameColonObject i) ()))"

lemma has_result_JsonObject[NER_simps]:
  "has_result (parse (JsonObject I)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i (Object od) l \<longleftrightarrow> has_result (parse (betweenBraces (separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ()))) i od l"
  "has_result (parse (JsonObject I)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonObject_def NER_simps takeMiddle_def)+

lemma JsonObject_first_char_result:
  "has_result (parse (JsonObject I)) (c # cs) r l \<Longrightarrow> c = CHR ''{''"
  by (cases r; clarsimp simp add: NER_simps takeMiddle_def split: if_splits)

lemma is_error_JsonObject[NER_simps]:
  "is_error (parse (JsonObject I)) []"
  "c \<noteq> CHR ''{'' \<Longrightarrow> is_error (parse (JsonObject I)) (c # i)"
  by (clarsimp simp add: JsonObject_def NER_simps takeMiddle_def)+

lemma JsonObject_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonObject I)) i [] \<longleftrightarrow> False"
  unfolding JsonObject_def
  by (clarsimp simp add: print_empty takeMiddle_def)

lemma PASI_PNGI_JsonObject[PASI_PNGI_intros]:
  assumes "PNGI (parse I)"
  shows "PASI (parse (JsonObject I))"
        "PNGI (parse (JsonObject I))"
  unfolding JsonObject_def apply (insert assms)
  by pasi_pngi+

lemma JsonObject_not_same_i_l[NER_simps]:
  assumes "PNGI (parse I)"
  shows "has_result (parse (JsonObject I)) l r l \<longleftrightarrow> False"
  using PASI_PNGI_JsonObject(1)[OF assms, unfolded PASI_def]
  by blast

lemma mono_JsonObject[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. JsonObject (A f))"
  unfolding JsonObject_def using ma
  by pf_mono_prover

lemma fpci_JsonObject[fpci_simps]:
  "first_printed_chari (print (JsonObject I )) i c \<Longrightarrow> c = CHR ''{''"
  unfolding JsonObject_def
  by (clarsimp simp add: fpci_simps takeMiddle_def print_empty split: JSON.splits if_splits)

lemma fpc_JsonObject[fpc_simps]:
  "fpc (parse (JsonObject I)) a c \<Longrightarrow> c = CHR ''{''"
  apply (clarsimp simp add: JsonObject_def fpc_simps)
  by (clarsimp simp add: fpc_def NER_simps str_literal_def takeMiddle_def)


lemma imply_and_eq_imply_one:
  "(a \<Longrightarrow> (A \<and> B)) \<Longrightarrow> (a \<Longrightarrow> B)"
  by blast
lemma eq_tl_dropWhile_append:
  assumes "c \<noteq> []"
  assumes "\<exists>x. x \<in> (set c) \<and> x \<notin> whitespace_chars"
  assumes "l = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) (c @ l))"
  shows "l' = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) (c @ l'))"
  apply (insert assms)
  apply (induction c; auto)
  by (metis dropWhile_eq_Nil_conv dropWhile_eq_self_iff)

lemma eq_tl_dropWhile_append2:
  assumes "cb' \<noteq> []"
  assumes "l2 \<noteq> []"
  assumes "l2 = tl (dropWhile (\<lambda>x. x \<in> whitespace_chars) (cb' @ l2))"
  shows "\<exists>x. x\<notin>whitespace_chars \<and> x\<in> (set cb')"
  using assms
  by (metis (no_types, lifting) Cons_eq_appendI dropWhile_append2 hd_Cons_tl list.simps(3) self_append_conv2 takeWhile_dropWhile_id tl_Nil)

lemma JsonObject_no_peek_past_end:
  assumes I_pngi: "PNGI (parse I)"
  assumes I_wf: "bidef_well_formed I"
  assumes I_dncp_b: "does_not_consume_past_char3 (parse I) CHR ''}''"
  assumes I_dncp_b': "does_not_consume_past_char3 (parse I) CHR '']''"
  assumes I_dncp_c: "does_not_consume_past_char3 (parse I) CHR '',''"
  assumes I_dncp_ws: "\<And>c. c \<in>whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse I) c"
  assumes I_fpc_no_ws: "\<And>i c. fpc (parse I) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes I_no_empty_parse: "\<nexists>r l. has_result (parse I) [] r l"
  assumes I_drop_leftover: "\<And>c l l' r. has_result (parse I) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse I) (c @ l) r l"

  assumes TEST: "does_not_consume_past_parse_consume (parse (separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ())) (parse (ws_char CHR ''}''))"

  shows "does_not_peek_past_end (parse (JsonObject I))"
  unfolding JsonObject_def
  apply (rule ftrans_does_not_peek_past_end)
  unfolding takeMiddle_def
  apply (rule transform_does_not_peek_past_end)
  apply (rule then_does_not_peek_past_end_with_inner_conflict)
  subgoal using I_pngi by pasi_pngi
  subgoal using I_pngi by pasi_pngi
  subgoal for ca cb a l b l''
    apply (rule exI[of _ \<open>cb @ l''\<close>]; rule conjI; clarsimp)
    subgoal
      apply (cases cb; clarsimp)
      subgoal
        using then_PASI_from_pngi_pasi[of \<open>separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ()\<close> \<open>ws_char CHR ''}''\<close>,
                                       OF separated_by_PNGI ws_char_PASI, OF PASI_PNGI_JsonNameColonObject(2), OF I_pngi,
                                       OF then_PASI_from_pasi_pngi, OF ws_char_ws_PASI, OF PASI_PNGI_JsonNameColonObject(2), OF I_pngi,
                                       \<comment> \<open>Wew\<close>
                                       unfolded PASI_def, rule_format, of l b l, simplified]
        by blast
      subgoal for cb' cbs
        apply (insert char_ws_has_result_implies_leftover_head[of \<open>CHR ''{''\<close> \<open>ca @ cb' # cbs @ l\<close> \<open>()\<close> \<open>cb' # cbs @ l\<close>]; clarsimp)
        apply (insert char_ws_does_not_consume_past_char3_rev[of cb' \<open>CHR ''{''\<close>, unfolded does_not_consume_past_char3_def]; clarsimp)
        by fast
      done
    subgoal
      apply (rule then_does_not_peek_past_end_with_inner_conflict[
                    of \<open>separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ()\<close> \<open>ws_char CHR ''}''\<close>,
                    unfolded does_not_peek_past_end_def, rule_format, of cb l b l'']; assumption?; clarsimp?)
      subgoal using I_pngi by pasi_pngi
      subgoal by pasi_pngi
      subgoal for ca' cb' rsb l2 l2'
        apply (rule exI[of _ \<open>cb'@l2'\<close>]; rule conjI)
        subgoal
          \<comment> \<open>Should probably remove the empty case here.\<close>
          apply (insert TEST[unfolded does_not_consume_past_parse_consume_def, rule_format, of ca' \<open>cb'@l2\<close> rsb cb' l2 \<open>()\<close> l2']; clarsimp)
          \<comment> \<open>How do we say that we do not peek past more than one char?\<close>
          \<comment> \<open>Maybe we adjust this?\<close>
          thm separated_by_no_consume_past_char

          using JsonNameColonObject_sepByComma_no_consume_past_chars
          thm separated_by_no_consume_past_char
          find_theorems separated_by name: "consume"
          sorry
        subgoal
          using ws_char_does_not_peek_past_end[of \<open>CHR ''}''\<close>, simplified, unfolded does_not_peek_past_end_def, rule_format] by blast
        done
      done
    done
  oops
  

abbreviation "betweenSquareBrackets bd \<equiv> takeMiddle (char_ws CHR ''['') bd (ws_char CHR '']'') () ()"
definition JsonList :: "JSON bidef \<Rightarrow> JSON bidef" where
  "JsonList i = ftransform
                  (Some o List)
                  (\<lambda>List l \<Rightarrow> Some l
                   | _ \<Rightarrow> None)
                  (betweenSquareBrackets (separated_by (ws_char_ws CHR '','') i ()))"

lemma PASI_PNGI_JsonList[PASI_PNGI_intros]:
  assumes "PNGI (parse I)"
  shows "PASI (parse (JsonList I))"
        "PNGI (parse (JsonList I))"
  unfolding JsonList_def apply (insert assms)
  by pasi_pngi+

lemma has_result_JsonList[NER_simps]:
  "has_result (parse (JsonList I)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (List ld) l \<longleftrightarrow> has_result (parse (betweenSquareBrackets (separated_by (ws_char_ws CHR '','') I ()))) i ld l"
  "has_result (parse (JsonList I)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonList_def NER_simps takeMiddle_def)+

lemma JsonList_first_char_result:
  "has_result (parse (JsonList I)) (c # cs) r l \<Longrightarrow> c = CHR ''[''"
  by (cases r; clarsimp simp add: NER_simps takeMiddle_def split: if_splits)

lemma JsonList_not_same_i_l[NER_simps]:
  assumes "PNGI (parse I)"
  shows "has_result (parse (JsonList I)) l r l \<longleftrightarrow> False"
  using PASI_PNGI_JsonList(1)[OF assms, unfolded PASI_def]
  by blast

lemma is_error_JsonList[NER_simps]:
  "is_error (parse (JsonList I)) []"
  "c \<noteq> CHR ''['' \<Longrightarrow> is_error (parse (JsonList I)) (c # i)"
  by (clarsimp simp add: JsonList_def NER_simps takeMiddle_def)+

lemma JsonList_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonList I)) i [] \<longleftrightarrow> False"
  unfolding JsonList_def
  by (clarsimp simp add: print_empty takeMiddle_def)

lemma mono_JsonList[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. JsonList (A f))"
  unfolding JsonList_def using ma
  by pf_mono_prover

lemma fpci_JsonList[fpci_simps]:
  "first_printed_chari (print (JsonList I )) i c \<Longrightarrow> c = CHR ''[''"
  unfolding JsonList_def
  by (clarsimp simp add: fpci_simps takeMiddle_def print_empty split: JSON.splits)

lemma fpc_JsonList[fpc_simps]:
  "fpc (parse (JsonList I)) a c \<Longrightarrow> c = CHR ''[''"
  apply (clarsimp simp add: JsonList_def fpc_simps)
  by (clarsimp simp add: fpc_def NER_simps takeMiddle_def)


lemma wf_Json_sepby_ws_char_ws_comma:
  assumes J_wf: "bidef_well_formed J"
  assumes J_error_empty: "is_error (parse J) []"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_fpc_no_ws: "\<And>i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_dncpc_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  shows "bidef_well_formed (separated_by (ws_char_ws CHR '','') J ())"
  apply (rule separated_by_well_formed_no_consume_past_char; clarsimp?)
  subgoal by (clarsimp simp add: good_separated_by_oracle_def fp_NER)
  subgoal by (rule J_wf)
  subgoal by (rule ws_char_ws_well_formed; clarsimp)
  subgoal by (rule J_error_empty)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by pasi_pngi
  subgoal for i c
    by (insert ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> c, simplified]; clarsimp simp add: J_fpci_no_ws)
  subgoal for c
    by (insert ws_char_ws_fpci[of \<open>CHR '',''\<close> \<open>()\<close> c]; clarsimp simp add: J_dncpc_comma)
  subgoal for b c
    apply (clarsimp simp add: fpci_simps print_empty)
    apply (rule then_does_not_consume_past3; clarsimp?)
    subgoal by (rule ws_char_ws_well_formed; clarsimp)
    subgoal by (rule J_wf)
    subgoal by (rule J_dncpc_comma)
    subgoal for b_pr i c
      by (insert ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> c, simplified]; clarsimp simp add: J_fpc_no_ws)
    subgoal using J_error_empty has_result_implies_not_is_error by fast
    done
  done

lemma Json_sepBy_ws_comma_ws_no_consume_past_closing_bracket:
  assumes J_error_empty: "is_error (parse J) []"
  assumes J_error_on_close_bracket: "\<And>l. is_error (parse J) (CHR '']'' # l)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_dncpc_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse J) c"
  assumes J_dncpc_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_dncpc_closing_bracket: "does_not_consume_past_char3 (parse J) CHR '']''"
  assumes J_can_drop_leftover: "\<And>c l l' a. has_result (parse J) (c @ l @ l') a (l @ l') \<Longrightarrow> has_result (parse J) (c @ l) a l"
  assumes J_pngi: "PNGI (parse J)"
  assumes J_fpc_no_ws: "\<And>i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3 (parse (separated_by (ws_char_ws CHR '','') J ())) CHR '']''"
  apply (rule separated_by_no_consume_past_char; clarsimp?)
  subgoal by (rule J_error_empty)
  subgoal by (rule J_error_on_close_bracket)
  subgoal by (rule J_wf)
  subgoal \<comment> \<open>bidef_well_formed (many (b_then (ws_char_ws CHR '','') J))\<close>
    apply (rule wf_many_then; clarsimp?)
    subgoal by (rule J_wf)
    subgoal by (rule ws_char_ws_well_formed; clarsimp)
    subgoal by (rule J_error_empty)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal by pasi_pngi
    subgoal for i c
      by (insert ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> c, simplified]; clarsimp simp add: J_fpci_no_ws)
    subgoal for b c
      apply (clarsimp simp add: fpci_simps print_empty)
      apply (rule then_does_not_consume_past3)
      subgoal by (rule ws_char_ws_well_formed; clarsimp)
      subgoal by (rule J_wf)
      subgoal by (rule J_dncpc_comma)
      subgoal for b_pr i c
        by (insert ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> c, simplified]; clarsimp simp add: J_fpc_no_ws)
      subgoal
        using J_error_empty J_wf is_error_implies_not_has_result by blast
      done
    done
  subgoal for i c
    apply (cases i; clarsimp simp add: fpc_simps) \<comment> \<open>Empty case dispatched\<close>
    apply (auto simp add: fpc_def NER_simps split: if_splits)
    subgoal by (rule J_dncpc_ws)
    subgoal by (rule J_dncpc_ws)
    subgoal by (rule J_dncpc_comma)
    subgoal by (rule J_dncpc_comma)
    subgoal by (rule J_dncpc_comma)
    done
  subgoal by (rule J_dncpc_closing_bracket)
  subgoal by (rule J_can_drop_leftover)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by pasi_pngi
  subgoal using J_pngi by pasi_pngi
  subgoal by (rule ws_char_ws_can_drop_past_leftover)
  subgoal for i c
    by (insert ws_char_ws_does_not_consume_past_char3[of \<open>CHR '',''\<close> c, simplified]; clarsimp simp add: J_fpc_no_ws)
  done

lemma wf_JsonList:
  assumes J_wf: "bidef_well_formed J"
  assumes J_error_empty: "is_error (parse J) []"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_fpc_no_ws: "\<And>i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_dncpc_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse J) c"
  assumes J_dncpc_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_dncpc_closing_bracket: "does_not_consume_past_char3 (parse J) CHR '']''"
  assumes J_no_print_empty: "\<And>a. \<not>p_has_result (print J) a []"
  assumes J_can_drop_leftover: "\<And>c l l' a. has_result (parse J) (c @ l @ l') a (l @ l') \<Longrightarrow> has_result (parse J) (c @ l) a l"
  assumes J_pngi: "PNGI (parse J)"
  assumes J_error_on_close_bracket: "\<And>l. is_error (parse J) (CHR '']'' # l)"
  shows "bidef_well_formed (JsonList J)"
  unfolding JsonList_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def fp_NER split: JSON.splits)
  unfolding takeMiddle_def
  apply (rule transform_well_formed4)
  subgoal by (clarsimp simp add: well_formed_transform_funcs4_def)
  apply (rule b_then_well_formed)
  subgoal by (rule char_ws_well_formed; clarsimp)
   defer \<comment> \<open>bidef_well_formed (b_then (separated_by (ws_char_ws CHR '','') J ()) (ws_char CHR '']''))\<close>
  subgoal
    apply (rule first_printed_does_not_eat_into3; clarsimp?)
    subgoal by (rule char_ws_well_formed; clarsimp)
    subgoal for a c
      apply (cases a; clarsimp simp add: fpci_simps print_empty J_no_print_empty)
      subgoal
        using char_ws_does_not_consume_past_char3[of \<open>CHR ''[''\<close> \<open>CHR '']''\<close>, simplified]
        by fast
      subgoal for a' as
        apply (insert J_fpci_no_ws[of a' c]; clarsimp)
        using char_ws_does_not_consume_past_char3[of \<open>CHR ''[''\<close> c, simplified]
        by fast
      done
    done
  apply (rule b_then_well_formed) \<comment> \<open>Other possible here\<close>
  subgoal
    apply (rule wf_Json_sepby_ws_char_ws_comma)
    by (auto simp add: J_wf J_error_empty J_fpci_no_ws J_fpc_no_ws J_dncpc_comma)
  subgoal by (rule ws_char_well_formed; clarsimp)
  apply (rule first_printed_does_not_eat_into3; clarsimp?)
  subgoal
    apply (rule wf_Json_sepby_ws_char_ws_comma)
    by (auto simp add: J_wf J_error_empty J_fpci_no_ws J_fpc_no_ws J_dncpc_comma)
  subgoal for c
    apply (insert ws_char_fpci[of \<open>CHR '']''\<close> \<open>()\<close> c]; clarsimp)
    apply (rule Json_sepBy_ws_comma_ws_no_consume_past_closing_bracket)
    by (auto simp add: J_error_empty J_wf J_dncpc_comma J_dncpc_ws J_dncpc_closing_bracket
                       J_can_drop_leftover J_pngi J_fpc_no_ws J_fpci_no_ws J_error_on_close_bracket)
  done




definition JsonTrue :: "JSON bidef" where
  "JsonTrue = ftransform
                  (Some o (const JTrue))
                  (\<lambda>JTrue \<Rightarrow> Some ''true''
                   | _ \<Rightarrow> None)
                  (this_string ''true'')"

lemma has_result_JsonTrue[NER_simps]:
  "has_result (parse (JsonTrue)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i JTrue l \<longleftrightarrow> has_result (parse (this_string ''true'')) i ''true'' l"
  "has_result (parse (JsonTrue)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i JNull l \<longleftrightarrow> False"
  "has_result (parse JsonTrue) l r l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonTrue_def NER_simps)+

lemma JsonTrue_first_char_result:
  "has_result (parse (JsonTrue)) (c # cs) r l \<Longrightarrow> c = CHR ''t''"
  by (cases r; clarsimp simp add: NER_simps split: if_splits)

lemma is_error_JsonTrue[NER_simps]:
  "is_error (parse (JsonTrue)) []"
  "c \<noteq> CHR ''t'' \<Longrightarrow> is_error (parse (JsonTrue)) (c # i)"
  by (clarsimp simp add: JsonTrue_def NER_simps)+

lemma JsonTrue_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonTrue)) i [] \<longleftrightarrow> False"
  unfolding JsonTrue_def
  by (clarsimp simp add: print_empty)

lemma PASI_PNGI_JsonTrue[PASI_PNGI_intros]:
  shows "PASI (parse JsonTrue)"
        "PNGI (parse JsonTrue)"
  unfolding JsonTrue_def
  by pasi_pngi+

lemma fpci_JsonTrue[fpci_simps]:
  "first_printed_chari (print (JsonTrue)) i c \<Longrightarrow> c = CHR ''t''"
  unfolding JsonTrue_def
  by (clarsimp simp add: fpci_simps print_empty split: JSON.splits)

lemma fpc_JsonTrue[fpc_simps]:
  "fpc (parse (JsonTrue)) a c \<Longrightarrow> c = CHR ''t''"
  by (clarsimp simp add: JsonTrue_def fpc_simps)

lemma JsonTrue_can_drop_leftover_on_error:
  assumes "is_error (parse JsonTrue) (c @ l)"
  shows "is_error (parse JsonTrue) c"
  using assms
  by (clarsimp simp add: NER_simps JsonTrue_def)

lemma JsonTrue_can_drop_leftover_on_error2:
  assumes "is_error (parse JsonTrue) (c @ l @ l')"
  shows "is_error (parse JsonTrue) (c @ l)"
  using assms
  apply (clarsimp simp add: NER_simps JsonTrue_def)
  by (smt (verit, ccfv_threshold) append.assoc append_is_Nil_conv hd_append2 tl_append2)

lemma JsonTrue_no_peek_past_end:
  "does_not_peek_past_end (parse JsonTrue)"
  unfolding JsonTrue_def
  apply (rule ftrans_does_not_peek_past_end)
  by (rule this_string_does_not_peek_past_end)

lemma JsonTrue_drop_leftover:
  shows "has_result (parse JsonTrue) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse JsonTrue) (c @ l) r l"
  using JsonTrue_no_peek_past_end[unfolded does_not_peek_past_end_def]
  by blast

lemma wf_JsonTrue:
  "bidef_well_formed JsonTrue"
  unfolding JsonTrue_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def NER_simps fp_NER split: JSON.splits)
  subgoal by (rule this_string_wf)
  done



definition JsonFalse :: "JSON bidef" where
  "JsonFalse = ftransform
                  (Some o (const JFalse))
                  (\<lambda>JFalse \<Rightarrow> Some ''false''
                   | _ \<Rightarrow> None)
                  (this_string ''false'')"

lemma has_result_JsonFalse[NER_simps]:
  "has_result (parse (JsonFalse)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i JFalse l \<longleftrightarrow> has_result (parse (this_string ''false'')) i ''false'' l"
  "has_result (parse (JsonFalse)) i JNull l \<longleftrightarrow> False"
  "has_result (parse JsonFalse) l r l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonFalse_def NER_simps)+

lemma JsonFalse_first_char_result:
  "has_result (parse (JsonFalse)) (c # cs) r l \<Longrightarrow> c = CHR ''f''"
  by (cases r; clarsimp simp add: NER_simps)

lemma is_error_JsonFalse[NER_simps]:
  "is_error (parse (JsonFalse)) []"
  "c \<noteq> CHR ''f'' \<Longrightarrow> is_error (parse (JsonFalse)) (c # i)"
  by (clarsimp simp add: JsonFalse_def NER_simps)+

lemma JsonFalse_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonFalse)) i [] \<longleftrightarrow> False"
  unfolding JsonFalse_def
  by (clarsimp simp add: print_empty)

lemma PASI_PNGI_JsonFalse[PASI_PNGI_intros]:
  shows "PASI (parse JsonFalse)"
        "PNGI (parse JsonFalse)"
  unfolding JsonFalse_def
  by pasi_pngi+

lemma fpci_JsonFalse[fpci_simps]:
  "first_printed_chari (print (JsonFalse)) i c \<Longrightarrow> c = CHR ''f''"
  unfolding JsonFalse_def
  by (clarsimp simp add: fpci_simps print_empty split: JSON.splits)

lemma fpc_JsonFalse[fpc_simps]:
  "fpc (parse (JsonFalse)) a c \<Longrightarrow> c = CHR ''f''"
  by (clarsimp simp add: JsonFalse_def fpc_simps)

lemma JsonFalse_can_drop_leftover_on_error:
  assumes "is_error (parse JsonFalse) (c @ l)"
  shows "is_error (parse JsonFalse) c"
  using assms
  by (clarsimp simp add: NER_simps JsonFalse_def)

lemma JsonFalse_can_drop_leftover_on_error2:
  assumes "is_error (parse JsonFalse) (c @ l @ l')"
  shows "is_error (parse JsonFalse) (c @ l)"
  apply (insert assms)
  unfolding JsonFalse_def
  apply (clarsimp simp add: ftransform_is_error)
  by (rule this_string_drop_leftover_on_error)

lemma JsonFalse_drop_leftover:
  shows "has_result (parse JsonFalse) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse JsonFalse) (c @ l) r l"
  unfolding JsonFalse_def
  apply (clarsimp simp add: ftransform_has_result)
  subgoal for r
    apply (rule exI[of _ r])
    by (rule this_string_drop_leftover)
  done


lemma JsonFalse_no_peek_past_end:
  "does_not_peek_past_end (parse JsonFalse)"
  unfolding JsonFalse_def
  apply (rule ftrans_does_not_peek_past_end)
  by (rule this_string_does_not_peek_past_end)

lemma wf_JsonFalse:
  "bidef_well_formed JsonFalse"
  unfolding JsonFalse_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def NER_simps fp_NER split: JSON.splits)
  subgoal by (rule this_string_wf)
  done



definition JsonNull :: "JSON bidef" where
  "JsonNull = ftransform
                  (Some o (const JNull))
                  (\<lambda>JNull \<Rightarrow> Some ''null''
                   | _ \<Rightarrow> None)
                  (this_string ''null'')"

lemma has_result_JsonNull[NER_simps]:
  "has_result (parse (JsonNull)) [] r l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i JNull l \<longleftrightarrow> has_result (parse (this_string ''null'')) i ''null'' l"
  "has_result (parse JsonNull) l r l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonNull_def NER_simps)+

lemma JsonNull_first_char_result:
  "has_result (parse (JsonNull)) (c # cs) r l \<Longrightarrow> c = CHR ''n''"
  by (cases r; clarsimp simp add: NER_simps)

lemma is_error_JsonNull[NER_simps]:
  "is_error (parse (JsonNull)) []"
  "c \<noteq> CHR ''n'' \<Longrightarrow> is_error (parse (JsonNull)) (c # i)"
  by (clarsimp simp add: JsonNull_def NER_simps)+

lemma JsonNull_print_empty[fp_NER, print_empty]:
  "p_has_result (print (JsonNull)) i [] \<longleftrightarrow> False"
  unfolding JsonNull_def
  by (clarsimp simp add: print_empty)

lemma PASI_PNGI_JsonNull[PASI_PNGI_intros]:
  shows "PASI (parse JsonNull)"
        "PNGI (parse JsonNull)"
  unfolding JsonNull_def
  by pasi_pngi+

lemma fpci_JsonNull[fpci_simps]:
  "first_printed_chari (print (JsonNull)) i c \<Longrightarrow> c = CHR ''n''"
  unfolding JsonNull_def
  by (clarsimp simp add: fpci_simps print_empty split: JSON.splits)

lemma fpc_JsonNull[fpc_simps]:
  "fpc (parse (JsonNull)) a c \<Longrightarrow> c = CHR ''n''"
  by (clarsimp simp add: JsonNull_def fpc_simps)

lemma JsonNull_can_drop_leftover_on_error:
  assumes "is_error (parse JsonNull) (c @ l)"
  shows "is_error (parse JsonNull) c"
  using assms
  by (clarsimp simp add: NER_simps JsonNull_def)

lemma JsonNull_can_drop_leftover_on_error2:
  assumes "is_error (parse JsonNull) (c @ l @ l')"
  shows "is_error (parse JsonNull) (c @ l)"
  apply (insert assms)
  unfolding JsonNull_def
  apply (clarsimp simp add: ftransform_is_error)
  by (rule this_string_drop_leftover_on_error)

lemma JsonNull_drop_leftover:
  shows "has_result (parse JsonNull) (c @ l @ l') r (l @ l')
            \<Longrightarrow> has_result (parse JsonNull) (c @ l) r l"
  unfolding JsonNull_def
  apply (clarsimp simp add: ftransform_has_result)
  subgoal for r
    apply (rule exI[of _ r])
    by (rule this_string_drop_leftover)
  done

lemma JsonNull_no_peek_past_end:
  "does_not_peek_past_end (parse JsonNull)"
  unfolding JsonNull_def
  apply (rule ftrans_does_not_peek_past_end)
  by (rule this_string_does_not_peek_past_end)

lemma wf_JsonNull:
  "bidef_well_formed JsonNull"
  unfolding JsonNull_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def NER_simps fp_NER split: JSON.splits)
  subgoal by (rule this_string_wf)
  done



\<comment> \<open>Seems to me like this could be done better?\<close>
fun sum_take_many :: "JSON + JSON + JSON + JSON + JSON + JSON + JSON \<Rightarrow> JSON" where
  "sum_take_many (Inl j) = j"
| "sum_take_many (Inr (Inl j)) = j"
| "sum_take_many (Inr (Inr (Inl j))) = j"
| "sum_take_many (Inr (Inr (Inr (Inl j)))) = j"
| "sum_take_many (Inr (Inr (Inr (Inr (Inl j))))) = j"
| "sum_take_many (Inr (Inr (Inr (Inr (Inr (Inl j)))))) = j"
| "sum_take_many (Inr (Inr (Inr (Inr (Inr (Inr j)))))) = j"


fun sum_untake_many :: "JSON \<Rightarrow> JSON + JSON + JSON + JSON + JSON + JSON + JSON" where
  "sum_untake_many (String s) = Inl (String s)"
| "sum_untake_many (Number s) = Inr (Inl (Number s))"
| "sum_untake_many (Object s) = Inr (Inr (Inl (Object s)))"
| "sum_untake_many (List s)   = Inr (Inr (Inr (Inl (List s))))"
| "sum_untake_many JTrue      = Inr (Inr (Inr (Inr (Inl JTrue))))"
| "sum_untake_many JFalse     = Inr (Inr (Inr (Inr (Inr (Inl JFalse)))))"
| "sum_untake_many JNull      = Inr (Inr (Inr (Inr (Inr (Inr JNull)))))"


\<comment> \<open>Strictly speaking JSON is only correct\<close>
partial_function (bd) JsonR :: "unit \<Rightarrow> JSON bidef" where
  "JsonR u = transform
            sum_take_many
            sum_untake_many
            (or JsonString
            (or JsonNumber
            (or (JsonObject (JsonR ()))
            (or (JsonList (JsonR ()))
            (or JsonTrue
            (or JsonFalse
                JsonNull
             ))))))"
abbreviation "Json \<equiv> JsonR ()"

\<comment> \<open>Note that this is not provable using the induction method as the bottom type does not error on empty.\<close>
lemma Json_error_on_empty:
  "(is_error (parse Json) [])"
  apply (subst JsonR.simps)
  by (clarsimp simp add: NER_simps)

\<comment> \<open>Note that this is not provable using the induction method as the bottom parser always nonterms.\<close>
lemma Json_error_on_close_bracket:
  "\<forall>l. is_error (parse Json) (CHR '']'' # l)"
  apply (subst JsonR.simps)
  by (clarsimp simp add: NER_simps)


lemma char_ws_not_eat_into_object:
  shows "pa_does_not_eat_into_pb_nondep
           (char_ws CHR ''{'')
           (b_then (separated_by (ws_char_ws CHR '','') (JsonNameColonObject J) ()) (ws_char CHR ''}''))"
  apply (rule first_printed_does_not_eat_into3)
  subgoal by (rule char_ws_well_formed; clarsimp)
  apply (auto simp add: fpci_simps print_empty split: list.splits)
  subgoal by (clarsimp simp add: char_ws_does_not_consume_past_char3)
  subgoal for c a b
    \<comment> \<open>Why did this not apply in auto?\<close>
    apply (insert fpci_JsonNameColonObject[of J \<open>(a,b)\<close> c]; clarsimp)
    by (clarsimp simp add: char_ws_does_not_consume_past_char3)
  done

\<comment> \<open>We may be able to copy this proof and slighly change it for ]\<close>
lemma JsonNameColonObject_sepBy_ws_char_ws_no_eat_into_ws_char_closing_brace:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse J) CHR ''}''"
  assumes J_no_consume_past_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_no_consume_past_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse J) c"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  assumes J_drop_leftover: "\<And>c l l' r. has_result (parse J) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse J) (c @ l) r l"
  assumes many_comma_then_jcno_wf: "bidef_well_formed (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject J)))"
  assumes inner_wf: "bidef_well_formed (separated_by (ws_char_ws CHR '','') (JsonNameColonObject J) ())"
  shows "pa_does_not_eat_into_pb_nondep (separated_by (ws_char_ws CHR '','') (JsonNameColonObject J) ()) (ws_char CHR ''}'')"
  apply (rule first_printed_does_not_eat_into3)
  subgoal by (rule inner_wf)
  apply (clarsimp simp add: fpci_simps)
  thm JsonNameColonObject_sepByComma_no_consume_past_chars \<comment> \<open>TODO: move to this rule (but only if below fails, which it looks like it wont.)\<close>
  apply (clarsimp simp add: separated_by_def)
  apply (rule transform_does_not_consume_past_char3)
  apply (rule optional_does_not_consume_past_char3)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps)
  subgoal
    apply (clarsimp simp add: separated_byBase_def)
    apply (rule then_does_not_consume_past3_from_can_drop_leftover)
    subgoal by (rule wf_JsonNameColonObject; clarsimp simp add: J_wf J_fpci_no_ws)
    subgoal by (rule many_comma_then_jcno_wf)
    subgoal
      apply (rule many_does_not_consume_past_char3)
      subgoal using J_pngi by pasi_pngi
      subgoal using J_pngi by pasi_pngi
      subgoal by (clarsimp simp add: NER_simps)
      subgoal by (clarsimp simp add: NER_simps)
      subgoal for c l l' r
        \<comment> \<open>Inner can drop past leftover\<close>
        apply (rule then_can_drop_leftover[of _ _ c l l' r]; assumption?)
        subgoal by (rule ws_char_ws_can_drop_past_leftover; assumption)
        subgoal by pasi_pngi
        subgoal for cJ wJ lJ rJ
          \<comment> \<open>JsonNameColonObject can drop past leftover\<close>
          apply (rule JsonNameColonObject_drop_leftover[of J cJ wJ lJ rJ, OF J_pngi]; assumption?)
          by (rule J_drop_leftover)
        subgoal using J_pngi by pasi_pngi
        done
      subgoal
        apply (rule ws_char_ws_then_JNCO_no_consume_past_char[of J \<open>CHR ''}''\<close>,
                      OF J_pngi J_wf _ _ _ J_no_consume_past_closing_brace _ J_no_consume_past_ws])
        by (auto simp add: J_fpc_no_ws J_fpci_no_ws J_no_parse_empty)
      subgoal for i c
        apply (auto simp add: fpc_def NER_simps split: if_splits)
        subgoal
          apply (rule ws_char_ws_then_JNCO_no_consume_past_char[of J c,
                        OF J_pngi J_wf _ _ _ J_no_consume_past_ws _ J_no_consume_past_ws])
          by (auto simp add: J_fpc_no_ws J_fpci_no_ws J_no_parse_empty)
        subgoal
          apply (rule ws_char_ws_then_JNCO_no_consume_past_char[of J c,
                        OF J_pngi J_wf _ _ _ J_no_consume_past_ws _ J_no_consume_past_ws])
          by (auto simp add: J_fpc_no_ws J_fpci_no_ws J_no_parse_empty)
        subgoal
          apply (rule ws_char_ws_then_JNCO_no_consume_past_char[of J \<open>CHR '',''\<close>,
                        OF J_pngi J_wf _ _ _ J_no_consume_past_comma _ J_no_consume_past_ws])
          by (auto simp add: J_fpc_no_ws J_fpci_no_ws J_no_parse_empty)
        subgoal
          apply (rule ws_char_ws_then_JNCO_no_consume_past_char[of J \<open>CHR '',''\<close>,
                        OF J_pngi J_wf _ _ _ J_no_consume_past_comma _ J_no_consume_past_ws])
          by (auto simp add: J_fpc_no_ws J_fpci_no_ws J_no_parse_empty)
        subgoal
          apply (rule ws_char_ws_then_JNCO_no_consume_past_char[of J \<open>CHR '',''\<close>,
                        OF J_pngi J_wf _ _ _ J_no_consume_past_comma _ J_no_consume_past_ws])
          by (auto simp add: J_fpc_no_ws J_fpci_no_ws J_no_parse_empty)
        done
      done
    subgoal for i c
      apply (cases i; clarsimp simp add: fpc_simps) \<comment> \<open>Empty case is dispatched\<close>
      subgoal for a b abs
        apply (auto simp add: fpc_def many_has_result_safe(2) b_then_has_result ws_char_ws_has_result split: if_splits)
        subgoal
          apply (insert J_fpc_no_ws)
          apply (rule JsonNameColonObject_no_consume_past_ws[of _ c, OF J_pngi J_wf J_no_consume_past_ws, simplified]; assumption?)
          using J_no_parse_empty by blast
        subgoal
          apply (insert J_fpc_no_ws)
          apply (rule JsonNameColonObject_no_consume_past_ws[of _ c, OF J_pngi J_wf J_no_consume_past_ws, simplified]; assumption?)
          using J_no_parse_empty by blast
        subgoal
          apply (rule JsonNameColonObject_no_consume_past_comma[OF J_pngi J_wf J_no_consume_past_comma])
          using J_fpc_no_ws J_no_parse_empty by blast+
        subgoal
          apply (rule JsonNameColonObject_no_consume_past_comma[OF J_pngi J_wf J_no_consume_past_comma])
          using J_fpc_no_ws J_no_parse_empty by blast+
        subgoal
          apply (rule JsonNameColonObject_no_consume_past_comma[OF J_pngi J_wf J_no_consume_past_comma])
          using J_fpc_no_ws J_no_parse_empty by blast+
        done
      done
    subgoal
      apply (rule JsonNameColonObject_no_consume_past_closing_brace)
      subgoal by (rule J_pngi)
      subgoal by (rule J_wf)
      subgoal by (rule J_no_consume_past_closing_brace)
      subgoal by (rule J_fpc_no_ws)
      subgoal by (rule J_no_parse_empty)
      done
    subgoal by (rule JsonNameColonObject_drop_leftover[OF J_pngi]; assumption?; rule J_drop_leftover)
    done
  done


lemma WF_JsonObject:
  assumes J_wf: "bidef_well_formed J"
  assumes J_pngi: "PNGI (parse J)"
  assumes J_dncpc_closing_brace: "does_not_consume_past_char3 (parse J) CHR ''}''"
  assumes J_dncpc_comma: "does_not_consume_past_char3 (parse J) CHR '',''"
  assumes J_no_consume_past_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse J) c"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_fpci_no_ws: "\<And>i c. first_printed_chari (print J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  assumes J_drop_leftover: "\<And>c l l' r. has_result (parse J) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse J) (c @ l) r l"
  shows "bidef_well_formed (JsonObject J)"
  unfolding JsonObject_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: well_formed_ftransform_funcs_def fp_NER split: JSON.splits)
  subgoal
    unfolding takeMiddle_def
    apply (rule transform_well_formed4)
    subgoal by (clarsimp simp add: well_formed_transform_funcs4_def)
    subgoal
      apply (rule b_then_well_formed[rotated, rotated])
      subgoal by (rule char_ws_not_eat_into_object)
      subgoal by (rule char_ws_well_formed; clarsimp)
      subgoal
        apply (rule b_then_well_formed)
        subgoal
          apply (rule wf_JNCO_sepBy_ws_char_ws_comma)
          by (auto simp add: J_pngi J_wf J_fpci_no_ws J_dncpc_comma J_fpc_no_ws J_no_parse_empty)
        subgoal by (rule ws_char_well_formed; clarsimp)
        subgoal
          apply (rule JsonNameColonObject_sepBy_ws_char_ws_no_eat_into_ws_char_closing_brace)
          apply (auto simp add: J_pngi J_wf J_dncpc_closing_brace J_dncpc_comma J_no_consume_past_ws
              J_fpc_no_ws J_no_parse_empty J_drop_leftover J_fpci_no_ws)
          subgoal
            apply (rule wf_many_then_ws_char_ws_comma_JNCO)
            by (auto simp add: J_pngi J_wf J_fpci_no_ws J_dncpc_comma J_fpc_no_ws J_no_parse_empty)
          subgoal
            apply (rule wf_JNCO_sepBy_ws_char_ws_comma)
            by (auto simp add: J_pngi J_wf J_fpci_no_ws J_dncpc_comma J_fpc_no_ws J_no_parse_empty)
          done
        done
      done
    done
  done


lemma Json_well_formed_inductive:
  assumes J_wf: "bidef_well_formed (J ())"
  assumes J_pngi: "PNGI (parse (J ()))"
  assumes J_no_result_from_empty: "\<forall>r x. \<not> has_result (parse (J ())) [] r x"
  assumes J_fpc_no_ws: "\<forall>i c. fpc (parse (J ())) i c \<longrightarrow> c \<notin> whitespace_chars"
  assumes J_dncpc_closing_brace: "does_not_consume_past_char3 (parse (J ())) CHR ''}''"
  assumes J_dncpc_closing_bracket: "does_not_consume_past_char3 (parse (J ())) CHR '']''"
  assumes J_dncpc_comma: "does_not_consume_past_char3 (parse (J ())) CHR '',''"
  assumes J_dncpc_ws: "\<And>c. c \<in> whitespace_chars \<Longrightarrow> does_not_consume_past_char3 (parse (J ())) c"
  assumes J_drop_leftover: "\<And>c l l' r. has_result (parse (J ())) (c @ l @ l') r (l @ l') \<Longrightarrow> has_result (parse (J ())) (c @ l) r l"
  assumes J_error_on_close_bracket: "\<And>l. is_error (parse (J ())) (CHR '']'' # l)"
  assumes J_error_empty: "is_error (parse (J ())) []"
  shows "bidef_well_formed
          (transform
             sum_take_many
             sum_untake_many 
            (or JsonString
            (or JsonNumber
            (or (JsonObject (J ()))
            (or (JsonList (J ()))
            (or JsonTrue
            (or JsonFalse
                JsonNull)))))))"
  apply (rule transform_well_formed4)
  subgoal
    apply (auto simp add: well_formed_transform_funcs4_def)
    subgoal for i v l
      apply (cases v rule: sum_take_many.cases; auto simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      subgoal for a by (cases a; clarsimp simp add: NER_simps)
      done
    subgoal for pr t by (cases t; auto simp add: NER_simps)
    done
  apply (rule or_well_formed)
  subgoal by (rule JsonString_well_formed)
  subgoal
    apply (rule or_well_formed)
    subgoal by (rule wf_JsonNumber)
    subgoal
      apply (rule or_well_formed)
      subgoal
        apply (rule WF_JsonObject)
          apply (auto simp add: J_wf J_pngi J_dncpc_closing_brace J_dncpc_comma J_dncpc_ws J_fpc_no_ws J_no_result_from_empty J_drop_leftover)
        using fpci_implies_fpc[OF J_wf] J_fpc_no_ws by blast
      subgoal
        apply (rule or_well_formed)
        subgoal
          apply (rule wf_JsonList)
            apply (auto simp add: J_wf J_fpc_no_ws J_dncpc_ws J_dncpc_comma J_dncpc_closing_bracket J_drop_leftover J_pngi J_error_on_close_bracket)
          subgoal by (rule J_error_empty)
          subgoal
            using fpci_implies_fpc[OF J_wf] J_fpc_no_ws by blast
          subgoal
            using J_error_empty J_wf wf_no_empty_parse_means_no_empty_print by fast
          done
        subgoal
          apply (rule or_well_formed)
          subgoal by (rule wf_JsonTrue)
          subgoal
            apply (rule or_well_formed)
            subgoal by (rule wf_JsonFalse)
            subgoal by (rule wf_JsonNull)
            subgoal
              apply (rule wf_or_pair_from_fpci)
              subgoal using fpci_JsonNull is_error_JsonFalse by blast
              subgoal by (clarsimp simp add: print_empty)
              done
            done
          subgoal
            apply (rule wf_or_pair_from_fpci)
            subgoal for i i' c
              apply (auto simp add: fpci_simps NER_simps split: sum.splits)
              subgoal for x by (insert fpci_JsonFalse[of x c]; clarsimp simp add: is_error_JsonTrue)
              subgoal for x by (insert fpci_JsonNull[of x c]; clarsimp simp add: is_error_JsonTrue)
              done
            subgoal by (clarsimp simp add: print_empty NER_simps split: sum.splits)
            done
          done
        subgoal
          apply (rule wf_or_pair_from_fpci)
          subgoal for i i' c
            apply (auto simp add: fpci_simps NER_simps split: sum.splits)
            subgoal for x by (insert fpci_JsonTrue[of x c]; clarsimp simp add: is_error_JsonList)
            subgoal for x by (insert fpci_JsonFalse[of x c]; clarsimp simp add: is_error_JsonList)
            subgoal for x by (insert fpci_JsonNull[of x c]; clarsimp simp add: is_error_JsonList)
            done
          subgoal by (clarsimp simp add: print_empty NER_simps split: sum.splits)
          done
        done
      subgoal
        apply (rule wf_or_pair_from_fpci)
        subgoal for i i' c
          apply (auto simp add: fpci_simps NER_simps split: sum.splits)
          subgoal for x by (insert fpci_JsonList[of \<open>J ()\<close> x c]; clarsimp simp add: is_error_JsonObject)
          subgoal for x by (insert fpci_JsonTrue[of x c]; clarsimp simp add: is_error_JsonObject)
          subgoal for x by (insert fpci_JsonFalse[of x c]; clarsimp simp add: is_error_JsonObject)
          subgoal for x by (insert fpci_JsonNull[of x c]; clarsimp simp add: is_error_JsonObject)
          done
        subgoal by (clarsimp simp add: print_empty NER_simps split: sum.splits)
        done
      done
    subgoal
      apply (rule wf_or_pair_from_fpci)
      subgoal for i i' c
        apply (auto simp add: fpci_simps NER_simps split: sum.splits)
        subgoal for x by (insert fpci_JsonObject[of \<open>J ()\<close> x c]; clarsimp simp add: is_error_JsonNumber)
        subgoal for x by (insert fpci_JsonList[of \<open>J ()\<close> x c]; clarsimp simp add: is_error_JsonNumber)
        subgoal for x by (insert fpci_JsonTrue[of x c]; clarsimp simp add: is_error_JsonNumber)
        subgoal for x by (insert fpci_JsonFalse[of x c]; clarsimp simp add: is_error_JsonNumber)
        subgoal for x by (insert fpci_JsonNull[of x c]; clarsimp simp add: is_error_JsonNumber)
        done
      subgoal by (clarsimp simp add: print_empty NER_simps split: sum.splits)
      done
    done
  subgoal
    apply (rule wf_or_pair_from_fpci)
    subgoal
      apply (auto simp add: fpci_simps NER_simps split: sum.splits)
      using fpci_JsonNumber fpci_JsonObject fpci_JsonList fpci_JsonTrue fpci_JsonFalse fpci_JsonNull
            is_error_JsonString
      by blast+
    subgoal by (clarsimp simp add: print_empty NER_simps split: sum.splits)
    done
  done

lemma inductive_Json_no_empty_result:
  shows "\<not> has_result
                  (parse
                    (transform sum_take_many sum_untake_many
                      (derived_or.or JsonString (derived_or.or JsonNumber (derived_or.or (JsonObject (J ())) (derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))))))))
                  [] r x"
  by (clarsimp simp add: NER_simps split: sum.splits)

\<comment> \<open>wew\<close>
lemma inductive_Json_fpc_not_ws:
  "\<forall>i c. fpc (parse (transform
                       sum_take_many
                       sum_untake_many
                       (derived_or.or JsonString (derived_or.or JsonNumber (derived_or.or (JsonObject (J ())) (derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))))))))
                i c \<longrightarrow>
               c \<notin> whitespace_chars"
  apply (clarsimp simp add: transform_fpc)
  subgoal for c i
    apply (cases i; clarsimp)
    subgoal for a
      apply (insert fpc_or_safe(1)[of JsonString \<open>derived_or.or JsonNumber (derived_or.or (JsonObject (J ())) (derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))))\<close> a c])
      apply clarsimp
      using fpc_JsonString[of a c]
      by simp
    subgoal for b
      apply (cases b; clarsimp)
      subgoal for c'
        apply (insert fpc_or[of JsonString \<open>derived_or.or JsonNumber (derived_or.or (JsonObject (J ())) (derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))))\<close> \<open>Inr b\<close> c])
        apply clarsimp
        apply (insert fpc_or[of JsonNumber \<open>derived_or.or (JsonObject (J ())) (derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull)))\<close> \<open>Inl c'\<close> c])
        apply clarsimp
        by (insert fpc_JsonNumber[of c' c]; auto)
      subgoal for c'
        apply (insert fpc_or_safe(2)[THEN fpc_or_safe(2), of JsonString JsonNumber \<open>derived_or.or (JsonObject (J ())) (derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull)))\<close> c' c]; clarsimp)
        apply (cases c'; clarsimp)
        subgoal for d
          apply (insert fpc_or_safe(1)[of \<open>JsonObject (J ())\<close> \<open>derived_or.or (JsonList (J ())) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))\<close> d c]; clarsimp)
          by (insert fpc_JsonObject[of \<open>J ()\<close> d c]; clarsimp)
        subgoal for d
          apply (cases d; clarsimp)
          subgoal for e
            apply (insert fpc_or_safe(2)[THEN fpc_or_safe(1), of \<open>JsonObject (J ())\<close> \<open>JsonList (J ())\<close> \<open>derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull)\<close> e c]; clarsimp)
            by (insert fpc_JsonList[of \<open>J ()\<close> e c]; clarsimp)
          subgoal for e
            apply (cases e; clarsimp)
            subgoal for f
              apply (insert fpc_or_safe(2)[THEN fpc_or_safe(2)[THEN fpc_or_safe(1)], of \<open>JsonObject (J ())\<close> \<open>JsonList (J ())\<close> JsonTrue \<open>derived_or.or JsonFalse JsonNull\<close> f c]; clarsimp)
              by (insert fpc_JsonTrue[of f c]; clarsimp)
            subgoal for f
              apply (cases f; clarsimp)
              subgoal for g
                apply (insert fpc_or_safe(2)[THEN fpc_or_safe(2)[THEN fpc_or_safe(2)[THEN fpc_or_safe(1)]], of \<open>JsonObject (J ())\<close> \<open>JsonList (J ())\<close> JsonTrue JsonFalse JsonNull g c]; clarsimp)
                by (insert fpc_JsonFalse[of g c]; clarsimp)
              subgoal for g
                apply (insert fpc_or_safe(2)[THEN fpc_or_safe(2)[THEN fpc_or_safe(2)[THEN fpc_or_safe(2)]], of \<open>JsonObject (J ())\<close> \<open>JsonList (J ())\<close> JsonTrue JsonFalse JsonNull g c]; clarsimp)
                by (insert fpc_JsonNull[of g c]; clarsimp)
              done
            done
          done
        done
      done
    done
  done

lemma inductive_Json_no_consume_past_closing_brace:
  assumes J_wf: "bidef_well_formed (J ())"
  assumes J_pngi: "PNGI (parse (J ()))"
  assumes J_no_result_from_empty: "\<forall>r x. \<not> has_result (parse (J ())) [] r x"
  assumes J_fpc_no_ws: "\<forall>i c. fpc (parse (J ())) i c \<longrightarrow> c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3
          (parse
            (transform sum_take_many sum_untake_many
              (derived_or.or JsonString
              (derived_or.or JsonNumber
              (derived_or.or (JsonObject (J ()))
              (derived_or.or (JsonList (J ()))
              (derived_or.or JsonTrue
              (derived_or.or JsonFalse
                             JsonNull))))))))
          CHR ''}''"
  apply (rule transform_does_not_consume_past_char3)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonString_drop_leftover_on_error)
  subgoal for c l l' r
    \<comment> \<open>This holds, if we fail on c@l and the rest of Json succeeds then it cannot start with quot_chr anyways\<close>
    \<comment> \<open>So that should be the direction we take this proof.\<close>
    \<comment> \<open>And if c is empty then we fail too.\<close>
    apply (cases c; clarsimp)
    subgoal \<comment> \<open>Empty, proof is trivial because JsonString errors when not start with "\<close> by (clarsimp simp add: NER_simps)
    subgoal for c' cs \<comment> \<open>Nonempty\<close>
      \<comment> \<open>For the rest of Json to succeed c' cannot be ", so JsonString fails.\<close>
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x
        apply (insert JsonNumber_first_char_result[of c' \<open>cs@l\<close> x l]; auto simp add: is_error_JsonString(2))
        apply (insert is_error_JsonString(2)[of c' \<open>cs @ CHR ''}'' # l'\<close>])
        by fastforce
      subgoal for x by (insert JsonObject_first_char_result[of \<open>J ()\<close> c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      done
    done
  subgoal by (rule JsonString_no_consume_past_any_char)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonNumber_can_drop_leftover_on_error)
  subgoal for c l by (rule JsonNumber_stays_error_with_injected_char[of c l \<open>CHR ''}''\<close>, simplified])
  subgoal by (rule JsonNumber_no_consume_past_non_digit_chars[of \<open>CHR ''}''\<close>, simplified])
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c l r
    \<comment> \<open>If the other Json parsers have result then JsonObject can never succeed\<close>
    apply (cases c; clarsimp simp add: NER_simps) \<comment> \<open>Empty case is trivially true\<close>
    subgoal for c' cs
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c l r
    \<comment> \<open>If the other Json parsers have result then JsonObject can never succeed\<close>
    apply (cases c; clarsimp simp add: NER_simps) \<comment> \<open>Empty case is trivially true\<close>
    subgoal for c' cs
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>I believe we should be able to get does not peek past end for this even.\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c l r
    \<comment> \<open>If the other Json parsers have result then JsonList can never succeed\<close>
    apply (cases c; clarsimp simp add: NER_simps) \<comment> \<open>Empty case is trivially true\<close>
    subgoal for c' cs
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c l r
    \<comment> \<open>If the other Json parsers have result then JsonList can never succeed\<close>
    apply (cases c; clarsimp simp add: NER_simps) \<comment> \<open>Empty case is trivially true\<close>
    subgoal for c' cs
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c' \<open>cs@l\<close> x l]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>I believe we should be able to get does not peek past end for this even.\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonTrue_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonFalse_def JsonNull_def split: sum.splits)
  subgoal
    using JsonTrue_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonFalse_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonNull_def)
  subgoal
    using JsonFalse_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  subgoal
    using JsonNull_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  oops


lemma inductive_Json_no_consume_past_ws:
  assumes J_wf: "bidef_well_formed (J ())"
  assumes J_pngi: "PNGI (parse (J ()))"
  assumes J_no_result_from_empty: "\<forall>r x. \<not> has_result (parse (J ())) [] r x"
  assumes J_fpc_no_ws: "\<forall>i c. fpc (parse (J ())) i c \<longrightarrow> c \<notin> whitespace_chars"
  shows "\<forall>c. c \<in> whitespace_chars \<longrightarrow>
          does_not_consume_past_char3
            (parse
              (transform sum_take_many sum_untake_many
                (derived_or.or JsonString
                (derived_or.or JsonNumber
                (derived_or.or (JsonObject (J ()))
                (derived_or.or (JsonList (J ()))
                (derived_or.or JsonTrue
                (derived_or.or JsonFalse
                               JsonNull))))))))
            c"
  apply clarsimp
  apply (rule transform_does_not_consume_past_char3)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonString_drop_leftover_on_error)
  subgoal for c c' l l' r
    \<comment> \<open>If the others have a result then c' cannot start with quot_chr\<close>
    apply (cases c'; clarsimp)
    subgoal \<comment> \<open>Empty, proof is trivial because JsonString errors when not start with "\<close>
      by (rule is_error_JsonString(2); clarsimp)
    subgoal for c'' c's \<comment> \<open>Nonempty\<close>
      \<comment> \<open>For the rest of Json to succeed c'' cannot be ", so JsonString fails.\<close>
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x
        apply (insert JsonNumber_first_char_result[of c'' \<open>c's@l\<close> x l]; auto simp add: is_error_JsonString(2))
        apply (insert is_error_JsonString(2)[of c'' \<open>c's @ c # l'\<close>])
        by fastforce
      subgoal for x by (insert JsonObject_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal by (rule JsonString_no_consume_past_any_char)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonNumber_can_drop_leftover_on_error)
  subgoal for c'' l l' by (rule JsonNumber_stays_error_with_injected_char[of l l' c'', simplified]; assumption?; fastforce)
  subgoal by (rule JsonNumber_no_consume_past_non_digit_chars; clarsimp)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c c' l r
    apply (cases c'; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c c' l l' r
    apply (cases c'; clarsimp)
    subgoal by (auto simp add: NER_simps J_pngi split: sum.splits)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>JsonObject no consume past ws\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c c' l r
    apply (cases c'; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c c' l l' r
    apply (cases c'; clarsimp)
    subgoal by (auto simp add: NER_simps J_pngi split: sum.splits)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>JsonList no consume past ws\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonTrue_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonFalse_def JsonNull_def split: sum.splits)
  subgoal
    using JsonTrue_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonFalse_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonNull_def)
  subgoal
    using JsonFalse_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  subgoal
    using JsonNull_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  oops


lemma inductive_Json_no_consume_past_comma:
  assumes J_wf: "bidef_well_formed (J ())"
  assumes J_pngi: "PNGI (parse (J ()))"
  assumes J_no_result_from_empty: "\<forall>r x. \<not> has_result (parse (J ())) [] r x"
  assumes J_fpc_no_ws: "\<forall>i c. fpc (parse (J ())) i c \<longrightarrow> c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3
            (parse
              (transform sum_take_many sum_untake_many
                (derived_or.or JsonString
                (derived_or.or JsonNumber
                (derived_or.or (JsonObject (J ()))
                (derived_or.or (JsonList (J ()))
                (derived_or.or JsonTrue
                (derived_or.or JsonFalse
                               JsonNull))))))))
            CHR '',''"
  apply (rule transform_does_not_consume_past_char3)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonString_drop_leftover_on_error)
  subgoal for c' l l' r
    \<comment> \<open>If the others have a result then c' cannot start with quot_chr\<close>
    apply (cases c'; clarsimp)
    subgoal \<comment> \<open>Empty, proof is trivial because JsonString errors when not start with "\<close>
      by (rule is_error_JsonString(2); clarsimp)
    subgoal for c'' c's \<comment> \<open>Nonempty\<close>
      \<comment> \<open>For the rest of Json to succeed c'' cannot be ", so JsonString fails.\<close>
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x
        apply (insert JsonNumber_first_char_result[of c'' \<open>c's@l\<close> x l]; auto simp add: is_error_JsonString(2))
        apply (insert is_error_JsonString(2)[of c'' \<open>c's @ CHR '','' # l'\<close>])
        by fastforce
      subgoal for x by (insert JsonObject_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal by (rule JsonString_no_consume_past_any_char)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonNumber_can_drop_leftover_on_error)
  subgoal for c'' l l' by (rule JsonNumber_stays_error_with_injected_char[of c'' l \<open>CHR '',''\<close> l', simplified]; assumption?; fastforce)
  subgoal by (rule JsonNumber_no_consume_past_non_digit_chars; clarsimp)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c' l r
    apply (cases c'; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c' l l' r
    apply (cases c'; clarsimp)
    subgoal by (auto simp add: NER_simps J_pngi split: sum.splits)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>JsonObject no consume past comma\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c' l r
    apply (cases c'; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c' l l' r
    apply (cases c'; clarsimp)
    subgoal by (auto simp add: NER_simps J_pngi split: sum.splits)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>JsonList no consume past comma\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonTrue_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonFalse_def JsonNull_def split: sum.splits)
  subgoal
    using JsonTrue_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonFalse_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonNull_def)
  subgoal
    using JsonFalse_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  subgoal
    using JsonNull_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  oops


lemma inductive_Json_no_consume_past_closing_bracket:
  assumes J_wf: "bidef_well_formed (J ())"
  assumes J_pngi: "PNGI (parse (J ()))"
  assumes J_no_result_from_empty: "\<forall>r x. \<not> has_result (parse (J ())) [] r x"
  assumes J_fpc_no_ws: "\<forall>i c. fpc (parse (J ())) i c \<longrightarrow> c \<notin> whitespace_chars"
  shows "does_not_consume_past_char3
            (parse
              (transform sum_take_many sum_untake_many
                (derived_or.or JsonString
                (derived_or.or JsonNumber
                (derived_or.or (JsonObject (J ()))
                (derived_or.or (JsonList (J ()))
                (derived_or.or JsonTrue
                (derived_or.or JsonFalse
                               JsonNull))))))))
            CHR '']''"
  apply (rule transform_does_not_consume_past_char3)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonString_drop_leftover_on_error)
  subgoal for c' l l' r
    \<comment> \<open>If the others have a result then c' cannot start with quot_chr\<close>
    apply (cases c'; clarsimp)
    subgoal \<comment> \<open>Empty, proof is trivial because JsonString errors when not start with "\<close>
      by (rule is_error_JsonString(2); clarsimp)
    subgoal for c'' c's \<comment> \<open>Nonempty\<close>
      \<comment> \<open>For the rest of Json to succeed c'' cannot be ", so JsonString fails.\<close>
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x
        apply (insert JsonNumber_first_char_result[of c'' \<open>c's@l\<close> x l]; auto simp add: is_error_JsonString(2))
        apply (insert is_error_JsonString(2)[of c'' \<open>c's @ CHR '']'' # l'\<close>])
        by fastforce
      subgoal for x by (insert JsonObject_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal by (rule JsonString_no_consume_past_any_char)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonNumber_can_drop_leftover_on_error)
  subgoal for c'' l l' by (rule JsonNumber_stays_error_with_injected_char[of c'' l \<open>CHR '']''\<close> l', simplified]; assumption?; fastforce)
  subgoal by (rule JsonNumber_no_consume_past_non_digit_chars; clarsimp)
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c' l r
    apply (cases c'; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c' l l' r
    apply (cases c'; clarsimp)
    subgoal by (auto simp add: NER_simps J_pngi split: sum.splits)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonList_first_char_result[of \<open>J ()\<close> c'' \<open>c's @ l\<close> x l]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>JsonObject no consume past comma\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal for c' l r
    apply (cases c'; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal for c' l l' r
    apply (cases c'; clarsimp)
    subgoal by (auto simp add: NER_simps J_pngi split: sum.splits)
    subgoal for c'' c's
      apply (clarsimp simp add: NER_simps split: sum.splits)
      subgoal for x by (insert JsonTrue_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonFalse_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      subgoal for x by (insert JsonNull_first_char_result[of c'' \<open>c's @ l\<close> x l ]; clarsimp simp add: NER_simps)
      done
    done
  subgoal
    \<comment> \<open>JsonList no consume past comma\<close>
    sorry
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonTrue_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonFalse_def JsonNull_def split: sum.splits)
  subgoal
    using JsonTrue_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  apply (rule or_no_consume_past_char[rotated, rotated])
  subgoal by (rule JsonFalse_can_drop_leftover_on_error)
  subgoal for c by (cases c; clarsimp simp add: NER_simps JsonNull_def)
  subgoal
    using JsonFalse_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  subgoal
    using JsonNull_no_peek_past_end does_not_consume_past_any_char3_eq_not_peek_past_end
    by blast
  oops



lemma inductive_Json_drop_past_leftover:
  assumes J_drop_leftover: "\<forall>c l l' r. has_result (parse J) (c @ l @ l') r (l @ l') \<longrightarrow> has_result (parse J) (c @ l) r l"
  shows "has_result
             (parse
               (transform sum_take_many sum_untake_many
                 (derived_or.or JsonString (derived_or.or JsonNumber (derived_or.or (JsonObject J) (derived_or.or (JsonList J) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))))))))
             (c @ l @ l') r (l @ l') \<Longrightarrow>
            has_result
             (parse
               (transform sum_take_many sum_untake_many
                 (derived_or.or JsonString (derived_or.or JsonNumber (derived_or.or (JsonObject J) (derived_or.or (JsonList J) (derived_or.or JsonTrue (derived_or.or JsonFalse JsonNull))))))))
             (c @ l) r l"
  apply (rule transform_can_drop_leftover; assumption?)
  apply (rule or_can_drop_leftover; assumption?)
  subgoal by (rule JsonString_drop_leftover)
  subgoal by (rule JsonString_drop_leftover_on_error2)

  apply (rule or_can_drop_leftover; assumption?)
  subgoal by (rule JsonNumber_drop_leftover)
  subgoal by (rule JsonNumber_can_drop_leftover_on_error2)

  apply (rule or_can_drop_leftover; assumption?)
  subgoal \<comment> \<open>JsonObject can drop leftover\<close>
    sorry
  subgoal \<comment> \<open>JsonObject can drop lefter on error\<close>
    sorry

  apply (rule or_can_drop_leftover; assumption?)
  subgoal \<comment> \<open>JsonList can drop leftover\<close>
    sorry
  subgoal \<comment> \<open>JsonList can drop lefter on error\<close>
    sorry

  apply (rule or_can_drop_leftover; assumption?)
  subgoal by (rule JsonTrue_drop_leftover)
  subgoal by (rule JsonTrue_can_drop_leftover_on_error2)

  apply (rule or_can_drop_leftover; assumption?)
  subgoal by (rule JsonFalse_drop_leftover)
  subgoal by (rule JsonFalse_can_drop_leftover_on_error2)

  subgoal by (rule JsonNull_drop_leftover)
  done



\<comment> \<open>Other needed premises:


  These two:
  is_error (parse (J ())) []
  \<forall>l. is_error (parse (J ())) (CHR '']'' # l)
  are not possible using the induction rule because the bottom parser always nonterms.
  We can prove both of these for JSON, but how do we include that in this proof?
  
\<close>
\<comment> \<open>We can use this but then the assms require us to prove is_error [] from nothing.\<close>
lemma drop_the_is_error_part:
  assumes "bd.admissible (\<lambda>x. X x)"
  shows "bd.admissible
     (\<lambda>JsonR.
         is_error (parse (JsonR ())) [] \<longrightarrow> (X JsonR))"
  apply (insert assms)
  by (auto simp add: is_error_def)


\<comment> \<open>Definitely write in the thesis that this process is shit.\<close>
\<comment> \<open>It would be amazing if we could create some sort of "state" that all proofs for these inner things are in,\<close>
\<comment> \<open>Wich automatically has all these premises as facts.\<close>
\<comment> \<open>Because right now we have to thread these premises though all kinds of proofs to reach the right place, which is whack.\<close>
\<comment> \<open>In essence, the transitive assumption story isn't great.\<close>
lemma Json_well_formed:
  "bidef_well_formed Json
  \<and> (PNGI (parse Json))
  \<and> (\<nexists>r l. has_result (parse Json) [] r l)
  \<and> (\<forall> i c. fpc (parse Json) i c \<longrightarrow> c \<notin> whitespace_chars)
  \<and> (does_not_consume_past_char3 (parse Json) CHR ''}'')
  \<and> (\<forall>c. c \<in>whitespace_chars \<longrightarrow> does_not_consume_past_char3 (parse Json) c)
  \<and> (does_not_consume_past_char3 (parse Json) CHR '','')
  \<and> (does_not_consume_past_char3 (parse Json) CHR '']'')
  \<and> (\<forall>c l l' r. has_result (parse Json) (c @ l @ l') r (l @ l') \<longrightarrow> has_result (parse Json) (c @ l) r l)
"
  apply (induction rule: JsonR.fixp_induct)
  subgoal
    by clarsimp
  subgoal
    apply (clarsimp simp add: strict_WF strict_PNGI)
    using bottom_no_empty_result bottom_has_no_fpc bottom_no_consume_past_char3 bottom_drop_past_leftover
    by fast
  subgoal for J
    apply clarsimp
    apply (repeat_new \<open>rule conjI\<close>) \<comment> \<open>Split all the mutual-recursion conjunctions.\<close>
    subgoal
      apply (rule Json_well_formed_inductive; assumption?)
      subgoal by blast
      subgoal by blast
      subgoal \<comment> \<open>\<forall>l. is_error (parse (J ())) (CHR '']'' # l)\<close>
        using Json_error_on_close_bracket \<comment> \<open>We break here!\<close>
        sorry
      subgoal \<comment> \<open>is_error (parse (J ())) []\<close>
        using Json_error_on_empty \<comment> \<open>We break here!\<close>
        sorry
      done
    subgoal by pasi_pngi
    subgoal using inductive_Json_no_empty_result by blast
    subgoal by (rule inductive_Json_fpc_not_ws)
    subgoal
      \<comment> \<open>Does not consume past closing brace\<close>
      sorry
    subgoal
      \<comment> \<open>Does not consume past whitespace chars\<close>
      sorry
    subgoal
      \<comment> \<open>Does not consume past comma\<close>
      sorry
    subgoal
      \<comment> \<open>Does not consume past closing bracket\<close>
      sorry
    subgoal
      \<comment> \<open>Drop past leftover\<close>
      sorry
    done
  oops




end
