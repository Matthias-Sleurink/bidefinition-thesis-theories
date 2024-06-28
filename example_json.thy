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


lemma str_literal_no_parse_empty[NER_simps]:
  "has_result (parse str_literal) [] r l \<longleftrightarrow> False"
  by (clarsimp simp add: NER_simps str_literal_def takeMiddle_def quot_def)

lemma is_error_str_literal[NER_simps]:
  "is_error (parse str_literal) []"
  "c \<noteq> quot_chr \<Longrightarrow> is_error (parse str_literal) (c # l)"
  by (clarsimp simp add: str_literal_def NER_simps takeMiddle_def quot_def)+

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
  by (clarsimp simp add: JsonString_def NER_simps)+

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
  by (clarsimp simp add: JsonNumber_def NER_simps)+

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

lemma fpc_JsonNameColonObject[fpc_simps]:
  "fpc (parse (JsonNameColonObject I)) a c \<Longrightarrow> c = quot_chr"
  apply (clarsimp simp add: JsonNameColonObject_def fpc_simps)
  by (clarsimp simp add: fpc_def NER_simps str_literal_def takeMiddle_def quot_def)



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
  by (clarsimp simp add: JsonTrue_def NER_simps)+

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
  by (clarsimp simp add: JsonFalse_def NER_simps)+

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
  by (clarsimp simp add: JsonNull_def NER_simps)+

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

lemma JsonNameColonObject_sepBy_ws_char_ws_no_eat_into_ws_char:
  assumes J_pngi: "PNGI (parse J)"
  assumes J_wf: "bidef_well_formed J"
  assumes J_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse J) CHR ''}''"
  assumes J_fpc_no_ws: "\<And> i c. fpc (parse J) i c \<Longrightarrow> c \<notin> whitespace_chars"
  assumes J_no_parse_empty: "\<nexists>r l. has_result (parse J) [] r l"
  assumes jnco_wf: "bidef_well_formed (JsonNameColonObject J)"
  assumes many_comma_then_jcno_wf: "bidef_well_formed (many (b_then (ws_char_ws CHR '','') (JsonNameColonObject J)))"
  assumes inner_wf: "bidef_well_formed (separated_by (ws_char_ws CHR '','') (JsonNameColonObject J) ())"
  shows "pa_does_not_eat_into_pb_nondep (separated_by (ws_char_ws CHR '','') (JsonNameColonObject J) ()) (ws_char CHR ''}'')"
  apply (rule first_printed_does_not_eat_into3)
  subgoal by (rule inner_wf)
  apply (clarsimp simp add: fpci_simps separated_by_def)
  apply (rule transform_does_not_consume_past_char3)
  apply (rule optional_does_not_consume_past_char3)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps)
  subgoal by (clarsimp simp add: separated_byBase_def NER_simps)
  subgoal
    apply (clarsimp simp add: separated_byBase_def)
    apply (rule then_does_not_consume_past3_from_can_drop_leftover)
    subgoal by (rule jnco_wf)
    subgoal by (rule many_comma_then_jcno_wf)
    subgoal
      
      sorry
    subgoal for i c \<comment> \<open>Need to do an fpc many rule\<close> sorry
    subgoal
      apply (rule JsonNameColonObject_no_consume_past_closing_brace)
      subgoal by (rule J_pngi)
      subgoal by (rule J_wf)
      subgoal by (rule J_no_consume_past_closing_brace)
      subgoal by (rule J_fpc_no_ws)
      subgoal by (rule J_no_parse_empty)
      done
    subgoal sorry
    done
  oops


lemma WF_JsonObject:
  assumes J_wf: "bidef_well_formed J"
  assumes J_pngi: "PNGI (parse J)"
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
          
          sorry
        subgoal by (rule ws_char_well_formed; clarsimp)
        subgoal
          
          sorry
        done
      done
    done
  oops


lemma Json_well_formed_inductive:
  assumes J_wf: "bidef_well_formed (J ())"
  assumes J_pngi: "PNGI (parse (J ()))"
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
        \<comment> \<open>Well formed JsonObject\<close>
        sorry
      subgoal
        apply (rule or_well_formed)
        subgoal
          \<comment> \<open>Well formed JsonList\<close>
          sorry
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
  oops

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


\<comment> \<open>Other needed premises:

  J_no_consume_past_closing_brace: "does_not_consume_past_char3 (parse J) CHR ''}''"

\<close>

lemma Json_well_formed:
  "bidef_well_formed Json
  \<and> (PNGI (parse Json))
  \<and> (\<nexists>r l. has_result (parse Json) [] r l)
  \<and> (\<forall> i c. fpc (parse Json) i c \<longrightarrow> c \<notin> whitespace_chars)
"
  apply (induction rule: JsonR.fixp_induct)
  subgoal by clarsimp
  subgoal apply (clarsimp simp add: strict_WF strict_PNGI) using bottom_no_empty_result bottom_has_no_fpc by fast
  subgoal for J
    apply clarsimp
    apply (repeat_new \<open>rule conjI\<close>) \<comment> \<open>Split all the mutual-recursion conjunctions.\<close>
    subgoal
      \<comment> \<open>WF\<close>
      sorry
    subgoal by pasi_pngi
    subgoal using inductive_Json_no_empty_result by blast
    subgoal by (rule inductive_Json_fpc_not_ws)
    done
  oops




end
