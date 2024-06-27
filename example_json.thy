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


lemma PNGI_str_literal[PASI_PNGI_intros]:
  shows "PNGI (parse str_literal)"
  unfolding str_literal_def
  by pasi_pngi
lemma PASI_str_literal[PASI_PNGI_intros]:
  shows "PASI (parse str_literal)"
  unfolding str_literal_def takeMiddle_def
  by pasi_pngi

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



definition JsonString :: "JSON bidef" where
  "JsonString = ftransform
                 (Some o String)
                 (\<lambda>String s \<Rightarrow> Some s
                  | _ \<Rightarrow> None)
                 str_literal"

lemma has_result_JsonString[NER_simps]:
  "has_result (parse (JsonString)) i (String str) l \<longleftrightarrow> has_result (parse str_literal) i str l"
  "has_result (parse (JsonString)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonString)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonString_def NER_simps)+

lemma PASI_PNGI_JsonString[PASI_PNGI_intros]:
  shows "PASI (parse JsonString)"
        "PNGI (parse JsonString)"
  unfolding JsonString_def
  by pasi_pngi+

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
  "has_result (parse (JsonNumber)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i (Number n) l \<longleftrightarrow> has_result (parse int_b) i n l"
  "has_result (parse (JsonNumber)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonNumber)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonNumber_def NER_simps)+

lemma PASI_PNGI_JsonNumber[PASI_PNGI_intros]:
  shows "PASI (parse JsonNumber)"
        "PNGI (parse JsonNumber)"
  unfolding JsonNumber_def
  by pasi_pngi+


definition JsonNameColonObject :: "JSON bidef \<Rightarrow> (string \<times> JSON) bidef" where
  "JsonNameColonObject i = b_then str_literal (then_drop_first (ws_char_ws CHR ''\"'') i ())"

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


abbreviation "betweenBraces bd \<equiv> takeMiddle (char_ws CHR ''{'') bd (ws_char CHR ''}'') () ()"
definition JsonObject :: "JSON bidef \<Rightarrow> JSON bidef" where
  "JsonObject i = ftransform
                    (Some o Object)
                    (\<lambda>Object ob \<Rightarrow> Some ob
                     | _ \<Rightarrow> None)
                    (betweenBraces (separated_by (ws_char_ws CHR '','') (JsonNameColonObject i) ()))"

lemma has_result_JsonObject[NER_simps]:
  "has_result (parse (JsonObject I)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i (Object od) l \<longleftrightarrow> has_result (parse (betweenBraces (separated_by (ws_char_ws CHR '','') (JsonNameColonObject I) ()))) i od l"
  "has_result (parse (JsonObject I)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonObject I)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonObject_def NER_simps)+

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
  "has_result (parse (JsonList I)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i (List ld) l \<longleftrightarrow> has_result (parse (betweenSquareBrackets (separated_by (ws_char_ws CHR '','') I ()))) i ld l"
  "has_result (parse (JsonList I)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonList I)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonList_def NER_simps)+

lemma mono_JsonList[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. JsonList (A f))"
  unfolding JsonList_def using ma
  by pf_mono_prover



definition JsonTrue :: "JSON bidef" where
  "JsonTrue = ftransform
                  (Some o (const JTrue))
                  (\<lambda>JTrue \<Rightarrow> Some ''true''
                   | _ \<Rightarrow> None)
                  (this_string ''true'')"

lemma has_result_JsonTrue[NER_simps]:
  "has_result (parse (JsonTrue)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i JTrue l \<longleftrightarrow> has_result (parse (this_string ''true'')) i ''true'' l"
  "has_result (parse (JsonTrue)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonTrue)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonTrue_def NER_simps)+

lemma PASI_PNGI_JsonTrue[PASI_PNGI_intros]:
  shows "PASI (parse JsonTrue)"
        "PNGI (parse JsonTrue)"
  unfolding JsonTrue_def
  by pasi_pngi+


definition JsonFalse :: "JSON bidef" where
  "JsonFalse = ftransform
                  (Some o (const JFalse))
                  (\<lambda>JFalse \<Rightarrow> Some ''false''
                   | _ \<Rightarrow> None)
                  (this_string ''false'')"

lemma has_result_JsonFalse[NER_simps]:
  "has_result (parse (JsonFalse)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonFalse)) i JFalse l \<longleftrightarrow> has_result (parse (this_string ''false'')) i ''false'' l"
  "has_result (parse (JsonFalse)) i JNull l \<longleftrightarrow> False"
  by (clarsimp simp add: JsonFalse_def NER_simps)+

lemma PASI_PNGI_JsonFalse[PASI_PNGI_intros]:
  shows "PASI (parse JsonFalse)"
        "PNGI (parse JsonFalse)"
  unfolding JsonFalse_def
  by pasi_pngi+


definition JsonNull :: "JSON bidef" where
  "JsonNull = ftransform
                  (Some o (const JNull))
                  (\<lambda>JNull \<Rightarrow> Some ''null''
                   | _ \<Rightarrow> None)
                  (this_string ''null'')"

lemma has_result_JsonNull[NER_simps]:
  "has_result (parse (JsonNull)) i (String str) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (Number n) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (Object od) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i (List ld) l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i JTrue l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i JFalse l \<longleftrightarrow> False"
  "has_result (parse (JsonNull)) i JNull l \<longleftrightarrow> has_result (parse (this_string ''null'')) i ''null'' l"
  by (clarsimp simp add: JsonNull_def NER_simps)+

lemma PASI_PNGI_JsonNull[PASI_PNGI_intros]:
  shows "PASI (parse JsonNull)"
        "PNGI (parse JsonNull)"
  unfolding JsonNull_def
  by pasi_pngi+


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
  
  oops


lemma Json_well_formed:
  "bidef_well_formed Json \<and>
   (PNGI (parse Json))"
  apply (induction rule: JsonR.fixp_induct)
  subgoal by clarsimp
  subgoal by (clarsimp simp add: strict_WF strict_PNGI)
  subgoal for J
    apply clarsimp
    apply (repeat_new \<open>rule conjI\<close>) \<comment> \<open>Split all the mutual-recursion conjunctions.\<close>
    subgoal
      \<comment> \<open>WF\<close>
      sorry
    subgoal by pasi_pngi
    done
  oops




end
