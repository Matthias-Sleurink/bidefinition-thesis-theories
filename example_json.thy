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


definition end_str where "end_str = until one_char (this_char CHR ''\"'')"
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
  | True
  | False
  | Null


abbreviation "quot_chr \<equiv> CHR ''\"''"
definition quot :: "char bidef" where
  "quot = this_char quot_chr"
lemma quot_PASI_PNGI[PASI_PNGI_intros]:
  "PNGI (parse quot)"
  "PASI (parse quot)"
  unfolding quot_def by pasi_pngi+


definition str_literal :: "string bidef" where
  "str_literal = takeMiddle quot (until one_char quot) quot quot_chr quot_chr"
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


definition JsonString :: "JSON bidef" where
  "JsonString = ftransform
                 (Some o String)
                 (\<lambda>String s \<Rightarrow> Some s
                  | _ \<Rightarrow> None)
                 str_literal"

lemma PASI_PNGI_JsonString[PASI_PNGI_intros]:
  shows "PASI (parse JsonString)"
        "PNGI (parse JsonString)"
  unfolding JsonString_def
  by pasi_pngi+


definition JsonNumber :: "JSON bidef" where
  "JsonNumber = ftransform
                 (Some o Number)
                 (\<lambda>Number n \<Rightarrow> Some n
                  | _ \<Rightarrow> None)
                 int_b"

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

lemma mono_JsonList[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. JsonList (A f))"
  unfolding JsonList_def using ma
  by pf_mono_prover



definition JsonTrue :: "JSON bidef" where
  "JsonTrue = ftransform
                  (Some o (const True))
                  (\<lambda>True \<Rightarrow> Some ''true''
                   | _ \<Rightarrow> None)
                  (this_string ''true'')"

lemma PASI_PNGI_JsonTrue[PASI_PNGI_intros]:
  shows "PASI (parse JsonTrue)"
        "PNGI (parse JsonTrue)"
  unfolding JsonTrue_def
  by pasi_pngi+


definition JsonFalse :: "JSON bidef" where
  "JsonFalse = ftransform
                  (Some o (const False))
                  (\<lambda>True \<Rightarrow> Some ''false''
                   | _ \<Rightarrow> None)
                  (this_string ''false'')"

lemma PASI_PNGI_JsonFalse[PASI_PNGI_intros]:
  shows "PASI (parse JsonFalse)"
        "PNGI (parse JsonFalse)"
  unfolding JsonFalse_def
  by pasi_pngi+


definition JsonNull :: "JSON bidef" where
  "JsonNull = ftransform
                  (Some o (const Null))
                  (\<lambda>True \<Rightarrow> Some ''null''
                   | _ \<Rightarrow> None)
                  (this_string ''null'')"

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
| "sum_untake_many True       = Inr (Inr (Inr (Inr (Inl True))))"
| "sum_untake_many False      = Inr (Inr (Inr (Inr (Inr (Inl False)))))"
| "sum_untake_many Null       = Inr (Inr (Inr (Inr (Inr (Inr Null)))))"


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
