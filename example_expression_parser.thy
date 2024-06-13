theory example_expression_parser
  imports all_definitions
begin

text \<open>
A recursive expression parser.
The intended grammar is basically this:
E : M ['+'M]*
M : B ['*'B]*
B : nat
  | '(' E ')'
\<close>
datatype Ex
  = Additive (getList: "Ex list")
  | Multiply (getList: "Ex list")
  | Literal (getNat: nat)
  | Parenthesised (getE: Ex)
print_theorems
\<comment> \<open>Note that this is not the AST, more like a parse tree, it's up to the user to create an AST.\<close>
\<comment> \<open>Which should be a simple fold over the lists.\<close>
(*
datatype ExA = Additive "ExM list"
and
 ExM = Multiply \<open>ExL list\<close>
and
  ExL = Literal "nat" | Parenthesised ExA
*)

fun val :: "Ex \<Rightarrow> nat" where
  "val (Additive []) = 0"
| "val (Additive (x#xs)) = (val x) + (val (Additive xs))"
| "val (Multiply []) = 1"
| "val (Multiply (x#xs)) = (val x) * (val (Multiply xs))"
| "val (Literal v) = v"
| "val (Parenthesised e) = val e"

lemma val_tests:
  "0 = val (Additive [])"
  "1 = val (Additive [Literal 1])"
  "3 = val (Additive [Literal 1, Multiply [Literal 2]])"
  "7 = val (Additive [Literal 1, Multiply [Literal 2, Parenthesised (Literal 3)]])"
  by simp_all

abbreviation star :: "unit bidef" where
  "star \<equiv> ws_char_ws CHR ''*''"
abbreviation plus :: "unit bidef" where
  "plus \<equiv> ws_char_ws CHR ''+''"
lemma expression_punctuation_charsets[simp]:
  "CHR ''*'' \<notin> digit_chars"
  "CHR ''+'' \<notin> digit_chars"
  "CHR ''('' \<notin> digit_chars"
  "CHR '')'' \<notin> digit_chars"

  "CHR ''*'' \<notin> derived_digit_char.digit_chars"
  "CHR ''+'' \<notin> derived_digit_char.digit_chars"

  "CHR ''*'' \<notin> whitespace_chars"
  "CHR ''+'' \<notin> whitespace_chars"
  "CHR ''('' \<notin> whitespace_chars"
  "CHR '')'' \<notin> whitespace_chars"
  unfolding derived_digit_char.digit_chars_def whitespace_chars_def
  by blast+
lemma chars_not_in_whitespace[simp]:
  "c \<in> digit_chars \<longrightarrow> c\<notin>whitespace_chars"
  "c \<in> derived_digit_char.digit_chars \<longrightarrow> c\<notin>whitespace_chars"
  unfolding derived_digit_char.digit_chars_def whitespace_chars_def
  by blast+

abbreviation triple :: "'a bidef \<Rightarrow> 'b bidef \<Rightarrow> 'c bidef \<Rightarrow> ('a \<times> 'b \<times> 'c) bidef" where
  "triple A B C \<equiv> b_then A (b_then B C)"

definition ws_parenthesised :: "'a bidef \<Rightarrow> 'a bidef" where
  "ws_parenthesised A = transform
                      (fst o snd)
                      (\<lambda>a. ((), a, ())) \<comment> \<open>ws_char_ws is a unit bidef\<close>
                      (triple (ws_char_ws CHR ''('') A (ws_char_ws CHR '')''))"

lemma mono_ws_parenthesised[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. ws_parenthesised (A f))"
  unfolding ws_parenthesised_def using ma
  by pf_mono_prover

\<comment> \<open>The two ideas for making small combinators have easier NER rules is to add the definition to NER simps.\<close>
\<comment> \<open>This requires the rule to be "safe" to unfold, which ws_parenthesised is.\<close>
\<comment> \<open>Cannot add this to fp_NER too, since it'll give us duplicate fact added warnings when we add both NER and fp_NER.\<close>
\<comment> \<open>So maybe the better solution is to add an unfold rule specific to the has_result, is_error, etc?\<close>
\<comment> \<open>But in that case we're almost back to how complex it was at the start again.\<close>
lemmas ws_paren_def[NER_simps] = ws_parenthesised_def

lemma lt_lte_lt:
  assumes "(l :: nat) < l''"
  assumes "l'' \<le> l'"
  shows "l<l'"
  using assms
  by simp
  


lemma paren_drop_leftover:
  assumes PNGI_e: "PNGI (parse E)"
  assumes hr: "has_result (parse (ws_parenthesised E)) (c @ l) r l"
  shows "has_result (parse (ws_parenthesised E)) c r []"
  using hr
  apply (clarsimp simp add: NER_simps simp del: ws_char_ws_has_result)
  subgoal for l' l''
    \<comment> \<open>list_upto longer shorter drops the lenth of shorter from longer\<close>
    apply (rule exI[of _ \<open>list_upto l' l\<close>]; rule conjI)
    subgoal
      \<comment> \<open>To show we this kinda need to show that the hd of list_upto l' l is not in ws\<close>
      using ws_char_ws_has_result_implies_leftover_head[of \<open>CHR ''(''\<close> \<open>c@l\<close>  \<open>()\<close> l']
      apply clarsimp

      using ws_char_ws_PASI[THEN PASI_as_has_result, of _ l'' _ l]
      using PNGI_e[THEN PNGI_as_has_result, of l' _ l'']
      using lt_lte_lt[of \<open>length l\<close> \<open>length l''\<close> \<open>length l'\<close>]
      using hd_list_upto[of l l']
      using gr_implies_not0[of \<open>length l\<close> \<open>length l'\<close>]
      
      sorry
    subgoal
      
      sorry
  oops


\<comment> \<open>Is there way some way of saying that this is just the Literal branch of the type?\<close>
definition Number :: "Ex bidef" where
  "Number = ftransform
              (Some o Literal)
              (\<lambda> Literal n \<Rightarrow> Some n
               | e \<Rightarrow> None)
              nat_b"

lemma Number_has_result[NER_simps]:
  "has_result (parse Number) i r l \<longleftrightarrow> (\<exists>n. has_result (parse nat_b) i n l \<and> r = Literal n)"
  by (auto simp add: Number_def NER_simps)
lemma Number_is_error[NER_simps]:
  "is_error (parse Number) i \<longleftrightarrow> is_error (parse nat_b) i"
  by (clarsimp simp add: Number_def NER_simps)
lemma Number_is_nonterm[NER_simps]:
  "is_nonterm (parse Number) i \<longleftrightarrow> False"
  by (clarsimp simp add: Number_def NER_simps)

lemma Number_p_has_result[fp_NER]:
  "p_has_result (print Number) i r \<longleftrightarrow> (\<exists>n. i = Literal n \<and> p_has_result (print nat_b) n r)"
  by (clarsimp simp add: Number_def fp_NER split: Ex.splits)
lemma Number_b_is_error[fp_NER]:
  "p_is_error (print Number) i \<longleftrightarrow> (\<nexists>n. i = Literal n)"
  by (clarsimp simp add: Number_def fp_NER split: Ex.splits)
lemma Number_b_is_nonterm[fp_NER]:
  "p_is_nonterm (print Number) i \<longleftrightarrow> False"
  by (clarsimp simp add: Number_def fp_NER)
lemma Number_p_print_empty[print_empty, fp_NER]:
  "p_has_result (print Number) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: Number_def print_empty)

lemma Number_well_formed:
  "bidef_well_formed Number"
  unfolding Number_def
  apply (rule ftransform_well_formed)
  subgoal
    unfolding ftrans_wf_funcs_parser_can_parse_def
    apply (clarsimp split: Ex.splits)
    using nat_b_wf_from_transform_many1[THEN get_parser_can_parse_unfold]
    by fast
  subgoal
    unfolding ftrans_wf_funcs_printer_can_print_def
    apply (clarsimp split: Ex.splits)
    using nat_b_wf_from_transform_many1[THEN get_printer_can_print_unfold]
    by fast
  subgoal by (rule nat_b_well_formed)
  done

\<comment> \<open>Number or expression.\<close>
definition NOE :: "Ex bidef \<Rightarrow> Ex bidef" where
  "NOE E = ftransform
              (\<lambda> Inl l \<Rightarrow> Some l \<comment> \<open>Result of Number stays the same.\<close>
               | Inr r \<Rightarrow> Some (Parenthesised r)) \<comment> \<open>Result of parenthesised needs to get Parenthesised\<close>
              (\<lambda> Literal n       \<Rightarrow> Some (Inl (Literal n)) \<comment> \<open>We can print Numbers as literals\<close>
               | Parenthesised e \<Rightarrow> Some (Inr e)  \<comment> \<open>We can print Parenthesised with ws _parenthesised.\<close>
               | e               \<Rightarrow> None ) \<comment> \<open>All other options are an error.\<close>
              (derived_or.or Number (ws_parenthesised E))"


lemma mono_NOE[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. NOE (A f))"
  unfolding NOE_def using ma
  by pf_mono_prover

\<comment> \<open>Some quick tests to see how this 'else' case in case expressions works.\<close>
value "(\<lambda>Literal n \<Rightarrow> Inl (Literal n) | e \<Rightarrow> Inr e) (Literal 4)"
value "(\<lambda>Literal n \<Rightarrow> Inl (Literal n) | e \<Rightarrow> Inr e) (Additive [Literal 1])"
value "(\<lambda>Literal n \<Rightarrow> Inl (Literal n) | e \<Rightarrow> Inr e) (Additive [Literal 1, Multiply [Literal 2]])"

\<comment> \<open>Where E stands for the recursed Expression, which does not matter here\<close>
lemma NOE_no_consume_past_star:
  "does_not_consume_past_char3 (parse (NOE (E))) CHR ''*''"
  unfolding does_not_consume_past_char3_def NOE_def
  apply (clarsimp; rule conjI)
  subgoal for c r l
    apply (clarsimp simp add: NER_simps simp del: ws_parenthesised_def)
    subgoal for r'
      apply (cases r'; clarsimp)
      subgoal
        apply (rule exI[of _ \<open>Inl r\<close>]; clarsimp)
        apply (subst Number_has_result; subst (asm) Number_has_result)
        by (clarsimp simp add: nat_b_leftover_can_be_dropped[of c l _ \<open>[]\<close>])
      subgoal for r'r
        apply (rule exI[of _ \<open>Inr r'r\<close>]; clarsimp; rule conjI)
        subgoal
          apply (subst Number_is_error; subst (asm) Number_is_error) 
          by (clarsimp simp add: nat_b_error_leftover_can_be_dropped)
        subgoal
          \<comment> \<open>This makes me feel like we need some sort of system for saying that changes to the leftover don't matter mod some things that do.\<close>
          \<comment> \<open>But how do we do that?\<close>
          \<comment> \<open>thm paren_drop_leftover\<close>
          \<comment> \<open>Just need to prove it now.\<close>
          sorry
        done
      done
    done
  subgoal sorry
  oops


definition MultE :: "Ex bidef \<Rightarrow> Ex bidef" where
  "MultE E = ftransform
               (Some o Multiply)
               (\<lambda>Multiply ms \<Rightarrow> Some ms
                |_ \<Rightarrow> None)
               (separated_by1 (NOE E) star ())"

lemma mono_MultE[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. MultE (A f))"
  unfolding MultE_def using ma
  by pf_mono_prover

definition AddE :: "Ex bidef \<Rightarrow> Ex bidef" where
  "AddE E = ftransform
              (Some o Additive)
              ((\<lambda>Additive as \<Rightarrow> Some as
                |_ \<Rightarrow> None))
              ((separated_by1 (MultE E) plus ()) :: Ex list bidef)"

lemma mono_AddE[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. AddE (A f))"
  unfolding AddE_def using ma
  by pf_mono_prover

\<comment> \<open>Need to take the unit param to make partial function work.\<close>
partial_function (bd) expressionR :: "unit \<Rightarrow> Ex bidef" where [code]:
  "expressionR u = ftransform
                    (Some o id)
                    (\<lambda> Additive a \<Rightarrow> Some (Additive a)
                     | e          \<Rightarrow> None)
                    (AddE (expressionR ()))"
print_theorems
(*
partial_function (bd) expressionR :: "unit \<Rightarrow> Ex bidef" where [code]:
  "expressionR u = transform
                    (id)
                    (\<lambda> Additive a      \<Rightarrow> Additive a \<comment> \<open>The idea here is that any Expression should be printable.\<close>
                     | Multiply a      \<Rightarrow> Additive [Multiply a]
                     | Literal n       \<Rightarrow> Additive [Multiply[Literal n]]
                     | Parenthesised a \<Rightarrow> Additive [Multiply [Parenthesised a]])
                    (AddE (expressionR ()))"
*)
abbreviation Expression :: "Ex bidef" where
  "Expression \<equiv> expressionR ()"
\<comment> \<open>We introduce this so that we can act like Expression is a real parser.\<close>
lemmas Expression_def = expressionR.simps


subsection \<open>Some parsing examples\<close>

lemma "is_error (parse Expression) ''''"
  apply (subst expressionR.simps)
  by (clarsimp simp add: NER_simps AddE_def MultE_def NOE_def Number_def)
lemma "has_result (parse Expression) [] r l \<longleftrightarrow> False"
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def NOE_def Number_def)
  unfolding separated_by1_has_result
  apply (split list.splits; clarsimp simp add: NER_simps)
  unfolding separated_by1_has_result
  apply (split list.splits; clarsimp simp add: NER_simps)
  by (split sum.splits; clarsimp simp add: NER_simps)

lemma "has_result (parse Expression) ''1'' (Additive [Multiply [Literal 1]]) []"
  apply (subst expressionR.simps)
  by (clarsimp simp add: NER_simps AddE_def MultE_def NOE_def Number_def split: sum.splits)

lemma "has_result (parse Expression) ''1*2'' (Additive [Multiply [Literal 1, Literal 2]]) []"
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def split: sum.splits)
  apply (rule exI[of _ \<open>''*2''\<close>]; rule conjI)
  subgoal by (auto simp add: NER_simps NOE_def Number_def split: sum.splits)
  by (auto simp add: NER_simps NOE_def Number_def split: sum.splits)


lemma "has_result (parse Expression) ''1*2+3''   (Additive [Multiply [Literal 1, Literal 2], Multiply [Literal 3]]) []"
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def split: sum.splits)
  apply (rule exI[of _ \<open>''+3''\<close>]; rule conjI)
  subgoal
    apply (rule exI[of _ \<open>''*2+3''\<close>]; rule conjI)
    subgoal by (auto simp add: NER_simps NOE_def Number_def split: sum.splits)
    subgoal
      apply (auto simp add: NER_simps NOE_def Number_def split: sum.splits)
      done
    done
  by (auto simp add: NER_simps NOE_def Number_def split: sum.splits)

lemma "has_result (parse Expression) ''1*(2+3)'' (Additive [Multiply [Literal 1, Parenthesised (Additive [Multiply [Literal 2], Multiply [Literal 3]])]]) []"
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def split: sum.splits)
  apply (rule exI[of _ \<open>''*(2+3)''\<close>]; rule conjI)
  subgoal by (auto simp add: NER_simps NOE_def Number_def split: sum.splits)
  apply (auto simp add: NER_simps NOE_def Number_def split: sum.splits)
  apply (rule exI[of _ \<open>'')''\<close>]; clarsimp)
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def split: sum.splits)
  apply (rule exI[of _ \<open>''+3)''\<close>]; clarsimp; rule conjI)
  subgoal by (auto simp add: NER_simps NOE_def Number_def split: sum.splits)
  by (clarsimp simp add: NER_simps NOE_def Number_def split: sum.splits)

lemma "p_has_result (print Expression) (Additive [Multiply [Literal 1, Parenthesised (Additive [Multiply [Literal 2], Multiply [Literal 3]])]]) ''1*(2+3)'' "
  apply (subst expressionR.simps)
  apply (auto simp add: fp_NER AddE_def MultE_def NOE_def Number_def ws_parenthesised_def)
  apply (subst expressionR.simps)
  by (auto simp add: fp_NER AddE_def MultE_def NOE_def Number_def)

lemma "p_has_result (print Expression) (Additive [Multiply [Parenthesised (Additive [Multiply [Literal 1], Multiply [Literal 2]])]]) ''(1+2)''"
  apply (subst expressionR.simps)
  apply (clarsimp simp add: fp_NER AddE_def MultE_def NOE_def ws_parenthesised_def)
  apply (subst expressionR.simps)
  by (clarsimp simp add: fp_NER AddE_def MultE_def NOE_def Number_def)
\<comment> \<open>We may be able to do some automation here by making rules for Expression to unfold if there is a ( at the first char.\<close>

lemma "has_result (parse Expression) ''1+2'' (Additive [Multiply [Literal 1], Multiply[ Literal 2]]) []"
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def NOE_def Number_def)
  apply (rule exI[of _ \<open>''+2''\<close>]; clarsimp; rule conjI)
  subgoal by (rule exI[of _ \<open>Inl (Literal (Suc 0))\<close>]; clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>Inl (Literal 2)\<close>]; clarsimp simp add: NER_simps)
  done


lemma "p_has_result (print Expression) (Additive [Multiply [Literal 1], Multiply[ Literal 2]]) ''1+2''"
  apply (subst Expression_def)
  by (auto simp add: fp_NER AddE_def MultE_def NOE_def Number_def)

lemma "has_result (parse Expression) ''(1+2)'' (Additive [Multiply [Parenthesised (Additive [Multiply [Literal 1], Multiply [Literal 2]])]]) []"
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def NOE_def Number_def)
  apply (rule exI[of _ \<open>Inr (Additive [Multiply [Literal (Suc 0)], Multiply [Literal 2]])\<close>]; clarsimp)
  apply (clarsimp simp add: NER_simps)
  apply (rule exI[of _ \<open>'')''\<close>]; clarsimp)
  apply (subst expressionR.simps)
  apply (auto simp add: NER_simps AddE_def MultE_def NOE_def Number_def)
  apply (rule exI[of _ \<open>''+2)''\<close>]; clarsimp; rule conjI)
  subgoal by (rule exI[of _ \<open>Inl (Literal (Suc 0))\<close>]; clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>Inl (Literal 2)\<close>]; clarsimp simp add: NER_simps)
  done


lemma "p_has_result (print Expression) (Additive [Multiply [Parenthesised (Additive [Multiply [Literal 1], Multiply [Literal 2]])]]) ''(1+2)''"
  apply (subst Expression_def)
  apply (auto simp add: fp_NER AddE_def MultE_def NOE_def Number_def ws_parenthesised_def)
  apply (subst Expression_def)
  by (auto simp add: fp_NER AddE_def MultE_def NOE_def Number_def)

\<comment> \<open>This should be generalisable to all constructors right?\<close>
lemma not_both_lit_and_paren:
  "x1 = Literal n \<and> x1 = Parenthesised e \<longleftrightarrow> False"
  by blast


lemma NOE_has_result_safe[NER_simps]:
  "has_result (parse (NOE Expression)) i (Additive as) l \<longleftrightarrow> False"
  "has_result (parse (NOE Expression)) i (Multiply ms) l \<longleftrightarrow> False"
  "has_result (parse (NOE Expression)) i (Literal n) l \<longleftrightarrow> has_result (parse nat_b) i n l"
  "has_result (parse (NOE Expression)) i (Parenthesised e) l \<longleftrightarrow> has_result (parse (ws_parenthesised Expression)) i e l"
  unfolding NOE_def
  subgoal by (clarsimp simp add: NER_simps split: sum.splits)
  subgoal by (clarsimp simp add: NER_simps split: sum.splits)
  subgoal by (clarsimp simp add: NER_simps split: sum.splits; argo)
  subgoal
    apply (auto simp add: NER_simps not_both_lit_and_paren split: sum.splits)
    by (metis char_not_in_digit_chars(3) chars_not_in_whitespace(2) dropWhile_hd_no_match)
  done

lemma MultE_has_result_safe[NER_simps]:
  "has_result (parse (MultE Expression)) i (Additive as) l \<longleftrightarrow> False"
  "has_result (parse (MultE Expression)) i (Literal n) l \<longleftrightarrow> False"
  "has_result (parse (MultE Expression)) i (Parenthesised e) l \<longleftrightarrow> False"
  "has_result (parse (MultE Expression)) i (Multiply []) l \<longleftrightarrow> False"
  "has_result (parse (MultE Expression)) i (Multiply [m]) l \<longleftrightarrow> has_result (parse (NOE Expression)) i m l \<and> (is_error (parse star) l \<or> (\<exists>l'. has_result (parse star) l () l' \<and> is_error (parse (NOE Expression)) l'))"
  "has_result (parse (MultE Expression)) i (Multiply (m#ms)) l \<longleftrightarrow> (\<exists>l'. has_result (parse (NOE Expression)) i m l' \<and> has_result (parse (many (b_then star (NOE Expression)))) l' (zip (replicate (length ms) ()) ms) l)"
  unfolding MultE_def
  by (clarsimp simp add: NER_simps split: sum.splits)+

lemma AddE_has_result_safe[NER_simps]:
  "has_result (parse (AddE Expression)) i (Literal n) l \<longleftrightarrow> False"
  "has_result (parse (AddE Expression)) i (Parenthesised e) l \<longleftrightarrow> False"
  "has_result (parse (AddE Expression)) i (Multiply ms) l \<longleftrightarrow> False"
  "has_result (parse (AddE Expression)) i (Additive []) l \<longleftrightarrow> False"
  "has_result (parse (AddE Expression)) i (Additive [a]) l \<longleftrightarrow> has_result (parse (MultE Expression)) i a l \<and> (is_error (parse plus) l \<or> (\<exists>l'. has_result (parse plus) l () l' \<and> is_error (parse (AddE Expression)) l'))"
  "has_result (parse (AddE Expression)) i (Additive (a#as)) l \<longleftrightarrow> (\<exists>l'. has_result (parse (MultE Expression)) i a l' \<and> has_result (parse (many (b_then plus (MultE Expression)))) l' (zip (replicate (length as) ()) as) l)"
  unfolding AddE_def
  by (clarsimp simp add: NER_simps split: sum.splits)+


lemma Expression_has_result_safe[NER_simps]:
  "has_result (parse Expression) i (Literal n) l \<longleftrightarrow> False"
  "has_result (parse Expression) i (Parenthesised e) l \<longleftrightarrow> False"
  "has_result (parse Expression) i (Multiply ms) l \<longleftrightarrow> False"
  "has_result (parse Expression) i (Additive []) l \<longleftrightarrow> False"
  "has_result (parse Expression) i (Additive [a]) l \<longleftrightarrow> has_result (parse (MultE Expression)) i a l \<and> (is_error (parse plus) l \<or> (\<exists>l'. has_result (parse plus) l () l' \<and> is_error (parse (MultE Expression)) l'))"
  "has_result (parse Expression) i (Additive (a#as)) l \<longleftrightarrow> (\<exists>l'. has_result (parse (MultE Expression)) i a l' \<and> has_result (parse (many (b_then plus (MultE Expression)))) l' (zip (replicate (length as) ()) as) l)"
  by (subst Expression_def; clarsimp simp add: NER_simps)+

\<comment> \<open>This is one of the most complex examples that we show above.
    Note how with these safe NER rules any combination of the constructors can be unfolded by clarsimp.\<close>
lemma "has_result (parse Expression) ''1*(2+3)'' (Additive [Multiply [Literal 1, Parenthesised (Additive [Multiply [Literal 2], Multiply [Literal 3]])]]) []"
  by (clarsimp simp add: NER_simps)


\<comment> \<open>These both use admissible and strict rules defined in the types file.\<close>
lemma PNGI_Expression:
  "PNGI (parse Expression)"
  apply (induction rule: expressionR.fixp_induct)
  subgoal by (rule admissible_PNGI)
  subgoal by (simp add: strict_PNGI)
  subgoal
    unfolding AddE_def MultE_def NOE_def Number_def ws_parenthesised_def
    by (intro ftransform_PNGI transform_PNGI_rev[THEN iffD2] separated_by1_PNGI or_PNGI PASI_PNGI  then_PASI then_PASI_from_pasi_pngi; assumption)
  done


lemma Expression_no_print_empty:
  "\<not>p_has_result (print Expression) e []"
  apply (induction rule: expressionR.fixp_induct)
  subgoal by (rule admissible_no_empty_result)
  subgoal by (clarsimp simp add: fp_NER)
  by (clarsimp simp add: print_empty AddE_def MultE_def separated_by1_def NOE_def ws_parenthesised_def split: Ex.splits list.splits)




(*
  = Additive (getList: "Ex list")
  | Multiply (getList: "Ex list")
  | Literal (getNat: nat)
  | Parenthesised (getE: Ex)
*)
section \<open>Well formed\<close>
lemma Expression_no_eat_into_paren:
  "pa_does_not_eat_into_pb_nondep Expression (ws_char_ws CHR '')'')"
  unfolding pa_does_not_eat_into_pb_nondep_def
  apply (auto simp add: NER_simps fp_NER)
  subgoal for r t
    apply (cases r; clarsimp)
    subgoal for xs
      apply (induction xs arbitrary: t rule: rev_induct)
      subgoal by (subst (asm) Expression_def; auto simp add: fp_NER AddE_def)
      subgoal for m ms t''
        apply (subst Expression_def)
        apply (subst (asm) (3) Expression_def)
        apply (subst (asm) (1) Expression_def)
        apply (subst (asm) (2) Expression_def)
        apply (auto simp add: fp_NER NER_simps AddE_def)
        
        
        sorry
      done
    \<comment> \<open>All other Ex's cannot be printed by Expression so the assm is false:\<close>
    subgoal by (subst (asm) Expression_def; clarsimp simp add: fp_NER)
    subgoal by (subst (asm) Expression_def; clarsimp simp add: fp_NER)
    subgoal by (subst (asm) Expression_def; clarsimp simp add: fp_NER)
    done
  oops


lemma expression_well_formed:
  "bidef_well_formed Expression"
  apply (induction rule: expressionR.fixp_induct)
  subgoal by (rule admissible_WF)
  subgoal by (simp add: strict_WF)
  apply (rule ftransform_well_formed2)
  subgoal by (auto simp add: NER_simps fp_NER AddE_def well_formed_ftransform_funcs_def split: Ex.splits)
  unfolding AddE_def
  apply (rule ftransform_well_formed2)
  subgoal by (clarsimp simp add: fp_NER well_formed_ftransform_funcs_def split: Ex.splits)
  unfolding MultE_def
  apply (rule separated_by1_well_formed)
  subgoal by (clarsimp simp add: fp_NER)
  subgoal
    apply (rule ftransform_well_formed2)
    subgoal by (clarsimp simp add: fp_NER well_formed_ftransform_funcs_def split: Ex.splits)
    apply (rule separated_by1_well_formed)
    subgoal by (clarsimp simp add: fp_NER)
    subgoal
      unfolding NOE_def
      apply (rule ftransform_well_formed2)
      subgoal by (clarsimp simp add: NER_simps fp_NER well_formed_ftransform_funcs_def split: Ex.splits sum.splits)
      apply (rule or_well_formed)
      subgoal by (rule Number_well_formed)
      subgoal \<comment> \<open>bidef_well_formed (ws_parenthesised (f_ ()))\<close>
        unfolding ws_parenthesised_def
        apply (rule transform_well_formed4)
        subgoal by (clarsimp simp add: fp_NER well_formed_transform_funcs4_def)
        apply (rule b_then_well_formed)
        subgoal by (rule ws_char_ws_well_formed[OF expression_punctuation_charsets(9)])
        subgoal
          \<comment> \<open>This is there we need to create something like "chars can be taken from start of input"\<close>
          \<comment> \<open>Because the inner parser (Expression) may end in ws)ws, which will eat into ws)ws (by eating away the ws.)\<close>
          \<comment> \<open>But, of course, this does not matter for the parse result.\<close>
          \<comment> \<open>Note that I'm fairly sure that we can resolve this in the creation of the bidefs,
               but I purposefully did not to surface this issue.\<close>
          sorry
        subgoal
          apply (rule first_printed_does_not_eat_into3)
          subgoal by (rule ws_char_ws_well_formed[OF expression_punctuation_charsets(9)])
          subgoal
            apply (subst ws_char_ws_does_not_consume_past_char3[of \<open>CHR ''(''\<close>, OF expression_punctuation_charsets(9)])
            find_theorems first_printed_chari b_then
            find_theorems does_not_consume_past_char3 ws_char_ws
            sorry
          done
        done
      subgoal by (clarsimp simp add: fp_NER NER_simps well_formed_or_pair_def)
      done
    apply (rule b_then_well_formed) 
    subgoal \<comment> \<open>bidef_well_formed (f_ ()) \<Longrightarrow> bidef_well_formed (NOE (f_ ()))\<close>
      unfolding NOE_def
      apply (rule ftransform_well_formed2)
      subgoal by (clarsimp simp add: NER_simps fp_NER well_formed_ftransform_funcs_def split: Ex.splits sum.splits)
      apply (rule or_well_formed)
      subgoal by (rule Number_well_formed)
      subgoal \<comment> \<open>bidef_well_formed (ws_parenthesised (f_ ())) is already a subgoal above.\<close> sorry
      subgoal by (clarsimp simp add: well_formed_or_pair_def NER_simps fp_NER)
      done
    subgoal
      
      sorry
    subgoal
      apply (rule first_printed_does_not_eat_into3)
      subgoal \<comment> \<open>bidef_well_formed (f_ ()) \<Longrightarrow> bidef_well_formed (NOE (f_ ())) is already a subgoal above.\<close> sorry
      subgoal
        apply (subst many_fpci)
        apply (clarsimp simp add: fp_NER fpci_simps split: list.splits)
        \<comment> \<open>does_not_consume_past_char3 (parse (NOE (f_ ()))) CHR ''*''\<close>
        
        
        
        sorry
      done
    done
  subgoal sorry
  oops



end