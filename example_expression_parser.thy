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
lemmas ws_paren_def[NER_simps] = ws_parenthesised_def


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


\<comment> \<open>This is done with the classic recursive method, which cannot work for us.\<close>
lemma PNGI_Expression:
  "PNGI (parse Expression)"
  apply (subst Expression_def)
  apply (auto intro!: ftransform_PNGI separated_by1_PNGI or_PNGI then_PNGI
            simp add: AddE_def MultE_def NOE_def Number_def ws_parenthesised_def
                      transform_PNGI_rev nat_b_PNGI ws_char_ws_PNGI)
  \<comment> \<open>First subgoal is now again `PNGI parse Expression`\<close>
  oops  

lemma mcont_parse[cont_intro]:
  "mcont bd.lub_fun bd.le_fun (flat_lub None) (flat_ord None) (\<lambda>x. parse (x ()) i)"
  apply (rule)
  subgoal
    apply (rule monotoneI)
    by (simp add: bd_ord_def fun_ord_def)
  apply (rule cont_intro)
  unfolding bd_ord_def fun_ord_def
  apply (rule contI)
  unfolding bd_lub_def
  apply clarsimp
  by (smt (verit, ccfv_SIG) Inf.INF_cong fun_lub_apply image_image)

lemma admissible_PNGI[cont_intro]:
  "bd.admissible (\<lambda>expressionR. PNGI (parse (expressionR ())))"
  unfolding PNGI_def
  unfolding has_result_def
  by simp

lemma strict_PNGI:
  "PNGI ((\<lambda>u. None))"
  by (simp add: PNGI_def has_result_def)

lemma PNGI_Expression:
  "PNGI (parse Expression)"
  apply (induction rule: expressionR.fixp_induct)
  subgoal by (rule admissible_PNGI)
  subgoal by (simp add: strict_PNGI)
  subgoal
    unfolding AddE_def MultE_def NOE_def Number_def ws_parenthesised_def
    by (intro ftransform_PNGI transform_PNGI_rev[THEN iffD2] separated_by1_PNGI or_PNGI PASI_PNGI  then_PASI then_PASI_from_pasi_pngi; assumption)
  done

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


lemma mcont_print[cont_intro]:
  "mcont bd.lub_fun bd.le_fun (flat_lub None) (flat_ord None) (\<lambda>x. print (x ()) i)"
  apply (rule)
  subgoal
    apply (rule monotoneI)
    by (simp add: bd_ord_def fun_ord_def)
  apply (rule cont_intro)
  unfolding bd_ord_def fun_ord_def
  apply (rule contI)
  unfolding bd_lub_def
  apply clarsimp
  by (smt (verit, ccfv_SIG) Inf.INF_cong fun_lub_apply image_image)

lemma admissible_parser_can_parse[cont_intro]:
  "bd.admissible (\<lambda>expressionR. parser_can_parse_print_result (parse (expressionR ())) (print (expressionR ())))"
  unfolding parser_can_parse_print_result_def p_has_result_def has_result_def
  by simp

lemma admissible_exist_printable[cont_intro]:
  "bd.admissible (\<lambda>expressionR. \<exists>s. print (expressionR ()) t = Some (Some s))"
  apply (rule ccpo.admissibleI)
  unfolding bd_ord_def fun_ord_def fun_lub_def bd_lub_def
  apply clarsimp
  by (smt (z3) all_not_in_conv chain_def flat_ord_def mem_Collect_eq option.lub_upper option.simps(3))

lemma admissible_parse_result_eq[cont_intro]:
  "bd.admissible (\<lambda>expressionR. parse (expressionR ()) i \<noteq> Some (Some (t, l)))"
  by simp

lemma admissible_printer_can_print[cont_intro]:
  "bd.admissible (\<lambda>expressionR. printer_can_print_parse_result (parse (expressionR ())) (print (expressionR ())))"
  unfolding printer_can_print_parse_result_def p_has_result_def has_result_def
  by simp

lemma admissible_WF:
  "bd.admissible (\<lambda>expressionR. bidef_well_formed ((expressionR ())))"
  unfolding bidef_well_formed_def
  by simp

lemma strict_WF:
  "bidef_well_formed (bdc (\<lambda>u. None) (\<lambda>u. None))"
  unfolding bidef_well_formed_def
  by (simp add: strict_PNGI parser_can_parse_print_result_def p_has_result_def printer_can_print_parse_result_def has_result_def)


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
      subgoal
        unfolding ws_parenthesised_def
        apply (rule transform_well_formed4)
        subgoal by (clarsimp simp add: fp_NER well_formed_transform_funcs4_def)
        
        sorry
      subgoal by (clarsimp simp add: fp_NER NER_simps well_formed_or_pair_def)
      done
    oops



end