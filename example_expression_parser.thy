theory example_expression_parser
  imports all_definitions
begin

text \<open>
A recursive expression parser.
\<close>
datatype Ex
  = Additive (getList: "Ex list")
  | Subtract (getList: "Ex list")
  | Multiply (getList: "Ex list")
  | Literal (getNat: nat)
  | Braced Ex

fun val :: "Ex \<Rightarrow> nat" where
  "val (Additive []) = 0"
| "val (Additive (x#xs)) = (val x) + (val (Additive xs))"
| "val (Subtract []) = 0"
| "val (Subtract (x#xs)) = (val x) - (val (Subtract xs))"
| "val (Multiply []) = 1"
| "val (Multiply (x#xs)) = (val x) * (val (Multiply xs))"
| "val (Literal v) = v"
| "val (Braced e) = val e"

lemma val_tests:
  "0 = val (Additive [])"
  "1 = val (Additive [Literal 1])"
  "3 = val (Additive [Literal 1, Multiply [Literal 2]])"
  "7 = val (Additive [Literal 1, Multiply [Literal 2, Braced (Literal 3)]])"
  by simp_all

definition star :: "unit bidef" where
  "star = ws_char_ws CHR ''*''"
definition plus :: "unit bidef" where
  "plus = ws_char_ws CHR ''+''"
lemma expression_punctuation_charsets[simp]:
  "CHR ''*'' \<notin> digit_chars"
  "CHR ''+'' \<notin> digit_chars"
  "CHR ''('' \<notin> digit_chars"
  "CHR '')'' \<notin> digit_chars"

  "CHR ''*'' \<notin> derived_digit_char.digit_chars"
  "CHR ''+'' \<notin> derived_digit_char.digit_chars"
  "CHR ''('' \<notin> derived_digit_char.digit_chars"
  "CHR '')'' \<notin> derived_digit_char.digit_chars"

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


\<comment> \<open>Is there way some way of saying that this is just the Literal branch of the type?\<close>
definition Number :: "Ex bidef" where
  "Number = transform Literal getNat nat_b"
\<comment> \<open>This is where we'd want to take a parameter of Exp bidef to create the (Expr) case.\<close>


definition Mult :: "Ex bidef" where
  "Mult = transform
            Multiply
            getList
            (separated_by1 Number star ())"

definition Add :: "Ex bidef" where
  "Add = transform
          Additive
          getList
          (separated_by1 Mult plus ())"


definition expression :: "Ex bidef" where
  "expression = transform
                  (id)
                  \<comment> \<open>Is there something like lambdacase in haskell?\<close>
                  \<comment> \<open>This would not be needed if we could do the 'This branch of type' thing above.\<close>
                  (\<lambda>e. case e of
                         Additive a \<Rightarrow> Additive a
                       | Multiply a \<Rightarrow> Additive [Multiply a]
                       | Literal n \<Rightarrow> Additive [Multiply[Literal n]]
                  ) \<comment> \<open>Expr \<Rightarrow> Addl\<close>
                  Add"

lemma "has_result (parse expression) ''123'' (Additive [Multiply [Literal 123]]) []"
  apply (clarsimp simp add: NER_simps expression_def Add_def Mult_def Number_def star_def plus_def)
  by (clarsimp simp add: nat_from.simps(2))
lemma "p_has_result (print expression) (Additive [Multiply [Literal 123]]) ''123''"
  apply (clarsimp simp add: fp_NER expression_def Add_def Mult_def Number_def star_def plus_def print_nat_def)
  by (clarsimp simp add: numeral_2_eq_2 numeral_3_eq_3)

lemma "has_result (parse expression) ''1+2'' (Additive [Multiply [Literal 1], Multiply [Literal 2]]) []"
  apply (clarsimp simp add: NER_simps expression_def Add_def Mult_def Number_def star_def plus_def)
  apply (rule exI[of _ \<open>[()]\<close>])
  by (clarsimp simp add: NER_simps)
lemma "p_has_result (print expression) (Additive [Multiply [Literal 1], Multiply [Literal 2]]) ''1+2''"
  apply (clarsimp simp add: fp_NER expression_def Add_def Mult_def Number_def star_def plus_def print_nat_def)
  by (clarsimp simp add: numeral_2_eq_2)

lemma "has_result (parse expression) ''1+2*3'' (Additive [Multiply [Literal 1], Multiply [Literal 2, Literal 3]]) []"
  apply (clarsimp simp add: NER_simps expression_def Add_def Mult_def Number_def star_def plus_def)
  apply (rule exI[of _ \<open>[()]\<close>])
  apply (clarsimp simp add: NER_simps)
  apply (rule exI[of _ \<open>[()]\<close>])
  by (clarsimp simp add: NER_simps)
lemma "p_has_result (print expression) (Additive [Multiply [Literal 1], Multiply [Literal 2, Literal 3]]) ''1+2*3''"
  apply (clarsimp simp add: fp_NER expression_def Add_def Mult_def Number_def star_def plus_def print_nat_def)
  by (clarsimp simp add: numeral_2_eq_2 numeral_3_eq_3)



\<comment> \<open>NER\<close>
\<comment> \<open>Kinda seems like we need this for the underlying as well.\<close>
lemma expression_is_nonterm[NER_simps]:
  "is_nonterm (parse expression) i \<longleftrightarrow> False"
  apply (auto simp add: expression_def Add_def Mult_def Number_def star_def plus_def NER_simps)
  subgoal by (smt (verit) b_then_is_nonterm many_not_nonterm_when_base_not_nonterm nat_b_PASI nat_is_nonterm then_PASI transform_PASI transform_is_nonterm ws_char_ws_PASI ws_char_ws_is_nonterm)
  subgoal
    using many_not_nonterm_when_base_not_nonterm[of \<open>(b_then (ws_char_ws CHR ''+'') (transform Multl getNList (separated_by (ws_char_ws CHR ''*'') (transform Num getNumber nat_b) ())))\<close>]
    using then_PASI_from_pasi_pngi[of \<open>ws_char_ws CHR ''+''\<close> \<open>transform Multl getNList (separated_by (ws_char_ws CHR ''*'') (transform Num getNumber nat_b) ())\<close>, OF ws_char_ws_PASI]
    using separated_by_PNGI[of \<open>transform Num getNumber nat_b\<close> \<open>ws_char_ws CHR ''*''\<close>,
                            OF transform_PNGI[THEN iffD1, OF nat_b_PNGI]
                               then_PASI[OF ws_char_ws_PASI transform_PASI[THEN iffD1, OF nat_b_PASI]]]
    apply (auto simp add: PASI_PNGI)
    unfolding b_then_is_nonterm
    apply (clarsimp simp add: ws_char_ws_is_nonterm transform_is_nonterm separated_by_is_nonterm nat_is_nonterm transform_has_result)
    using many_not_nonterm_when_base_not_nonterm[of \<open>b_then (ws_char_ws CHR ''*'') (transform Num getNumber nat_b)\<close>]
    by (auto simp add: PASI_PNGI then_PASI b_then_is_nonterm ws_char_ws_is_nonterm transform_is_nonterm nat_is_nonterm)
  done

lemma fail_is_error[NER_simps]:
  "is_error (parse fail) i \<longleftrightarrow> True"
  "is_error fail_p       i \<longleftrightarrow> True"
  by (simp add: fail_def is_error_def)+

lemma fail_has_result[NER_simps]:
  "has_result (parse fail) i r l \<longleftrightarrow> False"
  "has_result fail_p       i r l \<longleftrightarrow> False"
  by (simp add: fail_def has_result_def)+

lemma fail_has_result_c[NER_simps]:
  "has_result_c (parse fail) c r l \<longleftrightarrow> False"
  "has_result_c fail_p       c r l \<longleftrightarrow> False"
  by (simp add: has_result_c_def fail_has_result)+

lemma fail_has_result_ci[NER_simps]:
  "has_result_ci (parse fail) i c r l \<longleftrightarrow> False"
  "has_result_ci fail_p       i c r l \<longleftrightarrow> False"
  by (simp add: has_result_ci_def fail_has_result_c)+



\<comment> \<open>FP NER\<close>
lemma fail_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print fail) i \<longleftrightarrow> False"
  "p_is_nonterm fail_pr i \<longleftrightarrow> False"
  by (simp add: fail_def p_is_nonterm_def)+

lemma fail_p_is_error[fp_NER]:
  "p_is_error (print fail) i \<longleftrightarrow> True"
  "p_is_error fail_pr      i \<longleftrightarrow> True"
  by (simp add: fail_def p_is_error_def)+

lemma fail_p_has_result[fp_NER]:
  "p_has_result (print fail) i r \<longleftrightarrow> False"
  "p_has_result fail_pr      i r \<longleftrightarrow> False"
  by (simp add: fail_def p_has_result_def)+

lemma fail_print_empty[print_empty, fp_NER]:
  "p_has_result (print fail) i [] \<longleftrightarrow> False"
  by (rule fail_p_has_result(1))



\<comment> \<open>PNGI, PASI\<close>
lemma fail_PNGI:
  "PNGI (parse fail)"
  by (simp add: PNGI_def NER_simps)

lemma fail_PASI:
  "PASI (parse fail)"
  by (simp add: PASI_def NER_simps)



\<comment> \<open>Charset\<close>
lemma charset_fail:
  "charset (parse fail) = {}"
  unfolding charset_def
  by (clarsimp simp add: NER_simps)

lemma first_chars_fail:
  "first_chars (print fail) = {}"
  unfolding first_chars_def
  by (clarsimp simp add: fp_NER)



\<comment> \<open>Does not peek past end\<close>
lemma fail_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse fail)"
  unfolding does_not_peek_past_end_def
  by (clarsimp simp add: fail_has_result)


\<comment> \<open>Does not consume past char.\<close>
lemma fail_does_not_consume_past_char:
  shows "does_not_consume_past_char (parse fail) ch"
  unfolding does_not_consume_past_char_def
  by (clarsimp simp add: fail_has_result)

lemma fail_does_not_consume_past_char2:
  shows "does_not_consume_past_char2 (parse fail) ch"
  unfolding does_not_consume_past_char2_def
  by (clarsimp simp add: fail_has_result)


\<comment> \<open>First printed char\<close>
lemma fail_fpci[fpci_simps]:
  shows "\<nexists>i c. first_printed_chari (print fail) i c"
        "first_printed_chari (print fail) i c \<longleftrightarrow> False"
  unfolding first_printed_chari_def
  by (clarsimp simp add: fail_p_has_result)+

lemma fail_fpc[fpc_simps]:
  shows "\<nexists>i c. fpc (parse fail) i c"
        "fpc (parse fail) i c \<longleftrightarrow> False"
  unfolding fpc_def
  by (clarsimp simp add: fail_has_result)+



\<comment> \<open>Well Formed\<close>
lemma fail_well_formed:
  "bidef_well_formed fail"
  apply wf_init
  subgoal by (rule fail_PNGI)
  subgoal by (simp add: parser_can_parse_print_result_def fp_NER)
  subgoal by (simp add: printer_can_print_parse_result_def NER_simps)
  done



end