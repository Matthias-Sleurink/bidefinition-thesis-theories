theory all_definitions
  imports basic_definitions
          derived_or
          derived_dep_then
          derived_then
          derived_optional
          derived_peek_boolean
          derived_then_drop_first
          derived_then_drop_second
          derived_many
          derived_many1
          derived_char_for_predicate
          derived_any_from_set
          derived_this_char
          derived_this_string
          derived_digit_char
          derived_alphabet_char
          derived_eof
          derived_alphanumeric_char
          derived_char_not_in_set
          derived_uppercase_char
          derived_lowercase_char
          derived_nat
          derived_whitespace_char
          derived_separated_by
          derived_drop
          derived_ws_comma_ws
          derived_ws_char_ws
          derived_ws_char
          derived_char_ws
          derived_separated_by1
          derived_int
          \<comment> \<open>Add all derived definitions here\<close>
begin

text \<open>
This is the second collation phase of the dependency graph.
Importing this files give you all the basic and the derived definitions.
The intention is for this file to be the entry point to the library.
So the examples will also import this file to start.
The dependency graph should contain as much parallelism as attainable using the
 "multiple diamond" structure as explained in the basic definitions file.
\<close>



lemma charset_example:
  "charset (parse (if_then_else (this_char CHR ''a'') return (this_char CHR ''b'') id)) = {CHR ''a'', CHR ''b''}"
  unfolding charset_def
  apply (subst if_then_else_has_result_no_split)
  apply (subst this_char_has_result)
  apply (subst this_char_has_result)
  apply (subst this_char_is_error)
  apply (subst return_has_result)
  apply (simp split: sum.splits)
  apply auto
  subgoal for x X r l c
    apply (cases r)
    subgoal for rl by clarsimp
    subgoal for rb by force
    done
  subgoal
    by fastforce
  subgoal
    apply (rule exI[of _ \<open>{CHR ''b''}\<close>])
    apply clarsimp
    apply (rule exI[of _ \<open>Inr CHR ''b''\<close>])
    by clarsimp
  done


lemma expression_punctuation_charsets[simp]:
  "CHR ''*'' \<notin> digit_chars"
  "CHR ''+'' \<notin> digit_chars"
  "CHR ''('' \<notin> digit_chars"
  "CHR '')'' \<notin> digit_chars"
  "CHR ''{'' \<notin> digit_chars"
  "CHR ''}'' \<notin> digit_chars"
  "CHR ''['' \<notin> digit_chars"
  "CHR '']'' \<notin> digit_chars"
  "CHR ''t'' \<notin> digit_chars"
  "CHR ''f'' \<notin> digit_chars"
  "CHR ''n'' \<notin> digit_chars"
  "CHR ''\"'' \<notin> digit_chars"
  "CHR '':'' \<notin> digit_chars"
  "CHR ''-'' \<notin> digit_chars"

  "CHR ''*'' \<notin> derived_digit_char.digit_chars"
  "CHR ''+'' \<notin> derived_digit_char.digit_chars"
  "CHR ''t'' \<notin> derived_digit_char.digit_chars"
  "CHR ''f'' \<notin> derived_digit_char.digit_chars"
  "CHR ''n'' \<notin> derived_digit_char.digit_chars"
  "CHR ''\"'' \<notin> derived_digit_char.digit_chars"
  "CHR '':'' \<notin> derived_digit_char.digit_chars"

  "CHR ''*'' \<notin> whitespace_chars"
  "CHR ''+'' \<notin> whitespace_chars"
  "CHR ''('' \<notin> whitespace_chars"
  "CHR '')'' \<notin> whitespace_chars"
  "CHR ''{'' \<notin> whitespace_chars"
  "CHR ''}'' \<notin> whitespace_chars"
  "CHR ''['' \<notin> whitespace_chars"
  "CHR '']'' \<notin> whitespace_chars"
  "CHR ''t'' \<notin> whitespace_chars"
  "CHR ''f'' \<notin> whitespace_chars"
  "CHR ''n'' \<notin> whitespace_chars"
  "CHR ''\"'' \<notin> whitespace_chars"
  "CHR '':'' \<notin> whitespace_chars"
  "CHR ''-'' \<notin> whitespace_chars"
  unfolding derived_digit_char.digit_chars_def whitespace_chars_def
  by blast+

lemma chars_not_in_whitespace[simp]:
  "c \<in> digit_chars \<longrightarrow> c\<notin>whitespace_chars"
  "c \<in> derived_digit_char.digit_chars \<longrightarrow> c\<notin>whitespace_chars"
  unfolding derived_digit_char.digit_chars_def whitespace_chars_def
  by blast+
lemma in_ws_and_digits_eq_false[simp]:
  "c \<in> digit_chars                    \<and> c \<in> whitespace_chars \<longleftrightarrow> False"
  "c \<in> derived_digit_char.digit_chars \<and> c \<in> whitespace_chars \<longleftrightarrow> False"
  unfolding derived_digit_char.digit_chars_def whitespace_chars_def
  by blast+






end
