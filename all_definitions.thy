theory all_definitions
  imports basic_definitions
          derived_or
          derived_dep_then
          derived_then
          derived_optional
          derived_peek_boolean
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



end
