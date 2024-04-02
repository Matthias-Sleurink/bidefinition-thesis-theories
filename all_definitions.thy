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

end