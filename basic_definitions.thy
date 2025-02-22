theory basic_definitions
  imports types
          basic_fallible_transform
          basic_dependent_if_then_else
          basic_fail
          basic_return
          basic_peek_result
          basic_one_char
                \<comment> \<open>Add other basic definitions here.\<close>
begin

text \<open>

This file is the first "diamond closing" part of the dependency graph:

types
|  |  |
|  B1 B2 ...       (All basic definitions, one per file)
|  |  |
basic_definitions
|  |  |
|  D1 D2 ...       (All derived definitions, one per file)
|  |  |
all_definitions
|  |  |
|  E1 E2 ...       (All examples, one per file)
|  |  |
everything

The types are defined in their own file.
The basic definitions all import the types, and the other basic definitions that they might need.
Then the basic_definitions file (this file) exists to collate all those imports to one place.
From there the "derived" definitions can import all the basic definitions with one file import.
The rule is that files can only import the "big" file from the layer above, and inside the layer.
If we did not have the big file we could get an even better dependency graph,
 but that would require a lot more import statements.


This allows Isabelle to build a dependency graph that is more parallel than just one file that
 contains the definitions for all basic definitions.
My hope is that this will improve startup times,
 and also decrease re-proof times when things high in the graph are changed.



\<close>

end