theory all_definitions
  imports basic_definitions
          derived_or
          derived_dep_then
          derived_then
          derived_optional
          derived_peek_boolean
          \<comment> \<open>Add all derived definitions here\<close>
begin

text \<open>
This is the second collation phase of the dependency graph.
Importing this files give you all the basic and the derived definitions.
The intention is for this file to be the entrypoint to the library.
So the examples will also import this file to start.
The dependency graph should contain as much parallelism as attainable using the
 "multiple diamond" structure as explained in the basic definitions file.
\<close>

end