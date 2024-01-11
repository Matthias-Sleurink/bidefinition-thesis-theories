theory types
  imports Main
begin

section \<open>Introduction\<close>
text  \<open>
To reduce Isabelle startup times we will split out most things into their own files.
This will help Isabelle proof as many things as possible in parallel,
and will also clarify the source dependencies.
\<close>

section \<open>Types for the parser\<close>

type_synonym '\<alpha> parse_result = "('\<alpha> \<times> string)"

\<comment> \<open>The outer option defines termination,
    The inner option defines parsing success\<close>
type_synonym '\<alpha> parser = "string \<Rightarrow> '\<alpha> parse_result option option"

\<comment> \<open>this is to make the parsers easier to write.
   Some (Some xyz) can be confusing to read, so we can use this to help explain what's what..\<close>
definition terminate_with where [simp]: "terminate_with = Some"


section \<open>NER\<close>
text \<open>NEW lemmas are lemmas about the Nonterm, Error, and Result state of the parsers.
      These lemmas aim to shortcut the source of the parser to jump to the result.
      This simplifies proofs using the parsers and combinators.
\<close>

named_theorems NER_simps
named_theorems NER_high_level_simps
text \<open>The high level simps are tried before the NER_simps,
      this allows us to have rules for a combinator,
      and also have rules for specific invocations of a combinator.\<close>

definition is_nonterm :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> bool" where
  "is_nonterm p i \<longleftrightarrow> p i = None"

definition is_error :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> bool" where
  "is_error p i \<longleftrightarrow> p i = Some None"

definition has_result :: "'\<alpha> parser \<Rightarrow> string \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "has_result p i r l \<longleftrightarrow> p i = Some (Some (r, l))"



lemma has_result_implies_not_is_error:
  "has_result p i r l \<Longrightarrow> \<not> is_error p i"
  by (simp add: has_result_def is_error_def)

lemma has_result_implies_not_is_nonterm:
  "has_result p i r l \<Longrightarrow> \<not> is_nonterm p i"
  by (simp add: has_result_def is_nonterm_def)

lemma is_error_implies_not_has_result:
  "is_error p i \<Longrightarrow> (\<nexists> r l . has_result p i r l)"
  by (simp add: has_result_def is_error_def)

lemma is_nonterm_implies_not_has_result:
  "is_nonterm p i \<Longrightarrow> (\<nexists> r l . has_result p i r l)"
  by (simp add: has_result_def is_nonterm_def)


text \<open>Some basic NER simps that are so quick to prove
      they are not worth splitting into their own file.\<close>

subsection \<open>NER for if\<close>
lemma if_is_nonterm[NER_simps]:
  "is_nonterm (if B then T else F) i \<longleftrightarrow> (if B then is_nonterm T i else is_nonterm F i)"
  by simp

lemma if_is_error[NER_simps]:
  "is_error (if B then T else F) i \<longleftrightarrow> (if B then is_error T i else is_error F i)"
  by simp

lemma if_has_result[NER_simps]:
  "has_result (if B then T else F) i r l \<longleftrightarrow> (if B then has_result T i r l else has_result F i r l)"
  by simp



section \<open>Types for the printer\<close>
type_synonym '\<alpha> printer = "'\<alpha> \<Rightarrow> string option"

section \<open>FP NER\<close>
definition p_has_result :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "p_has_result fp v s \<longleftrightarrow> fp v = Some s"

definition p_is_error :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "p_is_error fp v \<longleftrightarrow> fp v = None"


section \<open>Bidefinition types\<close>

type_synonym '\<alpha> bidef = "('\<alpha> parser \<times> '\<alpha> printer)"

abbreviation parse :: "'\<alpha> bidef \<Rightarrow> '\<alpha> parser" where "parse \<equiv> fst"
abbreviation print :: "'\<alpha> bidef \<Rightarrow> '\<alpha> printer" where "print \<equiv> snd"



end