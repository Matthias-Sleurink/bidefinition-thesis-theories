theory types
  imports Main
          "HOL-Eisbach.Eisbach" \<comment> \<open>For the method bidef_init\<close>
begin

\<comment> \<open>MARK TO MAKE PRE-CHANGE COMMIT\<close>

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



subsection \<open>NER for inlined bind\<close>
lemma bind_is_nonterm[NER_simps]:
  "is_nonterm (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i \<longleftrightarrow> is_nonterm A i \<or> (\<exists>r l. has_result A i r l \<and> is_nonterm (B r) l)"
  by (simp add: is_nonterm_def has_result_def split: option.splits)

lemma bind_is_error[NER_simps]:
  "is_error (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i \<longleftrightarrow> is_error A i \<or> (\<exists>r l. has_result A i r l \<and> is_error (B r) l)"
  by (clarsimp simp add: is_error_def has_result_def split: option.splits)

lemma bind_has_result[NER_simps]:
  "has_result (\<lambda> i. case A i of None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some (r,l)) \<Rightarrow> B r l) i r l \<longleftrightarrow> (\<exists>r' l'. has_result A i r' l' \<and> has_result (B r') l' r l)"
  by (clarsimp simp add: has_result_def split: option.splits)



section \<open>Types for the printer\<close>
type_synonym '\<alpha> printer = "'\<alpha> \<Rightarrow> string option"

section \<open>FP NER\<close>
definition p_has_result :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> string \<Rightarrow> bool" where
  "p_has_result fp v s \<longleftrightarrow> fp v = Some s"

definition p_is_error :: "'\<alpha> printer \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "p_is_error fp v \<longleftrightarrow> fp v = None"

named_theorems fp_NER

lemma p_has_result_impl_not_error:
  "p_has_result fp v s \<Longrightarrow> \<not>p_is_error fp v"
  unfolding p_has_result_def p_is_error_def
  by simp

lemma p_is_error_impl_not_result:
  "p_is_error fp v \<Longrightarrow> \<nexists> s. p_has_result fp v s"
  unfolding p_is_error_def p_has_result_def
  by simp

lemma p_has_result_eq_not_is_error:
  "(\<exists> s. p_has_result fp v s) \<longleftrightarrow> \<not>p_is_error fp v"
  unfolding p_is_error_def p_has_result_def
  by simp



section \<open>Bidefinition types\<close>

type_synonym '\<alpha> bidef = "('\<alpha> parser \<times> '\<alpha> printer)"

abbreviation parse :: "'\<alpha> bidef \<Rightarrow> '\<alpha> parser" where "parse \<equiv> fst"
abbreviation print :: "'\<alpha> bidef \<Rightarrow> '\<alpha> printer" where "print \<equiv> snd"



section \<open>Well formed\<close>

definition parser_can_parse_print_result :: "'\<alpha> parser \<Rightarrow> '\<alpha> printer \<Rightarrow> bool" where
  "parser_can_parse_print_result par pri \<longleftrightarrow>
      (\<forall>(t :: '\<alpha>) pr. p_has_result pri t pr \<longrightarrow> has_result par pr t [])"

\<comment> \<open>note how due to the parse '015' = 15 print 15 = '15' issue we cannot attach the text here.\<close>
definition printer_can_print_parse_result :: "'\<alpha> parser \<Rightarrow> '\<alpha> printer \<Rightarrow> bool" where
  "printer_can_print_parse_result par pri \<longleftrightarrow>
      (\<forall>(t :: '\<alpha>) i l. has_result par i t l \<longrightarrow> (\<exists>pr. p_has_result pri t pr))"


definition bidef_well_formed :: "'\<alpha> bidef \<Rightarrow> bool" where
  "bidef_well_formed bi = (parser_can_parse_print_result (parse bi) (print bi) \<and>
                           printer_can_print_parse_result (parse bi) (print bi))"
named_theorems bi_well_formed_simps

lemma conjI3:
  "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> A \<and> B \<and> C"
  by blast

method wf_init = ((simp only: bidef_well_formed_def); (rule conjI))

lemma print_results_always_same:
  assumes "p_has_result printer ojb res1"
  assumes "p_has_result printer ojb res2"
  shows "res1 = res2"
  using assms
  by (simp add: p_has_result_def)


lemma print_result_is_canon_result:
  assumes "bidef_well_formed (parser, printer)"
  assumes "p_has_result printer obj canon"
  shows "has_result parser canon obj []"
  using assms
  by (simp add: bidef_well_formed_def parser_can_parse_print_result_def)

lemma print_result_is_canon_result2:
  assumes "bidef_well_formed (parser, printer)"
  assumes "p_has_result printer obj canon"
  assumes "has_result parser canon obj2 []"
  shows "obj = obj2"
  using assms
  unfolding bidef_well_formed_def parser_can_parse_print_result_def
  by (simp add: p_has_result_def has_result_def)



\<comment> \<open>PASI, Parser Always Shrinks Input (Including it being a tail of the input)\<close>
definition PASI :: "'\<alpha> parser \<Rightarrow> bool" where
  "PASI p \<longleftrightarrow> (\<forall> i r l. has_result p i r l \<longrightarrow> (\<exists> c. (i = c @ l \<and> c \<noteq> [])))"

\<comment> \<open>PNGI, Parser Never Grows Input (Including it being a tail of the input)\<close>
definition PNGI :: "'\<alpha> parser \<Rightarrow> bool" where
  "PNGI p \<longleftrightarrow> (\<forall> i r l. has_result p i r l \<longrightarrow> (\<exists> c. i = c @ l))"


lemma PASI_as_has_result:
  assumes "PASI p"
  shows "has_result p i r l \<longrightarrow> length i > length l"
  using assms PASI_def
  by fastforce

lemma PNGI_as_has_result:
  assumes "PNGI p"
  shows "has_result p i r l \<longrightarrow> length i \<ge> length l"
  using assms PNGI_def
  by fastforce


lemma PASI_implies_PNGI:
  "PASI p \<longrightarrow> PNGI p"
  using PASI_def PNGI_def
  by fast

lemma PASI_implies_res_length_shorter:
  assumes "PASI p"
  shows "has_result p i r l \<longrightarrow> length i > length l"
  using PASI_def assms
  by fastforce

lemma PASI_implies_no_result_from_empty:
  assumes "PASI p"
  shows "\<not>has_result p [] r l"
  using PASI_def assms
  by fast

lemma if_PNGI:
  assumes "PNGI (parse T)"
  assumes "PNGI (parse F)"
  shows "PNGI (parse (if P then T else F))"
  by (simp add: assms)

lemma if_PNGI_p:
  assumes "PNGI (parse (T p))"
  assumes "PNGI (parse (F p))"
  shows "PNGI (parse (if P p then T p else F p))"
  using assms
  by (rule if_PNGI)

lemma if_PASI:
  assumes "PASI (parse T)"
  assumes "PASI (parse F)"
  shows "PASI (parse (if P then T else F))"
  by (simp add: assms)

lemma if_PASI_p:
  assumes "PASI (parse (T p))"
  assumes "PASI (parse (F p))"
  shows "PASI (parse (if P p then T p else F p))"
  using assms
  by (rule if_PASI)


end