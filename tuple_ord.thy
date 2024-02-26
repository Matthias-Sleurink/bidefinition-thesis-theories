theory tuple_ord
  imports Main
          HOL.Partial_Function
begin

\<comment> \<open>An attempt to create an ordering for bidefs that compares both.\<close>


\<comment> \<open>From ordering 'ord', make an ordering for two tuples\<close>
definition "tuple_ord ord p1 p2 = (ord (fst p1) (fst p2) \<and> ord (snd p1) (snd p2))"


\<comment> \<open>From a LUB, create a lub for tuples\<close>
\<comment> \<open>QUESTION: Verify that image (`) is over sets as map is over lists\<close>
definition tuple_lub :: "('a set \<Rightarrow> 'a) \<Rightarrow> (('a \<times> 'a) set) \<Rightarrow> ('a\<times>'a)" where
  "tuple_lub lub s = (lub (fst ` s), lub (snd ` s))"
\<comment> \<open>Sadly, parsers and printers have a different exact type.
    But in a perfect world this may work.\<close>


\<comment> \<open>Unnamed in partial function sources\<close>
abbreviation "option_lub \<equiv> flat_lub None"

abbreviation "parser_ord \<equiv> fun_ord option_ord"
abbreviation "parser_lub \<equiv> fun_lub option_lub"

definition "tuple_bidef_ord = tuple_ord parser_ord"
definition "tuple_bidef_lub = tuple_lub parser_lub"


lemma partial_function_definitions_tuple_lift:
  assumes "partial_function_definitions ord lub"
  shows "partial_function_definitions (tuple_ord ord) (tuple_lub lub)"  (is "partial_function_definitions ?ordf ?lubf")
  proof -
    interpret partial_function_definitions ord lub by fact
    show ?thesis
    proof
      fix x show "?ordf x x"
        unfolding tuple_ord_def by (simp add: leq_refl)
    next
      fix x y z assume "?ordf x y" "?ordf y z"
      thus "?ordf x z" unfolding tuple_ord_def 
        by (force dest: leq_trans)
    next
      fix x y assume "?ordf x y" "?ordf y x"
      thus "x = y" unfolding tuple_ord_def
        by (simp add: leq_antisym prod.expand)
    next
      fix A x assume x: "x \<in> A" and A: "Complete_Partial_Order.chain ?ordf A"
      thus "?ordf x (?lubf A)"
        unfolding tuple_ord_def tuple_lub_def
        by (simp add: chain_imageI partial_function_definitions.lub_upper partial_function_definitions_axioms)
    next
      fix A :: "('a \<times> 'a) set" and g :: "'a \<times> 'a"
      assume A: "Complete_Partial_Order.chain ?ordf A"
      assume g: "\<And>f. f \<in> A \<Longrightarrow> ?ordf f g"
      show "?ordf (?lubf A) g" unfolding tuple_ord_def tuple_lub_def
        by (smt (verit, best) A chain_imageI fst_conv g imageE lub_least snd_conv tuple_ord_def)
    qed
  qed
      
    
    oops \<comment> \<open>DANGEROUS! COUNTEREXAMPLE FOUND!\<close>

\<comment> \<open>Main proof for the interpretation below\<close>
lemma bidef_tuple_pfd: "partial_function_definitions tuple_bidef_ord tuple_bidef_lub"
  unfolding tuple_bidef_ord_def tuple_bidef_lub_def
  apply (rule partial_function_definitions_tuple_lift)
  apply (rule partial_function_lift)
  apply (rule flat_interpretation)
  done


interpretation tuple_bidef:
  partial_function_definitions "tuple_bidef_ord" "tuple_bidef_lub"
  rewrites "flat_lub None {} \<equiv> None"
 \<comment> \<open>What does this line do? It kinda looks like it appears in the proof goal, but what does it do?\<close>
  by (rule bidef_tuple_pfd)(simp add: flat_lub_def)



declaration \<open>Partial_Function.init "tuple_bidef" \<^term>\<open>tuple_bidef.fixp_fun\<close>
  \<^term>\<open>tuple_bidef.mono_body\<close> @{thm tuple_bidef.fixp_rule_uc} @{thm tuple_bidef.fixp_induct_uc}
  (SOME @{thm fixp_induct_option})\<close> \<comment> \<open>Not sure if the fixp_induct_option rule here is good?\<close>



type_synonym '\<alpha> parse_result = "('\<alpha> \<times> string)"

\<comment> \<open>The inner option defines parsing success\<close>
type_synonym '\<alpha> parser = "string \<Rightarrow> '\<alpha> parse_result option"

section \<open>Types for the printer\<close>
type_synonym '\<alpha> printer = "'\<alpha> \<Rightarrow> string option"


type_synonym '\<alpha> bidef = "('\<alpha> parser \<times> '\<alpha> printer)"

\<comment> \<open>partial function fails when there are no arguments\<close>
partial_function (tuple_bidef) test :: "'a bidef" where [code]:
  "test = ((\<lambda>x. None), (\<lambda>x. None))"

\<comment> \<open>Sadly, adding a dummy argument does not work since that is not in our partial_function setup\<close>
partial_function (tuple_bidef) test :: "'dummy \<Rightarrow> 'a bidef" where [code]:
  "test _ = ((\<lambda>x. None), (\<lambda>x. None))"


end