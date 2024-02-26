theory fst_ord
  imports Main
          HOL.Partial_Function
begin

\<comment> \<open>An attempt to create an ordering for bidefs that just ignore the printer.\<close>


\<comment> \<open>From ordering 'ord', make an ordering for two tuples (that ignores the rhs)\<close>
definition "fst_ord ord p1 p2 = ord (fst p1) (fst p2)"


\<comment> \<open>From a LUB, create a lub for tuples (that ignores the rhs)\<close>
\<comment> \<open>QUESTION: Verify that image (`) is over sets as map is over lists\<close>
definition fst_lub :: "('a set \<Rightarrow> 'a) \<Rightarrow> (('a \<times> 'b) set) \<Rightarrow> ('a\<times>'b)" where
  "fst_lub lub s = (lub (fst ` s), undefined)"
\<comment> \<open>This undefined is super not ideal I believe.
    Since we only apply this for bidefs,
     could we not replace this with some (\<lambda>x. None),
     that at least looks like some minimal printer?\<close>


\<comment> \<open>Unnamed in partial function sources\<close>
abbreviation "option_lub \<equiv> flat_lub None"

abbreviation "parser_ord \<equiv> fun_ord option_ord"
abbreviation "parser_lub \<equiv> fun_lub option_lub"

definition "lhs_bidef_ord = fst_ord parser_ord"
definition "lhs_bidef_lub = fst_lub parser_lub"


lemma partial_function_definitions_lhs_lift:
  assumes "partial_function_definitions ord lub"
  shows "partial_function_definitions (fst_ord ord) (fst_lub lub)"  (is "partial_function_definitions ?ordf ?lubf")
  proof -
    interpret partial_function_definitions ord lub by fact
    show ?thesis
    proof
      fix x show "?ordf x x"
        unfolding fst_ord_def by (simp add: leq_refl)
    next
      fix x y z assume "?ordf x y" "?ordf y z"
      thus "?ordf x z" unfolding fst_ord_def 
        by (force dest: leq_trans)
    next \<comment> \<open>Part of the counterexample is here. We are only comparing LHS, but then showing LHS,RHS = LHS,RHS\<close>
      fix x y assume "?ordf x y" "?ordf y x"
      thus "x = y" unfolding fst_ord_def
        sorry
    next
    
    oops \<comment> \<open>DANGEROUS! COUNTEREXAMPLE FOUND!\<close>

\<comment> \<open>Main proof for the interpretation below\<close>
lemma bidef_pfd: "partial_function_definitions lhs_bidef_ord lhs_bidef_lub"
  unfolding lhs_bidef_ord_def lhs_bidef_lub_def
  apply (rule partial_function_definitions_lhs_lift)
  apply (rule partial_function_lift)
  apply (rule flat_interpretation)
  oops

interpretation bidef:
  partial_function_definitions "lhs_bidef_ord" "lhs_bidef_lub"
  rewrites "flat_lub None {} \<equiv> None"
 \<comment> \<open>What does this line do? It kinda looks like it appears in the proof goal, but what does it do?\<close>
by (rule bidef_pfd)(simp add: flat_lub_def)



declaration \<open>Partial_Function.init "bidef" \<^term>\<open>option.fixp_fun\<close>
  \<^term>\<open>option.mono_body\<close> @{thm option.fixp_rule_uc} @{thm option.fixp_induct_uc}
  (SOME @{thm fixp_induct_option})\<close>



end