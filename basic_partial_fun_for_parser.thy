theory basic_partial_fun_for_parser
  imports types
  HOL.Partial_Function
begin

abbreviation "option_lub \<equiv> flat_lub None"

definition "parser_ord = fun_ord option_ord"
definition "parser_lub = fun_lub option_lub"

abbreviation "mono_parser \<equiv> monotone (fun_ord parser_ord) parser_ord"

lemma parser_pfd: "partial_function_definitions parser_ord (parser_lub)"
  unfolding parser_ord_def parser_lub_def
    apply (rule partial_function_lift)
    by (rule flat_interpretation)

lemma parser_lub_empty: "parser_lub {} = (\<lambda> _. None)"
  unfolding parser_lub_def img_lub_def flat_lub_def fun_lub_def
  by (auto simp: fun_eq_iff)


interpretation parser:
partial_function_definitions "parser_ord" "parser_lub"
rewrites "flat_lub None {} \<equiv> None"
  apply (rule parser_pfd)
  by(simp add: flat_lub_def)

declaration \<open>Partial_Function.init "parser" \<^term>\<open>parser.fixp_fun\<close>
  \<^term>\<open>parser.mono_body\<close> @{thm parser.fixp_rule_uc} @{thm parser.fixp_induct_uc}
  (NONE)\<close>

(*monotonicity:*)
(* bind parser mono but with bind inlined for places where the syntax rules are not used *)
lemma bind_parser_mono[partial_function_mono]:
    assumes mf: "mono_parser B" and mg: "\<And>y. mono_parser (\<lambda>f. C y f)"
    shows "mono_parser
              (\<lambda>f. (\<lambda> a a2b i. case a i of
                                None \<Rightarrow> None
                              | Some None \<Rightarrow> Some None
                              | Some (Some (r, l)) \<Rightarrow> a2b r l
                   ) (B f) (\<lambda>y. C y f))"
  using assms
  apply -
  apply (rule monotoneI)
  unfolding parser_ord_def fun_ord_def flat_ord_def terminate_with_def monotone_def
  apply (auto simp add:  split: option.splits)
      apply (metis not_None_eq)
     apply (metis option.distinct(1) option.inject)
    apply (metis option.discI)
  apply (metis not_None_eq option.inject)
  by (metis (no_types, lifting) option.distinct(1) option.sel prod.inject)


method_setup pf_mono_prover = \<open>Scan.succeed (SIMPLE_METHOD' o Subgoal.FOCUS_PREMS (fn {context=ctxt,...} => CHANGED (ALLGOALS (Partial_Function.mono_tac ctxt))))\<close>


end