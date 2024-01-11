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

(*
 lemma then_else_mono[partial_function_mono]:
    assumes ma: "mono_ssn A" and mb: "\<And>y. mono_ssn (\<lambda>f. B y f)" and mc: "\<And>e. mono_ssn (\<lambda>f. C e f)"
    shows "mono_ssn (\<lambda>f. then_else (A f) (\<lambda>y. B y f) (\<lambda>e. C e f))"
    supply [[show_abbrevs=false]]
    apply (rule monotoneI)
    using assms
    (* TODO: conceptually, we would prove mono etc also for the underlying monads' combinators*)
    apply (auto simp: fun_ord_def ssn_ord_def img_ord_def flat_ord_def then_else_def then_else_so_def then_else_sum_def)
    apply (auto split: option.splits Option.bind_splits sum.splits simp: fun_ord_def monotone_def)
    subgoal by (metis opt ion.distinct(1))
    subgoal by (metis option.discI)
    subgoal by (metis fst_conv option.distinct(1) option.sel snd_conv sum.inject(1))
    subgoal by (metis option.discI option.inject sum.simps(4))
    subgoal by (metis option.discI option.inject sum.simps(4))
    subgoal by (metis Pair_inject option.distinct(1) option.inject sum.inject(2))
    done
*)
(*monotonicity:*)
(*
lemma bind_parser_mono[partial_function_mono]:
    assumes mf: "mono_parser B" and mg: "\<And>y. mono_parser (\<lambda>f. C y f)"
    shows "mono_parser (\<lambda>f. p_bind (B f) (\<lambda>y. C y f))"
  using assms
  unfolding p_bind_def
  apply -
  apply (rule monotoneI)
  unfolding parser_ord_def fun_ord_def flat_ord_def terminate_with_def monotone_def
  apply (auto simp add:  split: option.splits)
      apply (metis not_None_eq)
     apply (metis option.distinct(1) option.inject)
    apply (metis option.discI)
  apply (metis not_None_eq option.inject)
  by (metis (no_types, lifting) option.distinct(1) option.sel prod.inject)
*)
(*
lemma try_except_mono[partial_function_mono]:
    assumes mf: "mono_parser B" and mg: "mono_parser (\<lambda>f. C f)"
    shows "mono_parser (\<lambda>f. try_except (B f) (C f))"
     using assms
  unfolding try_except_def
  apply -
  apply (rule monotoneI)
  unfolding parser_ord_def fun_ord_def flat_ord_def terminate_with_def monotone_def
  apply (auto simp add: split!: option.splits)
                   apply (metis not_None_eq option.inject option.distinct(1) prod.inject)+
  done (*17 subgoals all use subsets of the four lemmas inserted above.*)
*)

method_setup pf_mono_prover = \<open>Scan.succeed (SIMPLE_METHOD' o Subgoal.FOCUS_PREMS (fn {context=ctxt,...} => CHANGED (ALLGOALS (Partial_Function.mono_tac ctxt))))\<close>


end