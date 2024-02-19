theory basic_fallible_transform
  imports types
          basic_partial_fun_for_parser
begin


text \<open>
Fallible transform is a basic definition.
Transform the result of a parser.
If the transformer fails it is reported as a parse or print error.
The transformer has no access to the parser state.
\<close>


fun ftransform_p :: "('\<alpha> \<Rightarrow> '\<beta> option) \<Rightarrow> '\<alpha> parser \<Rightarrow> '\<beta> parser" where
  "ftransform_p t p i = (
    case p i of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some (r, l)) \<Rightarrow> (
      case t r of
        None \<Rightarrow> Some None
      | Some r' \<Rightarrow> Some (Some (r', l))
))"

lemma mono_ftransform[partial_function_mono]:
  assumes ma: "mono_parser A"
    shows "mono_parser (\<lambda>f. ftransform_p f' (A f))"
  using assms
  unfolding ftransform_p.simps
  apply -
  apply (rule monotoneI)
  unfolding parser_ord_def fun_ord_def flat_ord_def terminate_with_def monotone_def
  apply (auto split: option.splits)
  subgoal by (metis option.distinct(1)                          )
  subgoal by (metis option.distinct(1) option.inject            )
  subgoal by (metis option.distinct(1)                          )
  subgoal by (metis option.distinct(1) option.inject prod.inject)
  subgoal by (metis option.distinct(1)                          )
  subgoal by (metis option.distinct(1) option.inject            )
  subgoal by (metis option.distinct(1) option.sel fst_conv)
  subgoal by (metis option.inject      option.simps(3) prod.inject)
  subgoal by (metis option.distinct(1) option.sel snd_conv)
  done

fun ftransform_pr :: "('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> printer \<Rightarrow> '\<beta> printer" where
  "ftransform_pr t p i = Option.bind (t i) p"


definition ftransform :: "('\<alpha> \<Rightarrow> '\<beta> option) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> bidef \<Rightarrow> '\<beta> bidef" where
  "ftransform t t' bi = (
    ftransform_p t (parse bi),
    ftransform_pr t' (print bi)
)"



\<comment> \<open>NER\<close>
lemma ftransform_is_nonterm[NER_simps]:
  "is_nonterm (parse (ftransform t t' bi)) i \<longleftrightarrow> is_nonterm (parse bi) i"
  by (simp add: ftransform_def is_nonterm_def split: option.splits)

lemma ftransform_is_error[NER_simps]:
  "is_error (parse (ftransform t t' bi)) i \<longleftrightarrow> is_error (parse bi) i \<or> (\<exists> r l. has_result (parse bi) i r l \<and> t r = None)"
  by (simp add: ftransform_def is_error_def has_result_def split: option.splits)

lemma ftransform_has_result[NER_simps]:
  "has_result (parse (ftransform t t' bi)) i r l \<longleftrightarrow> (\<exists> r'. has_result (parse bi) i r' l \<and> t r' = Some r)"
  by (auto simp add: ftransform_def has_result_def split: option.splits)



\<comment> \<open>FP NER\<close>
lemma ftransform_p_is_error[fp_NER]:
  "p_is_error (print (ftransform t t' bi)) i \<longleftrightarrow> t' i = None \<or> (\<exists> i'. Some i' = t' i \<and> p_is_error (print bi) i')"
  apply (simp add: ftransform_def p_is_error_def)
  by (cases \<open>t' i\<close>) simp_all

lemma f_transform_p_has_result[fp_NER]:
  "p_has_result (print (ftransform t t' bi)) i r \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_has_result (print bi) i' r)"
  apply (simp add: ftransform_def p_has_result_def)
  by (cases \<open>t' i\<close>) simp_all



\<comment> \<open>PNGI, PASI\<close>
lemma ftransform_PASI:
  assumes "PASI (parse bi)"
  shows "PASI (parse (ftransform t t' bi))"
  using assms
  by (auto simp add: PASI_def NER_simps fp_NER)

lemma ftransform_PNGI:
  assumes "PNGI (parse bi)"
  shows "PNGI (parse (ftransform t t' bi))"
  using assms
  by (auto simp add: PNGI_def NER_simps fp_NER)



\<comment> \<open>Well Formed\<close>



end