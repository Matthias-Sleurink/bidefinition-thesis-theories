theory basic_fallible_transform
  imports types
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


fun ftransform_pr :: "('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> printer \<Rightarrow> '\<beta> printer" where
  "ftransform_pr t p i = (
    case t i of
      None \<Rightarrow> Some None
    | Some (ti) \<Rightarrow> p ti)"


definition ftransform :: "('\<alpha> \<Rightarrow> '\<beta> option) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> bidef \<Rightarrow> '\<beta> bidef" where
  "ftransform t t' bd = bdc (ftransform_p t (parse bd)) (ftransform_pr t' (print bd))"


\<comment> \<open>NER\<close>
lemma ftransform_is_nonterm[NER_simps]:
  "is_nonterm (parse (ftransform t t' bi)) i \<longleftrightarrow> is_nonterm (parse bi) i"
  "is_nonterm (ftransform_p t p) i \<longleftrightarrow> is_nonterm p i"
  by (simp add: ftransform_def is_nonterm_def split: option.splits)+

lemma ftransform_is_error[NER_simps]:
  "is_error (parse (ftransform t t' bi)) i \<longleftrightarrow> is_error (parse bi) i \<or> (\<exists> r l. has_result (parse bi) i r l \<and> t r = None)"
  "is_error (ftransform_p t p) i \<longleftrightarrow> is_error p i \<or> (\<exists> r l. has_result p i r l \<and> t r = None)"
  by (simp add: ftransform_def is_error_def has_result_def split: option.splits)+

lemma ftransform_has_result[NER_simps]:
  "has_result (parse (ftransform t t' bi)) i r l \<longleftrightarrow> (\<exists> r'. has_result (parse bi) i r' l \<and> t r' = Some r)"
  "has_result (ftransform_p t p) i r l \<longleftrightarrow> (\<exists> r'. has_result p i r' l \<and> t r' = Some r)"
  by (auto simp add: ftransform_def has_result_def split: option.splits)



\<comment> \<open>FP NER\<close>
lemma ftransform_p_is_error[fp_NER]:
  "p_is_error (print (ftransform t t' bi)) i \<longleftrightarrow> t' i = None \<or> (\<exists> i'. Some i' = t' i \<and> p_is_error (print bi) i')"
  "p_is_error (ftransform_pr t' p) i \<longleftrightarrow> t' i = None \<or> (\<exists> i'. Some i' = t' i \<and> p_is_error p i')"
  apply (auto simp add: ftransform_def p_is_error_def)
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  done

lemma f_transform_p_has_result[fp_NER]:
  "p_has_result (print (ftransform t t' bi)) i r \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_has_result (print bi) i' r)"
  "p_has_result (ftransform_pr t' p) i r \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_has_result p i' r)"
  apply (auto simp add: ftransform_def p_has_result_def)
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  done


\<comment> \<open>Monotone\<close>
declare [[show_types=false]]
lemma mono_ftransform[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. ftransform f_trans f_trans' (A f))"
  using assms
  unfolding ftransform_def monotone_def bd_ord_def flat_ord_def fun_ord_def
  apply (auto split: option.splits)
  subgoal by (smt (verit, ccfv_threshold) option.distinct(1))
  subgoal by (smt (verit, ccfv_threshold) option.sel option.simps(3))
  subgoal by (smt (verit, ccfv_threshold) option.discI)
  subgoal by (smt (verit, ccfv_threshold) option.distinct(1) option.inject prod.inject)
  subgoal by (smt (verit, del_insts) option.distinct(1))
  subgoal by (smt (verit, ccfv_threshold) option.discI option.inject)
  subgoal by (smt (verit, ccfv_threshold) fst_conv option.distinct(1) option.sel)
  subgoal by (smt (verit, ccfv_threshold) option.distinct(1) option.inject prod.inject)
  subgoal by (smt (verit, del_insts) option.distinct(1) option.inject prod.inject)
  done


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