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

lemma ftransform_has_result_c[NER_simps]:
  "has_result_c (parse (ftransform t t' bi)) c r l \<longleftrightarrow> (\<exists> r'. has_result_c (parse bi) c r' l \<and> t r' = Some r)"
  "has_result_c (ftransform_p t p)           c r l \<longleftrightarrow> (\<exists> r'. has_result_c p c r' l \<and> t r' = Some r)"
  by (auto simp add: ftransform_def has_result_c_def NER_simps split: option.splits)

lemma ftransform_has_result_ci[NER_simps]:
  "has_result_ci (parse (ftransform t t' bi)) i c r l \<longleftrightarrow> (\<exists> r'. has_result_ci (parse bi) i c r' l \<and> t r' = Some r)"
  "has_result_ci (ftransform_p t p)           i c r l \<longleftrightarrow> (\<exists> r'. has_result_ci p          i c r' l \<and> t r' = Some r)"
  by (auto simp add: ftransform_def has_result_ci_def NER_simps split: option.splits)



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

lemma ftransform_p_has_result[fp_NER]:
  "p_has_result (print (ftransform t t' bi)) i r \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_has_result (print bi) i' r)"
  "p_has_result (ftransform_pr t' p) i r \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_has_result p i' r)"
  apply (auto simp add: ftransform_def p_has_result_def)
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  done

lemma ftransform_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (ftransform t t' bi)) i \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_is_nonterm (print bi) i')"
  "p_is_nonterm (ftransform_pr t' p) i \<longleftrightarrow> (\<exists> i'. Some i' = t' i \<and> p_is_nonterm p i')"
  apply (auto simp add: ftransform_def p_is_nonterm_def)
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  subgoal by (cases \<open>t' i\<close>) simp_all
  done

lemma ftransform_print_empty[print_empty, fp_NER]:
  "p_has_result (print (ftransform t t' bi)) i [] \<longleftrightarrow> (\<exists>i'. Some i' = t' i \<and> p_has_result (print bi) i' [])"
  by (rule ftransform_p_has_result(1))



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
lemma ftransform_PASI[PASI_PNGI]:
  assumes "PASI (parse bi)"
  shows "PASI (parse (ftransform t t' bi))"
  using assms
  by (auto simp add: PASI_def NER_simps fp_NER)

lemma ftransform_PNGI[PASI_PNGI]:
  assumes "PNGI (parse bi)"
  shows "PNGI (parse (ftransform t t' bi))"
  using assms
  by (auto simp add: PNGI_def NER_simps fp_NER)



\<comment> \<open>Charset\<close>
lemma charset_ftransform:
  "charset (parse (ftransform f f' b)) = \<Union> {set c | i r l c. has_result (parse b) i r l \<and> i = c@l \<and> f r \<noteq> None}"
  unfolding charset_def ftransform_def ftransform_p.simps has_result_def
  apply (auto split: option.splits)
  subgoal by (metis option.exhaust)
  by fastforce

lemma charset_ftransform_subset:
  "charset (parse (ftransform f f' b)) \<subseteq> charset (parse b)"
  unfolding charset_def ftransform_def ftransform_p.simps has_result_def
  apply (auto split: option.splits)
  by (metis not_Some_eq)

lemma first_chars_ftransform:
  "first_chars (print (ftransform f f' b)) = {hd pr | i' pr. (f' i') \<noteq> None \<and> p_has_result (print b) (the (f' i')) pr \<and> pr \<noteq> []}"
  unfolding first_chars_def ftransform_def ftransform_p.simps p_has_result_def
  apply (auto split: option.splits)
  by force

lemma first_chars_ftransform_subset:
  "first_chars (print (ftransform f f' b)) \<subseteq> first_chars (print b)"
  unfolding first_chars_def ftransform_def ftransform_p.simps p_has_result_def
  by (auto split: option.splits)



\<comment> \<open>Does not peek past end\<close>
lemma ftrans_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  shows "does_not_peek_past_end (parse (ftransform f f' A))"
  using assms ftransform_has_result
  unfolding does_not_peek_past_end_def
  by meson


\<comment> \<open>Does not consume past char.\<close>
lemma ftrans_does_not_consume_past_char:
  assumes "does_not_consume_past_char (parse a) ch"
  shows "does_not_consume_past_char (parse (ftransform f f' a)) ch"
  using assms
  unfolding does_not_consume_past_char_def
  by (auto simp add: ftransform_has_result)

lemma ftrans_does_not_consume_past_char2:
  assumes "does_not_consume_past_char2 (parse a) ch"
  shows "does_not_consume_past_char2 (parse (ftransform f f' a)) ch"
  using assms
  unfolding does_not_consume_past_char2_def
  by (auto simp add: ftransform_has_result)

lemma ftransform_does_not_consume_past_char3:
  assumes "does_not_consume_past_char3 (parse a) ch"
  shows "does_not_consume_past_char3 (parse (ftransform f f' a)) ch"
  using assms unfolding does_not_consume_past_char3_def
  by (auto simp add: ftransform_has_result)



\<comment> \<open>First printed char\<close>
lemma ftransform_fpci:
  assumes "first_printed_chari (print A) (the (f' i)) c"
  assumes "\<exists>i'. f' i = Some i'"
  shows "first_printed_chari (print (ftransform f f' A)) i c"
  using assms unfolding first_printed_chari_def
  by (auto simp add: ftransform_p_has_result)

lemma ftransform_fpci2[fpci_simps]:
  shows "first_printed_chari (print (ftransform f f' A)) i c \<longleftrightarrow>
            first_printed_chari (print A) (the (f' i)) c \<and>
            (\<exists>i'. f' i = Some i')"
  unfolding first_printed_chari_def
  apply (auto simp add: ftransform_p_has_result)
  subgoal by (cases \<open>f' i\<close>; auto)
  subgoal by (cases \<open>f' i\<close>; auto)
  done

lemma ftransform_fpc[fpc_simps]:
  shows "fpc (parse (ftransform f f' A)) i c \<longleftrightarrow> (\<exists>i'. fpc (parse A) i' c \<and> f i' = Some i)"
  unfolding fpc_def ftransform_has_result
  by blast



\<comment> \<open>Well Formed\<close>
\<comment> \<open>This is for sure not great, as this is basically the wf requirements but not worded in terms of wf.
    So the user cannot use any existing combinators for it. How do we solve this?\<close>
definition ftrans_wf_funcs_parser_can_parse :: "('\<alpha> \<Rightarrow> '\<beta> option) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "ftrans_wf_funcs_parser_can_parse f f' b \<longleftrightarrow>
    (\<forall> pr t. (\<exists>t'. Some t' = f' t \<and> p_has_result (print b) t' pr) \<longrightarrow> (\<exists>l r'. has_result (parse b) pr r' l \<and> Some t = f r'))"

definition ftrans_wf_funcs_printer_can_print :: "('\<alpha> \<Rightarrow> '\<beta> option) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "ftrans_wf_funcs_printer_can_print f f' b \<longleftrightarrow>
    (\<forall> i r l. (\<exists>r'. has_result (parse b) i r' l \<and> f r' = Some r) \<longrightarrow> (\<exists>r' t. f' r = Some r' \<and> p_has_result (print b) r' t))"

lemma ftransform_well_formed:
  assumes "ftrans_wf_funcs_parser_can_parse f f' b"
  assumes "ftrans_wf_funcs_printer_can_print f f' b"
  assumes b_wf: "bidef_well_formed b"
  shows "bidef_well_formed (ftransform f f' b)"
  apply wf_init
  subgoal by (rule b_wf[THEN get_pngi, THEN ftransform_PNGI])
  subgoal
    using b_wf[THEN get_parser_can_parse]
          assms(1)[unfolded ftrans_wf_funcs_parser_can_parse_def]
    apply (auto simp add: parser_can_parse_print_result_def fp_NER NER_simps)
    unfolding has_result_def by fastforce \<comment> \<open>Why does unfolding has_result here help?\<close>
  subgoal
    using b_wf[THEN get_printer_can_print]
          assms(2)[unfolded ftrans_wf_funcs_printer_can_print_def]
    apply (auto simp add: printer_can_print_parse_result_def fp_NER NER_simps)
    unfolding has_result_def by fastforce
    \<comment> \<open>Again, fastforce is consistently slower when has_result is unfolded.\<close>
  done

definition well_formed_ftransform_funcs :: "('\<alpha> \<Rightarrow> '\<beta> option) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha> option) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "well_formed_ftransform_funcs f f' b \<longleftrightarrow> (
        (\<forall> i v l v'. has_result (parse b) i v l \<and> Some v' = f v \<longrightarrow> f' v' = Some v)
      \<and> (\<forall> pr t. p_has_result (print (ftransform f f' b)) t pr \<longrightarrow> (\<exists>t'. f' t = Some t' \<and> f t' = Some t)))"

lemma ftransform_well_formed2:
  assumes funcs: "well_formed_ftransform_funcs f f' b"
  assumes wf: "bidef_well_formed b"
  shows "bidef_well_formed (ftransform f f' b)"
  apply wf_init
  subgoal using wf[THEN get_pngi] ftransform_PNGI by blast
  subgoal
    using wf[THEN get_parser_can_parse] funcs[unfolded well_formed_ftransform_funcs_def]
    apply (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
    by fastforce
  subgoal
    using wf[THEN get_printer_can_print] funcs[unfolded well_formed_ftransform_funcs_def]
    apply (simp add: printer_can_print_parse_result_def fp_NER NER_simps)
    by fastforce
  done


end
