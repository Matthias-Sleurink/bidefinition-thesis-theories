theory basic_transform
  imports types
          basic_partial_fun_for_parser
begin

text \<open>
Transform is the first basic definition.
It transforms the result of a parser.
The transformer has no access to the parser state.
\<close>


fun transform_p :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> '\<alpha> parser \<Rightarrow> '\<beta> parser" where
  "transform_p t p i = (
    case p i of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some (r,l)) \<Rightarrow> Some (Some (t r, l))
)"

lemma mono_transform[partial_function_mono]:
  assumes ma: "mono_parser A"
    shows "mono_parser (\<lambda>f. transform_p f' (A f))"
  using assms
  unfolding transform_p.simps
  apply -
  apply (rule monotoneI)
  unfolding parser_ord_def fun_ord_def flat_ord_def terminate_with_def monotone_def
  apply (auto split: option.splits)
  apply (metis option.distinct(1)                          )
  apply (metis option.distinct(1) option.inject            )
  apply (metis option.distinct(1)                          )
  apply (metis option.distinct(1) option.inject            )
  apply (metis option.distinct(1) option.inject prod.inject)
  apply (metis option.distinct(1) option.inject prod.inject)
  done

fun transform_pr :: "('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> printer \<Rightarrow> '\<beta> printer" where
  "transform_pr t p i = p (t i)"


definition transform :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> bidef \<Rightarrow> '\<beta> bidef" where
  "transform t t' bi = (
    transform_p t (parse bi),
    transform_pr t' (print bi)
)"



lemma transform_is_nonterm[NER_simps]:
  "is_nonterm (parse (transform f f' p)) i \<longleftrightarrow> is_nonterm (parse p) i"
  "is_nonterm (transform_p f p') i \<longleftrightarrow> is_nonterm p' i"
  by (simp add: transform_def is_nonterm_def split: option.splits)+

lemma transform_is_error[NER_simps]:
  "is_error (parse (transform f f' p)) i \<longleftrightarrow> is_error (parse p) i"
  "is_error (transform_p f p') i \<longleftrightarrow> is_error p' i"
  by (simp add: transform_def is_error_def split: option.splits)+

lemma transform_has_result[NER_simps]:
  "has_result (parse (transform f f' p)) i r l \<longleftrightarrow> (\<exists>r'. has_result (parse p) i r' l \<and> r = f r')"
  "has_result (transform_p f p') i r l \<longleftrightarrow> (\<exists>r'. has_result p' i r' l \<and> r = f r')"
  apply (simp_all add: transform_def has_result_def split: option.splits)
  by auto



lemma transform_p_has_result[fp_NER]:
  "p_has_result (print (transform f f' b)) i t \<longleftrightarrow> p_has_result (print b) (f' i) t"
  "p_has_result (transform_pr f' p) i t \<longleftrightarrow> p_has_result p (f' i) t"
  by (simp_all add: transform_def p_has_result_def)

lemma transform_p_is_error[fp_NER]:
  "p_is_error (print (transform f f' b)) i \<longleftrightarrow> p_is_error (print b) (f' i)"
  "p_is_error (transform_pr f' p) i \<longleftrightarrow> p_is_error p (f' i)"
  by (simp_all add: transform_def p_is_error_def)



\<comment> \<open>PNGI, PASI\<close>
lemma transform_PASI:
  shows "PASI (parse b) \<longleftrightarrow> PASI (parse (transform f f' b))"
  apply (simp add: PASI_def NER_simps)
  by blast

lemma transform_PNGI:
  shows "PNGI (parse b) \<longleftrightarrow> PNGI (parse (transform f f' b))"
  apply (simp add: PNGI_def NER_simps)
  by blast



\<comment> \<open>I believe that the f \<circ> f' = id requirement can be relaxed.\<close>
definition well_formed_transform_funcs :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "well_formed_transform_funcs f f' b \<longleftrightarrow> ((\<forall> i v l. has_result (parse b) i v l \<longrightarrow> f' (f v) = v)
                                            \<and> f \<circ> f' = id )"

lemma transform_well_formed:
  assumes "bidef_well_formed b"
  assumes "well_formed_transform_funcs f f' b"
  shows "bidef_well_formed (transform f f' b)"
  apply wf_init
  subgoal
    using assms[unfolded bidef_well_formed_def
                         well_formed_transform_funcs_def]
    apply (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
    by (metis comp_eq_dest_lhs id_apply)
  subgoal
    using assms[unfolded bidef_well_formed_def
                         well_formed_transform_funcs_def]
    apply (simp add: printer_can_print_parse_result_def fp_NER NER_simps)
    by metis
  done

lemma id_is_well_formed_transform_func[simp]:
  "well_formed_transform_funcs id id b"
  unfolding well_formed_transform_funcs_def
  by simp

\<comment> \<open>A first attempt at shrinking the requirements on the functions, still not wf = funcs2 though.\<close>
definition well_formed_transform_funcs2 :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "well_formed_transform_funcs2 f f' b \<longleftrightarrow> (
        (\<forall> i v l. has_result (parse b) i v l \<longrightarrow> f' (f v) = v)
      \<and> (\<forall> pr t. p_has_result (print b) (f' t) pr \<longrightarrow> (\<exists>l r'. has_result (parse b) pr r' l \<and> t = f r')))"

lemma transform_well_formed2:
  assumes "bidef_well_formed b"
  assumes "well_formed_transform_funcs2 f f' b"
  shows "bidef_well_formed (transform f f' b)"
  apply wf_init
  subgoal
    using assms[unfolded bidef_well_formed_def
                         well_formed_transform_funcs2_def]
    apply (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
    by metis
  subgoal
    using assms[unfolded bidef_well_formed_def
                         well_formed_transform_funcs2_def]
    apply (simp add: printer_can_print_parse_result_def fp_NER NER_simps)
    by metis
  done

lemma id_is_well_formed_transform_func2[simp]:
  assumes "bidef_well_formed b"
  shows "well_formed_transform_funcs2 id id b"
  unfolding well_formed_transform_funcs2_def
  using assms[unfolded bidef_well_formed_def parser_can_parse_print_result_def]
  by auto



end