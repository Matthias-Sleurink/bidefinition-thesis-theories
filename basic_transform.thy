theory basic_transform
  imports types
          basic_fallible_transform
begin

text \<open>
Transform is the first basic definition.
It transforms the result of a parser.
The transformer has no access to the parser state.
\<close>

definition transform :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> bidef \<Rightarrow> '\<beta> bidef" where
  "transform t t' bi = ftransform (Some o t) (Some o t') bi"



\<comment> \<open>NER\<close>
lemma transform_is_nonterm[NER_simps]:
  "is_nonterm (parse (transform f f' p)) i \<longleftrightarrow> is_nonterm (parse p) i"
  by (simp add: transform_def NER_simps)

lemma transform_is_error[NER_simps]:
  "is_error (parse (transform f f' p)) i \<longleftrightarrow> is_error (parse p) i"
  by (simp add: transform_def NER_simps)

lemma transform_has_result[NER_simps]:
  "has_result (parse (transform f f' p)) i r l \<longleftrightarrow> (\<exists>r'. has_result (parse p) i r' l \<and> r = f r')"
  by (auto simp add: transform_def NER_simps)

lemma transform_has_result_c[NER_simps]:
  "has_result_c (parse (transform f f' p)) c r l \<longleftrightarrow> (\<exists>r'. has_result_c (parse p) c r' l \<and> r = f r')"
  by (auto simp add: transform_def NER_simps)

lemma transform_has_result_ci[NER_simps]:
  "has_result_ci (parse (transform f f' p)) i c r l \<longleftrightarrow> (\<exists>r'. has_result_ci (parse p) i c r' l \<and> r = f r')"
  by (auto simp add: transform_def NER_simps)



\<comment> \<open>FP ner\<close>
lemma transform_p_has_result[fp_NER]:
  "p_has_result (print (transform f f' b)) i t \<longleftrightarrow> p_has_result (print b) (f' i) t"
  by (simp add: transform_def fp_NER)

lemma transform_p_is_error[fp_NER]:
  "p_is_error (print (transform f f' b)) i \<longleftrightarrow> p_is_error (print b) (f' i)"
  by (simp add: transform_def fp_NER)

lemma transform_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (transform f f' b)) i \<longleftrightarrow> p_is_nonterm (print b) (f' i)"
  by (simp add: transform_def fp_NER)

lemma transform_print_empty[print_empty, fp_NER]:
  "p_has_result (print (transform f f' b)) i [] \<longleftrightarrow> p_has_result (print b) (f' i) []"
  by (rule transform_p_has_result)



\<comment> \<open>Monotone\<close>
declare [[show_types=false]]
lemma mono_transform[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. transform f_trans f_trans' (A f))"
  unfolding transform_def
  apply (rule mono_ftransform)
  by fact



\<comment> \<open>PNGI, PASI\<close>
lemma transform_PASI:
  shows "PASI (parse b) \<longleftrightarrow> PASI (parse (transform f f' b))"
  apply (simp add: PASI_def NER_simps)
  by blast
lemmas transform_PASI_rev[PASI_PNGI] = transform_PASI[symmetric]

lemma transform_PNGI:
  shows "PNGI (parse b) \<longleftrightarrow> PNGI (parse (transform f f' b))"
  apply (simp add: PNGI_def NER_simps)
  by blast

lemmas transform_PNGI_rev[PASI_PNGI] = transform_PNGI[symmetric]



\<comment> \<open>Charset\<close>
lemma charset_transform:
  "charset (parse (transform f f' b)) = charset (parse b)"
  unfolding transform_def
  apply (subst charset_ftransform)
  unfolding charset_def
  by force

lemma first_chars_ftransform_subset:
  "first_chars (print (transform f f' b)) \<subseteq> first_chars (print b)"
  unfolding transform_def
  apply (subst first_chars_ftransform)
  unfolding first_chars_def
  by blast

\<comment> \<open>Sadly not equal to b's first_chars since the image of f' is a subset of the domain of the type.\<close>
lemma first_chars_ftransform:
  "first_chars (print (transform f f' b)) = {hd pr | i' pr. p_has_result (print b) (f' i') pr \<and> pr \<noteq> []}"
  unfolding transform_def
  apply (subst first_chars_ftransform)
  by force



\<comment> \<open>Does not peek past end\<close>
lemma transform_does_not_peek_past_end[peek_past_end_simps]:
  assumes "does_not_peek_past_end (parse A)"
  shows "does_not_peek_past_end (parse (transform f f' A))"
  using assms
  unfolding does_not_peek_past_end_def
  by (auto simp add: transform_has_result)


\<comment> \<open>Does not consume past char.\<close>
lemma transform_does_not_consume_past_char:
  assumes "does_not_consume_past_char (parse a) ch"
  shows "does_not_consume_past_char (parse (transform f f' a)) ch"
  using assms
  unfolding does_not_consume_past_char_def
  by (auto simp add: transform_has_result)

lemma transform_does_not_consume_past_char2:
  assumes "does_not_consume_past_char2 (parse a) ch"
  shows "does_not_consume_past_char2 (parse (transform f f' a)) ch"
  using assms
  unfolding does_not_consume_past_char2_def
  by (auto simp add: transform_has_result)

lemma transform_does_not_consume_past_char3:
  assumes "does_not_consume_past_char3 (parse a) ch"
  shows "does_not_consume_past_char3 (parse (transform f f' a)) ch"
  using assms
  unfolding does_not_consume_past_char3_def
  by (auto simp add: transform_has_result)



\<comment> \<open>First printed char\<close>
lemma transform_fpci:
  assumes "first_printed_chari (print A) (f' i) c"
  shows "first_printed_chari (print (transform f f' A)) i c"
  using assms unfolding first_printed_chari_def
  by (auto simp add: transform_p_has_result)

lemma transform_fpci2[fpci_simps]:
  shows "first_printed_chari (print (transform f f' A)) i c \<longleftrightarrow> first_printed_chari (print A) (f' i) c"
  unfolding first_printed_chari_def
  by (auto simp add: transform_p_has_result)

lemma transform_fpc[fpc_simps]:
  shows "fpc (parse (transform f f' A)) i c \<longleftrightarrow> (\<exists>i'. fpc (parse A) i' c \<and> f i' = i)"
  unfolding fpc_def transform_has_result
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
  subgoal using assms[unfolded bidef_well_formed_def] transform_PNGI
    by blast
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
  subgoal using assms[unfolded bidef_well_formed_def] transform_PNGI
    by blast
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

definition well_formed_transform_funcs3 :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "well_formed_transform_funcs3 f f' b \<longleftrightarrow> ( \<comment> \<open>f' (f v) = v\<close>
        (\<forall> i v l. has_result (parse b) i v l \<longrightarrow> (\<exists> t. p_has_result (print b) (f' (f v)) t))
      \<and> (\<forall> pr t. p_has_result (print b) (f' t) pr \<longrightarrow> (\<exists>l r'. has_result (parse b) pr r' l \<and> t = f r')))"

\<comment> \<open>TODO, the order of the assumptions here is very unfortunate. Invert some time\<close>
lemma transform_well_formed3:
  assumes "bidef_well_formed b"
  assumes "well_formed_transform_funcs3 f f' b"
  shows "bidef_well_formed (transform f f' b)"
  apply wf_init
  subgoal using assms[unfolded bidef_well_formed_def] transform_PNGI
    by blast
  subgoal
    using assms[unfolded bidef_well_formed_def
                         well_formed_transform_funcs3_def]
    apply (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
    by (simp add: has_result_def)
  subgoal
    using assms[unfolded bidef_well_formed_def
                         well_formed_transform_funcs3_def]
    apply (simp add: printer_can_print_parse_result_def fp_NER NER_simps)
    by blast
  done

\<comment> \<open>Best definition since it does not require re-stating WF\<close>
\<comment> \<open>TODO: This, but for ftransform!\<close>
definition well_formed_transform_funcs4 :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha> bidef \<Rightarrow> bool" where
  "well_formed_transform_funcs4 f f' b \<longleftrightarrow> (
        (\<forall> i v l. has_result (parse b) i v l \<longrightarrow> f' (f v) = v)
      \<and> (\<forall> pr t. p_has_result (print (transform f f' b)) t pr \<longrightarrow> f (f' t) = t))"

lemma transform_well_formed4:
  assumes funcs: "well_formed_transform_funcs4 f f' b"
  assumes wf: "bidef_well_formed b"
  shows "bidef_well_formed (transform f f' b)"
  apply wf_init
  subgoal using wf[THEN get_pngi] transform_PNGI by blast
  subgoal
    using wf[THEN get_parser_can_parse] funcs[unfolded well_formed_transform_funcs4_def]
    apply (simp add: parser_can_parse_print_result_def fp_NER NER_simps)
    by (simp add: has_result_def)
  subgoal
    using wf[THEN get_printer_can_print] funcs[unfolded well_formed_transform_funcs4_def]
    apply (simp add: printer_can_print_parse_result_def fp_NER NER_simps)
    by fastforce
  done

end
