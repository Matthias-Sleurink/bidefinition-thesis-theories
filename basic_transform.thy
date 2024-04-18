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

lemma transform_PNGI:
  shows "PNGI (parse b) \<longleftrightarrow> PNGI (parse (transform f f' b))"
  apply (simp add: PNGI_def NER_simps)
  by blast



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


end
