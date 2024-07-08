theory derived_optional
  imports basic_definitions
begin

definition optional :: "'\<alpha> bidef \<Rightarrow> '\<alpha> option bidef" where
  "optional b = transform
                  \<comment> \<open>The _ here is not () but () is the only element of type unit.\<close>
                  (\<lambda>r. case r of Inl v\<Rightarrow> Some v | Inr _ \<Rightarrow> None)
                  (\<lambda>r. case r of None \<Rightarrow> Inr () | Some v \<Rightarrow> Inl v)
                  (if_then_else b (return :: '\<alpha> \<Rightarrow> '\<alpha> bidef) (return ()) id)"

lemma mono_optional[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. optional (A f))"
  unfolding optional_def using ma
  by pf_mono_prover



\<comment> \<open>NER\<close>
lemma optional_is_nonterm[NER_simps]:
  "is_nonterm (parse (optional b)) i \<longleftrightarrow> is_nonterm (parse b) i"
  by (simp add: optional_def NER_simps)

lemma optional_is_error[NER_simps]:
  "is_error (parse (optional b)) i \<longleftrightarrow> False"
  by (simp add: optional_def NER_simps)

lemma optional_has_result[NER_simps]:
  "has_result (parse (optional p)) i None     l \<longleftrightarrow> is_error (parse p) i \<and> i = l"
  "has_result (parse (optional p)) i (Some r) l \<longleftrightarrow> has_result (parse p) i r l"
  "has_result (parse (optional p)) i rr l \<longleftrightarrow> (case rr of None \<Rightarrow> is_error (parse p) i \<and> i = l | Some r \<Rightarrow> has_result (parse p) i r l)"
  apply (auto simp add: optional_def NER_simps split: sum.splits option.splits)
  by (metis (full_types) old.sum.exhaust old.unit.exhaust)+

lemma optional_has_result_ci[NER_simps]:
  "has_result_ci (parse (optional p)) i c None     l \<longleftrightarrow> is_error (parse p) i \<and> i = l \<and> c = []"
  "has_result_ci (parse (optional p)) i c (Some r) l \<longleftrightarrow> has_result_ci (parse p) i c r l"
  "has_result_ci (parse (optional p)) i c rr       l \<longleftrightarrow> (case rr of None \<Rightarrow> is_error (parse p) i \<and> i = l \<and> c = [] | Some r \<Rightarrow> has_result_ci (parse p) i c r l)"
  by (auto simp add: NER_simps has_result_c_def has_result_ci_def split: option.splits)



\<comment> \<open>fp_NER\<close>
lemma optional_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (optional p)) None \<longleftrightarrow> False"
  "p_is_nonterm (print (optional p)) (Some rr) \<longleftrightarrow> p_is_nonterm (print p) rr"
  "p_is_nonterm (print (optional p)) r \<longleftrightarrow> (case r of None \<Rightarrow> False | Some rr \<Rightarrow> p_is_nonterm (print p) rr)"
  by (simp add: optional_def fp_NER split: option.splits)+

lemma optional_p_is_error[fp_NER]:
  "p_is_error (print (optional p)) None \<longleftrightarrow> False"
  "p_is_error (print (optional p)) (Some rr) \<longleftrightarrow> p_is_error (print p) rr"
  "p_is_error (print (optional p)) r \<longleftrightarrow> (case r of None \<Rightarrow> False | Some rr \<Rightarrow> p_is_error (print p) rr)"
  by (simp add: optional_def fp_NER split: option.splits)+

lemma optional_p_has_result[fp_NER]:
  "p_has_result (print (optional p)) None t \<longleftrightarrow> t = []"
  "p_has_result (print (optional p)) (Some rr) t \<longleftrightarrow> p_has_result (print p) rr t"
  "p_has_result (print (optional p)) r t \<longleftrightarrow> (case r of None \<Rightarrow> t=[] | Some rr \<Rightarrow> p_has_result (print p) rr t)"
  by (simp add: optional_def fp_NER split: option.splits)+

lemma optional_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (optional b)) None     [] \<longleftrightarrow> True"
  "p_has_result (print (optional b)) (Some i) [] \<longleftrightarrow> p_has_result (print b) i []"
  by (clarsimp simp add: optional_def print_empty)+

lemma optional_print_empty:
  "p_has_result (print (optional b)) i [] \<longleftrightarrow>(
    case i of
      None \<Rightarrow> True
    | Some i' \<Rightarrow> p_has_result (print b) i' []
  )"
  by (clarsimp simp add: optional_def print_empty split: option.splits)



\<comment> \<open>PNGI, PASI\<close>
lemma optional_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PNGI (parse p)"
  shows "PNGI (parse (optional p))"
  unfolding optional_def
  unfolding transform_PNGI[symmetric]
  apply (rule PNGI_dep_if_then_else)
  subgoal by (rule assms(1))
  subgoal using return_PNGI by fast
  subgoal using return_PNGI by fast
  done

lemma optional_PASI[PASI_PNGI, PASI_PNGI_intros]:
  assumes "PASI (parse p)"
  assumes "\<nexists>i. is_error (parse p) i"
  shows "PASI (parse (optional p))"
  using assms
  by (auto simp add: PASI_def NER_simps split: option.splits)



\<comment> \<open>Does not peek past end\<close>
lemma optional_does_not_peek_past_end:
  assumes "PNGI (parse b)"
  assumes "does_not_peek_past_end (parse b)"
  assumes "is_error (parse b) []"
  shows "does_not_peek_past_end (parse (optional b))"
  unfolding optional_def
  apply (rule transform_does_not_peek_past_end)
  apply (rule if_then_else_does_not_peek_past_end)
  apply (auto simp add: assms return_PNGI peek_past_end_simps A_is_error_on_C_consumed_def return_has_result)
  \<comment> \<open>\<And>x. is_error (parse b) x\<close>
  oops \<comment> \<open>So, via combinators not viable, are they too constrained?\<close>

lemma optional_does_not_peek_past_end:
  assumes "does_not_peek_past_end (parse b)"
  shows "does_not_peek_past_end (parse (optional b))"
  unfolding does_not_peek_past_end_def
  apply (auto simp add: NER_simps split: option.splits)
  subgoal using assms(1)[unfolded does_not_peek_past_end_def] by blast
  subgoal for l l'
    \<comment> \<open>is_error (parse b) l \<Longrightarrow> is_error (parse b) l'\<close>
    sorry
  subgoal using is_error_implies_not_has_result by blast
  oops \<comment> \<open>So, via this also not really feasible.\<close>
  \<comment> \<open>I'm convinced this cannot work without \<forall>x. is_error (parse b) x.
The idea being, when b fails to parse, optional succeeds with r=None and c=[].
Then, we need to prove that optional succeeds with r=None and i=[]@x for any x.
But, this can only be true if b always fails.
I could not get an actual proof of this to work easily, so not going to spend more time on it,
but the intuition seems clear, so I'm also not going to spend more time on it.
\<close>


lemma optional_does_not_peek_past_end:
  assumes "does_not_peek_past_end (parse b)"
  assumes "\<forall>x. is_error (parse b) x"
  shows "does_not_peek_past_end (parse (optional b))"
  unfolding does_not_peek_past_end_def
  apply (auto simp add: NER_simps assms(1)[unfolded does_not_peek_past_end_def] assms(2) split: option.splits)
  using assms(2) is_error_implies_not_has_result
  by blast

lemma optional_does_not_peek_past_end_not_if_has_result_and_error:
  assumes "\<exists>i r l. has_result (parse b) i r l"
  assumes "\<exists>i. is_error (parse b) i"
  shows "\<not>does_not_peek_past_end (parse (optional b))"
  using assms unfolding does_not_peek_past_end_def
  apply (auto simp add: NER_simps split: option.splits)
  subgoal for i r l
    apply (rule exI[of _ \<open>[]\<close>])
    apply (rule exI[of _ None])
    apply (auto simp add: assms(1))
    by (meson has_result_implies_not_is_error)
  done



\<comment> \<open>First printed char\<close>
lemma optional_fpci_none[fpci_simps]:
  "first_printed_chari (print (optional b)) None c \<longleftrightarrow> False"
  unfolding optional_def
  by (clarsimp simp add: transform_fpci2 if_then_else_fpci_ri_iff return_fpci)

lemma optional_fpci_some[fpci_simps]:
  "first_printed_chari (print (optional b)) (Some i) c \<longleftrightarrow> first_printed_chari (print b) i c"
  unfolding optional_def
  by (auto simp add: transform_fpci2
                     if_then_else_fpci_li_iff
                     return_fpci
                     empty_result_means_no_first_char
                     return_p_has_result(1))

lemma optional_fpci[fpci_simps]:
  "first_printed_chari (print (optional b)) i c \<longleftrightarrow>(
    case i of None \<Rightarrow> False
            | Some i' \<Rightarrow> first_printed_chari (print b) i' c)"
  by (clarsimp simp add: optional_fpci_none optional_fpci_some split: option.splits)



\<comment> \<open>No peek past char\<close>
lemma optional_does_not_consume_past_char3:
  assumes I_error_empty: "is_error (parse I) []"
  assumes I_fail_if_first_char: "\<And>l. is_error (parse I) (c # l)"
  assumes I_ncpc: "does_not_consume_past_char3 (parse I) c"
  shows "does_not_consume_past_char3 (parse (optional I)) c"
  unfolding optional_def
  apply (rule transform_does_not_consume_past_char3)
  using I_ncpc unfolding does_not_consume_past_char3_def
  by (auto simp add: NER_simps I_error_empty I_fail_if_first_char split: sum.splits)


lemma optional_does_not_consume_past_parse_consume:
  assumes A_error_empty: "is_error (parse A) []"
  assumes A_error_on_B: "\<And>ea cb lb rb l'. \<lbrakk>is_error (parse A) ea; has_result (parse B) (cb @ lb) rb lb\<rbrakk> \<Longrightarrow> is_error (parse A) (cb @ l')"
  assumes A_dncppc_B: "does_not_consume_past_parse_consume (parse A) (parse B)"
  shows "does_not_consume_past_parse_consume (parse (optional A)) (parse B)"
  apply (auto simp add: does_not_consume_past_parse_consume_def NER_simps A_error_empty A_error_on_B split: option.splits)
  using A_dncppc_B[unfolded does_not_consume_past_parse_consume_def]
  by blast+



\<comment> \<open>Well formed\<close>
lemma optional_well_formed:
  assumes "is_error (parse b) []"
  assumes "bidef_well_formed b"
  shows "bidef_well_formed (optional b)"
  apply wf_init
  subgoal by (rule optional_PNGI[OF assms(2)[THEN get_pngi]])
  subgoal
    using assms
    unfolding parser_can_parse_print_result_def
              bidef_well_formed_def
    apply (subst optional_p_has_result(3))
    apply (unfold optional_has_result(3))
    by (clarsimp split: option.splits)
  subgoal
    using assms
    unfolding printer_can_print_parse_result_def
              bidef_well_formed_def
    apply (unfold optional_p_has_result(3))
    apply (unfold optional_has_result(3))
    apply clarsimp
    subgoal for t by (cases t) auto
    done
  done

lemma optional_well_formed_rev:
  assumes "bidef_well_formed b"
  assumes "bidef_well_formed (optional b)"
  shows "is_error (parse b) []"
  using assms
  unfolding bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
  by (auto simp add: fp_NER NER_simps split: option.splits)

lemma optional_well_formed_minimal:
  assumes "bidef_well_formed b"
  shows "bidef_well_formed (optional b) \<longleftrightarrow> is_error (parse b) []"
  by (auto simp add: assms optional_well_formed optional_well_formed_rev)

lemma optional_well_formed_minimal2:
  shows "bidef_well_formed (optional b) \<longleftrightarrow> (is_error (parse b) [] \<and> bidef_well_formed b)"
  unfolding bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
  unfolding fp_NER NER_simps
  unfolding is_error_def has_result_def p_has_result_def p_is_error_def
  using optional_PNGI
  apply auto
  subgoal by (metis (mono_tags, lifting) option.simps(4))
  subgoal by (meson PNGI_def optional_has_result(2))
  subgoal by (metis (mono_tags, lifting) option.simps(5))
  subgoal by (metis (mono_tags) option.simps(5))
  subgoal by (simp add: option.case_eq_if)
  subgoal by (metis (mono_tags, lifting) option.case_eq_if)
  done



end
