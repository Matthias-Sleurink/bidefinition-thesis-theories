theory derived_optional
  imports basic_definitions
begin

definition optional :: "'\<alpha> bidef \<Rightarrow> '\<alpha> option bidef" where
  "optional b = transform
                  \<comment> \<open>The _ here is not () but () is the only element of type unit.\<close>
                  (\<lambda>r. case r of Inl v\<Rightarrow> Some v | Inr _ \<Rightarrow> None)
                  (\<lambda>r. case r of None \<Rightarrow> Inr () | Some v \<Rightarrow> Inl v)
                  (if_then_else b (return :: '\<alpha> \<Rightarrow> '\<alpha> bidef) (return ()) id)"



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



\<comment> \<open>fp_NER\<close>
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



\<comment> \<open>PNGI, PASI\<close>
lemma optional_PNGI:
  assumes "PNGI (parse p)"
  shows "PNGI (parse (optional p))"
  unfolding optional_def
  unfolding transform_PNGI[symmetric]
  apply (rule PNGI_dep_if_then_else)
  subgoal by (rule assms(1))
  subgoal using return_PNGI by blast
  subgoal using return_PNGI by fast
  done


lemma optional_PASI:
  assumes "PASI (parse p)"
  assumes "\<nexists>i. is_error (parse p) i"
  shows "PASI (parse (optional p))"
  using assms
  by (auto simp add: PASI_def NER_simps split: option.splits)



\<comment> \<open>Well formed\<close>
lemma optional_well_formed:
  assumes "is_error (parse b) []"
  assumes "bidef_well_formed b"
  shows "bidef_well_formed (optional b)"
  apply wf_init
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
  apply auto
  subgoal by (metis (mono_tags, lifting) option.case_eq_if)
  subgoal by (metis (mono_tags, lifting) option.case(2))
  subgoal by (metis (mono_tags, lifting) option.simps(5))
  subgoal by (metis (mono_tags, lifting) option.case_eq_if)
  subgoal by (metis (mono_tags, lifting) option.case_eq_if)
  done


end