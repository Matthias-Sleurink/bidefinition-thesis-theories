theory derived_many
  imports basic_definitions
          derived_then
begin            


section \<open>many\<close>
fun sum_take :: "('\<alpha> + '\<alpha>) \<Rightarrow> '\<alpha>" where
  "sum_take (Inl a) = a"
| "sum_take (Inr a) = a"


(* This has some fragility, in that it depends on bind_parser_mono which defines the monotonicity for the inlined bind operator *)
(* We claim that this is a derived parser, yet we are operating on the input string directly here. Make basic? *)
partial_function (parser) many_p :: "'a parser \<Rightarrow> 'a list parser"
  where [code]:
  "many_p a = ftransform_p
                  (Some o sum_take)
                  (if_then_else_p
                    ((\<lambda> i:: string. 
                      case a i of
                        None \<Rightarrow> None
                      | Some None \<Rightarrow> Some None
                      | Some (Some (r, l)) \<Rightarrow> (
                        case many_p a l of
                          None \<Rightarrow> None
                        | Some None \<Rightarrow> Some None
                        | Some (Some (rs, l')) \<Rightarrow> Some (Some (r#rs, l')))
                      ) :: 'a list parser)
                    (return_p :: 'a list \<Rightarrow> 'a list parser)
                    (return_p [] :: 'a list parser)
                  )"
print_theorems

fun many_pr :: "'\<alpha> printer \<Rightarrow> '\<alpha> list printer" where
  "many_pr p []     = Some []"
| "many_pr p (x#xs) =(
    case p x of
      None \<Rightarrow> None
    | Some (xr) \<Rightarrow>(
      case many_pr p xs of
        None \<Rightarrow> None
      | Some (xsr) \<Rightarrow> Some (xr@xsr)
))"

definition many :: "'\<alpha> bidef \<Rightarrow> '\<alpha> list bidef" where
  "many b = (
    many_p (parse b),
    many_pr (print b)
)"

subsection \<open>NER\<close>
lemma many_is_nonterm: \<comment> \<open>not added to nersimp since it will unfold forever\<close>
  "is_nonterm (parse (many b)) i \<longleftrightarrow> is_nonterm (parse b) i \<or> (\<exists> r l. has_result (parse b) i r l \<and> is_nonterm (parse (many b)) l)"
  "is_nonterm (many_p (parse b)) i \<longleftrightarrow> is_nonterm (parse b) i \<or> (\<exists> r l. has_result (parse b) i r l \<and> is_nonterm (parse (many b)) l)"
  by ((clarsimp simp add: many_def);
  (subst many_p.simps);
  (clarsimp simp add: NER_simps))+

lemma many_is_error[NER_simps]:
  "is_error (parse (many b)) i \<longleftrightarrow> False"
  "is_error (many_p (parse b)) i \<longleftrightarrow> False"
  by ((clarsimp simp add: many_def);
      (subst (asm) many_p.simps);
      (simp add: NER_simps)
     )+

\<comment> \<open>Since these explicitly match on the constructors of list they are safe to be in NER.\<close>
lemma many_has_result_safe[NER_simps]:
  "has_result (parse (many b)) i []     l \<longleftrightarrow> i = l \<and> is_error (parse b) i"
  "has_result (parse (many b)) i (e#es) l \<longleftrightarrow> (\<exists>l' . has_result (parse b) i e l' \<and> has_result (parse (many b)) l' es l)"
  subgoal
    apply (clarsimp simp add: many_def)
    apply (subst many_p.simps)
    apply (auto simp add: NER_simps split: sum.splits)
    subgoal by (metis list.simps(3) sum_take.cases)
    subgoal by (metis neq_Nil_conv sumE)
    done
  subgoal
    apply (clarsimp simp add: many_def)
    apply (subst many_p.simps)
    apply (auto simp add: NER_simps split: sum.splits)
    subgoal by (metis (no_types, lifting) list.distinct(1) list.inject sum_take.cases)
    subgoal by fast
    done
  done

\<comment> \<open>Note how this lemma can be applied to it's own RHS, that makes it unsafe for NER_simps\<close>
lemma many_has_result:
  "has_result (parse (many b)) i rs l \<longleftrightarrow> (
      case rs of
        [] \<Rightarrow>  i = l \<and> is_error (parse b) i
      | (e#es) \<Rightarrow>  (\<exists>l' . has_result (parse b) i e l' \<and> has_result (parse (many b)) l' es l))"
  by (cases rs) (clarsimp simp add: many_has_result_safe)+


subsection \<open>fp_NER\<close>
lemma many_p_is_error_safe[fp_NER]:
  "p_is_error (print (many b)) [] \<longleftrightarrow> False"
  "p_is_error (print (many b)) (e#es) \<longleftrightarrow> p_is_error (print b) e \<or> p_is_error (print (many b)) es"
  by (auto simp add: many_def p_is_error_def split: option.splits)

lemma many_p_is_error:
  "p_is_error (print (many b)) rs \<longleftrightarrow>(
    case rs of
      [] \<Rightarrow> False
    | (e#es) \<Rightarrow> p_is_error (print b) e \<or> p_is_error (print (many b)) es
)"
  by (cases rs) (clarsimp simp add: many_p_is_error_safe)+

lemma many_p_has_result_safe[fp_NER]:
  "p_has_result (print (many b)) [] r \<longleftrightarrow> r = []"
  "p_has_result (print (many b)) (e#es) r \<longleftrightarrow> (\<exists> ir ir'. ir@ir' = r \<and> p_has_result (print b) e ir \<and> p_has_result (print (many b)) es ir')"
  by (auto simp add: p_has_result_def many_def split: option.splits)

lemma many_p_has_result:
  "p_has_result (print (many b)) l r \<longleftrightarrow>(
    case l of
      [] \<Rightarrow> r = []
    | (e#es) \<Rightarrow> (\<exists> ir ir'. ir@ir' = r \<and> p_has_result (print b) e ir \<and> p_has_result (print (many b)) es ir')
)"
  by (cases l) (clarsimp simp add: many_p_has_result_safe)+

lemma many_p_has_result_when_first_parse_fails:
  assumes "is_error p l"
  shows "has_result (many_p p) l [] l"
  apply (subst many_p.simps)
  by (auto simp add: assms NER_simps split: sum.splits)


\<comment> \<open>Induction\<close>

(*
Basically, If Q holds for the cases where the parser fails (and thus the list ends)
           And if for some success, with some succeeding list, we can make another longer succeeding list
           Then we know that it holds for any time that it succeeds.
*)
lemma many0_induct:
  assumes pasi: "PASI p"

  assumes step: "\<And> i r l. has_result p i r l \<longrightarrow> (\<forall>rr l'. (length l < length i \<and> Q l rr l') \<longrightarrow> Q i (r # rr) l')"
  assumes last_step: "\<And> i. is_error p i \<longrightarrow> Q i [] i"

  shows "has_result (many_p p) i r l \<longrightarrow> Q i r l"
  apply (induction i arbitrary: r l rule: length_induct)
  apply (subst many_p.simps)
  apply (auto simp add: NER_simps split: sum.splits)
  subgoal for xs r l r'
    apply (cases r')
    subgoal using step pasi PASI_implies_res_length_shorter by fastforce
    subgoal using last_step many_is_error(2) by force
    done
  done



subsection \<open>Well formed\<close>
lemma many_well_formed:
  assumes "is_error (parse b) []"
  assumes "bidef_well_formed b"
  assumes "pa_does_not_eat_into_pb_nondep b b"
  assumes "PASI (parse b)"
  shows "bidef_well_formed (many b)"
  apply wf_init
  subgoal
    supply [[show_types=false]]
    using assms
    unfolding parser_can_parse_print_result_def bidef_well_formed_def pa_does_not_eat_into_pb_nondep_def PASI_def
    apply auto
    subgoal for t pr
      apply (induction t arbitrary: pr)
      subgoal
        apply (clarsimp simp add: fp_NER)
        unfolding many_has_result_safe(1)[of b \<open>[]\<close>]
        by blast
      subgoal for r rs
        apply (clarsimp simp add: fp_NER)
        subgoal for ir ir'
          unfolding many_has_result_safe(2)[of b \<open>ir@ir'\<close>]
          unfolding many_p_has_result[of b rs ir']
          \<comment> \<open>We need many0 induct for this?\<close>
          sorry
        done
      done
    done
  subgoal
    using assms(2)[unfolded bidef_well_formed_def]
    unfolding printer_can_print_parse_result_def
    apply clarsimp
    subgoal for rs i l
      apply (induction rs arbitrary: i l)
      subgoal using many_p_has_result_safe(1) by blast
      subgoal by (metis many_has_result_safe(2) many_p_has_result_safe(2))
      done
    done
  oops



end