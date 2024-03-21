theory derived_many
  imports basic_definitions
          derived_then

          derived_char_for_predicate (*Only needed for the NER simps rule. Maybe split out to other file?*)
begin            


section \<open>many\<close>
fun sum_take :: "('\<alpha> + '\<alpha>) \<Rightarrow> '\<alpha>" where
  "sum_take (Inl a) = a"
| "sum_take (Inr a) = a"

\<comment> \<open>This is the "canonical" many implementation, and it makes a lot of sense.\<close>
\<comment> \<open>But, for this impl it's hard to prove that many never fails. (eg: is_error many bd i <--> False)\<close>
\<comment> \<open>So, we adjust the impl slightly to the one below.\<close>
\<comment> \<open>It has the same lemmas in NER and fp_NER, but it's trivial to prove that it never fails.\<close>
\<comment> \<open>Which is a very nice property to have for other proofs.\<close>
partial_function (bd) many' :: "'a bd \<Rightarrow> 'a list bd" where [code]:
  "many' a = transform
              sum_take
              (\<lambda>l. if l = [] then Inr [] else Inl l) \<comment> \<open>was: Inl\<close>
              (if_then_else
                a \<comment> \<open>test\<close>
                (\<lambda>r. dep_then (many' a) (\<lambda> rr. return (r#rr)) tl) \<comment> \<open>then\<close>
                (return []) \<comment> \<open>else\<close>
                (hd) \<comment> \<open>'a list \<Rightarrow> 'a (transform result of then back into result for test)\<close>
               )
"
print_theorems



partial_function (bd) many :: "'a bd \<Rightarrow> 'a list bd" where [code]:
  "many a = transform
              sum_take
              (\<lambda>l. if l = [] then Inr [] else Inl l) \<comment> \<open>was: Inl\<close>
              (if_then_else
                (dep_then a (\<lambda>r. dep_then (many a) (\<lambda> rr. return (r#rr)) tl) hd) \<comment> \<open>test\<close>
                return \<comment> \<open>then\<close>
                (return []) \<comment> \<open>else\<close>
                (id)
               )
"
print_theorems


subsection \<open>NER\<close>
lemma many_is_nonterm: \<comment> \<open>not added to nersimp since it will unfold forever\<close>
  "is_nonterm (parse (many b)) i \<longleftrightarrow> is_nonterm (parse b) i \<or> (\<exists> r l. has_result (parse b) i r l \<and> is_nonterm (parse (many b)) l)"
  apply (subst many.simps)
  by (clarsimp simp add: NER_simps)

\<comment> \<open>TODO\<close>
lemma many_is_error[NER_simps]:
  "is_error (parse (many b)) i \<longleftrightarrow> False"
  apply (subst many.simps)
  by (clarsimp simp add: NER_simps)

\<comment> \<open>Since these explicitly match on the constructors of list they are safe to be in NER.\<close>
lemma many_has_result_safe[NER_simps]:
  "has_result (parse (many b)) i []     l \<longleftrightarrow> i = l \<and> is_error (parse b) i"
  "has_result (parse (many b)) i (e#es) l \<longleftrightarrow> (\<exists>l' . has_result (parse b) i e l' \<and> has_result (parse (many b)) l' es l)"
  subgoal
    apply (subst many.simps)
    apply (auto simp add: NER_simps split: sum.splits)
    subgoal by (metis list.simps(3) sum_take.cases)
    subgoal for r' by (cases r'; auto split: sum.split)
    done
  subgoal
    apply (subst many.simps)
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
  "p_is_error (print (many b)) (e#es) \<longleftrightarrow> p_is_error (print b) e \<or> (\<exists>pr. p_has_result (print b) e pr \<and> p_is_error (print (many b)) es)"
  apply (auto simp add: fp_NER split: option.splits)
  subgoal
    apply (subst (asm) many.simps)
    by (clarsimp simp add: fp_NER Let_def)
  subgoal
    apply (subst (asm) many.simps)
    by (clarsimp simp add: fp_NER p_has_result_eq_not_is_error)
  subgoal
    apply (subst (asm) many.simps)
    by (clarsimp simp add: fp_NER)
  subgoal
    apply (subst many.simps)
    by (clarsimp simp add: fp_NER)
  subgoal
    apply (subst many.simps)
    apply (clarsimp simp add: fp_NER)
    using dep_then_p_is_error p_has_result_eq_not_is_error
    by fastforce
  done

lemma many_p_is_error:
  "p_is_error (print (many b)) rs \<longleftrightarrow>(
    case rs of
      [] \<Rightarrow> False
    | (e#es) \<Rightarrow> p_is_error (print b) e \<or> (\<exists>pr. p_has_result (print b) e pr \<and> p_is_error (print (many b)) es)
)"
  by (cases rs) (clarsimp simp add: many_p_is_error_safe)+


lemma many_p_no_error:
  assumes "\<forall> x \<in> set i. \<not>p_is_error (print p) x"
  shows "\<not>p_is_error (print (many p)) i"
  using assms
  apply (induction i)
  by (simp_all add: many_p_is_error_safe(1, 2))


lemma many_p_has_result_safe[fp_NER]:
  "p_has_result (print (many b)) [] r \<longleftrightarrow> r = []"
  "p_has_result (print (many b)) (e#es) r \<longleftrightarrow> (\<exists> ir ir'. ir@ir' = r \<and> p_has_result (print b) e ir \<and> p_has_result (print (many b)) es ir')"
  subgoal
    apply (subst many.simps)
    by (clarsimp simp add: fp_NER)
  apply (subst many.simps)
  by (auto simp add: fp_NER)

lemma many_p_has_result:
  "p_has_result (print (many b)) l r \<longleftrightarrow>(
    case l of
      [] \<Rightarrow> r = []
    | (e#es) \<Rightarrow> (\<exists> ir ir'. ir@ir' = r \<and> p_has_result (print b) e ir \<and> p_has_result (print (many b)) es ir')
)"
  by (cases l) (clarsimp simp add: many_p_has_result_safe)+

lemma many_p_is_nonterm_safe[fp_NER]:
  "p_is_nonterm (print (many b)) []     \<longleftrightarrow> False"
  "p_is_nonterm (print (many b)) (x#xs) \<longleftrightarrow> p_is_nonterm (print b) x \<or> (\<not>p_is_error (print b) x \<and> p_is_nonterm (print (many b)) xs)"
  by (subst many.simps; clarsimp simp add: fp_NER)+

lemma many_p_is_not_nonterm[fp_NER]:
  assumes "\<And>i. p_is_nonterm (print b) i \<longleftrightarrow> False"
  shows "p_is_nonterm (print (many b)) is \<longleftrightarrow> False"
  apply (induction \<open>is\<close>)
  by (clarsimp simp add: fp_NER assms)+

lemma many_p_is_not_nonterm_in_list[fp_NER]:
  assumes "\<forall>i \<in> set is. p_is_nonterm (print b) i \<longleftrightarrow> False"
  shows "p_is_nonterm (print (many b)) is \<longleftrightarrow> False"
  using assms apply (induction \<open>is\<close>)
  by (clarsimp simp add: fp_NER assms)+

lemma many_p_is_not_error[fp_NER]:
  assumes "\<And>i. p_is_error (print b) i \<longleftrightarrow> False"
  shows "p_is_error (print (many b)) is \<longleftrightarrow> False"
  apply (induction \<open>is\<close>)
  by (clarsimp simp add: fp_NER assms)+

lemma many_p_is_not_error_in_list[fp_NER]:
  assumes "\<forall>i \<in> set is. p_is_error (print b) i \<longleftrightarrow> False"
  shows "p_is_error (print (many b)) is \<longleftrightarrow> False"
  using assms apply (induction \<open>is\<close>)
  by (clarsimp simp add: fp_NER assms)+





lemma many_has_result_when_first_parse_fails:
  assumes "is_error (parse bd) l"
  shows "has_result (parse (many bd)) l [] l"
  by (auto simp add: assms NER_simps)



\<comment> \<open>Induction\<close>

(*
Basically, If Q holds for the cases where the parser fails (and thus the list ends)
           And if for some success, with some succeeding list, we can make another longer succeeding list
           Then we know that it holds for any time that it succeeds.
*)
lemma many0_induct:
  assumes pasi: "PASI (parse bd)"

  assumes step: "\<And> i r l. has_result (parse bd) i r l \<longrightarrow> (\<forall>rr l'. (length l < length i \<and> Q l rr l') \<longrightarrow> Q i (r # rr) l')"
  assumes last_step: "\<And> i. is_error (parse bd) i \<longrightarrow> Q i [] i"

  shows "has_result (parse (many bd)) i r l \<longrightarrow> Q i r l"
  apply (induction i arbitrary: r l rule: length_induct)
  apply (subst many.simps)
  apply (auto simp add: NER_simps split: sum.splits)
  subgoal for xs r l r'
    apply (cases r')
    subgoal using step pasi PASI_implies_res_length_shorter by fastforce
    subgoal using last_step by auto
    done
  done



\<comment> \<open>PNGI, PASI\<close>
lemma many_PNGI_from_PNGI:
  assumes "PNGI (parse bd)"
  shows "PNGI (parse (many bd))"
  using assms
  unfolding PNGI_def
  apply (subst many_has_result)
  apply (auto split: list.splits)
  oops

lemma many_PNGI:
  assumes "PASI (parse p)"
  shows "PNGI (parse (many p))"
  (*Should really figure out some way of exposing the input so that we can say is PASI when at least one success*)
  unfolding PASI_def PNGI_def
  apply (auto simp add: allI[of \<open>\<lambda>(i, r, l). has_result (parse (many p)) i r l \<longrightarrow> (\<exists>c. i = c @ l)\<close>])
  subgoal for i r l
  apply (subst many0_induct[of p \<open>\<lambda> i r l. (\<exists>c. i = c @ l)\<close> i r l])
  subgoal by (simp add: assms)
  subgoal
    apply (auto simp add: assms)
    using PASI_def assms by fastforce
    by simp_all
  done



\<comment> \<open>TODO: split out to other file?\<close>
lemma takeWhile_hd_no_match:
  assumes "\<not> p (hd i)"
  shows "[] = takeWhile p i"
  using assms
  by (induction i) simp_all

lemma dropWhile_hd_no_match:
  assumes "\<not> p (hd i)"
  shows "i = dropWhile p i"
  using assms
  by (induction i) simp_all


\<comment> \<open>Has result for many for_predicate has some nice properties\<close>
lemma many_char_for_predicate_has_result_forwards:
  shows "has_result (parse (many (char_for_predicate p))) i r l \<longrightarrow> r = takeWhile p i \<and> l = dropWhile p i"
  apply (rule many0_induct[of \<open>(char_for_predicate p)\<close> \<open>\<lambda>i r l. (r = takeWhile p i \<and> l = dropWhile p i)\<close> i r l])
  subgoal by (rule char_for_predicate_PASI)
  subgoal using char_for_predicate_has_result by force
  subgoal by (simp add: char_for_predicate_is_error dropWhile_hd_no_match takeWhile_hd_no_match)
  done

lemma many_char_for_predicate_has_result_reverse:
  shows "r = takeWhile p i \<and> l = dropWhile p i \<longrightarrow> has_result (parse (many (char_for_predicate p))) i r l"
  apply (induction i arbitrary: r l)
  by (auto simp add: NER_simps many_has_result_when_first_parse_fails)
  

lemma many_char_for_predicate_has_result[NER_simps]:
  shows "has_result (parse (many (char_for_predicate p))) i r l \<longleftrightarrow> r = takeWhile p i \<and> l = dropWhile p i"
  using many_char_for_predicate_has_result_forwards[of p i r l]
        many_char_for_predicate_has_result_reverse[of r p i l]
  by fast

lemma many_char_for_predicate_p_has_result_forwards:
  assumes "\<forall>c \<in> set i. p c"
  shows "p_has_result (print (many (char_for_predicate p))) i r \<longrightarrow> r = i"
  using assms
  apply (induction i arbitrary: r)
  subgoal by (clarsimp simp add: fp_NER)
  by (auto simp add: fp_NER)

lemma many_char_for_predicate_p_has_result_backwards:
  assumes "\<forall>c \<in> set i. p c"
  shows "r = i \<longrightarrow> p_has_result (print (many (char_for_predicate p))) i r"
  using assms
  apply (induction i arbitrary: r)
  subgoal by (clarsimp simp add: fp_NER)
  by (clarsimp simp add: fp_NER)

lemma many_char_for_predicate_p_has_result[fp_NER]:
  assumes "\<forall>c \<in> set i. p c"
  shows "p_has_result (print (many (char_for_predicate p))) i r \<longleftrightarrow> r = i"
  using many_char_for_predicate_p_has_result_forwards[OF assms]
        many_char_for_predicate_p_has_result_backwards[OF assms]
  by blast


lemma does_not_eat_into_conseq_parser:
  assumes "pa_does_not_eat_into_pb_nondep b b'"
  assumes "p_has_result (print b) i i_t"
  assumes "p_has_result (print b') i' i_t'"
  shows "has_result (parse b) (i_t @ i_t') i i_t'"
  using assms pa_does_not_eat_into_pb_nondep_def by fast
  
lemma does_not_eat_into_many:
  assumes "bidef_well_formed b"
  assumes "pa_does_not_eat_into_pb_nondep b b"
  shows "pa_does_not_eat_into_pb_nondep b (many b)"
  using assms
  unfolding pa_does_not_eat_into_pb_nondep_def
            bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
  apply clarsimp
  subgoal for t1 pr1 t2 pr2
    apply (induction t2 arbitrary: pr2)
    subgoal by (clarsimp simp add: fp_NER)
    subgoal apply (auto simp add: fp_NER NER_simps) 
      
      sorry
  

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
    unfolding parser_can_parse_print_result_def
    apply clarsimp
    subgoal for t pr
      apply (induction t arbitrary: pr)
      subgoal for pr
        by (simp add: assms(1) many_has_result_safe(1) many_p_has_result_safe(1))
      subgoal for r rs pr
        apply (subst (asm) many_p_has_result_safe(2)[of b r rs pr])
        apply clarsimp
        subgoal for i_pr is_pr
          apply (subst many_has_result_safe(2)[of b \<open>i_pr @ is_pr\<close> r rs \<open>[]\<close>])
          apply (cases rs)
          subgoal \<comment> \<open>rs = []\<close> by (clarsimp simp add: NER_simps fp_NER assms(2)[unfolded bidef_well_formed_def parser_can_parse_print_result_def])
          subgoal for r' rss \<comment> \<open>rs = r' # rss\<close>
            using does_not_eat_into_conseq_parser[of b r i_pr r']
            

            using assms(3)[unfolded pa_does_not_eat_into_pb_nondep_def]
            apply (auto simp add: NER_simps fp_NER)
            \<comment> \<open>if we have does not eat into pb for b b then WF and p_has_result -> should give us the induction step.\<close>
            
            sorry
          done
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