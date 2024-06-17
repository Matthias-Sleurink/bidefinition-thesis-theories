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

declare [[function_internals]] \<comment> \<open>Need this to get many_def.\<close>
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

lemma ord_to_fun_ord:
  shows "monotone ordA ordB F \<longleftrightarrow> monotone (fun_ord ordA) ordB (\<lambda>a. F (a ()))"
  unfolding monotone_def fun_ord_def
  by fast

lemma mono_many[partial_function_mono]:
  assumes ma: "mono_bd A"
  shows "mono_bd (\<lambda>f. many (A f))"
proof -
  have "monotone bd_ord bd_ord many"
  apply (unfold many_def)
  apply (rule bd.fixp_preserves_mono1[OF many.mono reflexive])
  thm ord_to_fun_ord[THEN iffD2]
  apply (rule ord_to_fun_ord[THEN iffD2])
  apply (intro partial_function_mono)
  by (rule ord_to_fun_ord[THEN iffD1])
  thus ?thesis using ma bd.mono2mono by fastforce
qed



subsection \<open>NER\<close>
lemma many_is_nonterm: \<comment> \<open>not added to nersimp since it will unfold forever\<close>
  "is_nonterm (parse (many b)) i \<longleftrightarrow> is_nonterm (parse b) i \<or> (\<exists> r l. has_result (parse b) i r l \<and> is_nonterm (parse (many b)) l)"
  apply (subst many.simps)
  by (clarsimp simp add: NER_simps)

lemma many_not_nonterm_when_base_not_nonterm[NER_simps]:
  assumes "\<nexists>i'. is_nonterm (parse b) i'"
  assumes "PASI (parse b)"
  shows "is_nonterm (parse (many b)) i \<longleftrightarrow> False"
  using assms[unfolded PASI_def]
  apply (induction i rule: length_induct)
  apply (auto simp add: NER_simps)
  apply (subst (asm) (2) many_is_nonterm)
  by force



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

lemma ex_many_p_has_result[fp_NER]:
  "Ex (p_has_result (print (many b)) [])"
  using many_p_has_result_safe(1) by blast

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

lemma many_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (many b)) [] [] \<longleftrightarrow> True"
  "p_has_result (print (many b)) (i#is) [] \<longleftrightarrow> p_has_result (print b) i [] \<and> p_has_result (print (many b)) is []"
  by (clarsimp simp add: fp_NER)+

lemma many_print_empty:
  "p_has_result (print (many b)) i [] \<longleftrightarrow>(
    case i of
      [] \<Rightarrow> True
    | (i'#is) \<Rightarrow> p_has_result (print b) i' [] \<and> p_has_result (print (many b)) is [])"
  by (clarsimp simp add: print_empty split: list.splits)



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



subsection \<open>PNGI PASI\<close>
lemma many_PNGI_from_PNGI:
  assumes "PNGI (parse bd)"
  shows "PNGI (parse (many bd))"
  using assms
  unfolding PNGI_def
  apply (subst many_has_result)
  apply (auto split: list.splits)
  oops

lemma many_PNGI[PASI_PNGI, PASI_PNGI_intros]:
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



\<comment> \<open>Does not peek past end\<close>
\<comment> \<open>This is the argument that shows that does_not_peek_past_end isn't true for "most" many parsers.\<close>
lemma many_does_peek_past_end[peek_past_end_simps]:
  assumes "\<exists> i r l. has_result (parse b) i r l \<and> is_error (parse b) l"
  assumes "PNGI (parse b)"
  shows "\<not>does_not_peek_past_end (parse (many b))"
  unfolding does_not_peek_past_end_def
  using assms[unfolded PNGI_def]
  apply (auto simp add: NER_simps)
  subgoal for i r l
    apply (rule exI[of _ \<open>list_upto i l\<close>])
    apply (rule exI[of _ \<open>[r]\<close>])
    apply (rule conjI)
    subgoal
      apply (rule exI[of _ l])
      apply (clarsimp simp add: NER_simps)
      by (metis list_upto_take_cons)
    subgoal
      apply (rule exI[of _ i])
      by (clarsimp simp add: NER_simps has_result_implies_not_is_error)
    done
  done



\<comment> \<open>First printed char\<close>
lemma many_fpci_nil[fpci_simps]:
  "first_printed_chari (print (many b)) [] c \<longleftrightarrow> False"
  unfolding first_printed_chari_def
  by (clarsimp simp add: fp_NER)

lemma many_fpci_cons[fpci_simps]:
  "first_printed_chari (print (many b)) (x#xs) c \<longleftrightarrow> (
    if p_has_result (print b) x [] then
      (first_printed_chari (print (many b)) xs c)
    else
      (first_printed_chari (print b) x c \<and> (\<exists>t. p_has_result (print (many b)) xs t))
  )"
  unfolding first_printed_chari_def
  apply (auto simp add: fp_NER fpci_simps)
  subgoal by (metis p_has_result_deterministic)
  subgoal using p_has_result_deterministic by fastforce
  subgoal by blast
  subgoal by (metis hd_append)
  subgoal by fastforce
  done

lemma many_fpci:
  "first_printed_chari (print (many b)) i c \<longleftrightarrow> (
    case i of
      [] \<Rightarrow> False
      | (x#xs) \<Rightarrow> (
        if p_has_result (print b) x [] then
          (first_printed_chari (print (many b)) xs c)
        else
          (first_printed_chari (print b) x c \<and> (\<exists>t. p_has_result (print (many b)) xs t))
  ))"
  by (clarsimp simp add: many_fpci_nil many_fpci_cons split: list.splits)



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

lemma many_char_for_predicate_p_has_result2:
  assumes "p_has_result (print (many (char_for_predicate p))) i r"
  shows "r = i"
  using assms
  by (induction i arbitrary: r; clarsimp simp add: fp_NER)

lemma many_char_for_predicate_p_has_result3:
  assumes "p_has_result (print (many (char_for_predicate p))) i r"
  shows "\<forall> i' \<in> set i. p i'"
  using assms
  by (induction i arbitrary: r; clarsimp simp add: fp_NER)


lemma many_char_for_predicate_fpci[fpci_simps]:
  "first_printed_chari (print (many (char_for_predicate P))) i c \<longleftrightarrow>(
    case i of
      [] \<Rightarrow> False
    | (i'#is) \<Rightarrow> (Ball (set i) P) \<and> c=i'
  )"
  apply (cases i; clarsimp simp add: fpci_simps print_empty many_char_for_predicate_p_has_result3)
  subgoal
    apply (auto simp add: many_char_for_predicate_p_has_result3)
    by (auto simp add: many_char_for_predicate_p_has_result)
  done

lemma many_char_for_predicate_does_not_consume_past_char3:
  "does_not_consume_past_char3 (parse (many (char_for_predicate P))) c \<longleftrightarrow> \<not>P c"
  unfolding does_not_consume_past_char3_def
  apply (auto simp add: NER_simps)
  subgoal by (metis append_Nil dropWhile.simps(1) dropWhile_eq_Cons_conv)
  subgoal by (metis append_same_eq takeWhile_dropWhile_id takeWhile_idem)
  subgoal by (metis append_self_conv2 dropWhile_append1 dropWhile_eq_Nil_conv)
  subgoal by (clarsimp simp add: takeWhile_tail \<open>\<And>l ca. \<lbrakk>\<not> P c; l = dropWhile P (ca @ l)\<rbrakk> \<Longrightarrow> takeWhile P (ca @ l) = takeWhile P ca\<close>)
  subgoal by (clarsimp simp add: dropWhile_append3 \<open>\<And>l ca. \<lbrakk>\<not> P c; l = dropWhile P (ca @ l)\<rbrakk> \<Longrightarrow> [] = dropWhile P ca\<close>)
  done



\<comment> \<open>The second half of many holds for all applications of many.\<close>
\<comment> \<open>Not really sure if this 'assumes A or B' is a good idea in general,
    but it makes it easier to apply if you do know the rhs\<close>
lemma printer_can_print_parse_result_many:
  assumes "printer_can_print_parse_result (parse b) (print b) \<or> bidef_well_formed b"
  shows "printer_can_print_parse_result (parse (many b)) (print (many b))"
  using assms unfolding bidef_well_formed_def printer_can_print_parse_result_def
  apply clarsimp
  subgoal for ts i l
    apply (induction ts arbitrary: i l)
    subgoal by (auto simp add: fp_NER)
    apply (auto simp add: fp_NER NER_simps)
    subgoal by (metis many_p_has_result_safe(2))
    subgoal by (meson many_p_has_result_safe(2))
    done
  done



lemma many_char_for_predicate_well_formed:
  shows "bidef_well_formed (many (char_for_predicate P))"
  apply wf_init
  subgoal using many_PNGI[OF char_for_predicate_PASI] by fast
  subgoal
    unfolding parser_can_parse_print_result_def
    apply (clarsimp simp add: NER_simps)
    subgoal for i ipr
      using many_char_for_predicate_p_has_result2[of P i ipr]
            many_char_for_predicate_p_has_result3[of P i ipr]
      apply simp
      by (metis dropWhile_eq_Nil_conv takeWhile_eq_all_conv)
    done
  subgoal
    apply (rule printer_can_print_parse_result_many)
    using char_for_predicate_well_formed
    by simp
  done


lemma does_not_eat_into_conseq_parser:
  assumes "pa_does_not_eat_into_pb_nondep b b'"
  assumes "p_has_result (print b) i i_t"
  assumes "p_has_result (print b') i' i_t'"
  shows "has_result (parse b) (i_t @ i_t') i i_t'"
  using assms pa_does_not_eat_into_pb_nondep_def by fast

\<comment> \<open>Still needs to be generalised\<close>
lemma does_not_eat_into_many_has_result_for_two:
  assumes "PASI (parse b)"
  assumes "\<not>is_nonterm (parse b) []"
  assumes "bidef_well_formed b"
  assumes "pa_does_not_eat_into_pb_nondep b b"
  assumes "p_has_result (print b) i it"
  assumes "p_has_result (print b) i' it'"
  shows "has_result (parse (many b)) (it@it') [i,i'] []"
  using assms[unfolded pa_does_not_eat_into_pb_nondep_def
                       bidef_well_formed_def parser_can_parse_print_result_def]
  apply (clarsimp simp add: fp_NER NER_simps)
  apply (rule exI[of _ it'])
  by (clarsimp simp add: PASI_implies_error_from_empty[OF assms(1, 2)])


\<comment> \<open>Convert this thing so that we can fill it in using of.\<close>
lemma parser_can_parse_print_result_simp:
  assumes "parser_can_parse_print_result parser printer"
  shows "p_has_result printer i pr \<Longrightarrow> has_result parser pr i []"
  using assms parser_can_parse_print_result_def by force

lemma can_parse_print_result:
  assumes "bidef_well_formed b"
  shows "p_has_result (print b) i pr \<Longrightarrow> has_result (parse b) pr i []"
  using assms[unfolded bidef_well_formed_def] parser_can_parse_print_result_simp
  by fast

lemma does_not_eat_into:
  assumes "pa_does_not_eat_into_pb_nondep ba bb"
  assumes "p_has_result (print ba) t1 pr1"
  assumes "p_has_result (print bb) t2 pr2"
  shows "has_result (parse ba) (pr1@pr2) t1 pr2"
  using assms[unfolded pa_does_not_eat_into_pb_nondep_def]
  by blast

lemma does_not_eat_into_many_has_result:
  assumes "PASI (parse b)"
  assumes "\<not>is_nonterm (parse b) []"
  assumes "bidef_well_formed b"
  assumes "pa_does_not_eat_into_pb_nondep b b"
  assumes "p_has_result (print b) i it"
  assumes "p_has_result (print (many b)) is it'"
  shows "has_result (parse (many b)) (it@it') (i#is) []"
  using assms[unfolded pa_does_not_eat_into_pb_nondep_def
                       bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def]
  apply (clarsimp simp add: fp_NER NER_simps)
  apply (rule exI[of _ it'])
  apply auto
  subgoal
    apply (induction \<open>is\<close> arbitrary: it') \<comment> \<open>The idea being, from is = [] this is trivial, and from i#iss we can get the first iteration\<close>
    subgoal by (clarsimp simp add: fp_NER)
    subgoal for i' iss it'
      apply clarsimp \<comment> \<open>replace is with i'#iss\<close>
      apply (subst (asm) many_p_has_result_safe(2)[of b i' iss it'])
      using can_parse_print_result[OF assms(3) \<open>p_has_result (print b) i it\<close>]

      using does_not_eat_into[OF assms(4) \<open>p_has_result (print b) i it\<close>, of i']
      using PASI_def[of \<open>parse b\<close>]
      apply clarsimp
      

      using assms(4)[unfolded pa_does_not_eat_into_pb_nondep_def]
      using assms(3)[unfolded bidef_well_formed_def parser_can_parse_print_result_def]
      sorry
    sorry
  subgoal 
    apply (induction \<open>is\<close> arbitrary: it')
    subgoal
      apply (auto simp add: fp_NER NER_simps)
      using PASI_implies_error_from_empty
      by blast
    subgoal
      apply (auto simp add: fp_NER NER_simps)
      sorry
    done
  oops



lemma does_not_eat_into_many:
  assumes "bidef_well_formed b"
  assumes "pa_does_not_eat_into_pb_nondep b b"
  shows "pa_does_not_eat_into_pb_nondep b (many b)"
  using assms
  unfolding pa_does_not_eat_into_pb_nondep_def
            bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
  apply clarsimp
  subgoal for t1 pr1 t2s pr2
    apply (induction t2s arbitrary: pr2)
    subgoal by (clarsimp simp add: fp_NER)
    subgoal for t2 t2ss pr2'
      apply clarsimp
      apply (subst (asm) many_p_has_result_safe(2))
      apply clarsimp
      
      sorry
    done
  oops
  

subsection \<open>Well formed\<close>
lemma many_well_formed:
  assumes "is_error (parse b) []"
  assumes "bidef_well_formed b"
  assumes "pa_does_not_eat_into_pb_nondep b b"
  assumes "PASI (parse b)"
  shows "bidef_well_formed (many b)"
  apply wf_init
  subgoal using many_PNGI[OF assms(4)] by fast
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
            (* using does_not_eat_into_conseq_parser[of b r i_pr r'] *)
            

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


lemma many_char_for_pred_well_formed:
  shows "bidef_well_formed (many (char_for_predicate p))"
  apply wf_init
  subgoal using many_PNGI[OF char_for_predicate_PASI] by fast
  subgoal
    unfolding parser_can_parse_print_result_def
    apply clarsimp
    subgoal for ts pr
      apply (induction ts arbitrary: pr)
      by (clarsimp simp add: fp_NER NER_simps)+
    done
  subgoal
    unfolding printer_can_print_parse_result_def
    apply clarsimp
    subgoal for ts i l
      apply (induction ts arbitrary: i l)
      subgoal by (auto simp add: fp_NER NER_simps)
      subgoal for t ts' i' l'
      apply (clarsimp simp add: fp_NER NER_simps)
        by (metis char_for_predicate_p_has_result many_p_has_result_safe(2))
      done
    done
  done

\<comment> \<open>Now for parsers that cannot be grown by any text.\<close>
definition parse_result_cannot_be_grown :: "'a parser \<Rightarrow> bool" where
  "parse_result_cannot_be_grown p \<longleftrightarrow> (\<forall>i r l i'. has_result p i r l \<longrightarrow> has_result p (i@i') r (l@i'))"

lemma parse_result_cannot_be_grown_char_for_predicate:
  "parse_result_cannot_be_grown (parse (char_for_predicate p))"
  unfolding parse_result_cannot_be_grown_def
  by (clarsimp simp add: NER_simps)
lemma parse_result_cannot_be_grown_one_char:
  "parse_result_cannot_be_grown (parse one_char)"
  unfolding parse_result_cannot_be_grown_def
  by (clarsimp simp add: NER_simps)

\<comment> \<open>This should be able to be done more easily?\<close>
lemma parse_result_cannot_be_grown_apply:
  assumes "parse_result_cannot_be_grown p"
  shows "has_result p i r l \<longrightarrow> has_result p (i@i') r (l@i')"
  using assms parse_result_cannot_be_grown_def
  by fast

lemma wf_parser_can_parse_print_result_apply:
  assumes "bidef_well_formed b"
  shows "p_has_result (print b) t pr \<Longrightarrow> has_result (parse b) pr t []"
  using assms[unfolded bidef_well_formed_def parser_can_parse_print_result_def]
  by blast

lemma well_formed_does_not_grow:
  assumes "parse_result_cannot_be_grown (parse b)"
  assumes "bidef_well_formed b"
  assumes "is_error (parse b) []"
  \<comment> \<open>This here really shows it would be great to have PNGI -> PNGI many, but not sure if that's possible.\<close>
  assumes "PASI (parse b)"
  shows "bidef_well_formed (many b)"
  apply wf_init
  subgoal using many_PNGI[OF assms(4)] by fast
  subgoal
    unfolding parser_can_parse_print_result_def
    apply clarsimp
    subgoal for ts pr
      apply (induction ts arbitrary: pr)
      subgoal by (clarsimp simp add: NER_simps fp_NER assms(3))
      subgoal for t ts' pr'
        unfolding many_p_has_result_safe many_has_result_safe
        apply clarsimp
        subgoal for tpr ts'pr
          apply (rule exI[where x=ts'pr])
          apply clarsimp
          \<comment> \<open>Cannot use literal fact here, why?\<close>
          apply (frule wf_parser_can_parse_print_result_apply[OF assms(2), of t tpr])
          (* using wf_parser_can_parse_print_result_apply[OF assms(2) \<open>p_has_result (print b) t tpr\<close>] *)
          using wf_parser_can_parse_print_result_apply[OF assms(2), of t tpr]
          using parse_result_cannot_be_grown_apply[OF assms(1), of tpr t \<open>[]\<close> ts'pr]
          by simp
        done
      done
    done
  subgoal
    apply (rule printer_can_print_parse_result_many)
    using assms(2) by blast
  done

\<comment> \<open>Next step: cannot be grown by outputs from self?\<close>
\<comment> \<open>Now for parsers that cannot be grown by any text.\<close>
definition parse_result_cannot_be_grown_by_printer :: "'a parser \<Rightarrow> 'b printer \<Rightarrow> bool" where
  "parse_result_cannot_be_grown_by_printer pa pr \<longleftrightarrow> (\<forall>i r l pri prt. has_result pa i r l \<and> p_has_result pr pri prt \<longrightarrow> has_result pa (i@prt) r (l@prt))"

lemma cannot_be_grown_by_when_no_peek_past:
  assumes "does_not_peek_past_end (parse A)"
  assumes "bidef_well_formed A"
  shows "parse_result_cannot_be_grown_by_printer (parse A) pB"
  unfolding parse_result_cannot_be_grown_by_printer_def
  using assms(1)[unfolded does_not_peek_past_end_def]
        assms(2)[THEN get_pngi, unfolded PNGI_def]
  by force

\<comment> \<open>This is not viable, but parse_result_cannot_be_grown_by_printer may not be needed for these cases.\<close>
\<comment> \<open>See \<^term>\<open>parser_can_parse_print_result_many\<close> below for more info. \<close>
lemma cannot_be_grown_by_when_no_peek_past3:
  assumes "\<forall>i c. first_printed_chari (print B) i c \<longrightarrow> does_not_consume_past_char3 (parse A) c"
  assumes "bidef_well_formed A"
  assumes "bidef_well_formed B"
  shows "parse_result_cannot_be_grown_by_printer (parse A) (print B)"
  unfolding parse_result_cannot_be_grown_by_printer_def
  apply auto
  subgoal for i r l pri prt
    using assms(3)[THEN get_parser_can_parse,
                   unfolded parser_can_parse_print_result_def,
                   rule_format, of pri prt]
    apply clarsimp
    apply (cases prt; clarsimp)
    subgoal for pr prs
      using assms(2)[THEN get_pngi, unfolded PNGI_def, rule_format, of i r l]
      apply clarsimp
      subgoal for c
        
        using assms(1)[rule_format, of pri,
                       unfolded first_printed_chari_def does_not_consume_past_char3_def]
        

  oops

\<comment> \<open>This should be able to be done more easily?\<close>
lemma parse_result_cannot_be_grown_by_printer_apply:
  assumes "parse_result_cannot_be_grown_by_printer pa pr"
  assumes "has_result pa i r l"
  assumes "p_has_result pr pri prt"
  shows "has_result pa (i@prt) r (l@prt)"
  using assms parse_result_cannot_be_grown_by_printer_def
  by fast


lemma cannot_be_grown_by_from_does_not_consume_and_fpci:
  assumes "\<forall>t c. first_printed_chari printer t c \<longrightarrow> does_not_consume_past_char3 parser c"
  shows "parse_result_cannot_be_grown_by_printer parser printer"
  unfolding parse_result_cannot_be_grown_by_printer_def
  apply clarsimp
  subgoal for i r l pri prt
    apply (cases prt; clarsimp) \<comment> \<open>If prt = [] then i@ptr = i and l@ptr = l, so we get it from assms.\<close>
    subgoal for p ps
      using assms[rule_format, of pri p, unfolded first_printed_chari_def, OF exI[of _ \<open>p#ps\<close>],
                  simplified, unfolded does_not_consume_past_char3_def, rule_format, of _ l r ps]
      \<comment> \<open>Note that this cannot work since cannot be grown by requires adding it to the end of the input
           and does not consume past adds it to the end of the consumed section.\<close>
      oops



\<comment> \<open>It seems reasonable to me that if a parser does not consume past it's own first char then we can get this?\<close>
\<comment> \<open>Then, if we have that, we can get wf many from does not consume past char3 from fpcpi.\<close>
\<comment> \<open>Which in turn will be usable to simplify the separated_by WF lemma.\<close>
\<comment> \<open>Especially, since intuitively separator then value should indeed not eat into itself.\<close>

lemma wf_no_empty_parse_means_no_empty_print:
  assumes "is_error (parse A) []"
  assumes "bidef_well_formed A"
  shows "\<not>p_has_result (print A) i []"
  using assms(1)[THEN is_error_implies_not_has_result]
        assms(2)[THEN get_parser_can_parse_unfold]
  by blast

lemma no_consume_past_own_first_char_parser_can_parse_print_result_many:
  assumes "is_error (parse A) []" \<comment> \<open>This is needed so that many a stops at empty input.\<close>
  assumes "bidef_well_formed A"
  assumes "\<forall>i c. first_printed_chari (print A) i c \<longrightarrow> does_not_consume_past_char3 (parse A) c"
  shows "parser_can_parse_print_result (parse (many A)) (print (many A))"
  unfolding parser_can_parse_print_result_def
  apply clarsimp
  subgoal for ts pr
    apply (induction ts arbitrary: pr)
    subgoal by (clarsimp simp add: NER_simps fp_NER assms(1))
    subgoal for t ts' pr'
      unfolding many_p_has_result_safe(2) many_has_result_safe(2)
      apply clarsimp
      subgoal for t_pr ts'_pr
        apply (rule exI[of _ ts'_pr])
        apply clarsimp \<comment> \<open>many part is dispatched by induction premise\<close>
        using assms(2)[THEN get_parser_can_parse,
                       unfolded parser_can_parse_print_result_def,
                       rule_format, of t t_pr]
        apply clarsimp \<comment> \<open>Now have that t_pr can be parsed completely into t\<close>
        apply (cases ts'_pr; clarsimp) \<comment> \<open>Case where tr'_pr =[] dispatched.\<close>
        subgoal for hd_ts'_pr tl_ts'_pr
          \<comment> \<open>Now we need to show that hd_ts'_pr is a char that parse A never eats into.\<close>
          \<comment> \<open>Since we know from the assm that the fpci of print A is never eating into by parse A.\<close>
          \<comment> \<open>We should be able to convert the fpci print A into fpci print many A and then we're done.\<close>
          using assms(3)[rule_format, of _ hd_ts'_pr,
                         unfolded does_not_consume_past_char3_def,
                         rule_format, of _ t_pr \<open>[]\<close> t tl_ts'_pr,
                         simplified]
          apply clarsimp
          \<comment> \<open>This metis does what we explain above.\<close>
          \<comment> \<open>If we ever redo this proof we should do it via ISAR.\<close>
          by (metis assms(1) assms(2)
                    empty_result_means_no_first_char
                    first_printed_chari_def
                    list.distinct(1) list.exhaust list.sel(1)
                    many_fpci_cons many_print_empty_safe(1)
                    wf_no_empty_parse_means_no_empty_print)
        done
      done
    done
  done

lemma no_consume_past_own_first_char_wf_many:
  assumes "PASI (parse A)" \<comment> \<open>This is needed so that many a stops at empty input, and for PNGI many A.\<close>
  assumes "is_error (parse A) [] \<or> \<not>is_nonterm (parse A) []" \<comment> \<open>Needed for many a stop at empty input.\<close>
  assumes "bidef_well_formed A"
  assumes "\<forall>i c. first_printed_chari (print A) i c \<longrightarrow> does_not_consume_past_char3 (parse A) c"
  shows "bidef_well_formed (many A)"
  apply wf_init
  subgoal using many_PNGI[OF assms(1)] by fast
  subgoal
    apply (rule no_consume_past_own_first_char_parser_can_parse_print_result_many)
    using assms(2,3,4) PASI_implies_error_from_empty[OF assms(1)]
    by blast+
  subgoal
    apply (rule printer_can_print_parse_result_many)
    using assms(3) by blast
  done

lemma parser_can_parse_print_result_many:
  assumes "parse_result_cannot_be_grown_by_printer (parse b) (print (many b))"
  assumes "bidef_well_formed b"
  assumes "is_error (parse b) []"
  shows "parser_can_parse_print_result (parse (many b)) (print (many b))"
  unfolding parser_can_parse_print_result_def
  apply clarsimp
  subgoal for ts pr
    apply (induction ts arbitrary: pr)
    subgoal by (clarsimp simp add: NER_simps fp_NER assms(3))
    subgoal for t ts' pr'
      unfolding many_p_has_result_safe many_has_result_safe
      apply clarsimp
      subgoal for tpr ts'pr
        apply (rule exI[where x=ts'pr])
        apply clarsimp
        \<comment> \<open>Cannot grab literal fact\<close>
        using wf_parser_can_parse_print_result_apply[OF assms(2), of t tpr]
        apply clarsimp \<comment> \<open>Succeeds in getting \<open>has_result (parse b) tpr t []\<close> into the assms\<close>
        \<comment> \<open>Cannot grab literal fact again here.\<close>
        using parse_result_cannot_be_grown_by_printer_apply[OF assms(1), of tpr t \<open>[]\<close> _ ts'pr]
        by auto
      done
    done
  done

lemma well_formed_does_not_grow_by_printer:
  assumes "parse_result_cannot_be_grown_by_printer (parse b) (print (many b))"
  assumes "bidef_well_formed b"
  assumes "is_error (parse b) []" \<comment> \<open>can get this from PASI...\<close>
  assumes "PASI (parse b)"
  shows "bidef_well_formed (many b)"
  apply wf_init
  subgoal using many_PNGI[OF assms(4)] by fast
  subgoal
    apply (rule parser_can_parse_print_result_many)
    using assms(1,2,3) by blast+
  subgoal
    apply (rule printer_can_print_parse_result_many)
    using assms(2) by blast
  done

lemma does_not_peek_past_well_formed_many:
  assumes "does_not_peek_past_end (parse A)"
  assumes "bidef_well_formed A"
  assumes "PASI (parse A)"
  assumes "\<not>is_nonterm (parse A) [] \<or> is_error (parse A) []"
  shows "bidef_well_formed (many A)"
  apply (rule well_formed_does_not_grow_by_printer)
  apply (rule cannot_be_grown_by_when_no_peek_past)
  apply (auto simp add: assms)+
  using PASI_implies_error_from_empty[OF assms(3)] assms(4)
  by blast



lemma charset_first_chars_to_parse_result_cannot_be_grown_by_printer:
  assumes "bidef_well_formed a"
  assumes "(first_chars (print b) \<inter> charset (parse a)) = {}"
  shows "parse_result_cannot_be_grown_by_printer (parse a) (print b)"
  using assms[unfolded bidef_well_formed_def parser_can_parse_print_result_def first_chars_def charset_def]
  unfolding parse_result_cannot_be_grown_by_printer_def
  apply auto
  oops


\<comment> \<open>Would be nice: cannot be grown by self implies cannot be grown by many self\<close>
\<comment> \<open> But not sure if that is realistic.\<close>

lemma cannot_be_grown_to_many:
  assumes "has_result (parse b) i r l \<and> p_has_result (print b) pri prt \<longrightarrow> has_result pa (i@prt) r (l@prt)"
  shows "has_result (parse b) i r l \<and> p_has_result (print (many b)) pris prts \<longrightarrow> has_result pa (i@prts) r (l@prts)"
  oops

lemma cannot_be_grown_to_many:
  assumes "PNGI (parse b)"
  assumes "parse_result_cannot_be_grown_by_printer (parse b) (print b)"
  shows "parse_result_cannot_be_grown_by_printer (parse b) (print (many b))"
  using assms unfolding parse_result_cannot_be_grown_by_printer_def PNGI_def
  apply clarsimp
  subgoal for i r l pri prt
    apply (induction pri arbitrary: prt)
    subgoal by (clarsimp simp add: many_p_has_result_safe(1))
    subgoal for pri1 pri' prt'
      apply (auto simp add: fp_NER NER_simps)
      
      sorry
    done
  oops



value "one_char"
value "parse one_char ''abcd''"
value "parse (b_then one_char one_char) ''abcd''"
value "parse (many (b_then one_char one_char)) ''abcde''"


end
