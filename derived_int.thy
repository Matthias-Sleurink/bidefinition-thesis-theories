theory derived_int
  imports basic_definitions
          derived_nat
          derived_this_char
begin

definition int_b :: "int bidef" where
  "int_b = transform 
                    (\<lambda>Inl i\<Rightarrow> - (int i) | Inr n \<Rightarrow> int n)
                    (\<lambda>n. if n < 0 then Inl (nat (-n)) else Inr (nat n))
                    (if_then_else
                      (this_char CHR ''-'')
                      (\<lambda>_. nat_b)
                      nat_b \<comment> \<open>else\<close>
                      (const CHR ''-''))
"
lemma some_int_b_examples:
  "has_result (parse int_b) ''12''   12   ''''"
  "has_result (parse int_b) ''12a''  12   ''a''"
  "has_result (parse int_b) ''-12'' (-12) ''''"
  "has_result (parse int_b) ''-0''   0    ''''"
  "has_result (parse int_b) ''0''    0    ''''"
  "p_has_result (print int_b) (-5) ''-5''"
  by eval+

lemma mono_int[partial_function_mono]:
  shows "mono_bd (\<lambda>f. int_b)"
  by pf_mono_prover



section NER
lemma int_b_is_nonterm[NER_simps]:
  "is_nonterm (parse int_b) i \<longleftrightarrow> False"
  by (clarsimp simp add: int_b_def NER_simps)

lemma int_b_is_error[NER_simps]:
  "is_error (parse int_b) [] \<longleftrightarrow> True"
  "is_error (parse int_b) (c#cs) \<longleftrightarrow> (c = CHR ''-'' \<and> takeWhile (\<lambda>c'. c'\<in>digit_chars) cs = []) \<or> c \<notin> ({CHR ''-''} \<union> digit_chars)"
  unfolding int_b_def
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (auto simp add: NER_simps takeWhile_hd_no_match takeWhile_eq_Nil_iff)
  done


\<comment> \<open>Would these be good in simp?\<close>
lemma exInr:
  "\<exists>r'. (\<forall>x1. r' \<noteq> Inl x1) \<and> (\<forall>x2. r' = Inr x2 \<longrightarrow> P x2) \<equiv> (\<exists>x2. P x2)"
  "\<exists>r'. (\<forall>x2. r' = Inr x2 \<longrightarrow> P x2) \<and> (\<forall>x1. r' \<noteq> Inl x1) \<equiv> (\<exists>x2. P x2)"
  by (smt (verit) Inl_Inr_False Inr_inject obj_sumE)+
lemma exInl:
  "\<exists>r'. (\<forall>x1. r' \<noteq> Inr x1) \<and> (\<forall>x2. r' = Inl x2 \<longrightarrow> P x2) \<equiv> (\<exists>x2. P x2)"
  "\<exists>r'. (\<forall>x2. r' = Inl x2 \<longrightarrow> P x2) \<and> (\<forall>x1. r' \<noteq> Inr x1) \<equiv> (\<exists>x2. P x2)"
  by (smt (verit) Inl_Inr_False Inl_inject obj_sumE)+
lemma exUnitList:
  "(\<exists>l:: unit list. length l = n \<and> P l) \<equiv> (P (replicate n ()))"
  by (smt (verit) length_replicate old.unit.exhaust replicate_length_same)
lemma exEq:
  "(\<exists>v. v = a \<and> P v) \<equiv> P a"
  by simp
lemma exId:
  "(\<exists>v. P v \<and> v = id a) \<equiv> P a"
  "(\<exists>v. P v \<and> id a = v) \<equiv> P a"
  "(\<exists>v. v = id a \<and> P v) \<equiv> P a"
  "(\<exists>v. id a = v \<and> P v) \<equiv> P a"
  by simp_all
lemmas ex_simps[simp] = exInr exInl exUnitList exEq exId

lemma remove_known_false_from_c_eq_minus:
  "(c \<in> derived_digit_char.digit_chars \<longrightarrow>
     (r = 0 \<and> c = CHR ''-'' \<longrightarrow> P) \<and> Q)
  \<equiv>
   (c \<in> derived_digit_char.digit_chars \<longrightarrow>
    (r = 0 \<and> False \<longrightarrow> P) \<and> Q)
  "
  apply auto
  by (smt (verit) char_not_in_digit_chars(10))
lemma remove_known_false_from_c_eq_minus_2:
  "(c \<in> derived_digit_char.digit_chars \<longrightarrow>
     (r = 0 \<longrightarrow> c \<noteq> CHR ''-'') \<longrightarrow>
     (r < 0 \<longrightarrow>
      (CHR ''-'' = c \<and> P ) =
      (c = CHR ''-'' \<and> P')) \<and> Q)
    \<equiv>
    (c \<in> derived_digit_char.digit_chars \<longrightarrow>
     (r = 0 \<longrightarrow> c \<noteq> CHR ''-'') \<longrightarrow>
     (r < 0 \<longrightarrow>
      (False \<and> P ) =
      (False \<and> P')) \<and> Q)"
  apply auto
  by (smt (verit, best) char_not_in_digit_chars(10))
lemma remove_known_true_from_neq_minus:
  "(c \<in> derived_digit_char.digit_chars \<longrightarrow>
     (r = 0 \<longrightarrow> c \<noteq> CHR ''-'') \<longrightarrow> P)
    \<equiv>
    (c \<in> derived_digit_char.digit_chars \<longrightarrow>
     (r = 0 \<longrightarrow> True) \<longrightarrow> P)"
  apply auto
  by (smt (verit, best) char_not_in_digit_chars(10))
lemma remove_known_false_from_eq_minus_3:
  "(c \<in> derived_digit_char.digit_chars \<longrightarrow>
     \<not> r < 0 \<longrightarrow>
     (\<exists>r'. (\<forall>x1. r' = Inl x1 \<longrightarrow>
                 CHR ''-'' = c \<and> P x1) \<and>
           (\<forall>x2. r' = Inr x2 \<longrightarrow> P' x2)) = Q)
  \<equiv>
  (c \<in> derived_digit_char.digit_chars \<longrightarrow>
     \<not> r < 0 \<longrightarrow>
     (\<exists>r'. (\<forall>x1. r' = Inl x1 \<longrightarrow>
                 False \<and> P x1) \<and>
           (\<forall>x2. r' = Inr x2 \<longrightarrow> P' x2)) = Q)"
  apply auto
  by (smt (verit) char_not_in_digit_chars(10) derived_int.ex_simps(1))

lemma int_b_has_result[NER_simps]:
  "has_result (parse int_b) []     r l \<longleftrightarrow> False"
  "has_result (parse int_b) (c#cs) r l \<longleftrightarrow> (if r < 0 then c = CHR ''-'' \<and> has_result (parse nat_b) cs (nat (-r)) l else (if r=0 \<and> c = CHR ''-'' then (has_result (parse nat_b) cs (nat r) l) else has_result (parse nat_b) (c#cs) (nat r) l))"
  "has_result (parse int_b) l r l \<longleftrightarrow> False"
  "i > 0 \<Longrightarrow> has_result (parse int_b) (print_nat (nat i)) i []"
  subgoal by (clarsimp simp add: int_b_def NER_simps split: sum.splits)
  subgoal
    apply (clarsimp simp add: int_b_def NER_simps
                       split: sum.splits)
    apply (subst remove_known_false_from_c_eq_minus)
    apply clarsimp
    apply (subst remove_known_false_from_c_eq_minus_2)
    apply clarsimp
    apply (subst remove_known_true_from_neq_minus)
    apply clarsimp
    apply (subst remove_known_false_from_eq_minus_3)
    by auto
  subgoal
    apply (clarsimp simp add: int_b_def NER_simps split: sum.splits)
    by (metis append_Cons neq_Nil_conv self_append_conv2 takeWhile_dropWhile_id)
  subgoal
    apply (auto simp add: int_b_def NER_simps dropWhile_eq_drop split: sum.splits)
    by (metis char_not_in_digit_chars(10) print_nat_hd_derived)
  done

lemma int_b_leftover_can_be_dropped:
  "has_result (parse int_b) (c @ l) r l \<Longrightarrow> has_result (parse int_b) c r []"
  apply (cases c; clarsimp)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal for c' cs
    apply (cases l; clarsimp)
    subgoal for l' ls
      apply (cases \<open>l' \<in> digit_chars\<close>; clarsimp simp add: NER_simps split: if_splits)
      by (metis dropWhile_takeWhile_same_predicate takeWhile_idem)+
    done
  done
\<comment> \<open>This is generalised below with name int_b_leftover_can_be_dropped_gen\<close>

lemma int_b_leftover_no_start_with_digit:
  "has_result (parse int_b) i r l \<longrightarrow> l = [] \<or> hd l \<notin> digit_chars"
  apply (cases i; auto simp add: NER_simps)
  by (meson dropWhile_eq_Nil_conv hd_dropWhile)+

lemma int_b_nat_with_extra_non_digit_chars:
  assumes "c \<notin> digit_chars"
  assumes "x \<ge> 0"
  shows "has_result (parse int_b) (print_nat (nat x) @ (c#cs)) x (c#cs)"
  using assms
  apply (cases \<open>print_nat (nat x)\<close>; clarsimp) \<comment> \<open>print_nat is never empty\<close>
  apply (auto simp add: NER_simps takeWhile_tail)
  subgoal by (metis nat_from_print_nat)
  subgoal by (metis list.inject print_nat_takeWhile(1) takeWhile.simps(2))
  subgoal by (metis dropWhile_append3 dropWhile_takeWhile_same_predicate self_append_conv2
                    \<open>\<And>list a. \<lbrakk>c \<notin> derived_digit_char.digit_chars; print_nat (nat x) = a # list; 0 \<le> x; a \<in> derived_digit_char.digit_chars; x \<noteq> 0\<rbrakk> \<Longrightarrow> list = takeWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars) list\<close>)
  subgoal by (metis nat_from_print_nat)
  subgoal by (metis list.inject print_nat_takeWhile(1) takeWhile.simps(2))
  subgoal by (metis append_self_conv2 dropWhile.simps(1) dropWhile_append3 list.inject nat_zero_as_int print_nat_one_chars(1)
                    \<open>\<And>list a. \<lbrakk>c \<notin> derived_digit_char.digit_chars; print_nat (nat x) = a # list; 0 \<le> x; a \<in> derived_digit_char.digit_chars; x \<noteq> 0\<rbrakk> \<Longrightarrow> c # cs = dropWhile (\<lambda>x. x \<in> derived_digit_char.digit_chars) (list @ c # cs)\<close>)
  subgoal by (metis digit_chars_def list.sel(1) print_nat_hd)
  subgoal by (metis digit_chars_def list.sel(1) print_nat_hd)
  done


section \<open>FP NER\<close>
lemma int_b_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print int_b) i \<longleftrightarrow> False"
  by (clarsimp simp add: int_b_def fp_NER)

lemma int_b_p_is_error[fp_NER]:
  "p_is_error (print int_b) i \<longleftrightarrow> False"
  by (clarsimp simp add: int_b_def fp_NER)

lemma int_b_p_has_result[fp_NER]:
  "p_has_result (print int_b) i r \<longleftrightarrow> (if i < 0 then (\<exists>r'. p_has_result (print nat_b) (nat (-i)) r' \<and> r = ''-''@r') else (p_has_result (print nat_b) (nat i) r))"
  by (clarsimp simp add: int_b_def fp_NER)

lemma int_b_print_empty[print_empty, fp_NER]:
  "p_has_result (print int_b) i [] \<longleftrightarrow> False"
  by (clarsimp simp add: fp_NER)



section \<open>PASI PNGI\<close>
lemma int_b_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  "PNGI (parse int_b)"
  by (clarsimp simp add: PASI_PNGI int_b_def)

lemma int_b_PASI[PASI_PNGI, PASI_PNGI_intros]:
  "PASI (parse int_b)"
  by (clarsimp simp add: PASI_PNGI int_b_def PASI_dep_if_then_else)



section \<open>Some more has result that uses PNGI\<close>
lemma int_b_leftover_can_be_dropped_gen:
  "has_result (parse int_b) (c @ l2) r (l@l2) \<Longrightarrow> has_result (parse int_b) c r l"
  apply (cases c; clarsimp)
  subgoal by(insert int_b_PNGI[unfolded PNGI_def, rule_format, of l2 r \<open>l@l2\<close>]; clarsimp simp add: NER_simps)
  subgoal for c' cs
    apply (cases l; clarsimp simp add: int_b_leftover_can_be_dropped)
    subgoal for l' ls
      apply (cases \<open>l' \<in> digit_chars\<close>; clarsimp simp add: NER_simps split: if_splits)
      subgoal by (metis dropWhile_eq_Cons_conv)
      subgoal by (metis dropWhile_eq_Cons_conv)
      subgoal by (metis dropWhile_eq_Cons_conv)
      subgoal by (metis (no_types, lifting) append_is_Nil_conv dropWhile_eq_Cons_conv takeWhile_tail)
      subgoal by (metis (no_types, lifting) dropWhile_eq_Cons_conv takeWhile_eq_Nil_iff takeWhile_tail)
      subgoal by (metis dropWhile_eq_Cons_conv takeWhile_tail)
      done
    done
  done



section \<open>Does not peek past end\<close>
lemma int_b_does_not_peek_past_end[peek_past_end_simps]:
  shows "does_not_peek_past_end (parse int_b) \<longleftrightarrow> False"
  unfolding does_not_peek_past_end_def
  apply clarsimp
  apply (rule exI[of _ \<open>''1''\<close>]; rule exI[of _ \<open>1\<close>])
  apply (rule conjI)
  subgoal by (rule exI[of _ \<open>[]\<close>]; clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>''1''\<close>]; clarsimp simp add: NER_simps)
  done



section \<open>Does not consume past char\<close>
lemma int_b_does_not_consume_past_char3:
  assumes "ch \<notin> digit_chars"
  shows "does_not_consume_past_char3 (parse int_b) ch"
  unfolding does_not_consume_past_char3_def
  apply auto
  subgoal by (rule int_b_leftover_can_be_dropped)
  subgoal for c r l l'
    using assms apply cleaning
    apply (cases c; clarsimp)
    subgoal by (clarsimp simp add: NER_simps)
    subgoal for c' cs
      apply (cases l; clarsimp)
      subgoal by (clarsimp simp add: NER_simps dropWhile_eq_drop takeWhile_tail split: if_splits)
      subgoal for lhd ls
        apply (clarsimp simp add: NER_simps split: if_splits)
        subgoal by (metis (no_types, lifting) dropWhile_eq_Cons_conv takeWhile_tail)
        subgoal by (metis (no_types, lifting) dropWhile_eq_Cons_conv takeWhile_tail)
        subgoal by (metis (no_types, lifting) dropWhile_eq_Cons_conv takeWhile_tail)
        done
      done
    done
  done



section \<open>First Printed/Parsed char\<close>
lemma int_b_fpci[fpci_simps]:
  shows "first_printed_chari (print int_b) i c \<longleftrightarrow> (if i < 0 then c = CHR ''-'' else c = hd (print_nat (nat i)))"
  unfolding first_printed_chari_def
  by (auto simp add: fp_NER)

lemma cases_in_digit_chars:
  assumes "c \<in> derived_digit_char.digit_chars"
  shows "c = CHR ''0'' \<or> c = CHR ''1'' \<or> c = CHR ''2'' \<or> c = CHR ''3'' \<or> c = CHR ''4'' \<or> c = CHR ''5'' \<or> c = CHR ''6'' \<or> c = CHR ''7'' \<or> c = CHR ''8'' \<or> c = CHR ''9''"
  using assms unfolding digit_chars_def
  by (smt (z3) char.simps(1) digit_chars_def insertE singletonD)

lemma first_char_not_zero:
  assumes "c \<noteq> CHR ''0''"
  shows "nat_from (c#cs) \<noteq> 0"
  using assms
  apply (induction cs rule: rev_induct; clarsimp)
  subgoal by (cases c rule: digit_char_to_nat.cases; clarsimp)
  subgoal for c' cs
    apply (subst nat_from.simps(2))
    by auto
  done

lemma l_eq_cons:
  "l = (c#cs) \<Longrightarrow> hd l = c"
  by simp

lemma int_b_fpc[fpc_simps]:
  shows "fpc (parse int_b) i c \<longleftrightarrow> (if i < 0 then c = CHR ''-'' else (if i = 0 then (c = CHR ''-'' \<or> c = hd (print_nat (nat i)) \<or> c = CHR ''0'') else (c = hd (print_nat (nat i)) \<or> c = CHR ''0'')))"
  unfolding fpc_def
  apply auto
  subgoal by (clarsimp simp add: NER_simps first_char_not_zero split: if_splits)
  subgoal by (rule exI[of _ \<open>''0''\<close>]; rule exI[of _ \<open>''''\<close>]; clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>''''\<close>]; rule exI[of _ \<open>''''\<close>]; clarsimp simp add: NER_simps)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>print_nat (nat (-i))\<close>]; rule exI[of _ \<open>''''\<close>]; clarsimp simp add: NER_simps dropWhile_eq_drop)
  subgoal for cs l
    apply (clarsimp simp add: NER_simps split: if_splits)
    apply (subst print_nat_nat_from[of \<open>c#cs\<close>, OF list.simps(3), THEN l_eq_cons])
    subgoal by (metis (no_types, lifting) digit_chars_def insert_iff list.simps(15) subsetI takeWhile_append1 takeWhile_eq_all_conv)
    subgoal by simp
    subgoal by blast
    done
  subgoal by (rule exI[of _ \<open>tl (print_nat (nat i))\<close>]; rule exI[of _ \<open>''''\<close>]; clarsimp simp add: NER_simps)
  subgoal by (rule exI[of _ \<open>print_nat (nat i)\<close>]; rule exI[of _ \<open>''''\<close>]; clarsimp simp add: NER_simps dropWhile_eq_drop nat_from_cons_zero)
  done



section \<open>Well Formed\<close>
lemma hd_of_print_nat_not_minus:
  "hd (print_nat i) = CHR ''-'' \<longleftrightarrow> False"
  by (metis char_not_in_digit_chars(10) print_nat_hd_derived)


lemma int_b_well_formed:
  "bidef_well_formed int_b"
  apply (auto intro!: transform_well_formed3 if_then_else_well_formed
            simp add: int_b_def this_char_well_formed nat_b_well_formed
                      b2_wf_for_res_of_b1_def
                      b2_res_trans_is_b1_res_def NER_simps
                      b1_cannot_parse_b3_print_result_def fp_NER hd_of_print_nat_not_minus
                      b1_then_b2_print_parse_loop_def
                      basic_dependent_if_then_else.pa_does_not_eat_into_pb_def)
  subgoal
    unfolding well_formed_transform_funcs3_def
    apply (auto simp add: NER_simps fp_NER dropWhile_eq_drop split: sum.splits)
    apply (rule exI[of _ \<open>[]\<close>]; clarsimp)
    subgoal for t by (rule exI[of _ \<open>Inr (nat t)\<close>]; clarsimp simp add: hd_of_print_nat_not_minus)
    done
  done

lemma int_does_not_eat_into_if_first_char_not_digit:
  assumes "\<forall>d \<in> digit_chars. \<nexists>i. first_printed_chari (print A) i d"
  shows "pa_does_not_eat_into_pb_nondep int_b A"
  unfolding pa_does_not_eat_into_pb_nondep_def
  using assms unfolding first_printed_chari_def
  apply clarsimp
  by (metis digit_chars_eq_digit_chars int_b_does_not_consume_past_char3
            int_b_well_formed no_consume_past3_wf_stronger self_append_conv wf_parser_can_parse_print_result_apply)






end