theory basic_m_map
  imports types
begin

\<comment> \<open>THEORY: It seems like it should be possible to derive this from dep_then?\<close>

fun mmap :: "('\<alpha> \<Rightarrow> '\<beta> parser) \<Rightarrow> '\<alpha> list \<Rightarrow> '\<beta> list parser" where
  "mmap _ []     i = terminate_with (Some ([], i))"
| "mmap f (x#xs) i = (
    case f x i of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some (r, l)) \<Rightarrow> (
      case mmap f xs l of
        None \<Rightarrow> None
      | Some None \<Rightarrow> Some None
      | Some (Some (r', l')) \<Rightarrow> (
          terminate_with (Some (r#r', l'))
)))"
print_theorems



fun m_map_pr :: "('\<alpha> \<Rightarrow> '\<beta> printer) \<Rightarrow> '\<alpha> list \<Rightarrow> '\<beta> list printer" where
  "m_map_pr _      []     []     = Some (Some [])"
| "m_map_pr _      []     (b#bs) = Some None"
| "m_map_pr _      (a#as) []     = Some None"
| "m_map_pr a2_bfp (a#as) (b#bs) = (
    case a2_bfp a b of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some r) \<Rightarrow> (
      case m_map_pr a2_bfp as bs of
        None \<Rightarrow> None
      | Some None \<Rightarrow> Some None
      | Some (Some rs) \<Rightarrow> Some (Some (r@rs))
))"

definition m_map :: "('\<alpha> \<Rightarrow> '\<beta> bidef) \<Rightarrow> '\<alpha> list \<Rightarrow> '\<beta> list bidef" where
  "m_map a2b_tri as = bdc
    (mmap (\<lambda>a. parse (a2b_tri a)) as)
    (m_map_pr (\<lambda>a. print (a2b_tri a)) as)
"

lemma mono_m_map[partial_function_mono]:
  assumes ma: "\<And>p. mono_bd (A p)"
  shows "mono_bd (\<lambda>f. m_map (\<lambda>p. A p f) ps)"
  apply (rule monotoneI)
  using ma
  apply (induction ps)
  subgoal unfolding m_map_def
    unfolding bd_ord_def fun_ord_def flat_ord_def monotone_def
    apply auto
    by (metis list.exhaust_sel m_map_pr.simps(1) m_map_pr.simps(2))
  subgoal for e es x y unfolding m_map_def
    unfolding bd_ord_def fun_ord_def flat_ord_def monotone_def
    apply (auto split: option.splits)
    subgoal by (smt (verit, ccfv_threshold) option.distinct(1))
    subgoal by (smt (verit, ccfv_threshold) option.sel option.simps(3))
    subgoal by (smt (verit, del_insts) option.distinct(1) option.inject)
    subgoal by (smt (verit, del_insts) option.distinct(1) option.inject)
    subgoal
      \<comment> \<open>Sledgehammer generates a few proofs here that always time out.\<close>
      sorry
    subgoal
      \<comment> \<open>Sledgehammer generates one proof here that always times out.\<close>
      sorry
    subgoal  sorry
    subgoal  sorry
    subgoal  sorry
    subgoal  sorry
    subgoal  sorry
    subgoal  sorry
    subgoal  sorry
    subgoal  sorry
    done
  oops



lemma m_map_is_nonterm[NER_simps]:
  "is_nonterm (parse (m_map tc []    )) i \<longleftrightarrow> False"
  "is_nonterm (parse (m_map tc (a#as))) i \<longleftrightarrow> is_nonterm (parse (tc a)) i \<or>
                            (\<exists> r l. has_result (parse (tc a)) i r l \<and> is_nonterm (parse (m_map tc as)) l)"
  by (simp add: m_map_def is_nonterm_def has_result_def split: option.splits)+

lemma mmap_not_nonterm_if_param_never_nonterm:
  assumes "\<forall>x s. \<not>is_nonterm (p x) s"
  shows "\<not>is_nonterm (mmap p l) s"
  using assms
  apply (induction l arbitrary: s)
  subgoal (* [] *) by (simp add: is_nonterm_def)
  subgoal for a as s
    apply (unfold mmap.simps(2))
    apply (unfold is_nonterm_def)
    apply (cases \<open>p a s\<close>)
    subgoal (* p a s = None *) by blast
    subgoal for res (* p a s = Some res *)
      apply (cases res)
      subgoal (* p a s = Some None *) by auto
      subgoal for rl (* p a s = Some Some rl *)
        apply (cases \<open>mmap p as (snd rl)\<close>)
        subgoal (* mmap p as (snd rl) = None *) by blast
        by (simp add: case_prod_unfold option.case_eq_if)
      done
    done
  done



lemma mmap_not_nonterm_if_param_never_nonterm2:
  assumes "\<forall>x \<in> set l . \<forall> s. \<not>is_nonterm (p x) s"
  shows "\<not>is_nonterm (mmap p l) s"
  using assms
  apply (induction l arbitrary: s)
  subgoal (* [] *) by (simp add: is_nonterm_def)
  subgoal for a as s
    apply (unfold mmap.simps(2))
    apply (unfold is_nonterm_def)
    apply (cases \<open>p a s\<close>)
    subgoal (* p a s = None *) by (meson list.set_intros(1))
    subgoal for res (* p a s = Some res *)
      apply (cases res)
      subgoal (* p a s = Some None *) by auto
      subgoal for rl (* p a s = Some Some rl *)
        apply (cases \<open>mmap p as (snd rl)\<close>)
        subgoal (* mmap p as (snd rl) = None *) by (meson list.set_intros(2))
        by (simp add: case_prod_unfold option.case_eq_if)
      done
    done
  done


lemma m_map_is_error[NER_simps]:
  "is_error (parse (m_map tc []    )) i \<longleftrightarrow> False"
  "is_error (parse (m_map tc (a#as))) i \<longleftrightarrow> is_error (parse (tc a)) i \<or>
                          (\<exists> r l. has_result (parse (tc a)) i r l \<and> is_error (parse (m_map tc as)) l)"
  by (simp add: m_map_def is_error_def has_result_def split: option.splits)+

lemma m_map_has_result[NER_simps]:
  "has_result (parse (m_map tc []    )) i r l \<longleftrightarrow> i = l \<and> r = []"
  "has_result (parse (m_map tc (a#as))) i r l \<longleftrightarrow> (\<exists> r' l' rs. has_result (parse (tc a)) i r' l' \<and>
                                                        has_result (parse (m_map tc as)) l' rs l \<and>
                                                        r = r'#rs)"
  by (auto simp add: m_map_def has_result_def split: option.splits)+

\<comment> \<open>has_result_c for m_map depends on PNGI m_map, so it's below that proof\<close>



lemma m_map_has_result_same_length:
  "has_result (parse (m_map tc as)) i r l \<Longrightarrow> length as = length r"
  by (induction as arbitrary: i r l) (auto simp add: NER_simps)

lemma m_map_has_result_not_same_length:
  "length as \<noteq> length r \<Longrightarrow> \<not>has_result (parse (m_map tc as)) i r l"
  by (induction as arbitrary: i r l) (auto simp add: NER_simps)


lemma m_map_has_result_rev[NER_simps]:
  "has_result (parse (m_map tc (as@[a]))) i r l \<longleftrightarrow> (\<exists> rs r' l'. has_result (parse (m_map tc as)) i rs l' \<and>
                                                                 has_result (parse (tc a)) l' r' l \<and>
                                                                 r = rs@[r'])"
  apply (induction as arbitrary: i r l)
  subgoal by (clarsimp simp add: NER_simps)
  subgoal for hd_as tl_as i' r' l'
    apply auto
    subgoal
      apply (rule exI[of _ \<open>butlast r'\<close>])
      apply (rule exI[of _ \<open>last r'\<close>])
      apply (auto simp add: m_map_has_result(2))
      by blast
    subgoal for r'' r_a l''
      apply (auto simp add: NER_simps)
      by blast
    done
  done



\<comment> \<open>FP_ner\<close>
lemma m_map_p_is_error[fp_NER]:
  "p_is_error (print (m_map bc [])) i \<longleftrightarrow> i \<noteq> []"
  "p_is_error (print (m_map bc (a#as))) i \<longleftrightarrow> (\<exists>i' is ir. i=[] \<or> (i = i'#is \<and>
                                                       (p_is_error (print (bc a)) i' \<or>
                                                        (p_has_result (print (bc a)) i' ir \<and>
                                                         p_is_error (print (m_map bc as)) is))))"
  apply (induction i)
  by (auto simp add: p_is_error_def p_has_result_def m_map_def split: option.splits)

lemma m_map_p_has_result[fp_NER]:
  "p_has_result (print (m_map bc []))     i t \<longleftrightarrow> i = [] \<and> t = []"
  "p_has_result (print (m_map bc (a#as))) i t \<longleftrightarrow> (\<exists> i' is t' ts . p_has_result (print (bc a)) i' t' \<and>
                                                        p_has_result (print (m_map bc as)) is ts \<and>
                                                        i = i'#is \<and> t = t'@ts)"
  apply (induction i)
  apply (auto simp add: p_has_result_def m_map_def split: option.splits)
  by fastforce+

lemma m_map_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (m_map bc [])) i \<longleftrightarrow> False"
  "p_is_nonterm (print (m_map bc (a#as))) i \<longleftrightarrow> (\<exists>i' is ir. i = i'#is \<and>
                                                       (p_is_nonterm (print (bc a)) i' \<or>
                                                        (p_has_result (print (bc a)) i' ir \<and>
                                                         p_is_nonterm (print (m_map bc as)) is)))"
  apply (induction i)
  by (auto simp add: m_map_def p_has_result_def p_is_nonterm_def split: option.splits)

lemma m_map_p_has_result_same_length:
  "p_has_result (print (m_map bc as)) is t \<Longrightarrow> length as = length is"
  by (induction as arbitrary:  \<open>is\<close> t) (auto simp add: fp_NER)

lemma m_map_pr_has_result_not_same_length:
  "length as \<noteq> length is \<Longrightarrow> \<not>p_has_result (print (m_map bc as)) is t"
  "length as \<noteq> length is \<Longrightarrow> p_is_error (print (m_map bc as)) is \<or> p_is_nonterm (print (m_map bc as)) is"
  apply (induction as arbitrary: \<open>is\<close> t)
     apply (auto simp add: fp_NER)
  by (metis length_Cons list.exhaust p_has_result_eq_not_is_error)

lemma m_map_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (m_map a2A []    )) []     [] \<longleftrightarrow> True"
  "p_has_result (print (m_map a2A (a#as))) (i#is) [] \<longleftrightarrow> p_has_result (print (a2A a)) i [] \<and> p_has_result (print (m_map a2A as)) is []"
  by (clarsimp simp add: fp_NER)+

lemma m_map_print_empty:
  "p_has_result (print (m_map a2A as)) is [] \<longleftrightarrow>(
    case as of
      [] \<Rightarrow> is=[]
    | (a#as') \<Rightarrow> (
      case is of [] \<Rightarrow> False | (i#is') \<Rightarrow>
        p_has_result (print (a2A a)) i [] \<and> p_has_result (print (m_map a2A as')) is' []
      ))"
  by (auto simp add: fp_NER split: list.splits)



\<comment> \<open>PNGI, PASI\<close>
lemma PNGI_m_map[PASI_PNGI, PASI_PNGI_intros]:
  assumes "\<forall>e\<in>set l. PNGI (parse (b e))"
  shows "PNGI (parse (m_map b l))"
  using assms
  apply (induction l)
  unfolding PNGI_def
  apply (auto simp add: NER_simps)
  by fastforce

lemma PNGI_m_map_all[PASI_PNGI]:
  assumes "\<And>e. PNGI (parse (b e))"
  shows "PNGI (parse (m_map b l))"
  using assms
  apply (induction l)
  unfolding PNGI_def
  apply (auto simp add: NER_simps)
  by fastforce

lemma PASI_m_map[PASI_PNGI, PASI_PNGI_intros]:
  assumes "\<forall>e\<in>set l. PASI (parse (b e))"
  assumes "l \<noteq> []"
  shows "PASI (parse (m_map b l))"
  using assms
  apply (induction l)
  unfolding PASI_def
  apply (auto simp add: NER_simps)
  by (metis (no_types, lifting) Nil_is_append_conv append.assoc m_map_has_result(1))




lemma m_map_has_result_c[NER_simps]:
  assumes "\<forall>a' \<in>set (a#as). PNGI (parse (tc a'))"
  shows 
  "has_result_c (parse (m_map tc []    )) c r l \<longleftrightarrow> c = [] \<and> r = []"
  "has_result_c (parse (m_map tc (a#as))) c r l \<longleftrightarrow> (\<exists> r' rs c' c''. c = c'@c'' \<and>
                                                       has_result_c (parse (tc a)) c' r' (c''@l) \<and>
                                                       has_result_c (parse (m_map tc as)) c'' rs l \<and>
                                                       r = r'#rs)"
  apply (auto simp add: has_result_c_def NER_simps split: option.splits)+
  subgoal for r' l' rs
    \<comment> \<open>l' = c'' @ l\<close>
    \<comment> \<open>c'@c''@l = c@l, so: c = c' @ c''\<close>
    \<comment> \<open>want to do exI with 'c' = c@l `upto` l'\<close>
    apply (rule exI[of _ \<open>list_upto (c@l) l'\<close>])
    using assms(1)[unfolded PNGI_def, rule_format, of a \<open>c@l\<close> r' l', OF list.set_intros(1)]
    using list_upto_take_cons[of \<open>c@l\<close> l' ]
    apply clarsimp
    subgoal for ca
      apply (rule exI[of _ \<open>drop (length ca) c\<close>])
      apply auto
      subgoal
        by (metis (no_types, lifting) PNGI_def PNGI_m_map append.assoc append_eq_conv_conj append_same_eq assms in_mono set_subset_Cons)
      subgoal
        by (metis \<open>\<lbrakk>has_result (parse (tc a)) (ca @ l') r' l'; has_result (parse (m_map tc as)) l' rs l; r = r' # rs; list_upto (ca @ l') l' = ca; c @ l = ca @ l'\<rbrakk> \<Longrightarrow> c = ca @ drop (length ca) c\<close>
                  append_eq_appendI same_append_eq)
      subgoal
        by (metis \<open>\<lbrakk>has_result (parse (tc a)) (ca @ l') r' l'; has_result (parse (m_map tc as)) l' rs l; r = r' # rs; list_upto (ca @ l') l' = ca; c @ l = ca @ l'\<rbrakk> \<Longrightarrow> c = ca @ drop (length ca) c\<close>
                  append_eq_appendI same_append_eq)
      done
    done
  done

lemma m_map_has_result_ci[NER_simps]:
  assumes "\<forall>a' \<in>set (a#as). PNGI (parse (tc a'))"
  shows 
  "has_result_ci (parse (m_map tc []    )) i c r l \<longleftrightarrow> c = [] \<and> r = [] \<and> l = i"
  "has_result_ci (parse (m_map tc (a#as))) i c r l \<longleftrightarrow> (\<exists> r' rs c' c''. c = c'@c'' \<and>
                                                       has_result_ci (parse (tc a))        i       c'  r' (c''@l) \<and>
                                                       has_result_ci (parse (m_map tc as)) (c''@l) c'' rs l \<and>
                                                       r = r'#rs)"
  subgoal by (auto simp add: has_result_ci_def has_result_c_def NER_simps)
  apply (auto simp add: has_result_ci_def has_result_c_def NER_simps)
  by (metis PNGI_def PNGI_m_map append.assoc append_same_eq assms list.set_intros(1) list.set_intros(2))



\<comment> \<open>Does not peek past end\<close>
lemma m_map_does_not_peek_past_end[peek_past_end_simps]:
  assumes "\<And>a. PNGI (parse (e2b a))"                      \<comment> \<open>TODO: constrain this to a\<in>as?\<close>
  assumes "\<And>a. does_not_peek_past_end (parse (e2b a))"    \<comment> \<open>TODO: constrain this to a\<in>as?\<close>
  shows "does_not_peek_past_end (parse (m_map e2b as))"
  using assms(1, 2) unfolding does_not_peek_past_end_def
  apply (induction as; clarsimp simp add: NER_simps)
  \<comment> \<open>This ISAR proof transplanted from and name-fixed from the sledgehammer generated proof at\<close>
  \<comment> \<open>then_does_not_peek_past_end (which is not in scope here)\<close>
  proof -
    fix a as c l r' l' l'a rs
    assume dnppe_induct: "\<forall>c r. (\<exists>l. has_result (parse (m_map e2b as)) (c @ l) r l) \<longrightarrow> (\<forall>l'. has_result (parse (m_map e2b as)) (c @ l') r l')"
    assume hr_A: "has_result (parse (e2b a)) (c @ l) r' l'"
    assume hr_B: "has_result (parse (m_map e2b as)) l' rs l"
    have f3: "\<forall>cs csa csb csc. (cs::char list) @ csb @ csa \<noteq> csc @ csa \<or> cs @ csb = csc"
      by auto
    obtain ccsa :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
       f5: "c @ l = ccsa l' (c @ l) @ l'"
      using hr_A by (meson assms(1)[unfolded PNGI_def])
    obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list" where
      f4: "l' = ccs l l' @ l"
      using hr_B by (meson PNGI_def PNGI_m_map[of as e2b] assms(1))
    have "\<forall>cs csa. cs @ l \<noteq> csa @ l' \<or> csa @ ccs l l' = cs"
      using f4 f3 by metis
    then have "\<forall>cs. ccsa l' (c @ l) @ ccs l l' @ cs = c @ cs"
      using f5 append_eq_appendI by blast
    then show "\<exists>cs. has_result (parse (e2b a)) (c @ l'a) r' cs \<and> has_result (parse (m_map e2b as)) cs rs l'a"
      using f4 hr_B hr_A dnppe_induct
      by (metis assms(2)[unfolded does_not_peek_past_end_def])
  qed



\<comment> \<open>First printed char\<close>
lemma m_map_fpci_empty[fpci_simps]:
  shows "\<not>first_printed_chari (print (m_map e2A [])) i c"
  unfolding first_printed_chari_def
  by (auto simp add: m_map_p_has_result)

lemma m_map_fpci_cons:
  assumes "first_printed_chari (print (e2A e)) i c"
  assumes "\<exists>ts. p_has_result (print (m_map e2A es)) is ts"
  shows "first_printed_chari (print (m_map e2A (e#es))) (i#is) c"
  using assms unfolding first_printed_chari_def
  apply (auto simp add: m_map_p_has_result)
  by fastforce

lemma m_map_fpci_cons_empty:
  assumes "p_has_result (print (e2A e)) i []"
  assumes "first_printed_chari (print (m_map e2A es)) is c"
  shows "first_printed_chari (print (m_map e2A (e#es))) (i#is) c"
  using assms unfolding first_printed_chari_def
  apply (auto simp add: m_map_p_has_result)
  by fast


lemma m_map_fpci_cons_iff[fpci_simps]:
  shows "first_printed_chari (print (m_map e2A (e#es))) (i#is) c \<longleftrightarrow>(
          if p_has_result (print (e2A e)) i [] then
            (first_printed_chari (print (m_map e2A es)) is c)
          else
            ((\<exists>t. p_has_result (print (m_map e2A es)) is t) \<and> first_printed_chari (print (e2A e)) i c)
)"
  unfolding first_printed_chari_def
  apply (auto simp add: m_map_p_has_result)
  subgoal by (simp add: p_has_result_deterministic)
  subgoal by (metis append_Nil p_has_result_deterministic)
  subgoal by fast
  subgoal by (metis hd_append)
  subgoal by fastforce
  done

lemma m_map_fpc_nil[fpc_simps]:
  shows "fpc (parse (m_map a2B [])) i c \<longleftrightarrow> False"
  unfolding fpc_def m_map_has_result
  by clarsimp

lemma m_map_fpc_cons[fpc_simps]:
  assumes "\<And>i. PNGI (parse (a2B i))"
  shows "fpc (parse (m_map a2B (a#as))) (i#is) c \<longleftrightarrow>(
      if (\<exists>l. has_result (parse (a2B a)) (c#l) i (c#l)) then
        (fpc (parse (m_map a2B as)) is c)
      else
        (fpc (parse (a2B a)) i c)
)"
  unfolding fpc_def m_map_has_result PNGI_def
  apply auto
  subgoal for l cs l' l''
    apply (rule exI[of _ cs])
    apply (rule exI[of _ l'])
    using PNGI_m_map_all[OF assms(1), of id as, simplified, unfolded PNGI_def]
    
    sorry
  subgoal  sorry
  subgoal  sorry
  subgoal  sorry
  oops


lemma m_map_fpc_cons[fpc_simps]:
  assumes "\<And>i. PNGI (parse (a2B i))"
  shows "fpc (parse (m_map a2B (a#as))) (i#is) c \<longleftrightarrow> test"
  unfolding fpc_def m_map_has_result(2)
  oops



\<comment> \<open>well formed\<close>
lemma m_map_well_formed_empty[bi_well_formed_simps]:
  shows "bidef_well_formed (m_map a2bi [])"
  apply wf_init
  unfolding parser_can_parse_print_result_def printer_can_print_parse_result_def
  by (auto simp add: fp_NER NER_simps PNGI_m_map)+

lemma m_map_well_formed_one[bi_well_formed_simps]:
  assumes "bidef_well_formed (a2bi x)"
  shows "bidef_well_formed (m_map a2bi [x])"
  using assms PNGI_m_map
  unfolding bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
            m_map_has_result \<comment> \<open>Due to these being stuck in Ex we cannot unfold normally.\<close>
            m_map_p_has_result
  by (metis list.discI list.set_cases self_append_conv set_ConsD)

(*
lemma m_map_well_formed_two[bi_well_formed_simps]:
  assumes "bidef_well_formed (a2bi x)"
  assumes "bidef_well_formed (a2bi x')"
  assumes "well_formed_then_pair (a2bi x) (a2bi x')"
  shows "bidef_well_formed (m_map a2bi [x, x'])"
  using assms
  unfolding bidef_well_formed_def parser_can_parse_print_result_def printer_can_print_parse_result_def
            well_formed_then_pair_def
            m_map_has_result \<comment> \<open>Due to these being stuck in Ex we cannot unfold normally.\<close>
            m_map_p_has_result
  by fastforce

lemma  well_formed_then_pair_m_map_empty[bi_well_formed_simps]:
  assumes "bidef_well_formed b1"
  shows "well_formed_then_pair b1 (m_map a2bi [])"
  using assms
  unfolding bidef_well_formed_def parser_can_parse_print_result_def
            well_formed_then_pair_def
            m_map_def
  apply (auto simp add: NER_simps fp_NER)
  subgoal
    by (metis append.right_neutral m_map_def m_map_p_has_result(1) snd_conv)
  by (metis m_map_def m_map_p_has_result(1) snd_conv)

lemma  well_formed_then_pair_m_map_one[bi_well_formed_simps]:
  assumes "well_formed_then_pair b1 (a2bi x)"
  shows "well_formed_then_pair b1 (m_map a2bi [x])"
  using assms
  unfolding well_formed_then_pair_def
  by (clarsimp simp add: fp_NER NER_simps)

lemma  well_formed_then_pair_m_map_all[bi_well_formed_simps]:
  assumes "well_formed_then_pair b1 (a2bi x)"
  assumes "bidef_well_formed (m_map a2bi (x#xs))"
  shows "well_formed_then_pair b1 (m_map a2bi (x#xs))"
  supply [[show_types=false]]
  unfolding well_formed_then_pair_def
  using assms(2)[unfolded bidef_well_formed_def parser_can_parse_print_result_def]
  using assms(1)[unfolded well_formed_then_pair_def]
  apply clarsimp
  subgoal for v1 v2 pr1 pr2
    oops


lemma m_map_well_formed_induct_step2[bi_well_formed_simps]:
  assumes "bidef_well_formed (a2bi x)"
  assumes "bidef_well_formed (m_map a2bi xs)"
  assumes "well_formed_then_pair (a2bi x) (m_map a2bi xs)"
    \<comment> \<open>to handle this case it would be nice if we could get a helper that does
        well_formed_then_pair for m_map => well formed then pair for first element of (or empty)\<close>
  shows "bidef_well_formed (m_map a2bi (x#xs))"
  apply bidef_init
  subgoal 
    using assms(3)
    unfolding parser_can_parse_print_result_def
              well_formed_then_pair_def
    apply (clarsimp simp add: NER_simps fp_NER)
    apply (unfold m_map_has_result(2)[of a2bi x xs])
    by fast
  subgoal
    using assms(1, 2)
    unfolding bidef_well_formed_def printer_can_print_parse_result_def
    apply (clarsimp simp add: NER_simps)
    apply (unfold m_map_p_has_result(2))
    by blast
  done
  
  


lemma m_map_well_formed_induct_step:
  assumes "bidef_well_formed (m_map a2bi (x'#xs))"
  assumes "bidef_well_formed (a2bi x)"
  assumes "well_formed_then_pair (a2bi x) (a2bi x')"
  shows "bidef_well_formed (m_map a2bi (x#x'#xs))"
  apply bidef_init
  supply [[show_types=false]]
  subgoal
    using assms
    unfolding parser_can_parse_print_result_def bidef_well_formed_def well_formed_then_pair_def
    apply clarsimp
    apply (induction xs arbitrary: x x')
    subgoal for t pr x x'
      apply (unfold m_map_has_result(2)[of a2bi x \<open>[x']\<close> pr t]) \<comment> \<open>the of here prevents unfolding in asm\<close>
      apply (unfold m_map_has_result(2)[of a2bi x' \<open>[]\<close>])
      apply (clarsimp simp add: NER_simps fp_NER)
      by blast
    subgoal for a xs t pr x x'
      \<comment> \<open>Super akward way of using the power of unfold to unfold in the rhs, and then un-unfold in the asm\<close>
      apply (unfold m_map_has_result(2))
      apply (subst (asm) m_map_has_result(2)[symmetric])
      unfolding m_map_p_has_result(2)
      apply (clarsimp simp add: NER_simps fp_NER)
    
      sorry
    done
  subgoal
    using assms
    unfolding printer_can_print_parse_result_def bidef_well_formed_def well_formed_then_pair_def
    apply (auto simp add: NER_simps fp_NER)
    apply (unfold m_map_p_has_result(2))
    by fast
  oops


lemma m_map_well_formed_nonempty[bi_well_formed_simps]:
  assumes "\<forall>x \<in> set xs. bidef_well_formed (a2bi x)"
  assumes "\<forall>x. bidef_well_formed (a2bi x)" \<comment> \<open>This should be removed when we learn how to induct inside the set.\<close>
  \<comment> \<open>It would really be best if we could do this in order, as this is too strong\<close>
  assumes "\<forall>e1 \<in> set xs. \<forall>e2\<in> set xs. well_formed_then_pair (a2bi e1) (a2bi e2)"
  assumes "\<forall>e1 e2. well_formed_then_pair (a2bi e1) (a2bi e2)"
  shows "bidef_well_formed (m_map a2bi xs)"
  apply (induction xs)
  subgoal by (rule m_map_well_formed_empty)
  apply (subst bidef_well_formed_def)
  apply (rule conjI)
  subgoal for x xs
    apply (subst parser_can_parse_print_result_def)
    apply (subst m_map_p_has_result(2))
    apply (unfold m_map_has_result(2))
    apply clarsimp
    using assms
    unfolding bidef_well_formed_def parser_can_parse_print_result_def well_formed_then_pair_def
    \<comment> \<open>The first issue I see here, there will be more later, is that I don't know how to induct inside a set.\<close>
    \<comment> \<open>How do I induct inside a set?\<close>
    sorry
  subgoal for x xs
    using assms(2)
    apply (subst printer_can_print_parse_result_def)
    apply (unfold m_map_p_has_result(2))
    apply (unfold m_map_has_result(2))
    apply clarsimp
    by (metis bidef_well_formed_def printer_can_print_parse_result_def)
  oops
*)

end