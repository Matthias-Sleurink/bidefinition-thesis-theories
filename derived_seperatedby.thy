theory derived_seperatedby
  imports basic_definitions
          derived_many
          derived_optional
begin

definition seperatedByBase :: "'b bd \<Rightarrow> 'a bd \<Rightarrow> ('a \<times> ('b \<times> 'a) list) bd" where
  "seperatedByBase sep elem = b_then elem (many (b_then sep elem))"

definition seperatedBy :: "'b bd \<Rightarrow> 'a bd \<Rightarrow> 'b \<Rightarrow> 'a list bd" where
  "seperatedBy sep elem sep_oracle =
      transform
         \<comment> \<open>('a \<times> ('b \<times> 'a) list) option \<Rightarrow> 'a list\<close>
        (\<lambda>m_al. case m_al of None \<Rightarrow> [] | Some (a, l) \<Rightarrow> a#(map snd l))
        \<comment> \<open>'a list \<Rightarrow> ('a \<times> ('b \<times> 'a) list) option\<close>
        (\<lambda>l. case l of [] \<Rightarrow> None | (a#as) \<Rightarrow> Some (a, map (Pair sep_oracle) as))
        \<comment> \<open>('a \<times> ('b \<times> 'a) list) option bd\<close>
        (optional (seperatedByBase sep elem))
"



definition good_seperatedBy_oracle :: "'a bidef \<Rightarrow> 'a \<Rightarrow> bool" where
  "good_seperatedBy_oracle sep oracle \<longleftrightarrow> (\<exists>r. p_has_result (print sep) oracle r)"



\<comment> \<open>NER\<close>
\<comment> \<open>Unsatisfying, should create also sep ~= nonterm, elem ~= nonterm, and both ~= nonterm cases\<close>
lemma seperatedBy_is_nonterm[NER_simps]:
  "is_nonterm (parse (seperatedBy sep elem sep_oracle)) i \<longleftrightarrow> 
      (is_nonterm (parse elem) i \<or>
        (\<exists>r l. has_result (parse elem) i r l \<and>
              is_nonterm (parse (many (b_then sep elem))) l))"
  by (simp add: seperatedBy_def seperatedByBase_def NER_simps)

lemma seperatedBy_is_nonterm_wf[NER_simps]:
  assumes "\<nexists>i'. is_nonterm (parse sep) i'"
  assumes "\<nexists>i'. is_nonterm (parse elem) i'"
  assumes "PASI (parse sep)"
  assumes "PASI (parse elem)"
  shows "is_nonterm (parse (seperatedBy sep elem sep_oracle)) i \<longleftrightarrow> False"
  using assms
  unfolding seperatedBy_def seperatedByBase_def
  apply (simp add: NER_simps)
  apply (subst many_not_nonterm_when_base_not_nonterm)
  subgoal by (simp add: NER_simps)
  subgoal by (auto simp add: NER_simps then_PASI)
  subgoal by fast
  done


lemma seperatedBy_is_error[NER_simps]:
  "is_error (parse (seperatedBy sep elem sep_oracle)) i \<longleftrightarrow> False"
  by (simp add: seperatedBy_def seperatedByBase_def NER_simps)

lemma seperatedBy_has_result[NER_simps]:
  "has_result (parse (seperatedBy sep elem sep_oracle)) i r l \<longleftrightarrow> test"
  unfolding seperatedBy_def seperatedByBase_def
  apply (simp add: NER_simps)
  oops

lemma seperatedBy_has_result_safe_Nil[NER_simps]:
  "has_result (parse (seperatedBy sep elem sep_oracle)) i [] l \<longleftrightarrow> is_error (parse elem) i \<and> l = i"
  unfolding seperatedBy_def seperatedByBase_def
  by (auto simp add: NER_simps split: option.splits)
  
lemma seperatedBy_has_result_safe_Cons[NER_simps]:
  "has_result (parse (seperatedBy sep elem sep_oracle)) i (a#as) l \<longleftrightarrow> (
      \<exists>l'. has_result (parse elem) i a l' \<and>
            ((is_error (parse sep) l' \<and> as = []) \<or>
             (\<exists>l''. has_result (parse sep) l' s l'' \<and> has_result (parse (seperatedBy sep elem sep_oracle)) l'' as l)
))"
  apply (subst seperatedBy_def)
  apply (subst seperatedByBase_def)
  oops


\<comment> \<open>fp_NER\<close>
lemma seperatedBy_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (seperatedBy sep elem sep_oracle)) [] \<longleftrightarrow> False"
  "p_is_nonterm (print (seperatedBy sep elem sep_oracle)) (a#as) \<longleftrightarrow> 
    (p_is_nonterm (print elem) a \<or>
      \<not> p_is_error (print elem) a \<and>
      p_is_nonterm (print (many (b_then sep elem))) (map (Pair sep_oracle) as))"
  unfolding seperatedBy_def seperatedByBase_def
  by (clarsimp simp add: fp_NER)+

lemma seperatedBy_p_is_nonterm2[fp_NER]:
  assumes "\<not>(p_is_nonterm (print sep ) sep_oracle)"
  assumes "\<not>(\<exists>i \<in> set as. p_is_nonterm (print elem) i)"
  shows "p_is_nonterm (print (seperatedBy sep elem sep_oracle)) as \<longleftrightarrow> False"
  unfolding seperatedBy_def seperatedByBase_def
  using assms
  by (clarsimp simp add: fp_NER split: list.splits)


lemma seperatedBy_p_is_error[fp_NER]:
  "p_is_error (print (seperatedBy sep elem sep_oracle)) [] \<longleftrightarrow> False"
  "p_is_error (print (seperatedBy sep elem sep_oracle)) (a#as) \<longleftrightarrow> p_is_error (print elem) a \<or>
     \<not> p_is_nonterm (print elem) a \<and> p_is_error (print (many (b_then sep elem))) (map (Pair sep_oracle) as)"
  unfolding seperatedBy_def seperatedByBase_def
  by (clarsimp simp add: fp_NER)+

lemma seperatedBy_p_is_error2[fp_NER]:
  assumes "\<not>(p_is_error (print sep ) sep_oracle)"
  assumes "\<not>(\<exists>i \<in>set as. p_is_error (print elem) i)"
  shows "p_is_error (print (seperatedBy sep elem sep_oracle)) as \<longleftrightarrow> False"
  unfolding seperatedBy_def seperatedByBase_def
  using assms
  by (clarsimp simp add: fp_NER split: list.splits)


lemma seperatedBy_p_has_result[fp_NER]:
  "p_has_result (print (seperatedBy sep elem sep_oracle)) [] pr \<longleftrightarrow> pr = []"
  "p_has_result (print (seperatedBy sep elem sep_oracle)) [i] pr \<longleftrightarrow> p_has_result (print elem) i pr"
  "p_has_result (print (seperatedBy sep elem sep_oracle)) (i#is) pr \<longleftrightarrow> (\<exists>ta tb.
        pr = ta @ tb \<and>
        p_has_result (print elem) i ta \<and>
        p_has_result (print (many (b_then sep elem))) (map (Pair sep_oracle) is) tb)"
  unfolding seperatedBy_def seperatedByBase_def
  apply (clarsimp simp add: fp_NER)+
  by blast

lemma snd_comp_pair_id[simp]:
  "(snd \<circ> Pair a) = id"
  by fastforce

\<comment> \<open>Well formed\<close>



end
