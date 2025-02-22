theory derived_peek_boolean
  imports basic_definitions
          derived_optional
begin

text \<open>
  Peek into a boolean value if it succeeded or not.
\<close>

text \<open>
The use of an oracle here is sub-optimal,
 but the peek printer executes the underlying printer to check for failure.
As such, we need to pass a printable value into it to make it succeed and print empty.
\<close>

definition peek_bool :: "'\<alpha> bidef \<Rightarrow> '\<alpha>  \<Rightarrow> bool bidef" where
  "peek_bool a oracle = transform  ((Not o Option.is_none )               :: '\<alpha> option \<Rightarrow> bool)
                                   ((\<lambda>b. if b then Some oracle else None) :: bool \<Rightarrow> '\<alpha> option)
                                   (peek (optional a)                     :: '\<alpha> option bidef)"

definition wf_peek_oracle :: "'\<alpha> bidef \<Rightarrow> '\<alpha> \<Rightarrow> bool" where
  "wf_peek_oracle b v \<longleftrightarrow> (\<exists>pr. p_has_result (print b) v pr)"



\<comment> \<open>NER\<close>
lemma peek_bool_is_nonterm[NER_simps]:
  "is_nonterm (parse (peek_bool a v)) i \<longleftrightarrow> is_nonterm (parse a) i"
  by (simp add: NER_simps peek_bool_def)

lemma peek_bool_is_error[NER_simps]:
  "is_error (parse (peek_bool a v)) i \<longleftrightarrow> False"
  by (simp add: NER_simps peek_bool_def)

lemma peek_bool_has_result[NER_simps]:
  "has_result (parse (peek_bool a v)) i False l \<longleftrightarrow> i = l \<and> is_error (parse a) i"
  "has_result (parse (peek_bool a v)) i True  l \<longleftrightarrow> i = l \<and> (\<exists> r l. has_result (parse a) i r l)"
  "has_result (parse (peek_bool a v)) i b     l \<longleftrightarrow> i = l \<and> (if b then (\<exists> r l. has_result (parse a) i r l) else is_error (parse a) i)"
  by (auto simp add: NER_simps peek_bool_def Option.is_none_def split: option.splits)

lemma peek_bool_has_result_ci[NER_simps]:
  assumes "PNGI (parse a)"
  shows
  "has_result_ci (parse (peek_bool a v)) i c False l \<longleftrightarrow> l = i \<and> c=[] \<and> is_error (parse a) i"
  "has_result_ci (parse (peek_bool a v)) i c True  l \<longleftrightarrow> l = i \<and> c=[] \<and> (\<exists> c' r l'. has_result_ci (parse a) i c' r l')"
  "has_result_ci (parse (peek_bool a v)) i c b     l \<longleftrightarrow> l = i \<and> c=[] \<and> (if b then (\<exists> c' r l'. has_result_ci (parse a) i c' r l') else is_error (parse a) i)"
    apply (auto simp add: NER_simps has_result_ci_def has_result_c_def split: option.splits)
  subgoal for r ll
    \<comment> \<open>c'@l' = l\<close>
    \<comment> \<open>l' = ll\<close>
    \<comment> \<open>c' = list_upto l ll\<close>
    apply (rule exI[of _ \<open>list_upto l ll\<close>])
    apply (rule exI[of _ r])
    apply (rule exI[of _ ll])
    subgoal
      using assms[unfolded PNGI_def]
      using list_upto_take_cons[of l ll]
      by force
    done
  subgoal by fast
  subgoal for r ll \<comment> \<open>Same argumentation as first subgoal.\<close>
    apply (rule exI[of _ \<open>list_upto l ll\<close>])
    apply (rule exI[of _ r])
    apply (rule exI[of _ ll])
    subgoal
      using assms[unfolded PNGI_def]
      using list_upto_take_cons[of l ll]
      by force
    done
  subgoal by fast
  done



\<comment> \<open>FP NER\<close>
lemma peek_bool_p_is_nonterm[fp_NER]:
  assumes "wf_peek_oracle a v"
  shows "p_is_nonterm (print (peek_bool a v)) b \<longleftrightarrow> (if b then p_is_nonterm (print a) v else False)"
  unfolding peek_bool_def
  by (auto simp add: fp_NER)

lemma peek_bool_p_is_error[fp_NER]:
  assumes "wf_peek_oracle a v"
  shows "p_is_error (print (peek_bool a v)) b \<longleftrightarrow> False"
  unfolding peek_bool_def
  apply (auto simp add: fp_NER)
  using assms[unfolded wf_peek_oracle_def]
        p_has_result_impl_not_error[of \<open>print a\<close> v]
  by blast

lemma peek_bool_p_has_result[fp_NER]:
  assumes "wf_peek_oracle a v"
  shows "p_has_result (print (peek_bool a v)) b t \<longleftrightarrow> t = []"
  by (auto simp add: fp_NER peek_bool_def assms[unfolded wf_peek_oracle_def])

lemma peek_bool_print_empty_safe[print_empty, fp_NER]:
  "p_has_result (print (peek_bool a oracle)) True  [] \<longleftrightarrow> wf_peek_oracle a oracle"
  "p_has_result (print (peek_bool a oracle)) False [] \<longleftrightarrow> True"
  by (clarsimp simp add: peek_bool_def wf_peek_oracle_def fp_NER)+

lemma peek_bool_print_empty:
  "p_has_result (print (peek_bool a oracle)) i  [] \<longleftrightarrow> (i \<longrightarrow> wf_peek_oracle a oracle)"
  by (clarsimp simp add: peek_bool_def wf_peek_oracle_def fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma peek_bool_PNGI[PASI_PNGI, PASI_PNGI_intros]:
  shows "PNGI (parse (peek_bool a oracle))"
  by (metis peek_PNGI peek_bool_def transform_PNGI)

lemma peek_bool_PASI[PASI_PNGI, PASI_PNGI_intros]:
  assumes "\<exists> i r l. has_result (parse a) i r l"
  shows "PASI (parse (peek_bool a oracle)) \<longleftrightarrow> False"
  unfolding peek_bool_def
  unfolding transform_PASI[symmetric]
  apply (subst peek_PASI)
  subgoal
    unfolding optional_has_result
    using assms
    by (auto split: option.splits)
  subgoal by simp
  done



\<comment> \<open>First printed char\<close>
lemma peek_bool_fpci[fpci_simps]:
  assumes "wf_peek_oracle a oracle"
  shows "first_printed_chari (print (peek_bool a oracle)) i c \<longleftrightarrow> False"
  using assms unfolding first_printed_chari_def
  by (clarsimp simp add: peek_bool_p_has_result)



\<comment> \<open>Well Formed\<close>
text \<open>
See the notes on well formedness in basic_peek_result.
\<close>


end