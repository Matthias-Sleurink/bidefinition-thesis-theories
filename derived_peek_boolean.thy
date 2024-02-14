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



\<comment> \<open>FP NER\<close>
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



\<comment> \<open>PNGI, PASI\<close>
lemma peek_bool_PNGI:
  shows "PNGI (parse (peek_bool a oracle))"
  by (metis peek_PNGI peek_bool_def transform_PNGI)

lemma peek_bool_PASI:
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



\<comment> \<open>Well Formed\<close>
text \<open>
See the notes on well formedness in basic_peek_result.
\<close>


end