theory derived_many1
  imports basic_definitions
          derived_many
          derived_then
begin

\<comment> \<open>Seems like we might want a fallible transform here\<close>
definition many1 :: "'\<alpha> bidef \<Rightarrow> '\<alpha> list bidef" where
  "many1 a = ftransform
                (\<lambda> (r, rs). Some (r#rs)) \<comment> \<open>pair to list\<close>
                (\<lambda> l. if l = [] then None else Some (hd l, tl l)) \<comment> \<open>list to pair\<close>
                (b_then a (many a)) \<comment> \<open>pair parser\<close>
"



\<comment> \<open>NER\<close>
lemma many1_is_nonterm[NER_simps]:
  "is_nonterm (parse (many1 a)) i \<longleftrightarrow> is_nonterm (parse a) i \<or> (\<exists>r l. has_result (parse a) i r l \<and> is_nonterm (parse (many a)) l)"
  by (simp add: many1_def NER_simps)

lemma many1_is_error[NER_simps]:
  "is_error (parse (many1 a)) i \<longleftrightarrow> is_error (parse a) i"
  by (simp add: many1_def NER_simps)

lemma many1_has_result[NER_simps]:
  "has_result (parse (many1 a)) i r l \<longleftrightarrow> r \<noteq> [] \<and> (\<exists> l'. has_result (parse a) i (hd r) l' \<and> has_result (parse (many a)) l' (tl r) l)"
  apply (clarsimp simp add: many1_def NER_simps)
  by fastforce

lemma many1_result_only_if_nonempty:
  assumes "has_result (parse (many1 bi)) i r l"
  shows "r \<noteq> []"
  using assms
  by (simp add: NER_simps)



\<comment> \<open>FP ner\<close>
lemma many1_p_is_error[fp_NER]:
  "p_is_error (print (many1 a)) i \<longleftrightarrow> i = [] \<or> p_is_error (print a) (hd i) \<or> p_is_error (print (many a)) (tl i)"
  by (simp add: many1_def fp_NER)

lemma many1_p_has_result[fp_NER]:
  "p_has_result (print (many1 a)) i r \<longleftrightarrow> (\<exists> r1 r2. r = r1@r2 \<and> i \<noteq> [] \<and> p_has_result (print a) (hd i) r1 \<and> p_has_result (print (many a)) (tl i) r2)"
  by (auto simp add: many1_def fp_NER)

lemma many1_p_has_result_only_if_nonempty:
  assumes "p_has_result (print (many1 a)) i r"
  shows "i \<noteq> []"
  using assms
  by (auto simp add: fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma many1_PNGI:
  assumes "PNGI (parse p)"
  shows "PNGI (parse (many1 p))"
  unfolding many1_def
  apply (rule ftransform_PNGI)
  apply (rule then_PNGI)
  subgoal by (rule assms)
  apply (rule many_PNGI)
  oops

lemma many1_PASI:
  assumes "PASI (parse p)"
  shows "PASI (parse (many1 p))"
  unfolding many1_def
  apply (rule ftransform_PASI)
  apply (rule then_PASI_from_pasi_pngi)
  subgoal by (rule assms(1))
  apply (rule many_PNGI)
  by (rule assms(1))



end