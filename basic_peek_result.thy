theory basic_peek_result
  imports types
begin

text \<open>
  Try to execute a parser, on failure, fail, on success, return the result, but undo any consumed input.
\<close>

fun peek_p :: "'\<alpha> parser \<Rightarrow> '\<alpha> parser" where
  "peek_p p i = (
    case p i of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some (r, l)) \<Rightarrow> Some (Some (r, i)))"

fun peek_pr :: "'\<alpha> printer \<Rightarrow> '\<alpha> printer" where
  "peek_pr pr i = (
    case pr i of
      None \<Rightarrow> None
    | Some None \<Rightarrow> Some None
    | Some (Some r) \<Rightarrow> Some (Some []) \<comment> \<open>print nothing since peek does not consume anything.\<close>
)"

definition peek :: "'\<alpha> bidef \<Rightarrow> '\<alpha> bidef" where
  "peek b = bdc
    (peek_p (parse b))
    (peek_pr (print b))
"



\<comment> \<open> NER\<close>
lemma peek_is_nonterm[NER_simps]:
  "is_nonterm (parse (peek b)) i \<longleftrightarrow> is_nonterm (parse b) i"
  "is_nonterm (peek_p p)       i \<longleftrightarrow> is_nonterm p         i"
  by (simp add: peek_def is_nonterm_def split: option.splits)+

lemma peek_is_error[NER_simps]:
  "is_error (parse (peek b)) i \<longleftrightarrow> is_error (parse b) i"
  "is_error (peek_p p)       i \<longleftrightarrow> is_error p         i"
  by (simp add: peek_def is_error_def split: option.splits)+

lemma peek_has_result[NER_simps]:
  "has_result (parse (peek b)) i r l \<longleftrightarrow> i=l \<and> (\<exists> l'. has_result (parse b) i r l')"
  "has_result (peek_p p)       i r l \<longleftrightarrow> i=l \<and> (\<exists> l'. has_result p         i r l')"
  by (auto simp add: peek_def has_result_def split: option.splits)

lemma peek_has_result_simple:
  "has_result (parse (peek b)) i r l \<longrightarrow> l = i"
  by (simp add: peek_has_result(1))

lemma peek_has_result_c[NER_simps]:
  assumes "PNGI (parse b)"
  assumes "PNGI p"
  shows
  "has_result_c (parse (peek b)) c r l \<longleftrightarrow> c=[] \<and> (\<exists> c' l'. has_result_c (parse b) c' r l' \<and> l = c'@l')"
  "has_result_c (peek_p p)       c r l \<longleftrightarrow> c=[] \<and> (\<exists> c' l'. has_result_c p         c' r l' \<and> l = c'@l')"
  apply (auto simp add: peek_has_result has_result_c_def split: option.splits)
  subgoal for l'
    apply (rule exI[of _ \<open>list_upto l l'\<close>])
    using list_upto_take_cons assms[unfolded PNGI_def]
    by metis
  subgoal for l'
    apply (rule exI[of _ \<open>list_upto l l'\<close>])
    using list_upto_take_cons assms[unfolded PNGI_def]
    by metis
  done

lemma peek_has_result_ci[NER_simps]:
  assumes "PNGI (parse b)"
  shows
  "has_result_ci (parse (peek b))   i c r l \<longleftrightarrow> c=[] \<and> l=i \<and> (\<exists> c' l'. has_result_ci (parse b) i c' r l' \<and> l = c'@l')"
  "has_result_ci (peek_p (parse b)) i c r l \<longleftrightarrow> c=[] \<and> l=i \<and> (\<exists> c' l'. has_result_ci (parse b) i c' r l' \<and> l = c'@l')"
  apply (clarsimp simp add: peek_def)+
  subgoal
    using assms has_result_ci_def peek_has_result_c(2)
    by fastforce
  subgoal
    using assms has_result_ci_def peek_has_result_c(2)
    by fastforce
  done



\<comment> \<open>FP NER\<close>
lemma peek_p_is_error[fp_NER]:
  "p_is_error (print (peek b)) i \<longleftrightarrow> p_is_error (print b) i"
  "p_is_error (peek_pr p)      i \<longleftrightarrow> p_is_error p         i"
  by (simp add: peek_def p_is_error_def split:option.splits)+

lemma peek_p_has_result[fp_NER]:
  "p_has_result (print (peek b)) v t \<longleftrightarrow> t=[] \<and> (\<exists> t'. p_has_result (print b) v t')"
  "p_has_result (peek_pr p)      v t \<longleftrightarrow> t=[] \<and> (\<exists> t'. p_has_result p         v t')"
  by (auto simp add: peek_def p_has_result_def split: option.splits)

lemma peek_p_is_nonterm[fp_NER]:
  "p_is_nonterm (print (peek b)) v \<longleftrightarrow> p_is_nonterm (print b) v"
  "p_is_nonterm (peek_pr p) v \<longleftrightarrow> p_is_nonterm p v"
  by (auto simp add: peek_def p_is_nonterm_def split: option.splits)

lemma peek_print_empty[print_empty, fp_NER]:
  "p_has_result (print (peek b)) i [] \<longleftrightarrow> (\<exists>t. p_has_result (print b) i t)"
  by (clarsimp simp add: fp_NER)



\<comment> \<open>PNGI, PASI\<close>
lemma peek_PNGI:
  "PNGI (parse (peek b))"
  by (simp add: PNGI_def NER_simps)

lemma peek_PASI:
  assumes "\<exists> i r l. has_result (parse b) i r l"
  shows "PASI (parse (peek b)) \<longleftrightarrow> False"
  by (simp add: assms PASI_def NER_simps)



\<comment> \<open>Charset\<close>
\<comment> \<open>This is somewhat iffy since peek never consumes.\<close>
lemma charset_peek:
  "charset (parse (peek b)) = {}"
  unfolding charset_def
  by (clarsimp simp add: NER_simps)

lemma first_chars_peek:
  "first_chars (print (peek b)) = {}"
  unfolding first_chars_def
  by (clarsimp simp add: fp_NER)



\<comment> \<open>Does not peek past end\<close>
lemma peek_result_does_not_peek_past_end[peek_past_end_simps]:
  assumes "bidef_well_formed A"
  assumes "does_not_peek_past_end (parse A)"
  shows "does_not_peek_past_end (parse (peek A))"
  using assms
  unfolding does_not_peek_past_end_def
  apply (auto simp add: peek_has_result)
  subgoal for r i l i'
    \<comment> \<open>i and i' are in no way connected here, so I don't think this is viable.\<close>
    oops


\<comment> \<open>First printed char\<close>
lemma peek_first_printed_char:
  shows "(\<nexists>c. first_printed_char (print (peek A)) B c)"
  unfolding first_printed_char_def
  by (clarsimp simp add: peek_p_has_result)

lemma peek_fpci[fpci_simps]:
  shows "\<nexists>i c. first_printed_chari (print (peek B)) i c"
        "first_printed_chari (print (peek B)) i c \<longleftrightarrow> False"
  unfolding first_printed_chari_def
  by (clarsimp simp add: peek_p_has_result)+

lemma peek_fpc[fpc_simps]:
  shows "fpc (parse (peek A)) i c \<longleftrightarrow> False"
  unfolding fpc_def peek_has_result
  by clarsimp



\<comment> \<open>Well Formed\<close>
text \<open>
It's not really clear to me how this can be well formed on its own.
Well defined requires being able to parse what is printed, but we don't consume anything here,
 so printing anything would also seem wrong.
Maybe only parsers that solely succeed on empty text can be well formed under peek?
Apart from that, combining this with 'then' and a parser that consumes what is peeked here
 should be able to be well formed?
\<close>

lemma peek_well_formed_empty:
  assumes "bidef_well_formed b"
  assumes "\<forall> t. t \<noteq> [] \<longrightarrow> is_error (parse b) t"
  shows "bidef_well_formed (peek b)"
  apply wf_init
  subgoal by (rule peek_PNGI)
  subgoal
    using assms(1,2)[unfolded bidef_well_formed_def]
    unfolding parser_can_parse_print_result_def
    unfolding peek_has_result(1) \<comment> \<open>inside and Ex F we need to force the lemma into applying\<close>
    apply (auto simp add: fp_NER NER_simps)
    by (metis has_result_implies_not_is_error)
  subgoal
    using assms(1)[unfolded bidef_well_formed_def]
    unfolding printer_can_print_parse_result_def
    unfolding peek_p_has_result(1) \<comment> \<open>inside and Ex F we need to force the lemma into applying\<close>
    by (auto simp add: fp_NER NER_simps)
  done



end