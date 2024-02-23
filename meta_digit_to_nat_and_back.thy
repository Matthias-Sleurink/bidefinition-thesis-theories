theory meta_digit_to_nat_and_back
  imports Main
begin

abbreviation "digit_chars \<equiv> {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'', CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}"

(*These functions take long to "proof", so we extract them here so changes to the main file aren't mega slow.*)

fun digit_char_to_nat :: "char \<Rightarrow> nat" where
  "digit_char_to_nat CHR ''0'' = 0"
| "digit_char_to_nat CHR ''1'' = 1"
| "digit_char_to_nat CHR ''2'' = 2"
| "digit_char_to_nat CHR ''3'' = 3"
| "digit_char_to_nat CHR ''4'' = 4"
| "digit_char_to_nat CHR ''5'' = 5"
| "digit_char_to_nat CHR ''6'' = 6"
| "digit_char_to_nat CHR ''7'' = 7"
| "digit_char_to_nat CHR ''8'' = 8"
| "digit_char_to_nat _ = 9"

abbreviation "digits \<equiv> {0,1,2,3,4,5,6,7,8,9}"
lemma digit_char_to_nat_domain:
  "digit_char_to_nat d_str \<in> digits"
  apply (cases d_str rule: digit_char_to_nat.cases)
  by auto

lemma digit_char_to_nat_lt_10[simp]:
  "digit_char_to_nat c < 10"
  apply (cases c rule: digit_char_to_nat.cases)
  by auto

fun digit_nat_to_char :: "nat \<Rightarrow> char" where
  "digit_nat_to_char 0 = CHR ''0''"
| "digit_nat_to_char (Suc 0) = CHR ''1''"
| "digit_nat_to_char (Suc (Suc 0)) = CHR ''2''"
| "digit_nat_to_char (Suc (Suc (Suc 0))) = CHR ''3''"
| "digit_nat_to_char (Suc (Suc (Suc (Suc 0)))) = CHR ''4''"
| "digit_nat_to_char (Suc (Suc (Suc (Suc (Suc 0))))) = CHR ''5''"
| "digit_nat_to_char (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = CHR ''6''"
| "digit_nat_to_char (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = CHR ''7''"
| "digit_nat_to_char (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = CHR ''8''"
| "digit_nat_to_char _ = CHR ''9''"

lemma digit_nat_to_char_domain:
  "digit_nat_to_char d_nat \<in> digit_chars"
  apply (cases d_nat rule: digit_nat_to_char.cases)
  by auto

fun print_nat_impl :: "nat \<Rightarrow> string" where
  "print_nat_impl n = (if n < 10 then [digit_nat_to_char n] else (print_nat_impl (n div 10)) @ [digit_nat_to_char (n mod 10)])"

definition "print_nat = print_nat_impl"

fun nat_from :: "string \<Rightarrow> nat" where
nat_from_base: "nat_from [] = 0"
| "nat_from s = nat_from (butlast s) * 10 + digit_char_to_nat (last s)"

lemma parse_nat_s2[simp]:
  "nat_from (ds @ [d]) = nat_from ds * 10 + digit_char_to_nat d"
  apply (cases ds)
  by simp_all

lemma parse_nat_s3[simp]:
  "nat_from [c] = digit_char_to_nat c"
  by simp

declare nat_from.simps[simp del]
declare nat_from_base[simp]

value "nat_from ''123''"
value "nat_from ''''"

lemma print_nat_domain[simp]:
  "(set (print_nat a)) \<subseteq> digit_chars"
  unfolding print_nat_def
  apply (induction a rule: print_nat_impl.induct)
  apply auto
  using digit_nat_to_char.elims by blast+


\<comment> \<open>Some tests:\<close>
value "print_nat 1"
value "print_nat 10"
value "print_nat 123"

\<comment> \<open>Some lemmas:\<close>
lemma print_nat_never_empty[simp]:
  "print_nat n \<noteq> []"
  by (simp add: print_nat_def)

lemma print_nat_hd[simp]:
  "hd (print_nat a) \<in> digit_chars"
  using hd_in_set print_nat_domain print_nat_never_empty by blast

lemma print_nat_10_one_or_more_chars:
  "size (print_nat n) \<ge> 1"
  by (simp add: print_nat_def)

lemma print_nat_10_or_larger_two_chars:
  "n \<ge> 10 \<Longrightarrow> size (print_nat n) \<ge> 2"
  by (simp add: print_nat_def)

lemma print_nat_100_or_larger_three_chars:
  "n \<ge> 100 \<Longrightarrow> size (print_nat n) \<ge> 3"
  by (simp add: print_nat_def)

lemma print_nat_100_or_less_two_chars:
  "n < 100 \<Longrightarrow> size (print_nat n ) \<le> 2"
  by (auto simp add: print_nat_def)

lemma digit_to_nat_to_digit:
  assumes "d \<in> digits"
  shows "digit_char_to_nat (digit_nat_to_char d) = d"
  using assms
  apply auto
  by eval+

lemma nat_to_digit_to_nat:
  assumes "d\<in> digit_chars"
  shows "digit_nat_to_char (digit_char_to_nat d) = d"
  using assms
  apply auto
  by eval+

lemma n_in_digits_eq_n_lt_10:
  "n \<in> digits \<equiv> n < 10" for n::nat
  by (simp, presburger)

lemma n_lt_10_eq_n_in_digits:
  "n < 10 \<equiv> n \<in> digits" for n::nat
  by (rule n_in_digits_eq_n_lt_10[symmetric])

lemma nat_from_print_nat_aux1[simp]:
  "n < 10 \<Longrightarrow> digit_char_to_nat (digit_nat_to_char (n)) = n"
  apply (cases n rule: digit_nat_to_char.cases)
  by auto

lemma nat_from_print_nat[simp]:
  "nat_from (print_nat n) = n"
  unfolding print_nat_def
  apply (induction n rule: print_nat_impl.induct)
  by auto

find_theorems print_nat_impl

lemma print_nat_unfold: "n\<ge>10 \<Longrightarrow> print_nat n = print_nat (n div 10) @ [digit_nat_to_char (n mod 10)]"
  unfolding print_nat_def by simp

lemma print_nat_nat_from_nonzero:
  assumes "t \<noteq> []"
  assumes "set t \<subseteq> digit_chars"
  assumes "hd t \<noteq> CHR ''0''"
  shows "print_nat (nat_from t) = t"
  using assms
  apply (induction t rule: rev_nonempty_induct) (* rev_nonempty_induct / rev_induct *)
  subgoal by (simp add: nat_to_digit_to_nat print_nat_def)
  subgoal for c s
    apply (subgoal_tac "nat_from s \<noteq> 0")
    apply (simp add: print_nat_unfold)
    apply (cases s; simp) (*empty case falls away with simp*)
    subgoal by (simp add: nat_to_digit_to_nat[of c])
    subgoal (* nat_from s \<noteq> 0 *)
      using hd_append2[of s \<open>[c]\<close>]
      apply clarsimp
      by (metis digit_nat_to_char.simps(1) gr0I list.sel(1) print_nat_def print_nat_impl.elims zero_less_numeral)
    done
  done

lemma print_nat_nat_from_0:
  shows "print_nat (nat_from ''0'') = ''0''"
  by eval

lemma print_nat_nat_from[simp]:
  assumes "t \<noteq> []"
  assumes "set t \<subseteq> digit_chars"
  assumes "hd t \<noteq> CHR ''0'' \<or> t = ''0''"
  shows "print_nat (nat_from t) = t"
  apply (cases \<open>t = ''0''\<close>)
  subgoal (* t=0 *) using print_nat_nat_from_0 by fast
  subgoal (* t\<noteq>0 *) using print_nat_nat_from_nonzero[of t] assms by fastforce
  done
end
