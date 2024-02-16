theory derived_many1
  imports basic_definitions
          derived_many
          derived_then
begin

definition many1 :: "'\<alpha> bidef \<Rightarrow> '\<alpha> list bidef" where
  "many1 a = transform
                (\<lambda> r rs. r#rs) \<comment> \<open>pair to list\<close>
                undefined \<comment> \<open>list to pair\<close>
                (b_then a (many a)) \<comment> \<open>pair parser\<close>

"

end