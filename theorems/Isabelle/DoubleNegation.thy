theory DoubleNegation
  imports HOL
begin

lemma notnotD: "\<not> \<not> P \<Longrightarrow> P".
proof
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done
qed

end