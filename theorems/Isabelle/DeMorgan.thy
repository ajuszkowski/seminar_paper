theory Scratch
  imports HOL
begin

lemma "\<lbrakk> A \<and> B; C \<and> D \<rbrakk> \<Longrightarrow> D"
  apply (erule_tac Q=D in conjE)
  apply assumption
  done

lemma DeMorganPropositional_Isabelle: "(\<not> (P \<and> Q)) = (\<not> P \<or> \<not> Q)"
  apply (rule iffI)         (* split equality into two subgoals *)

  (* "Forward" subgoal: 1. \<not>(P \<and> Q) \<Longrightarrow> \<not> P \<or> \<not> Q *)
  apply (rule classical)    (* 1. \<not> (P \<and> Q) ==> \<not> (\<not> P \<or> \<not> Q) ==> \<not> P \<or> \<not> Q *)
  apply (erule notE)        (* 1. \<not> (\<not> P \<or> \<not> Q) ==> P \<and> Q *)
  apply (rule conjI)        (* 1. \<not> (\<not> P \<or> \<not> Q) ==> P; 2. \<not> (\<not> P \<or> \<not> Q) ==> Q *)
  apply (rule classical)    (* 1. \<not> (\<not> P \<or> \<not> Q) ==> \<not> P ==> P *)
  apply (erule notE)        (* 1. \<not> P ==> \<not> P \<or> \<not> Q *)
  apply (rule disjI1)       (* 1. \<not> P ==> \<not> P *)
  apply assumption          (* 1. (solved). 2. \<not> (\<not> P \<or> \<not> Q) ==> Q *)
  apply (rule classical)    (* 2. \<not> (\<not> P \<or> \<not> Q) ==> \<not> Q ==> Q *)
  apply (erule notE)        (* 2. \<not> Q ==> \<not> P \<or> \<not> Q *)
  apply (rule disjI2)       (* 2. \<not> Q ==> \<not> Q *)
  apply assumption          (* 2. (solved) *)

  (* "Backward" subgoal: 3. \<not> P \<or> \<not> Q ==> \<not> (P \<and> Q) *)
  apply (rule notI)      (* 3. \<not> P \<or> \<not> Q ==> P \<and> Q ==> False *)   
  apply (erule conjE)    (* 3. \<not> P \<or> \<not> Q ==> P ==> Q ==> False *)
  apply (erule disjE)    (* 3.  P ==> Q ==> \<not> P ==> False; 4. P ==> Q ==> \<not> Q ==> False *)
  apply (erule notE, assumption)+  (* 3. (solved); 4. (solved) *)
  done

lemma "\<not> \<not> A \<longleftrightarrow> A"
  apply (rule notE)
  apply (classical)
  apply assumption
  done

lemma example3 : "(M \<or> L) \<and> (M \<or> W ) \<and> \<not>(L \<and> W ) \<longrightarrow> M \<or> (M \<and> L) \<or> (M \<and> W )"
apply (rule impI)
apply (erule conjE)+
apply (erule disjE)
apply (erule disjE)
apply (rule disjI1 )
apply assumption
apply (rule disjI1 )
apply assumption
apply (erule disjE)
apply (rule disjI1 )
apply assumption
apply (erule notE)
apply (rule conjI)
by assumption+


lemma notnotD: "\<not>(P \<or> Q) \<longleftrightarrow> \<not>P \<and> \<not>Q"
  apply (rule notE)
  
  apply assumption
  done
  
