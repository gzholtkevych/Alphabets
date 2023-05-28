Require Import Alphabets.Concepts.
Import ListNotations.


Module ALPHABET_THEORY (M : ALPHABET_CORE).
Include M.

  Definition in_chain_dec : ∀ (a : letter) c, {In a c} + {¬ In a c}.
  Proof.
    intros.
    induction c as [| h c' IHc'].
    - right. intro. inversion H.
    - destruct (eq_dec_letter a h) as [E | NE].
      + left. rewrite <- E. now left.
      + elim IHc'; intro H; [left | right ]; simpl.
        * now right.
        * intro H1. elim H1; intro H2; try symmetry in H2; contradiction.
  Defined.

  Inductive nodup : chain → Prop 
    := nil_nodup : nodup []
    |  cons_nodup : ∀ a c, ¬ In a c → nodup c → nodup (a :: c).

  Fixpoint nocc (a : letter) (c : chain) : nat
    := match c with
         []       => 0
       | a' :: c' => 
           if eq_dec_letter a a' then S (nocc a c') else nocc a c'
       end.

  Fixpoint remove_dup (c : chain) : chain
    := match c with
         []      => []
       | a :: c' =>
           match nocc a c' with
             0 => a :: (remove_dup c')
           | _ => remove_dup c' end
       end.

  Lemma nodup_without_dup : ∀ c : chain, nodup c → remove_dup c = c.
  Proof.
    intros.
    induction c as [| a s' IHc'].
    - trivial.
    - simpl in H. pose (nocc a c).
      assert (H1 : n = 0). { destruct n. reflexivity. 
  Admitted.

  Lemma cardinal : ∀ e' e'' : {e : chain A | ∀ a : A, In a e},
    length (proj1_sig e') = length (proj1_sig e'').
  Proof.
  Admitted.
  
  Definition card : nat := length (remove_dup (proj1_sig (fin_evidence A))).

End Cardinality.


Section Finiteness.
Variable A : Alphabet.
(*
  Definition enum := proj1_sig (fin_evidence A).
  Definition all_A := proj2_sig (fin_evidence A).

  Definition cons_with_all (c : chain A) : list (chain A) 
    := map (λ a, cons a c) enum.

  
*)
  Theorem bounded_finite :
    forall n : nat, exists cs : list (chain A), 
      forall c : chain A, length c <= n -> In c cs.
  Proof.
  Admitted.

End Finiteness.
