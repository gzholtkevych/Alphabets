Require Export Utf8.
Require Export Lists.List.
Import ListNotations.


Structure Alphabet := newAlphabet {
  letter :> Set;
  fin_evidence : {ls : list letter | ∀ a : letter, In a ls};
  eq_neq_dec : ∀ a b : letter, {a = b} + {a ≠ b}
}.

Definition chain (A : Alphabet) : Set := list (letter A).