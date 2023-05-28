Require Export Utf8.
Require Export Lists.List.
Import ListNotations.


Module Type ALPHABET_CORE.
  Parameter letter : Set.
  Definition chain := list letter.
  Parameter fin_letter : {enum : chain | ∀ a : letter, In a enum}.
  Parameter eq_dec_letter : ∀ a b : letter, {a = b} + {a ≠ b}.
End ALPHABET_CORE.

