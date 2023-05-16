Require Import Alphabets.Concepts.
Import ListNotations.


Module SELECTOR.
Inductive selector : Set := onleft | inward | onright.

Definition selector_fin_evidence : {e : list selector | forall s, In s e}.
Proof.
  exists [onleft; inward; onright].
  intro. destruct s; repeat (now left) || right.
Defined.

Definition selector_eq_neq_dec :
  forall s1 s2 : selector, {s1 = s2} + {s1 <> s2}.
Proof.
  intros. destruct s1, s2; (now left) || right; discriminate.
Defined.

Definition Selector := {|
  letter := selector;
  fin_evidence := selector_fin_evidence;
  eq_neq_dec := selector_eq_neq_dec
|}.
End SELECTOR.
