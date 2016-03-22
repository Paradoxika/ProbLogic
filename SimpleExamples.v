(* Probabilistic Temporal Logic *)


Require Import Coq.QArith.QArith.
Open Scope Q_scope.
Require Import ProbLogic.


(* Examples *)

Lemma L1: forall f: o, forall a: action, forall w0: W, forall w: W, (f w) /\ ((a w0) = (cons w nil)) -> ((prob f (cons a nil) ) w0  = 1).
Proof.
intros.
unfold prob.
destruct H as [H1 H2].
rewrite H2.
simpl.
destruct (dec f w).
    reflexivity.

    contradiction.
Qed.


Lemma L2: forall f: o, forall a: action, forall w0: W, forall w: W, (~ (f w)) /\ ((a w0) = (cons w nil)) -> ((prob f (cons a nil) ) w0  = 0).
Proof.
intros.
unfold prob.
destruct H as [H1 H2].
rewrite H2.
simpl.
destruct (dec f w).
    contradiction.

    reflexivity.
Qed.


Parameter head: i -> o.

Parameter tail: i -> o.

Parameter toss: action.

Axiom ht: [mforall x:i, (head x) m<-> m~ (tail x)].

Axiom two_sucs: forall w, exists w1 w2, (toss w) = (cons w1 (cons w2 nil)).


Axiom tossAx: [mforall x:i, (dia toss (head x))].

Axiom tossAx2: [mforall x:i, (dia toss (tail x))].

Lemma l: forall w w1 w2 x, (toss w) = (cons w1 (cons w2 nil)) -> (head x w1) -> (~ (head x w2)).
Proof.
intros.
intro H1.
assert ((dia toss (tail x)) w).
  apply tossAx2.

  unfold dia in H2.
  destruct H2 as [w3 [R1 H3]].
  unfold r in R1.
  unfold is_in in R1.
  rewrite H in R1.
  destruct R1 as [R11 | [R12 | R13] ].
    rewrite R11 in H3.
    apply ht in H0.
    contradiction.

    rewrite R12 in H3.
    apply ht in H1.
    contradiction.

    contradiction.
Qed.


Theorem p: [mforall x: i, (probPred (head x) (cons toss nil) (1 # 2))].
Proof. mv.
unfold probPred.
unfold A.
intros.
assert ((dia toss (head x)) w).
  apply tossAx.

  unfold dia in H.
  destruct H as [w1 [R1 H1]].
  unfold r in R1.
  assert (exists w3 w4, (toss w) = (cons w3 (cons w4 nil))).
    apply two_sucs.

    destruct H as [w3 [w4 H]].
    simpl.
    rewrite H.
    simpl.
    assert (w1 = w3 \/ w1 = w4).
      unfold is_in in R1.
      rewrite H in R1.
      destruct R1 as [R11 | [R12 | R13]].
        left; assumption.

        right; assumption.

        contradiction.

      destruct H0 as [H01 | H02].
        destruct (dec (head x) w3).
          destruct (dec (head x) w4).
            apply (l w w3 w4 x H) in h.
            contradiction.

            reflexivity.

          destruct (dec (head x) w4).
            reflexivity.

            rewrite H01 in H1.
            contradiction.

        destruct (dec (head x) w3).
          destruct (dec (head x) w4).
            apply (l w w3 w4 x H) in h.
            contradiction.

            reflexivity.

          destruct (dec (head x) w4).
            reflexivity.

            rewrite H02 in H1.
            contradiction.
Qed.

