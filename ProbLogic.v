(* Probabilistic Temporal Logic *)


Require Import Coq.QArith.QArith.
Open Scope Q_scope.


(* Type for individuals *)
Parameter i: Type.

(* Type for states (a.k.a. worlds) *)
Parameter W : Type.

(* Type for actions *)
(* An action is a function that takes a state and returns a list of possible next states. *)
Definition action := W -> list W.


(* Type of lifted propositions *)
Definition o := W -> Prop.



(* Modal connectives *)

Definition mequal {A: Type}(x y: A) := fun w: W => x = y.
Notation "x m= y" := (mequal x y) (at level 99, right associativity).

Definition mnot (p: o)(w: W) := ~ (p w).
Notation "m~  p" := (mnot p) (at level 74, right associativity).

Definition mand (p q:o)(w: W) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).

Definition mor (p q:o)(w: W) := (p w) \/ (q w).
Notation "p m\/ q" := (mor p q) (at level 79, right associativity).

Definition mimplies (p q:o)(w:W) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).

Definition mequiv (p q:o)(w:W) := (p w) <-> (q w).
Notation "p m<-> q" := (mequiv p q) (at level 99, right associativity).


(* Modal quantifiers *)

Definition A {t: Type}(p: t -> o)(w: W) := forall x, p x w.
Notation "'mforall'  x , p" := (A (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'mforall' x : t , p" := (A (fun x:t => p))
  (at level 200, x ident, right associativity, 
    format "'[' 'mforall' '/ '  x  :  t , '/ '  p ']'")
  : type_scope.


Definition E {t: Type}(p: t -> o)(w: W) := exists x, p x w.
Notation "'mexists' x , p" := (E (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'mexists' x : t , p" := (E (fun x:t => p))
  (at level 200, x ident, right associativity, 
    format "'[' 'mexists' '/ '  x  :  t , '/ '  p ']'")
  : type_scope.

(* Function that computes if an element occurs in a list. *)
Fixpoint is_in {A: Type} (x: A) (l: list A) := match l with 
  | nil => False
  | (cons h tail) => x = h \/ (is_in x tail)
end.

(* Accessibility relation based on actions *)
Definition r (w: W) (a: action) (w1: W) := (is_in w1 (a w)).


(* Modal operator for 'necessarily' *)
Definition box (a: action) (p: o) := fun w => forall w1, (r w a w1) -> (p w1).

(* Modal operator for 'possibly' *)
Definition dia (a: action) (p: o) := fun w => exists w1, (r w a w1) /\ (p w1).

(* Hybrid logic operator 'at' *)
Definition At (s: W) (f: o) := fun w: W => (f s).



(* Modal validity of lifted propositions *)
Definition V (p: o) := forall w, p w.
Notation "[ p ]" := (V p).
Ltac mv := match goal with [|- (V _)] => intro end.


(* Convenient tactics for modal operators *)

Ltac box_i := let w := fresh "w" in let R := fresh "R" in (intro w at top; intro R at top).

Ltac box_elim H w1 H1 := match type of H with 
                          ((box ?n ?p) ?w) =>  cut (p w1); [intros H1 | (apply (H w1); try assumption) ]
                         end.

Ltac box_e H H1:= match goal with | [ |- (_ ?w) ] => box_elim H w H1 end.

Ltac dia_e H := let w := fresh "w" in let R := fresh "R" in (destruct H as [w [R H]]; move w at top; move R at top).

Ltac dia_i w := (exists w; split; [auto | idtac]).

Create HintDb modal.
Hint Unfold mequal mimplies mnot mor mand dia box A E V : modal.


(* Convenient Functions *)

Fixpoint map {T1 T2: Type} (f: T1 -> T2) (l: list T1) := match l with 
  | nil => nil
  | (cons head tail) => (cons (f head) (map f tail))
end.

Fixpoint summation (l: list Q) := match l with
  | nil => 0
  | (cons head tail) => head + (summation tail)
end.

Parameter dec: forall (f: o) (w: W), {f w} + {~ (f w)}.

Parameter decProp: forall f: Prop, {f} + {~f}.


(* Probabilistic Operators *)

(* Probability function *)
Fixpoint prob (f: o) (l: list action) (w: W) := match l with
  | nil => if (dec f w) then 1 else 0
  | (cons a tail) => (summation (map (prob f tail) (a w))) / ((Z.of_nat (length (a w) )) # 1 )
end.

(* Probability Predicate *)
Definition probPred (f: o) (l: list action) (value: Q) (w: W) := (prob f l w) == value.




(* Some useful lemmas *)

Lemma mp_dia: [mforall p, mforall q, mforall n, (dia n p) m-> (box n (p m-> q)) m-> (dia n q)].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intros p q n.
intros H1 H2.
dia_e H1.
dia_i w0.
box_e H2 H3.
apply H3.
exact H1.
Qed.

Lemma not_dia_box_not: [mforall p, mforall n, (m~ (dia n p)) m-> (box n (m~ p))].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intros p n.
intro H.
box_i.
intro H2.
apply H.
dia_i w0.
exact H2.
Qed.

Lemma box_not_not_dia: [ mforall p, mforall n, (box n (m~ p)) m-> (m~ (dia n p)) ].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intros p n.
intro H1.
intro H2.
dia_e H2.
box_elim H1 w0 H3.
apply H3.
exact H2.
Qed.

Lemma dia_not_not_box: [ mforall p, mforall n, (dia n (m~ p)) m-> (m~ (box n p)) ].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intros p n.
intro H1.
intro H2.
dia_e H1.
apply H1.
box_e H2 H3.
exact H3.
Qed.