(* Probabilistic Temporal Logic *)


Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.BinInt.
Open Scope Q_scope.
Require Import ProbLogic.

(* Monty Hall problem *)

(* Formalization of the Monty Hall problem *)

(* Description of the problem by vos Savant *)
(* 
   Suppose you’re on a game show, and you’re given the choice of three doors: 
   Behind one door is a car; behind the others, goats. 
   You pick a door, say No. 1, 
   and the host, who knows what’s behind the doors, opens another door, say No. 3, which has a goat. 
   He then says to you, ‘Do you want to pick door No. 2?’ 
   Is it to your advantage to switch your choice?
*)

(* Type for doors *)
Inductive D : Type := 
  | d1 : D
  | d2 : D
  | d3 : D
.

(* Predicate symbols that indicate, respectively, whether a door d contains a car, contains a goat, is open or is picked. *)
Parameter C G O P: D -> o.

(* Proposition that holds at victorious states *)
Parameter Vic: o.

(* Possible actions *)
Parameter pick: D -> action.
Parameter open hide switch noswitch: action.

(* The initial state *)
Parameter s0: W.

(* Axioms specifying basic facts about the game *)
Axiom car_ax: [mexists d, (C d)].
Axiom goats_ax: [mforall d, (m~(C d) m<-> (G d))].

(* Axioms specifying the outcomes of actions *)
Axiom hide_ax: forall w, exists w1 w2 w3, (hide w) = (cons w1 (cons w2 (cons w3 nil))) /\ (C d1 w1) /\ (C d2 w2) /\ (C d3 w3). 
Axiom pick_ax: forall w, forall d, exists w1, (pick d w) = (cons w1 nil) /\ (P d w1).
Axiom open_ax1: forall w, forall d, forall dd, ((C d) w) -> ((P dd) w) -> exists w1, (open w) = (cons w1 nil) /\ exists do, ~(do = d) /\ ~(do = dd) /\ (O do w1).
Axiom open_ax2: forall w, forall d, ((C d) w) -> ((P d) w) -> exists w1 w2 d1 d2, (open w) = (cons w1 (cons w2 nil)) /\ ~(d1 = d) /\ ~(d2 = d) /\ ~(d1 = d2) /\ (O d1 w1) /\ (O d2 w2).
Axiom switch1: forall w, forall do, forall dp, ((O do) w) -> ((P dp) w) -> exists w1, (switch w) = (cons w1 nil) /\ exists dpn, (dpn <> do) /\ (dpn <> dp) /\ (P dpn w1).
Axiom noswitch1: forall w, forall dp, ((P dp) w) -> exists w1, (noswitch w) = (cons w1 nil) /\ (P dp w1).

(* Axioms specifying facts that are not changed by actions *)
Axiom pick_frame_ax: [mforall d, mforall dp, (C d) m-> (box (pick dp) (C d)) ].
Axiom open_frame_C_ax: [mforall d, (C d) m-> (box open (C d)) ].
Axiom open_frame_P_ax: [mforall d, (P d) m-> (box open (P d)) ].
Axiom switch_frame_ax: [mforall d, (C d) m-> (box switch (C d)) ].
Axiom noswitch_frame_ax: [mforall d, (C d) m-> (box noswitch (C d)) ].

(* Axioms specifying conditions for victory or defeat *)
Axiom victory: [ mforall d, (C d) m-> (P d) m-> Vic ].
Axiom defeat: [ mforall dc, mforall dp, (C dc) m-> (P dp) m-> (m~ (dp m= dc)) m-> (m~ Vic) ].

(* The probability of victory after switching is two thirds. *)
Lemma prob_after_switch_is_two_thirds: [ (At s0 (probPred Vic (cons hide (cons (pick d1) (cons open (cons switch nil) ) ) ) (2 # 3))) ].
Proof. mv.
unfold At.
unfold probPred.
unfold prob.
destruct (hide_ax s0) as [w1 [w2 [w3 H ]]].
destruct H as [H [H1C [H2C H3C]]].
rewrite H. simpl.
destruct (pick_ax w1 d1) as [w11 [H11 H11P]].
destruct (pick_ax w2 d1) as [w21 [H21 H21P]].
destruct (pick_ax w3 d1) as [w31 [H31 H31P]].
rewrite H11; rewrite H21; rewrite H31; simpl.
assert (C d1 w11).
  apply (pick_frame_ax w1 d1 d1 H1C); unfold r; unfold is_in; rewrite H11; left; reflexivity.

  assert (C d2 w21).
    apply (pick_frame_ax w2 d2 d1 H2C); unfold r; unfold is_in; rewrite H21; left; reflexivity.

    assert (C d3 w31).
      apply (pick_frame_ax w3 d3 d1 H3C); unfold r; unfold is_in; rewrite H31; left; reflexivity.

      destruct (open_ax2 w11 d1 H0 H11P) as [w112 [w113 [d112o [d113o [H11Open [D112_1 [D113_1 [D112_113 [H112O H113O]]]]] ]]]].
      rewrite H11Open; simpl.
      destruct (open_ax1 w21 d2 d1 H1 H21P) as [w213 [H21Open [d213o [D213_2  [D213_1 H213O]] ] ]].
      rewrite H21Open; simpl.
      destruct (open_ax1 w31 d3 d1 H2 H31P) as [w312 [H31Open [d312o [D312_3  [D312_1 H312O]] ] ]].
      rewrite H31Open; simpl.

      induction d312o.
        exfalso. apply D312_1. reflexivity.

        Focus 2. exfalso. apply D312_3. reflexivity.
        induction d213o.
          exfalso. apply D213_1. reflexivity.

          exfalso; apply D213_2; reflexivity.
          induction d113o.
            exfalso; apply D113_1; reflexivity.

            induction d112o.
              exfalso; apply D112_1; reflexivity.
 
              exfalso; apply D112_113; reflexivity.
              Focus 2.
              induction d112o.
                exfalso; apply D112_1; reflexivity.

                assert (P d1 w112).
                  apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                  destruct (switch1 w112 d2 d1 H112O) as [w1123 [H1123S [d3n [D3n_2 [D3n_1 H1123P]]]]].
                    exact H3.

                    induction d3n.
                      exfalso; apply D3n_1; reflexivity.

                      exfalso; apply D3n_2; reflexivity.

                      rewrite H1123S; simpl.
                      assert (P d1 w113).
                        apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                        destruct (switch1 w113 d3 d1 H113O) as [w1132 [H1132S [d2n [D2n_3 [D2n_1 H1132P]]]]].
                          exact H4.

                          induction d2n.
                            exfalso; apply D2n_1; reflexivity.

                            Focus 2. exfalso; apply D2n_3; reflexivity.

                            rewrite H1132S; simpl.
                            assert (P d1 w213).
                              apply (open_frame_P_ax w21 d1 H21P); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                              destruct (switch1 w213 d3 d1 H213O) as [w2132 [H2132S [d2132 [D2132_3 [D2132_1 H2132P]]]]].
                                exact H5.

                                induction d2132.
                                  exfalso; apply D2132_1; reflexivity.

                                  Focus 2. exfalso; apply D2132_3; reflexivity.

                                  rewrite H2132S; simpl.
                                  assert (P d1 w312).
                                    apply (open_frame_P_ax w31 d1 H31P); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                    destruct (switch1 w312 d2 d1 H312O) as [w3123 [H3123S [d3123 [D3123_2 [D3123_1 H3123P]]]]].
                                      exact H6.

                                      induction d3123.
                                        exfalso; apply D3123_1; reflexivity.

                                        exfalso; apply D3123_2; reflexivity.

                                        rewrite H3123S; simpl.

                                        assert (C d1 w112).
                                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                                          assert (C d1 w1123).
                                            apply (switch_frame_ax w112 d1 H7); unfold r; unfold is_in; rewrite H1123S; left; reflexivity.

                                        assert (C d1 w113).
                                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                                          assert (C d1 w1132).
                                            apply (switch_frame_ax w113 d1 H9); unfold r; unfold is_in; rewrite H1132S; left; reflexivity.

                                        assert (C d2 w213).
                                          apply (open_frame_C_ax w21 d2 H1); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                                          assert (C d2 w2132).
                                            apply (switch_frame_ax w213 d2 H12); unfold r; unfold is_in; rewrite H2132S; left; reflexivity.

                                        assert (C d3 w312).
                                          apply (open_frame_C_ax w31 d3 H2); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                          assert (C d3 w3123).
                                            apply (switch_frame_ax w312 d3 H14); unfold r; unfold is_in; rewrite H3123S; left; reflexivity.

                                        assert (Vic w3123). apply (victory w3123 d3); [exact H15 | exact H3123P].
                                        assert (Vic w2132). apply (victory w2132 d2); [exact H13 | exact H2132P].
                                        assert (~ (Vic w1123)). apply (defeat w1123 d1 d3). exact H8. exact H1123P. unfold mnot. unfold mequal. intro Equal_d3_d1. discriminate Equal_d3_d1.
                                        assert (~ (Vic w1132)). apply (defeat w1132 d1 d2). exact H10. exact H1132P. unfold mnot. unfold mequal. intro Equal_d2_d1. discriminate Equal_d2_d1.
                                        destruct (dec Vic w1123). 
                                          contradiction. 

                                        destruct (dec Vic w1132).
                                          contradiction.

                                        destruct (dec Vic w2132).
                                        destruct (dec Vic w3123).
                                          reflexivity.

                                          contradiction.

                                          contradiction.

                                          exfalso; apply D112_113; reflexivity.

(* Analogous to previous case *)

                assert (P d1 w112).
                  apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                  destruct (switch1 w112 d3 d1 H112O) as [w1123 [H1123S [d3n [D3n_2 [D3n_1 H1123P]]]]].
                    exact H3.

                    induction d3n.
                      exfalso; apply D3n_1; reflexivity.

                      Focus 2. exfalso; apply D3n_2; reflexivity.

                      rewrite H1123S; simpl.
                      assert (P d1 w113).
                        apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                        destruct (switch1 w113 d2 d1 H113O) as [w1132 [H1132S [d2n [D2n_3 [D2n_1 H1132P]]]]].
                          exact H4.

                          induction d2n.
                            exfalso; apply D2n_1; reflexivity.

                            exfalso; apply D2n_3; reflexivity.

                            rewrite H1132S; simpl.
                            assert (P d1 w213).
                              apply (open_frame_P_ax w21 d1 H21P); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                              destruct (switch1 w213 d3 d1 H213O) as [w2132 [H2132S [d2132 [D2132_3 [D2132_1 H2132P]]]]].
                                exact H5.

                                induction d2132.
                                  exfalso; apply D2132_1; reflexivity.

                                  Focus 2. exfalso; apply D2132_3; reflexivity.

                                  rewrite H2132S; simpl.
                                  assert (P d1 w312).
                                    apply (open_frame_P_ax w31 d1 H31P); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                    destruct (switch1 w312 d2 d1 H312O) as [w3123 [H3123S [d3123 [D3123_2 [D3123_1 H3123P]]]]].
                                      exact H6.

                                      induction d3123.
                                        exfalso; apply D3123_1; reflexivity.

                                        exfalso; apply D3123_2; reflexivity.

                                        rewrite H3123S; simpl.

                                        assert (C d1 w112).
                                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                                          assert (C d1 w1123).
                                            apply (switch_frame_ax w112 d1 H7); unfold r; unfold is_in; rewrite H1123S; left; reflexivity.

                                        assert (C d1 w113).
                                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                                          assert (C d1 w1132).
                                            apply (switch_frame_ax w113 d1 H9); unfold r; unfold is_in; rewrite H1132S; left; reflexivity.

                                        assert (C d2 w213).
                                          apply (open_frame_C_ax w21 d2 H1); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                                          assert (C d2 w2132).
                                            apply (switch_frame_ax w213 d2 H12); unfold r; unfold is_in; rewrite H2132S; left; reflexivity.

                                        assert (C d3 w312).
                                          apply (open_frame_C_ax w31 d3 H2); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                          assert (C d3 w3123).
                                            apply (switch_frame_ax w312 d3 H14); unfold r; unfold is_in; rewrite H3123S; left; reflexivity.

                                        assert (Vic w3123). apply (victory w3123 d3); [exact H15 | exact H3123P].
                                        assert (Vic w2132). apply (victory w2132 d2); [exact H13 | exact H2132P].
                                        assert (~ (Vic w1123)). apply (defeat w1123 d1 d2). exact H8. exact H1123P. unfold mnot. unfold mequal. intro Equal_d3_d1. discriminate Equal_d3_d1.
                                        assert (~ (Vic w1132)). apply (defeat w1132 d1 d3). exact H10. exact H1132P. unfold mnot. unfold mequal. intro Equal_d2_d1. discriminate Equal_d2_d1.
                                        destruct (dec Vic w1123). 
                                          contradiction. 

                                        destruct (dec Vic w1132).
                                          contradiction.

                                        destruct (dec Vic w2132).
                                        destruct (dec Vic w3123).
                                          reflexivity.

                                          contradiction.

                                          contradiction.
Qed.

(* The probability of victory without switching is one third. *)
Lemma prob_without_switch_is_one_third: [ (At s0 (probPred Vic (cons hide (cons (pick d1) (cons open (cons noswitch nil) ) ) ) (1 # 3))) ].
Proof.
(* Analogous to the proof of the previous lemma *)
mv.
unfold At.
unfold probPred.
unfold prob.
destruct (hide_ax s0) as [w1 [w2 [w3 H ]]].
destruct H as [H [H1C [H2C H3C]]].
rewrite H. simpl.
destruct (pick_ax w1 d1) as [w11 [H11 H11P]].
destruct (pick_ax w2 d1) as [w21 [H21 H21P]].
destruct (pick_ax w3 d1) as [w31 [H31 H31P]].
rewrite H11; rewrite H21; rewrite H31; simpl.
assert (C d1 w11).
  apply (pick_frame_ax w1 d1 d1 H1C); unfold r; unfold is_in; rewrite H11; left; reflexivity.

  assert (C d2 w21).
    apply (pick_frame_ax w2 d2 d1 H2C); unfold r; unfold is_in; rewrite H21; left; reflexivity.

    assert (C d3 w31).
      apply (pick_frame_ax w3 d3 d1 H3C); unfold r; unfold is_in; rewrite H31; left; reflexivity.

      destruct (open_ax2 w11 d1 H0 H11P) as [w112 [w113 [d112o [d113o [H11Open [D112_1 [D113_1 [D112_113 [H112O H113O]]]]] ]]]].
      rewrite H11Open; simpl.
      destruct (open_ax1 w21 d2 d1 H1 H21P) as [w213 [H21Open [d213o [D213_2  [D213_1 H213O]] ] ]].
      rewrite H21Open; simpl.
      destruct (open_ax1 w31 d3 d1 H2 H31P) as [w312 [H31Open [d312o [D312_3  [D312_1 H312O]] ] ]].
      rewrite H31Open; simpl.

      induction d312o.
        exfalso. apply D312_1. reflexivity.

        Focus 2. exfalso. apply D312_3. reflexivity.
        induction d213o.
          exfalso. apply D213_1. reflexivity.

          exfalso; apply D213_2; reflexivity.
          induction d113o.
            exfalso; apply D113_1; reflexivity.

            induction d112o.
              exfalso; apply D112_1; reflexivity.
 
              exfalso; apply D112_113; reflexivity.
              Focus 2.
              induction d112o.
                exfalso; apply D112_1; reflexivity.

                assert (P d1 w112).
                  apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                  destruct (noswitch1 w112 d1 H3) as [w1121 [H1121S H1121P]].
                  rewrite H1121S; simpl.
                  assert (P d1 w113).
                    apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                    destruct (noswitch1 w113 d1 H4) as [w1131 [H1131S H1131P]].
                    rewrite H1131S; simpl.
                    assert (P d1 w213).
                      apply (open_frame_P_ax w21 d1 H21P); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                      destruct (noswitch1 w213 d1 H5) as [w2131 [H2131S H2131P]].
                      rewrite H2131S; simpl.
                      assert (P d1 w312).
                        apply (open_frame_P_ax w31 d1 H31P); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                        destruct (noswitch1 w312 d1 H6) as [w3121 [H3121S H3121P]].
                        rewrite H3121S; simpl.
                        assert (C d1 w112).
                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                          assert (C d1 w1121).
                            apply (noswitch_frame_ax w112 d1 H7); unfold r; unfold is_in; rewrite H1121S; left; reflexivity.

                            assert (C d1 w113).
                              apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                              assert (C d1 w1131).
                                apply (noswitch_frame_ax w113 d1 H9); unfold r; unfold is_in; rewrite H1131S; left; reflexivity.

                                assert (C d2 w213).
                                  apply (open_frame_C_ax w21 d2 H1); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                                  assert (C d2 w2131).
                                    apply (noswitch_frame_ax w213 d2 H12); unfold r; unfold is_in; rewrite H2131S; left; reflexivity.

                                    assert (C d3 w312).
                                      apply (open_frame_C_ax w31 d3 H2); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                      assert (C d3 w3121).
                                        apply (noswitch_frame_ax w312 d3 H14); unfold r; unfold is_in; rewrite H3121S; left; reflexivity.

                                        assert (Vic w1121). apply (victory w1121 d1); [exact H8 | exact H1121P].
                                        assert (Vic w1131). apply (victory w1131 d1); [exact H10 | exact H1131P].
                                        assert (~ (Vic w3121)). apply (defeat w3121 d3 d1). exact H15. exact H3121P. unfold mnot. unfold mequal. intro Equal_d3_d1. discriminate Equal_d3_d1.
                                        assert (~ (Vic w2131)). apply (defeat w2131 d2 d1). exact H13. exact H2131P. unfold mnot. unfold mequal. intro Equal_d2_d1. discriminate Equal_d2_d1.
                                        destruct (dec Vic w1121). 
                                          Focus 2. contradiction. 

                                        destruct (dec Vic w1131).
                                          Focus 2. contradiction.

                                        destruct (dec Vic w2131).
                                          contradiction. 

                                        destruct (dec Vic w3121).
                                          contradiction.

                                          reflexivity.

(* Analogous to previous case *)

                assert (P d1 w112).
                  apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                  destruct (noswitch1 w112 d1 H3) as [w1121 [H1121S H1121P]].
                  rewrite H1121S; simpl.
                  assert (P d1 w113).
                    apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                    destruct (noswitch1 w113 d1 H4) as [w1131 [H1131S H1131P]].
                    rewrite H1131S; simpl.
                    assert (P d1 w213).
                      apply (open_frame_P_ax w21 d1 H21P); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                      destruct (noswitch1 w213 d1 H5) as [w2131 [H2131S H2131P]].
                      rewrite H2131S; simpl.
                      assert (P d1 w312).
                        apply (open_frame_P_ax w31 d1 H31P); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                        destruct (noswitch1 w312 d1 H6) as [w3121 [H3121S H3121P]].
                        rewrite H3121S; simpl.
                        assert (C d1 w112).
                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                          assert (C d1 w1121).
                            apply (noswitch_frame_ax w112 d1 H7); unfold r; unfold is_in; rewrite H1121S; left; reflexivity.

                            assert (C d1 w113).
                              apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                              assert (C d1 w1131).
                                apply (noswitch_frame_ax w113 d1 H9); unfold r; unfold is_in; rewrite H1131S; left; reflexivity.

                                assert (C d2 w213).
                                  apply (open_frame_C_ax w21 d2 H1); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                                  assert (C d2 w2131).
                                    apply (noswitch_frame_ax w213 d2 H12); unfold r; unfold is_in; rewrite H2131S; left; reflexivity.

                                    assert (C d3 w312).
                                      apply (open_frame_C_ax w31 d3 H2); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                      assert (C d3 w3121).
                                        apply (noswitch_frame_ax w312 d3 H14); unfold r; unfold is_in; rewrite H3121S; left; reflexivity.

                                        assert (Vic w1121). apply (victory w1121 d1); [exact H8 | exact H1121P].
                                        assert (Vic w1131). apply (victory w1131 d1); [exact H10 | exact H1131P].
                                        assert (~ (Vic w3121)). apply (defeat w3121 d3 d1). exact H15. exact H3121P. unfold mnot. unfold mequal. intro Equal_d3_d1. discriminate Equal_d3_d1.
                                        assert (~ (Vic w2131)). apply (defeat w2131 d2 d1). exact H13. exact H2131P. unfold mnot. unfold mequal. intro Equal_d2_d1. discriminate Equal_d2_d1.
                                        destruct (dec Vic w1121). 
                                          Focus 2. contradiction. 

                                        destruct (dec Vic w1131).
                                          Focus 2. contradiction.

                                        destruct (dec Vic w2131).
                                          contradiction. 

                                        destruct (dec Vic w3121).
                                          contradiction.

                                          reflexivity.


                assert (P d1 w112).
                  apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                  destruct (noswitch1 w112 d1 H3) as [w1121 [H1121S H1121P]].
                  rewrite H1121S; simpl.
                  assert (P d1 w113).
                    apply (open_frame_P_ax w11 d1 H11P); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                    destruct (noswitch1 w113 d1 H4) as [w1131 [H1131S H1131P]].
                    rewrite H1131S; simpl.
                    assert (P d1 w213).
                      apply (open_frame_P_ax w21 d1 H21P); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                      destruct (noswitch1 w213 d1 H5) as [w2131 [H2131S H2131P]].
                      rewrite H2131S; simpl.
                      assert (P d1 w312).
                        apply (open_frame_P_ax w31 d1 H31P); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                        destruct (noswitch1 w312 d1 H6) as [w3121 [H3121S H3121P]].
                        rewrite H3121S; simpl.
                        assert (C d1 w112).
                          apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; left; reflexivity.

                          assert (C d1 w1121).
                            apply (noswitch_frame_ax w112 d1 H7); unfold r; unfold is_in; rewrite H1121S; left; reflexivity.

                            assert (C d1 w113).
                              apply (open_frame_C_ax w11 d1 H0); unfold r; unfold is_in; rewrite H11Open; right; left; reflexivity.

                              assert (C d1 w1131).
                                apply (noswitch_frame_ax w113 d1 H9); unfold r; unfold is_in; rewrite H1131S; left; reflexivity.

                                assert (C d2 w213).
                                  apply (open_frame_C_ax w21 d2 H1); unfold r; unfold is_in; rewrite H21Open; left; reflexivity.

                                  assert (C d2 w2131).
                                    apply (noswitch_frame_ax w213 d2 H12); unfold r; unfold is_in; rewrite H2131S; left; reflexivity.

                                    assert (C d3 w312).
                                      apply (open_frame_C_ax w31 d3 H2); unfold r; unfold is_in; rewrite H31Open; left; reflexivity.

                                      assert (C d3 w3121).
                                        apply (noswitch_frame_ax w312 d3 H14); unfold r; unfold is_in; rewrite H3121S; left; reflexivity.

                                        assert (Vic w1121). apply (victory w1121 d1); [exact H8 | exact H1121P].
                                        assert (Vic w1131). apply (victory w1131 d1); [exact H10 | exact H1131P].
                                        assert (~ (Vic w3121)). apply (defeat w3121 d3 d1). exact H15. exact H3121P. unfold mnot. unfold mequal. intro Equal_d3_d1. discriminate Equal_d3_d1.
                                        assert (~ (Vic w2131)). apply (defeat w2131 d2 d1). exact H13. exact H2131P. unfold mnot. unfold mequal. intro Equal_d2_d1. discriminate Equal_d2_d1.
                                        destruct (dec Vic w1121). 
                                          Focus 2. contradiction. 

                                        destruct (dec Vic w1131).
                                          Focus 2. contradiction.

                                        destruct (dec Vic w2131).
                                          contradiction. 

                                        destruct (dec Vic w3121).
                                          contradiction.

                                          reflexivity.
Qed.

(* Therefore, switching is better than not switching. *)
Theorem switch_is_better_than_noswitch: [ mexists p_switch, mexists p_noswitch, (At s0 (probPred Vic (cons hide (cons (pick d1) (cons open (cons switch nil) ) ) ) p_switch)) m/\ (At s0 (probPred Vic (cons hide (cons (pick d1) (cons open (cons noswitch nil) ) ) ) p_noswitch)) m/\ (fun w => p_switch > p_noswitch)].
Proof. mv.
exists (2 # 3).
exists (1 # 3).
split.
  apply prob_after_switch_is_two_thirds.

  split.
   apply prob_without_switch_is_one_third.

   unfold Qlt. simpl. omega.
Qed.
