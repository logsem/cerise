From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros_new.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import monotone.
From cap_machine Require Import solve_pure proofmode map_simpl.

Definition addrwordLO := listO (prodO (leibnizO Addr) (leibnizO Word)).
Definition prefR (al al' : addrwordLO) := al `prefix_of` al'.
Class sealLLG Σ := CCounterG { ccounter_inG :> inG Σ (authUR (monotoneUR prefR)) }.

Section list.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}
          {mono : sealLLG Σ}.

  (* ------------------------------------------------------------------------------------------------- *)
  (* --------------------------- The monotone list of addresses -------------------------------------- *)

  Definition Exact γ a := (own γ (● (principal prefR a)))%I.
  Definition prefLL γ a := (own γ (◯ (principal prefR a)))%I.

  Lemma get_full_pref γ a :
    Exact γ a ==∗ Exact γ a ∗ prefLL γ a.
  Proof.
    iIntros "H".
    iMod (own_update _ _ ((● (principal prefR a)) ⋅ (◯ (principal prefR a)))
            with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply local_update_unital_discrete.
    intros ? ?; rewrite left_id; intros <-.
    split; first done.
      by rewrite principal_R_op.
  Qed.

  Lemma get_partial_pref γ a a' :
    a' `prefix_of` a → Exact γ a ==∗ Exact γ a ∗ prefLL γ a'.
  Proof.
    iIntros (Hpre) "H".
    iMod (own_update _ _ ((● (principal prefR a)) ⋅ (◯ (principal prefR a')))
            with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply local_update_unital_discrete.
    intros ? ?; rewrite left_id; intros <-.
    split; first done.
      by rewrite principal_R_op.
  Qed.

  Lemma know_pref γ a a' :
    Exact γ a -∗ prefLL γ a' -∗ ⌜a' `prefix_of` a⌝.
  Proof.
    iIntros "H1 H2".
      by iDestruct (own_valid_2 with "H1 H2") as
        %[?%(principal_included (R := prefR)) _]%auth_both_valid_discrete.
  Qed.

  Lemma update_ll γ a a' :
    a `prefix_of` a' → Exact γ a ==∗ Exact γ a' ∗ prefLL γ a'.
  Proof.
    iIntros (Hs) "H".
    iMod (own_update _ _ ((● (principal prefR a')) ⋅ (◯ (principal prefR a')))
            with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply local_update_unital_discrete.
    intros ? ?; rewrite left_id; intros <-.
    split; first done.
    by rewrite (comm op) (principal_R_op a a').
  Qed.

  Lemma snoc_ll γ a al :
    Exact γ al ==∗ Exact γ (al ++ [a]) ∗ prefLL γ (al ++ [a]).
  Proof.
    iApply update_ll.
    apply prefix_app_r. auto.
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* ----------- The isList predicate defines the proposition for a Key LL for seals ----------------- *)

  (* each link of the KeyLL for seals must be of the form (RWX,a,a+3,a), or WInt 0 for the tail *)

  Fixpoint isList (hd : Word) (awvals : list (Addr * Word)) : iProp Σ :=
    match awvals with
    | [] => (⌜hd = WInt 0%Z⌝)%I
    | (p1,w) :: awvals => (∃ hd' p p2 p3, ⌜ (p + 1)%a = Some p1
                                        ∧ (p + 2)%a = Some p2
                                        ∧ (p + 3)%a = Some p3
                                        ∧ hd = WCap RWX p p3 p1⌝
                                          ∗ p1 ↦ₐ w
                                          ∗ p2 ↦ₐ hd'
                                          ∗ isList hd' awvals)%I
    end.

  (* the sealLL invariant *)
  Definition sealLL ι ll γ (Φ : Word -> iProp Σ) {Hpers : ∀ w, Persistent (Φ w)} : iProp Σ
    := na_inv logrel_nais ι (∃ hd, ll ↦ₐ hd
                             ∗ ∃ awvals, isList hd awvals
                                         ∗ Exact γ awvals
                                         ∗ ([∗ list] aw ∈ awvals, Φ aw.2))%I.

  Lemma isList_length_hd vals :
    ⊢ isList (WInt 0%Z) vals → ⌜vals = []⌝.
  Proof.
    destruct vals as [| [p w] vals ];simpl;try iIntros (Hcontr);auto. iIntros "HH".
    iDestruct "HH" as (? ? ? ? (_&_&_&?)) "HH". done.
  Qed.

  Lemma isList_hd_length hd :
    ⊢ isList hd [] → ⌜hd = WInt 0%Z⌝.
  Proof.
    iIntros "H". simpl. done.
  Qed.

  Instance isList_timeless d bvals: (Timeless (isList d bvals)).
  Proof.
    intros. rewrite /isList.
    revert d. induction bvals as [| [p w] bvals]; apply _.
  Qed.

  Lemma isList_hd hd bvals :
    isList hd bvals -∗ ⌜hd = WInt 0%Z⌝ ∨
    ∃ p p1 p3 w, ⌜(p + 1)%a = Some p1 ∧ (p + 3)%a = Some p3 ∧ hd = WCap RWX p p3 p1⌝ ∗ p1 ↦ₐ w.
  Proof.
    iIntros "Hlist".
    destruct bvals as [|[p w] bvals'];simpl.
    - iSimplifyEq. by iLeft.
    - iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]". iRight.
      iExists _,_,_,_. iFrame "Hd". eauto.
  Qed.

  Lemma isList_hd_pure hd bvals :
    isList hd bvals -∗ ⌜hd = WInt 0%Z ∧ bvals = []⌝ ∨
    ∃ p p1 p3 w, ⌜(p + 1)%a = Some p1 ∧ (p + 3)%a = Some p3 ∧ hd = WCap RWX p p3 p1 ∧ (p1,w) ∈ bvals⌝.
  Proof.
    iIntros "Hlist".
    destruct bvals as [|[p w] bvals'];simpl.
    - iSimplifyEq. by iLeft.
    - iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]". iRight.
      iExists _,_,_,_. repeat iSplit;eauto. iPureIntro. constructor.
  Qed.

  Lemma isList_in hd ptrs a w :
    (a,w) ∈ ptrs ->
    isList hd ptrs -∗ a ↦ₐ w.
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (ptrs) as [|[p w'] ptrs] "IH" forall (hd).
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + inversion Heq. subst.
        simpl. iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        simplify_eq. auto.
      + simpl.
        iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as "Hw";auto.
  Qed.

  Lemma isList_in_fst hd ptrs a :
    a ∈ ptrs.*1 ->
    isList hd ptrs -∗ ∃ w, a ↦ₐ w.
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (ptrs) as [|[p w'] ptrs] "IH" forall (hd).
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + inversion Heq. subst.
        simpl. iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
         simplify_eq. eauto.
      + simpl.
        iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as "Hw";auto.
  Qed.

  Lemma isList_cut hd bvals a' w :
    (a',w) ∈ bvals ->
    isList hd bvals -∗
    ∃ l1 l2 a a'', ⌜bvals = l1 ++ l2 ∧ (a + 3)%a = Some a'' ∧ (a + 1)%a = Some a'⌝ ∗ isList (WCap RWX a a'' a') l2.
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (bvals) as [|[p w'] bvals'] "IH" forall (hd).
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin];[inversion Heq;subst|].
      + simpl. iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iExists [],((p,w')::bvals'),p',p'''. simpl. iFrame. iSplit;auto.
        iExists _,_,_,_. iFrame. eauto.
      + simpl. iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as (l1 l2 a a'' (Heq&Hnext1&Hnext2)) "Hlist";auto.
        iExists ((p,w') :: l1),l2,a,a''. iFrame. rewrite !Heq. auto.
  Qed.

  Lemma isList_NoDup hd ptrs :
    isList hd ptrs -∗ ⌜NoDup (ptrs.*1)⌝.
  Proof.
    iIntros "Hlist".
    iInduction (ptrs) as [|[p w] ptrs'] "IH" forall (hd).
    - iPureIntro. apply NoDup_nil. auto.
    - simpl. rewrite NoDup_cons.
      iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
      iDestruct ("IH" with "Hlist") as %Hdup;auto.
      iSplit;auto. iIntros (Hcontr).
      destruct ptrs' as [|[p4 w'''] ptrs'''];[inversion Hcontr|].
      simpl. iDestruct "Hlist" as (hd1 p1 p2 p3 ?) "[Hp [Hp' Hlist] ]".
      apply elem_of_list_fmap in Hcontr as [ [y k] [Heqy Hcontr] ].
      apply elem_of_cons in Hcontr as [Heq | Hcontr];subst.
      + inversion Heq. iApply (addr_dupl_false with "Hd Hp").
      + iDestruct (isList_in with "Hlist") as "Hw";[apply Hcontr|].
        iApply (addr_dupl_false with "Hd Hw").
  Qed.

  Lemma last_rest {A} (l : list A) (a : A) :
    a ∈ l → list.last l ≠ Some a -> ∃ l' rest, l = l' ++ rest ∧ a ∈ l' ∧ length rest > 0.
  Proof.
    intros Hin Hlast.
    induction l;[inversion Hin|].
    destruct l.
    - apply elem_of_list_singleton in Hin as ->. done.
    - apply elem_of_cons in Hin as [->|Hin].
      + exists [a0],(a1::l). repeat split;auto. constructor. simpl. lia.
      + apply IHl in Hin as [l' [rest [-> [Hin Hgt] ] ] ];auto.
        exists (a0::l'), rest. repeat split;auto. apply elem_of_cons. right;auto.
  Qed.

  Lemma rest_last {A} (l1 l2 l3 : list A) (a : A) :
    l1 `prefix_of` l2 ->
    l2 `prefix_of` l3 ->
    list.last l2 ≠ Some a ->
    NoDup l3 ->
    a ∈ l1 →
    list.last l3 ≠ Some a.
  Proof.
    intros Hpref1 Hpref2 Hlast Hdup Hin.
    destruct Hpref1,Hpref2.
    rewrite H -app_assoc in H0.
    destruct x0.
    { rewrite app_nil_r in H0. congruence. }
    rewrite H0 app_assoc -last_app_eq;[|simpl;lia].
    intros Hcontr. rewrite last_lookup /= in Hcontr.
    assert (a ∈ (a0 :: x0)) as Hin';[apply elem_of_list_lookup;eauto|].
    rewrite H0 in Hdup.
    apply NoDup_app in Hdup as (Hdup1 & Hnin & Hdup2).
    apply Hnin in Hin. apply not_elem_of_app in Hin as [_ Hin]. done.
  Qed.

  (* The following lemma extracts an element from the list, pointed to by a *)
  Lemma isList_extract_fst hd ptrs a :
    a ∈ ptrs.*1 ->
    isList hd ptrs -∗
    (∃ a' hd' w, ⌜(a + 1)%a = Some a' ∧ ((hd' = WInt 0%Z ∧ list.last ptrs.*1 = Some a)
                                         ∨ ∃ p0 p p3, (p0 + 1)%a = Some p ∧ (p0 + 3)%a = Some p3 ∧ hd' = WCap RWX p0 p3 p ∧ p ∈ ptrs.*1)⌝
                                                                                                                    ∗ a ↦ₐ w ∗ a' ↦ₐ hd'
    ∗ (a ↦ₐ w ∗ a' ↦ₐ hd' -∗ isList hd ptrs)).
  Proof.
    iIntros (Hin) "Hlist".
    apply elem_of_list_lookup in Hin as [i Hi].
    assert (∃ b, ptrs.*2 !! i = Some b) as [b Hj].
    { apply lookup_lt_is_Some_2. rewrite fmap_length -(fmap_length fst). apply lookup_lt_is_Some_1. eauto. }
    iInduction (ptrs) as [|[p w] ptrs] "IH" forall (hd i Hi Hj).
    - inversion Hi.
    - destruct i.
      { inversion Hi. inversion Hj. subst.
        simpl. iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iExists p'',_,_. iFrame.
        iDestruct (isList_hd_pure with "Hlist") as %Hhd'.
        repeat iSplit;auto. iPureIntro. solve_addr. iPureIntro. destruct Hhd' as [ [-> ->] | [? [? (?&?&?&?&?&?)] ] ];auto.
        right. repeat eexists;eauto. constructor. apply elem_of_list_fmap. exists (x0,x2); eauto.
        iIntros "[Ha Ha']".
        iExists _,_,_,_;iFrame. iSplit;auto. }
      { simpl in Hi,Hj.
        iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] [] Hlist") as (a' hd2 w2 (Hnext&Hhd')) "[Ha [Ha' Hcls ] ]";eauto.
        iExists _,_,_. iFrame.
        apply list_lookup_fmap_inv in Hi as [ [y1 y2] [Heqy Hi] ].
        apply list_lookup_fmap_inv in Hj as [ [k1 k2] [Heqk Hj] ]. simplify_eq.
        iSplit;auto.
        iPureIntro. split;auto. destruct Hhd' as [ [-> Heq] | [? [? (?&?&?&?&?)] ] ];auto.
        - left. rewrite fmap_cons. simpl. split;auto. rewrite Heq.
          destruct ptrs;inversion Heq. auto.
        - right. exists x,x0,x1. repeat split;eauto. constructor;auto.
        - iIntros "[Ha Ha']". iExists _,_,_,_. iSplit;eauto. iFrame.
          iApply "Hcls". iFrame.
      }
  Qed.

  Lemma isList_extract hd ptrs a w :
    (a,w) ∈ ptrs ->
    isList hd ptrs -∗
    (∃ a' hd', ⌜(a + 1)%a = Some a' ∧ ((hd' = WInt 0%Z ∧ list.last ptrs = Some (a,w))
                                       ∨ ∃ p0 p1 p3 w', (p0 + 1)%a = Some p1 ∧ (p0 + 3)%a = Some p3 ∧ hd' = WCap RWX p0 p3 p1 ∧ (p1,w') ∈ ptrs)⌝
                                                                                                                            ∗ a ↦ₐ w ∗ a' ↦ₐ hd'
    ∗ (a ↦ₐ w ∗ a' ↦ₐ hd' -∗ isList hd ptrs)).
  Proof.
    iIntros (Hin) "Hlist".
    apply elem_of_list_lookup in Hin as [i Hiz].
    iInduction (ptrs) as [|[p w'] ptrs] "IH" forall (hd i Hiz).
    - inversion Hiz.
    - destruct i.
      { inversion Hiz. subst. iSimpl in "Hlist".
        iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iExists _,_. iFrame.
        iDestruct (isList_hd_pure with "Hlist") as %Hhd'.
        repeat iSplit;auto. iPureIntro. solve_addr. destruct Hhd' as [ [-> ->] | [? [? (?&?&?&?&?&?)] ] ];auto.
        iPureIntro. right. repeat eexists;eauto. constructor. eauto.
        iIntros "[Ha Ha']".
        iExists _,_,_,_;iFrame. iSplit;auto. }
      { simpl in *.
        iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as (a' hd2 (Hnext&Hhd')) "[Ha [Ha' Hcls ] ]";eauto.
        iExists _,_. iFrame. iSplit;auto.
        iPureIntro. split;auto. destruct Hhd' as [ [-> Heq] | [? [? (?&?&?&?&?&?)] ] ];auto.
        destruct ptrs;inversion Heq. auto.
        right. repeat eexists;eauto. constructor;eauto.
        iIntros "[Ha Ha']". iExists _,_,_,_. iSplit;eauto. iFrame.
        iApply "Hcls". iFrame.
      }
  Qed.

  Lemma isList_extract_last hd ptrs a w :
    list.last ptrs = Some (a,w) ->
    isList hd ptrs -∗
    (∃ a', ⌜(a + 1)%a = Some a'⌝ ∗ a ↦ₐ w ∗ a' ↦ₐ WInt 0%Z
    ∗ (a ↦ₐ w ∗ a' ↦ₐ WInt 0%Z -∗ isList hd ptrs)).
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (ptrs) as [|[p w'] ptrs] "IH" forall (hd);[inversion Hin|].
    simpl. destruct ptrs.
    - iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hp [Hp' ->] ]".
      iExists _. inversion Hin;subst. iFrame. iSplit;auto. iPureIntro. solve_addr.
      iIntros "[Ha Hp']". iExists _,_,_. iFrame.
      repeat iSplit;eauto.
    - iDestruct "Hlist" as (hd' p' p'' p''' (?&?&?&->)) "[Hp [Hp' Hlist] ]".
      iDestruct ("IH" with "[] Hlist") as (a' Hincr) "(Ha & Ha' & Hcls)";auto.
      iExists _. iFrame. iSplit;auto.
      iIntros "[Ha Ha']".
      iExists _,_,_,_. iSplit;eauto. iFrame. iApply "Hcls". iFrame.
  Qed.

  (* the following lemma extracts and appends a new element to the last element of the list *)
  Lemma isList_extract_and_append_last hd ptrs a w' w p0 p1 p2 p3 :
    list.last ptrs = Some (a,w') →
    isList hd (ptrs) -∗
    (∃ a', ⌜(a + 1)%a = Some a'⌝ ∗ a ↦ₐ w' ∗ a' ↦ₐ WInt 0%Z
    ∗ (a ↦ₐ w' ∗ a' ↦ₐ WCap RWX p0 p3 p1 ∗ ⌜(p0 + 1)%a = Some p1 ∧ (p1 + 2)%a = Some p3 ∧ (p1 + 1)%a = Some p2⌝
       ∗ p1 ↦ₐ w ∗ p2 ↦ₐ WInt 0%Z -∗ isList hd (ptrs++[(p1,w)]))).
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (ptrs) as [|[p2' w2] ptrs] "IH" forall (hd Hin).
    - inversion Hin.
    - simpl. iDestruct "Hlist" as (hd' p0' p0'' p0''' (?&?&?&->)) "[Hd [Hd' Hlist] ]".
      destruct ptrs.
      + inversion Hin. subst.
        simpl. iDestruct "Hlist" as "->".
        iExists p0''. iFrame. iSplit;auto. iPureIntro. solve_addr.
        iIntros "(Ha & Ha' & (%&%&%) & Hp & Hp')". iExists _,p0',p0'',p0'''. iFrame. simplify_eq.
        subst; iSplit;auto. iExists _,_,_,_. iFrame. repeat iSplit;eauto.
        iPureIntro. solve_addr. iPureIntro. solve_addr.
      + iDestruct ("IH" with "[] Hlist") as (a' ?) "[Ha [Ha' Hcls] ]";auto.
        iExists _;iFrame. iSplit;auto.
        iIntros "(Ha & Ha' & (%&%&%) & Hp & Hp')". iExists _,_,_,_. iSplit;eauto. iFrame.
        iApply "Hcls". iFrame. auto.
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------- FINDB and APPEND ----------------------------------------- *)

  (* This find looks for an link address capability in the linked list which
     is of the following form: (-,b,-,-,-), where b is the input (Z) in r_t1 *)
  Definition findb_instr :=
    encodeInstrsW [ GetB r_t2 r_env
                  ; Sub r_t2 r_t2 r_t1
                  ; Mov r_t3 PC
                  ; Lea r_t3 6
                  ; Jnz r_t3 r_t2
                  ; Load r_t1 r_env
                  ; Mov r_t3 0
                  ; Jmp r_t0
                  ; Lea r_env 1
                  ; Load r_env r_env
                  ; Mov r_t2 PC
                  ; Lea r_t2 (-10)%Z
                  ; Jmp r_t2
                  ].

  Definition findb_loop a :=
    ([∗ list] a_i;w_i ∈ a;findb_instr, a_i ↦ₐ w_i)%I.

  Definition findb a :=
     ([∗ list] a_i;w_i ∈ a;load_r r_env r_env :: findb_instr, a_i ↦ₐ w_i)%I.

  (* The following appendb spec works on any word, but its specification will assume the structure of
     the input word to fit the LL for seals *)
  (* first we will define a macro which loops until the end of the linked list *)

  (* we have to be careful not to override the previous pointer, for when we reach the end *)
  (* the following iterate subroutine assumes the head is a pointer, and ends with the last
     pointer of the LL in r_env*)

  Definition iterate_to_last_instr (r temp1 temp2: RegName) :=
    encodeInstrsW [ Lea r 1
                    ; Load temp1 r
                    ; IsPtr temp1 temp1
                    ; Mov temp2 PC
                    ; Lea temp2 7
                    ; Jnz temp2 temp1
                    (* if r_env+1 points to a Z, r_env contains the last node of the list *)
                    ; Lea r (-1)%Z
                    ; Mov temp2 PC
                    ; Lea temp2 7
                    ; Jmp temp2
                    (* if r_env+1 points to a cap *)
                    ; Load r r
                    ; Mov temp2 PC
                    ; Lea temp2 (-11)%Z
                    ; Jmp temp2
                  ].

  Definition iterate_to_last a r temp1 temp2 :=
    ([∗ list] a_i;w_i ∈ a;iterate_to_last_instr r temp1 temp2, a_i ↦ₐ w_i)%I.

  Definition appendb_instr f_m :=
    encodeInstrsW [ Mov r_t6 r_t1
                  ]
                  ++ malloc_instrs f_m 3%nat ++
    encodeInstrsW [ Lea r_t1 1 (* move the pointer up one to leave place for the key *)
                    ; Store r_t1 r_t6 (* store the input value into the first cell of the allocated region *)
                    ; Load r_t4 r_env
                    ; IsPtr r_t2 r_t4 (* r_t2 = 1 if r_t2 is cap, = 0 otherwise *)
                    ; Mov r_t3 PC
                    ; Lea r_t3 7
                    ; Jnz r_t3 r_t2
                    (* r_env contains 0, we are done: the newly allocated capability is the head of the LL *)
                    ; Store r_env r_t1
                    ; Mov r_t3 0
                    ; Mov r_t6 0
                    ; Jmp r_t0
                  ]
    (* otherwise we must interate to last *)
    ++ iterate_to_last_instr r_t4 r_t2 r_t3 ++
    encodeInstrsW [ Lea r_t4 1
                  ; Store r_t4 r_t1
                  ; Mov r_t2 0
                  ; Mov r_t3 0
                  ; Mov r_t4 0
                  ; Mov r_t6 0
                  ; Jmp r_t0
                  ].

  Definition appendb a f_m :=
    ([∗ list] a_i;w_i ∈ a;appendb_instr f_m, a_i ↦ₐ w_i)%I.

  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------- SPECIFICATIONS ------------------------------------------- *)

  (* ------------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- APPEND ---------------------------------------------- *)

  (* TODO: move to rules/rules_Load.v *)
  Lemma wp_load_success_alt E r1 r2 pc_p pc_b pc_e pc_a w w' w'' p b e a pc_a' :
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap p b e a
             ∗ a ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  (* TODO: move to rules/rules_Load.v *)
  Lemma wp_load_success_same_alt E r1 pc_p pc_b pc_e pc_a w w' p b e a pc_a' :
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WCap p b e a
          ∗ ▷ a ↦ₐ w'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ w'
             ∗ pc_a ↦ₐ w
             ∗ a ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma iterate_to_last_spec_middle pc_p pc_b pc_e (* PC *)
        r temp1 temp2 (* temporary registers *)
        hd d d' d'' pbvals (* linked list head and pointers *)
        a_first (* special adresses *)
        φ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (iterate_to_last_instr r temp1 temp2))%a →

    (* linked list ptr element d *)
    (d + 3)%a = Some d'' →
    (d + 1)%a = Some d' →
    d' ∈ pbvals.*1 →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r ↦ᵣ WCap RWX d d'' d'
       ∗ (∃ w, temp1 ↦ᵣ w)
       ∗ (∃ w, temp2 ↦ᵣ w)
       (* list predicate for d *)
       ∗ isList hd pbvals
       (* trusted code *)
       ∗ codefrag a_first (iterate_to_last_instr r temp1 temp2)
       ∗ ▷ ((∃ dlast dlast' dlast'', PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (iterate_to_last_instr r temp1 temp2))%a
                        ∗ isList hd pbvals
                        ∗ ⌜list.last pbvals.*1 = Some dlast' ∧ (dlast + 1)%a = Some dlast' ∧ (dlast + 3)%a = Some dlast''⌝
                        ∗ r ↦ᵣ WCap RWX dlast dlast'' dlast'
                        ∗ (∃ w, temp1 ↦ᵣ w)
                        ∗ (∃ w, temp2 ↦ᵣ w)
                        ∗ codefrag a_first (iterate_to_last_instr r temp1 temp2))
              -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iLöb as "IH" forall (d d' d'' pbvals). (* we prove this spec by Löb induction for the case where we loop back *)
    iIntros (Hvpc Hcont Hd Hd' Hin) "(HPC & Hr_env & Htemp1 & Htemp2 & HisList & Hprog & Hφ)".
    iDestruct "Htemp1" as (w1) "Htemp1".
    iDestruct "Htemp2" as (w2) "Htemp2".

    assert (is_Some (d' + 1)%a) as [d2 Hd2];[clear -Hd Hd';destruct (d' + 1)%a eqn:Hnon;eauto;exfalso;solve_addr|].
    rewrite {6}/iterate_to_last_instr.
    codefrag_facts "Hprog". iInstr "Hprog".
    iDestruct (isList_extract_fst with "[$HisList]") as (a' hd' w (Hincr1&Hhd')) "[Ha [Ha' Hcls'] ]";
      [eauto..|]. rewrite Hincr1 in Hd2;inv Hd2.
    iInstr "Hprog". split; [solve_pure|]. solve_addr.
    iInstr "Hprog". iInstr "Hprog". iInstr "Hprog".
    destruct Hhd' as [Hhd' | Hhd'].
    { destruct Hhd' as [-> Hhd'].
      simpl is_cap. iInstr "Hprog".
      iGo "Hprog". instantiate (1 := d'). solve_addr.
      iGo "Hprog". generalize (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first ^+ 14)%a ltac:(destruct Hvpc; congruence)); rewrite /updatePcPerm; intros HX; rewrite HX; clear HX.
      iDestruct ("Hcls'" with "[$Ha' $Ha]") as "HisList".
      iApply "Hφ". iExists _, _,_. iFrame. iSplitR; [iPureIntro; auto|].
      iSplitL "Htemp1"; iExists _; eauto. }
    { destruct Hhd' as [p [p' [p'' [Hp'' [Hp' [-> Hp] ] ] ] ] ].
      simpl is_cap. iGo "Hprog". generalize (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first ^+ 10)%a ltac:(destruct Hvpc; congruence)); rewrite /updatePcPerm; intros HX; rewrite HX; clear HX.
      iGo "Hprog". solve_addr.
      iGo "Hprog". instantiate (1:= a_first). solve_addr.
      iInstr "Hprog". generalize (updatePcPerm_cap_non_E pc_p pc_b pc_e a_first ltac:(destruct Hvpc; congruence)); rewrite /updatePcPerm; intros HX; rewrite HX; clear HX.
      iDestruct ("Hcls'" with "[$Ha' $Ha]") as "HisList".
      iApply ("IH" with "[] [] [] [] [] [$HPC $Hr_env $HisList $Hφ Htemp1 Htemp2 Hprog]");auto.
      iFrame. iSplitL "Htemp1"; eauto. }
  Qed.

  Lemma iterate_to_last_spec pc_p pc_b pc_e (* PC *)
        r temp1 temp2 (* temporary registers *)
        hd pbvals (* linked list head and pointers *)
        a_first (* special adresses *)
        φ (* cont *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (iterate_to_last_instr r temp1 temp2))%a →

    (* linked list is not empty *)
    hd ≠ WInt 0%Z →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r ↦ᵣ hd
       ∗ (∃ w, temp1 ↦ᵣ w)
       ∗ (∃ w, temp2 ↦ᵣ w)
       (* list predicate for d *)
       ∗ isList hd pbvals
       (* trusted code *)
       ∗ codefrag a_first (iterate_to_last_instr r temp1 temp2)
       ∗ ▷ ((∃ dlast dlast' dlast'', PC ↦ᵣ WCap pc_p pc_b pc_e (a_first ^+ length (iterate_to_last_instr r temp1 temp2))%a
                        ∗ isList hd pbvals
                        ∗ ⌜list.last pbvals.*1 = Some dlast' ∧ (dlast + 1)%a = Some dlast' ∧ (dlast + 3)%a = Some dlast''⌝
                        ∗ r ↦ᵣ WCap RWX dlast dlast'' dlast'
                        ∗ (∃ w, temp1 ↦ᵣ w)
                        ∗ (∃ w, temp2 ↦ᵣ w)
                        ∗ codefrag a_first (iterate_to_last_instr r temp1 temp2))
              -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hne) "(HPC & Hr_env & Htemp1 & Htemp2 & HisList & Hprog & Hφ)".
    iDestruct (isList_hd_pure with "HisList") as %[ [-> ?] | [p [p' [p'' [w' [Hincr [Hincr' [-> Hhd] ] ] ] ] ] ] ]; [congruence|].
    iApply iterate_to_last_spec_middle;[..|iFrame];eauto. apply elem_of_list_fmap. exists (p',w');eauto.
  Qed.

  Lemma appendb_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w (* input z *)
        ll ll' pbvals (* linked list head and pointers *)
        a_first (* special adresses *)
        rmap (* register map *)
        f_m b_m e_m (* malloc addrs *)
        b_r e_r a_r a_r' (* environment table addrs *)
        ι ι1 γ Ep φ (* invariant/gname names *)
        Φ {Hpers: ∀ w, Persistent (Φ w)} (* client chosen predicate for all sealed values *) :

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length (appendb_instr f_m))%a →

    (* linked list ptr element head *)
    (ll + 1)%a = Some ll' →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_env; r_t0; r_t1 ]} →

    (* environment table *)
    withinBounds b_r e_r a_r' = true →
    (a_r + f_m)%a = Some a_r' →

    up_close (B:=coPset) ι ⊆ Ep →
    up_close (B:=coPset) ι1 ⊆ Ep ∖ ↑ι →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
       ∗ r_env ↦ᵣ WCap RWX ll ll' ll
       ∗ r_t1 ↦ᵣ w
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* the client must show that the value to seal satisfies their seal predicate  *)
       ∗ Φ w
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ codefrag a_first (appendb_instr f_m)
       (* malloc *)
       ∗ na_inv logrel_nais ι1 (malloc_inv b_m e_m)
       ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
       ∗ a_r' ↦ₐ WCap E b_m e_m b_m
       (* linked list invariants *)
       ∗ sealLL ι ll γ Φ
       ∗ prefLL γ pbvals
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_env ↦ᵣ WCap RWX ll ll' ll
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ WCap RO b_r e_r a_r
          ∗ a_r' ↦ₐ WCap E b_m e_m b_m
          ∗ ([∗ map] r↦w ∈ <[r_t2:=WInt 0%Z]> (<[r_t3:=WInt 0%Z]> (<[r_t4:=WInt 0%Z]>
                          (<[r_t5:=WInt 0%Z]> (<[r_t6:=WInt 0%Z]> rmap)))), r ↦ᵣ w)
          ∗ (∃ a a' a'' pbvals', ⌜(a + 1 = Some a')%a ∧ (a + 3 = Some a'')%a⌝ ∗ prefLL γ (pbvals ++ pbvals' ++ [(a',w)]) ∗ r_t1 ↦ᵣ WCap RWX a a'' a' ∗ a ↦ₐ WInt 0)
          ∗ codefrag a_first (appendb_instr f_m)
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hhd Hdom Hbounds Hf_m Hnclose Hnclose2) "(HPC & Hr_env & Hr_t1 & Hr_t0 & Hregs &#HΦw & Hown & Hprog & #Hmalloc & Hpc_b & Ha_r' & #Hseal_inv & #Hpref & Hφ)".
    iMod (na_inv_acc with "Hseal_inv Hown") as "(HisList & Hown & Hcls')";[auto|solve_ndisj|].
    iDestruct "HisList" as (hd) "[Hll HisList]". iDestruct "HisList" as (pbvals') "(>HisList & >Hexact & HΦ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    (* extract some registers *)
    assert (is_Some (rmap !! r_t6)) as [w6 Hw6];[rewrite elem_of_gmap_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]";[apply Hw6|].

    focus_block_0 "Hprog" as "Hprog" "Hcont".
    iInstr "Hprog".
    unfocus_block "Hprog" "Hcont" as "Hprog".

    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hregs $Hr_t6]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_env with "[$Hregs $Hr_env]") as "Hregs".
    { rewrite !lookup_insert_ne//. rewrite elem_of_gmap_dom_none Hdom. set_solver. }
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs".
    { rewrite !lookup_insert_ne//. rewrite elem_of_gmap_dom_none Hdom. set_solver. }
    iApply malloc_spec; iFrameCapSolve. 4: iFrame "∗ #". rewrite !dom_insert_L Hdom. clear. set_solver by lia.
    solve_ndisj. lia.
    iNext. iIntros "(HPC & Hmalloc_prog & Hpc_b & Ha_r' & Hreg & Hr_t0 & Hown & Hregs)".
    unfocus_block "Hmalloc_prog" "Hcont" as "Hprog".

    focus_block 2 "Hprog" as a_middle' Ha_middle' "Hprog" "Hcont".
    iDestruct "Hreg" as (bnew enew Hsize) "(Hr_t1 & Hbe')".
    rewrite /region_addrs_zeroes. assert (region_size bnew enew = 3) as Hbe_length;[clear -Hsize;rewrite /region_size;solve_addr|rewrite Hbe_length].
    assert (bnew <= enew)%a as Hle';[clear -Hsize;solve_addr|].
    pose proof (contiguous_between_region_addrs bnew enew Hle').
    rewrite /region_mapsto. set (l:=(region_addrs bnew enew)). rewrite -/l in H1.
    iDestruct (big_sepL2_length with "Hbe'") as %Hlen_eq. simpl in Hlen_eq.
    destruct l;[inversion Hlen_eq|]. apply contiguous_between_cons_inv_first in H1 as Heq. subst f.
    destruct l;[inversion Hlen_eq|].
    destruct l;[inversion Hlen_eq|]. destruct l;[|inversion Hlen_eq].
    iDestruct "Hbe'" as "[Hbnew [ Ha [Ha' _] ] ]".
    rewrite delete_insert. 2: rewrite !lookup_insert_ne// elem_of_gmap_dom_none Hdom;set_solver.
    repeat (rewrite -(insert_commute _ r_env)//).
    iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[apply lookup_insert|].
    rewrite !(insert_commute _ _ r_t6)// !(delete_insert_ne _ _ r_t6)//.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]";[apply lookup_insert|rewrite delete_insert_delete].
    rewrite !(insert_commute _ _ r_t4)// !(delete_insert_ne _ _ r_t4)//.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[apply lookup_insert|rewrite delete_insert_delete].
    rewrite !(insert_commute _ _ r_t2)// !(delete_insert_ne _ _ r_t2)//.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[apply lookup_insert|rewrite delete_insert_delete].
    rewrite !(insert_commute _ _ r_t3)// !(delete_insert_ne _ _ r_t3)//.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[apply lookup_insert|rewrite delete_insert_delete].
    iInstr "Hprog". eapply contiguous_between_incr_addr_middle with (i:=0); eauto.
    iInstr "Hprog". eapply contiguous_between_incr_addr_middle with (i:=0) (j:=1) in H1;eauto. solve_addr.
    iInstr "Hprog". split; [auto|solve_addr].
    do 3 iInstr "Hprog". (* Not using iGo so it stops before Jnz *)
    case_eq (is_cap hd); intro His_cap.
    { iGo "Hprog". generalize (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_middle' ^+ 11)%a ltac:(destruct Hvpc; congruence)); rewrite /updatePcPerm; intros HX; rewrite HX; clear HX.
      unfocus_block "Hprog" "Hcont" as "Hprog".

      focus_block 3 "Hprog" as a_middle'' Ha_middle'' "Hprog" "Hcont".
      iApply iterate_to_last_spec; iFrameCapSolve. destruct hd; simpl in His_cap; try congruence.
      iSplitL "Hr_t2"; [eauto|]. iSplitL "Hr_t3"; [eauto|]. iFrame.
      iNext. iIntros "Hiter".
      iDestruct "Hiter" as (dlast dlast' dlast'') "(HPC & HisList & (%&%&%) & Hr_t4 & Hr_t2 & Hr_t3 & Hprog)".
      unfocus_block "Hprog" "Hcont" as "Hprog".

      focus_block 4 "Hprog" as a_middle''' Ha_middle''' "Hprog" "Hcont".
      rewrite fmap_last in H2. apply fmap_Some in H2 as [ [plast wlast] [H2 Heq] ]. simpl in Heq; subst plast.
      iDestruct (isList_extract_and_append_last with "HisList") as (a' Hincr) "[Hdlast [Ha0 Hcls''] ]";[eauto|].
      iGo "Hprog". solve_addr.
      iDestruct "Hr_t2" as (w2) "Hr_t2".
      iDestruct "Hr_t3" as (w3) "Hr_t3".
      iGo "Hprog".
      iDestruct ("Hcls''" with "[$Hdlast $Ha0 $Ha $Ha']") as "HisList"; [repeat iSplit;iPureIntro|].
      iContiguous_next H1 0. eapply contiguous_between_middle_to_end with (ai := f) (i:=1) (k:=2) in H1; eauto.
      iContiguous_next H1 1.
      iDestruct (isList_NoDup with "HisList") as %Hdup.
      assert (f ∉ pbvals'.*1) as Hnin.
      { rewrite fmap_app in Hdup. apply NoDup_app in Hdup as (_ & Hdisj & _).
        intros Hin. apply Hdisj in Hin. clear -Hin. apply Hin. constructor. }

      iDestruct (know_pref with "Hexact Hpref") as %Hpref.
      iMod (update_ll _ _ (pbvals' ++ [(f,w)]) with "Hexact") as "[Hexact #Hpref']";[exists [(f,w)];auto|].

      iMod ("Hcls'" with "[HisList Hll Hexact HΦw HΦ $Hown]") as "Hown".
      { iNext. iExists _; iFrame. iExists _. iFrame "Hexact HisList HΦw". auto. }
      unfocus_block "Hprog" "Hcont" as "Hprog".
      iApply ("Hφ" with "[- $HPC $Hown $Hr_t0 $Hpc_b $Ha_r' $Hr_env]").
      iSplitR "Hr_t1 Hprog Hbnew".
      { iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        repeat (rewrite -delete_insert_ne//).
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|rewrite insert_delete -delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[apply lookup_delete|rewrite insert_delete; repeat (rewrite -delete_insert_ne//)].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        iFrameMapSolve+ Hdom "Hregs". }
      destruct Hpref. iFrame "∗".
      iExists bnew,f,enew,x. rewrite H app_assoc. iFrame "Hpref' Hr_t1 Hbnew".
      iPureIntro. split. iContiguous_next H1 0. eapply contiguous_between_length in H1. auto.
    }
    { iInstr "Hprog". iGo "Hprog". solve_addr.
      iGo "Hprog".
      unfocus_block "Hprog" "Hcont" as "Hprog".
      iDestruct (isList_hd_pure with "HisList") as %[ [-> ->] | (?&?&?&?&?&?&->&?)];[|done].
      iDestruct (isList_NoDup with "HisList") as %Hdup.
      iDestruct (know_pref with "Hexact Hpref") as %Hpre. destruct pbvals;[|by inversion Hpre].
      iMod (update_ll _ _ ([(f,w)]) with "Hexact") as "[Hexact #Hpref']";[exists [(f,w)];auto|].
      (* iMod ("HΦw" $! _ bnew with "[] HΦ") as "[HΦw HΨ]". iPureIntro. apply not_elem_of_nil. *)
      iMod ("Hcls'" with "[Ha Ha' Hll Hexact HΦw $Hown]") as "Hown".
      { iNext. iExists _; iFrame. iExists [(f,w)]. iSimpl. iFrame "∗ #". iExists _,bnew,f0,enew.
        repeat iSplit;eauto. iContiguous_next H1 0. iPureIntro.
        eapply contiguous_between_incr_addr_middle with (ai:=bnew) (i:=0) (j:=2) in H1; eauto. }
      iApply ("Hφ" with "[- $HPC $Hown $Hr_t0 $Hpc_b $Ha_r' $Hr_env]").
      iFrame "∗". iSplitR "Hr_t1 Hbnew".
      { iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        repeat (rewrite -delete_insert_ne//).
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|rewrite insert_delete -delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[apply lookup_delete|rewrite insert_delete; repeat (rewrite -delete_insert_ne//)].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        iFrameMapSolve+ Hdom "Hregs". }
      { iExists _,_,_,[]. iFrame. iFrame "Hpref'". iSplit;auto. iContiguous_next H1 0. } }
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------------- FINDB ---------------------------------------------- *)

  (* TODO: move this to the rules_Get.v file. small issue with the spec of failure: it does not actually
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Get_fail E get_i dst src pc_p pc_b pc_e pc_a w zsrc wdst :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap pc_p pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e pc_a
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ WInt zsrc }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  (* The following describes a generalized spec for one arbitrary iteration of the find loop *)
  Lemma findb_spec_middle pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        b (* input z *)
        ll pbvals hdw (* linked list head and pointers *)
        a_first (* special adresses *)
        E γ φ (* invariant/gname names *)
        Φ {Hpers: ∀ w, Persistent (Φ w)} (* client chosen seal predicate *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ length findb_instr)%a →

    (* linked list ptr element d *)
    hdw = WInt 0%Z ∨ (∃ d d' d'', hdw = WCap RWX d d'' d' ∧ (d + 1)%a = Some d' ∧ (d + 3)%a = Some d'' ∧ d' ∈ pbvals.*1) →

    (* up_close (B:=coPset) ι ⊆ E →  *)

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ hdw
      ∗ r_t1 ↦ᵣ WInt b
      ∗ (∃ w, r_t2 ↦ᵣ w)
      ∗ (∃ w, r_t3 ↦ᵣ w)
      (* invariant for d *)
      ∗ (* sealLL ι ll γ *) (∃ hd, ll ↦ₐ hd ∗ isList hd pbvals ∗ Exact γ pbvals ∗ ([∗ list] aw ∈ pbvals, Φ aw.2))
      (* ∗ prefLL γ pbvals *)
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais E
      (* trusted code *)
      ∗ codefrag a_first findb_instr
      ∗ ▷ φ FailedV
      ∗ ▷ (codefrag a_first findb_instr
          ∗ PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ WInt 0%Z
          ∗ (∃ b_a b3 b1 w, ⌜z_to_addr b = Some b_a ∧ (b_a + 3)%a = Some b3 ∧ (b_a + 1)%a = Some b1 ∧ (b1,w) ∈ pbvals⌝
                           ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ WCap RWX b_a b3 b1)
          ∗ r_t3 ↦ᵣ WInt 0%Z
          ∗ na_own logrel_nais E
          ∗ (∃ hd, ll ↦ₐ hd ∗ isList hd pbvals ∗ Exact γ pbvals ∗ ([∗ list] aw ∈ pbvals, Φ aw.2))
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iLöb as "IH" forall (pbvals hdw). (* we prove this spec by Löb induction for the case where we loop back *)
    iIntros (Hvpc Hcont Hd (* Hnclose *)) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3
    & Hseal_inv & Hown & Hprog & Hφfailed & Hφ)".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".

    (* Already now we must destruct on two possible cases: if this is the last element of the linked list,
       then the search has failed, and will crash with the getb instruction. *)
    destruct Hd as [-> | (d & d' & d'' & -> & Hd & Hd' & Hin)].
    { (* getb r_t2 r_env: FAILED INSTRUCTION *)
      codefrag_facts "Hprog".
      iInstr_lookup "Hprog" as "Hi" "Hcont".
      wp_instr.
      iApplyCapAuto @wp_Get_fail.
      wp_pure. iApply wp_value. iFrame. }

    (* the successful case lets us load the b bound *)
    codefrag_facts "Hprog".
    do 4 iInstr "Hprog". (* Can't use iGo as we need to do a case analysis. *)
    (* again we branch in two different cases: either the current word is the
       one we are searching for, and we will return to r_t0, or we must get the next pointer
       and start over *)

    destruct (decide (d - b = 0)%Z).
    { rewrite e.
      iDestruct "Hseal_inv" as (hd) "[Hll Hlist]". iDestruct "Hlist" as "[HisList [Hexact HΦ]]".
      apply elem_of_list_fmap in Hin as [ [dp dw] [Heq Hin] ]. simpl in Heq; subst dp.
      iDestruct (isList_extract _ _ d' with "HisList") as (a' hd' (Hd'' & Hcond)) "[Ha [Ha' Hcls'] ]"; eauto.
      iGo "Hprog". split; [auto|solve_addr].
      iGo "Hprog".
      iApply "Hφ". iFrame.
      iDestruct ("Hcls'" with "[$Ha $Ha']") as "HisList".
      iSplitR "Hll HisList";[|iExists _;iFrame]. iExists d,d'',d',_. iFrame. iSplit;auto.
      iPureIntro. assert (z_of d = b)%Z as <-;[clear -e;lia|]. apply finz_of_z_to_z. }

    iGo "Hprog". congruence.
    generalize (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first ^+ 8)%a ltac:(destruct Hvpc; congruence)); rewrite /updatePcPerm; intros HX; rewrite HX; clear HX.
    iDestruct "Hseal_inv" as (hd) "[Hll Hlist]".
    iDestruct "Hlist" as "[Hlist [Hexact HΦ]]".
    apply elem_of_list_fmap in Hin as [ [dp dw] [Heq Hin] ]. simpl in Heq; subst dp.
    iDestruct (isList_extract _ _ d' with "Hlist") as (a' hd' (Hincr&Hcond)) "(Ha1 & Ha2 & Hcls'')";eauto.
    simplify_eq.
    iGo "Hprog". solve_addr.
    iMod (get_full_pref with "Hexact") as "[Hexact #Hpref'']".
    iDestruct ("Hcls''" with "[$Ha1 $Ha2]") as "Hlist".
    iGo "Hprog". instantiate (1 := a_first). solve_addr.
    iInstr "Hprog". generalize (updatePcPerm_cap_non_E pc_p pc_b pc_e (a_first)%a ltac:(destruct Hvpc; congruence)); rewrite /updatePcPerm; intros HX; rewrite HX; clear HX.
    iApply ("IH" with "[] [] [] [$HPC $Hr_env $Hr_t0 $Hr_t1 $Hφ $Hφfailed $Hprog Hexact Hlist HΦ Hll Hr_t2 Hr_t3 $Hown]");auto.
    { iPureIntro. destruct Hcond as [ (-> & _) | (p & p' & p'' & w' & Hp & Hp' & -> & Hin') ];[by left|right].
      repeat eexists;auto. apply elem_of_list_fmap. exists (p',w'). eauto. }
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    iExists hd. iFrame.
  Qed.

  (* The following describes the spec for the full program, starting at the first node of the LL *)
  (* The list of known prefixes is arbitrary, since the proof builds up known prefixes as it goes along *)
  Lemma findb_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        b (* input z *)
        ll ll' (* linked list head and pointers *)
        a_first (* special adresses *)
        ι γ φ Ep (* invariant/gname names *)
        Φ {Hpers: ∀ w, Persistent (Φ w)} (* client defined sealed values predicate *):

    (* PC assumptions *)
    ExecPCPerm pc_p →

    (* Program adresses assumptions *)
    SubBounds pc_b pc_e a_first (a_first ^+ S (length findb_instr))%a →

    (* linked list ptr element d *)
    (ll + 1)%a = Some ll' →

    up_close (B:=coPset) ι ⊆ Ep →

    PC ↦ᵣ WCap pc_p pc_b pc_e a_first
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ WCap RWX ll ll' ll
      ∗ r_t1 ↦ᵣ WInt b
      ∗ (∃ w, r_t2 ↦ᵣ w)
      ∗ (∃ w, r_t3 ↦ᵣ w)
      (* invariant for d *)
      ∗ sealLL ι ll γ Φ
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais Ep
      (* trusted code *)
      ∗ codefrag a_first ((encodeInstrsW [Load r_env r_env])++findb_instr)
      ∗ ▷ φ FailedV
      ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ WInt 0%Z
          ∗ (∃ b_a b' b'' w pbvals, ⌜z_to_addr b = Some b_a ∧ (b_a + 1)%a = Some b' ∧ (b_a + 3)%a = Some b'' ∧
                                    (b',w) ∈ pbvals⌝ ∗ prefLL γ pbvals ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ WCap RWX b_a b'' b' ∗ Φ w)
          ∗ r_t3 ↦ᵣ WInt 0%Z
          ∗ codefrag a_first ((encodeInstrsW [Load r_env r_env])++findb_instr)
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hd Hnclose) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3
    & #Hseal_inv & Hown & Hprog & Hφfailed & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    iMod (na_inv_acc with "Hseal_inv Hown") as "(HisList & Hown & Hcls')";auto.
    iDestruct "HisList" as (hd) "[>Hll HisList]". iDestruct "HisList" as (pbvals') "[>HisList [>Hexact #HΦ]]".
    iDestruct (isList_hd_pure with "HisList") as %Hhd.
    iMod (get_full_pref with "Hexact") as "[Hexact #Hpref']".

    codefrag_facts "Hprog".
    iInstr "Hprog". solve_addr.
    focus_block 1 "Hprog" as a_middle Ha_middle "Hprog" "Hcont".
    cbn in Ha_middle. replace a_middle with (a_first ^+ 1)%a by solve_addr.
    iApply (findb_spec_middle with "[-]");[..|iFrame "∗ #"];eauto.
    { solve_addr+ H0. }
    { destruct Hhd as [ (->&_) | (?&?&?&?&?&?&->&?) ];auto. right.
      repeat eexists;auto. apply elem_of_list_fmap. exists (x0,x2). eauto. }
    iSplitL "Hll HisList". iExists _;iFrame.
    iNext. iIntros "(Hprog & HPC & Hr_t0 & Hr_t2 & Hres & Hr_t3 & Hna & Hlist)".
    iDestruct "Hres" as (b_a b'' b' w (Heq&Hincr&Hincr'&Hin)) "[Hr_t1 Hr_env]".
    iMod ("Hcls'" with "[Hlist $Hna]") as "Hown".
    { iNext. iDestruct "Hlist" as (hd') "[? [? ?] ]".
      iExists _; iFrame. iExists _; iFrame. }
    unfocus_block "Hprog" "Hcont" as "Hprog".
    iApply "Hφ". iFrame. iExists _,_,_,_,_. iFrame "∗ #". repeat iSplit; auto.
    iDestruct (big_sepL_elem_of with "HΦ") as "#HΦw";eauto.
  Qed.

End list.
