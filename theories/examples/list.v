From iris.algebra Require Import frac auth list.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import macros_helpers addr_reg_sample macros.
From cap_machine Require Import rules logrel contiguous.
From cap_machine Require Import monotone.

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

  Lemma know_pref γ a a' :
    Exact γ a -∗ prefLL γ a' -∗ ⌜a' `prefix_of` a⌝. 
  Proof.
    iIntros "H1 H2".
      by iDestruct (own_valid_2 with "H1 H2") as
        %[?%(principal_included (R := prefR)) _]%auth_both_valid.
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
  (* ------------- The isList predicate defines the proposition for a LL for seals ------------------- *)

  (* each link of the LL for seals must be of the form (RWX,a,a+2,a), or inl 0 for the tail *)

  Fixpoint isList (hd : Word) (awvals : list (Addr * Word)) : iProp Σ :=
    match awvals with
    | [] => (⌜hd = inl 0%Z⌝)%I
    | (p,w) :: awvals => (∃ hd' p' p'', ⌜ (p + 1)%a = Some p'
                                          ∧ (p + 2)%a = Some p''
                                          ∧ hd = inr (RWX,p,p'',p)⌝
                                          ∗ p ↦ₐ w
                                          ∗ p' ↦ₐ hd'
                                          ∗ isList hd' awvals)%I
    end.
  
  (* the sealLL invariant *)
  Definition sealLL ι ll γ : iProp Σ := na_inv logrel_nais ι (∃ hd, ll ↦ₐ hd ∗ ∃ awvals, isList hd awvals ∗ Exact γ awvals)%I.
  
  Lemma isList_length_hd vals : 
    (isList (inl 0%Z) vals → ⌜vals = []⌝)%I.
  Proof.
    destruct vals as [| [p w] vals ];simpl;try iIntros (Hcontr);auto. iIntros "HH".
    iDestruct "HH" as (? ? ? (_&_&?)) "HH". done. 
  Qed.

  Lemma isList_hd_length hd : 
    (isList hd [] → ⌜hd = inl 0%Z⌝)%I.
  Proof.
    iIntros "H". simpl. done. 
  Qed.
    
  Instance isList_timeless : (Timeless (isList d bvals)).
  Proof.
    intros. rewrite /isList.
    revert d. induction bvals as [| [p w] bvals]; apply _.
  Qed.
  
  Lemma isList_hd hd bvals :
    isList hd bvals -∗ ⌜hd = inl 0%Z⌝ ∨
    ∃ p p' w, ⌜(p + 2)%a = Some p' ∧ hd = inr (RWX,p,p',p)⌝ ∗ p ↦ₐ w.
  Proof.
    iIntros "Hlist".
    destruct bvals as [|[p w] bvals'];simpl.
    - iSimplifyEq. by iLeft. 
    - iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]". iRight.
      eauto. 
  Qed.

  Lemma isList_hd_pure hd bvals :
    (isList hd bvals -∗ ⌜hd = inl 0%Z ∧ bvals = []⌝ ∨
    ∃ p p' w, ⌜(p + 2)%a = Some p' ∧ hd = inr (RWX,p,p',p) ∧ (p,w) ∈ bvals⌝)%I.
  Proof.
    iIntros "Hlist".
    destruct bvals as [|[p w] bvals'];simpl.
    - iSimplifyEq. by iLeft. 
    - iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]". iRight.
      iExists _,_,_. repeat iSplit;eauto. iPureIntro. constructor. 
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
        simpl. iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        eauto. 
      + simpl. 
        iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
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
        simpl. iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        eauto. 
      + simpl. 
        iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as "Hw";auto. 
  Qed.
  
  Lemma isList_cut hd bvals a w :
    (a,w) ∈ bvals ->
    (isList hd bvals -∗
    ∃ l1 l2 a'', ⌜bvals = l1 ++ l2 ∧ (a + 2)%a = Some a''⌝ ∗ isList (inr (RWX,a,a'',a)) l2)%I.  
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (bvals) as [|[p w'] bvals'] "IH" forall (hd). 
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin];[inversion Heq;subst|]. 
      + simpl. iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        iExists [],((p,w')::bvals'),p''. simpl. iFrame. iSplit;auto.
        iExists _,_,_. iFrame. eauto. 
      + simpl. iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as (l1 l2 a'' (Heq&Hnext)) "Hlist";auto. 
        iExists ((p,w') :: l1),l2,a''. iFrame. rewrite !Heq. auto. 
  Qed.

  Lemma isList_NoDup hd ptrs :
    isList hd ptrs -∗ ⌜NoDup (ptrs.*1)⌝.
  Proof.
    iIntros "Hlist".
    iInduction (ptrs) as [|[p w] ptrs'] "IH" forall (hd). 
    - iPureIntro. apply NoDup_nil.
    - simpl. rewrite NoDup_cons_iff.
      iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
      iDestruct ("IH" with "Hlist") as %Hdup;auto. 
      iSplit;auto. iIntros (Hcontr%elem_of_list_In).
      destruct ptrs' as [|[p''' w'''] ptrs'''];[inversion Hcontr|]. 
      simpl. iDestruct "Hlist" as (hd1 p1 p2 ?) "[Hp [Hp' Hlist] ]".
      apply elem_of_list_fmap in Hcontr as [ [y k] [Heqy Hcontr] ].
      apply elem_of_cons in Hcontr as [Heq | Hcontr];subst. 
      + inversion Heq. iDestruct (mapsto_valid_2 with "Hd Hp") as %?. done.
      + iDestruct (isList_in with "Hlist") as "Hw";[apply Hcontr|]. 
        iDestruct (mapsto_valid_2 with "Hd Hw") as %?. done.
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
    apply NoDup_ListNoDup in Hdup. rewrite H0 in Hdup.
    apply NoDup_app in Hdup as (Hdup1 & Hnin & Hdup2).
    apply Hnin in Hin. apply not_elem_of_app in Hin as [_ Hin]. done. 
  Qed. 
        
  (* The following lemma extracts an element from the list, pointed to by a *)
  Lemma isList_extract_fst hd ptrs a :
    a ∈ ptrs.*1 -> 
    isList hd ptrs -∗
    (∃ a' hd' w, ⌜(a + 1)%a = Some a' ∧ ((hd' = inl 0%Z ∧ list.last ptrs.*1 = Some a)
                                         ∨ ∃ p p', (p + 2)%a = Some p' ∧ hd' = inr (RWX,p,p',p) ∧ p ∈ ptrs.*1)⌝ ∗ a ↦ₐ w ∗ a' ↦ₐ hd'
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
        simpl. iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]". 
        iExists _,_,_. iFrame.
        iDestruct (isList_hd_pure with "Hlist") as %Hhd'. 
        repeat iSplit;auto. iPureIntro. destruct Hhd' as [ [-> ->] | [? [? (?&?&?&?)] ] ];auto. 
        right. repeat eexists;eauto. constructor. apply elem_of_list_fmap. exists (x,x1); eauto. 
        iIntros "[Ha Ha']".
        iExists _,_,_;iFrame. iSplit;auto. } 
      { simpl in Hi,Hj. 
        iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] [] Hlist") as (a' hd2 w2 (Hnext&Hhd')) "[Ha [Ha' Hcls ] ]";eauto. 
        iExists _,_,_. iFrame.
        apply list_lookup_fmap_inv in Hi as [ [y1 y2] [Heqy Hi] ].
        apply list_lookup_fmap_inv in Hj as [ [k1 k2] [Heqk Hj] ]. simplify_eq.
        iSplit;auto.
        iPureIntro. split;auto. destruct Hhd' as [ [-> Heq] | [? [? (?&?&?)] ] ];auto.
        - left. rewrite fmap_cons. simpl. split;auto. rewrite Heq.
          destruct ptrs;inversion Heq. auto.
        - right. repeat eexists;eauto. constructor;auto. 
        - iIntros "[Ha Ha']". iExists _,_,_. iSplit;eauto. iFrame.
          iApply "Hcls". iFrame. 
      } 
  Qed.

  Lemma isList_extract hd ptrs a w :
    (a,w) ∈ ptrs -> 
    isList hd ptrs -∗
    (∃ a' hd', ⌜(a + 1)%a = Some a' ∧ ((hd' = inl 0%Z ∧ list.last ptrs = Some (a,w))
                                         ∨ ∃ p p' w', (p + 2)%a = Some p' ∧ hd' = inr (RWX,p,p',p) ∧ (p,w') ∈ ptrs)⌝ ∗ a ↦ₐ w ∗ a' ↦ₐ hd'
    ∗ (a ↦ₐ w ∗ a' ↦ₐ hd' -∗ isList hd ptrs)).
  Proof. 
    iIntros (Hin) "Hlist".
    apply elem_of_list_lookup in Hin as [i Hiz].
    iInduction (ptrs) as [|[p w'] ptrs] "IH" forall (hd i Hiz). 
    - inversion Hiz. 
    - destruct i. 
      { inversion Hiz. subst. iSimpl in "Hlist". 
        iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]". 
        iExists _,_. iFrame.
        iDestruct (isList_hd_pure with "Hlist") as %Hhd'. 
        repeat iSplit;auto. iPureIntro. destruct Hhd' as [ [-> ->] | [? [? (?&?&?&?)] ] ];auto. 
        right. repeat eexists;eauto. constructor. eauto. 
        iIntros "[Ha Ha']".
        iExists _,_,_;iFrame. iSplit;auto. } 
      { simpl in *. 
        iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hd [Hd' Hlist] ]".
        iDestruct ("IH" with "[] Hlist") as (a' hd2 (Hnext&Hhd')) "[Ha [Ha' Hcls ] ]";eauto. 
        iExists _,_. iFrame. iSplit;auto.
        iPureIntro. split;auto. destruct Hhd' as [ [-> Heq] | [? [? (?&?&?&?)] ] ];auto.
        destruct ptrs;inversion Heq. auto. 
        right. repeat eexists;eauto. constructor;eauto. 
        iIntros "[Ha Ha']". iExists _,_,_. iSplit;eauto. iFrame.
        iApply "Hcls". iFrame. 
      } 
  Qed.

  Lemma isList_extract_last hd ptrs a w :
    list.last ptrs = Some (a,w) ->
    isList hd ptrs -∗
    (∃ a', ⌜(a + 1)%a = Some a'⌝ ∗ a ↦ₐ w ∗ a' ↦ₐ inl 0%Z
    ∗ (a ↦ₐ w ∗ a' ↦ₐ inl 0%Z -∗ isList hd ptrs)). 
  Proof.
    iIntros (Hin) "Hlist".
    iInduction (ptrs) as [|[p w'] ptrs] "IH" forall (hd);[inversion Hin|]. 
    simpl. destruct ptrs. 
    - iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hp [Hp' ->] ]". 
      iExists _. inversion Hin;subst. iFrame. iSplit;auto. 
      iIntros "[Ha Hp']". iExists _,_,_. iFrame. 
      repeat iSplit;eauto.
    - iDestruct "Hlist" as (hd' p' p'' (?&?&->)) "[Hp [Hp' Hlist] ]".
      iDestruct ("IH" with "[] Hlist") as (a' Hincr) "(Ha & Ha' & Hcls)";auto.
      iExists _. iFrame. iSplit;auto.
      iIntros "[Ha Ha']".
      iExists _,_,_. iSplit;eauto. iFrame. iApply "Hcls". iFrame. 
  Qed.       
      
  (* the following lemma extracts and appends a new element to the last element of the list *)
  Lemma isList_extract_and_append_last hd ptrs a w' w p p' p'' :
    list.last ptrs = Some (a,w') →
    isList hd (ptrs) -∗
    (∃ a', ⌜(a + 1)%a = Some a'⌝ ∗ a ↦ₐ w' ∗ a' ↦ₐ inl 0%Z
    ∗ (a ↦ₐ w' ∗ a' ↦ₐ inr (RWX,p,p'',p) ∗ ⌜(p + 2)%a = Some p'' ∧ (p + 1)%a = Some p'⌝
       ∗ p ↦ₐ w ∗ p' ↦ₐ inl 0%Z -∗ isList hd (ptrs++[(p,w)]))).
  Proof. 
    iIntros (Hin) "Hlist".
    iInduction (ptrs) as [|[p2 w2] ptrs] "IH" forall (hd Hin). 
    - inversion Hin.
    - simpl. iDestruct "Hlist" as (hd' p0' p0'' (?&?&->)) "[Hd [Hd' Hlist] ]".
      destruct ptrs. 
      + inversion Hin. subst.
        simpl. iDestruct "Hlist" as "->". 
        iExists p0'. iFrame. iSplit;auto. 
        iIntros "(Ha & Ha' & (%&%) & Hp & Hp')". iExists _,p0',p0''. iFrame. simplify_eq.
        subst; iSplit;auto. iExists _,_,_. iFrame. iSplit;auto. 
      + iDestruct ("IH" with "[] Hlist") as (a' ?) "[Ha [Ha' Hcls] ]";auto. 
        iExists _;iFrame. iSplit;auto.
        iIntros "(Ha & Ha' & (%&%) & Hp & Hp')". iExists _,_,_. iSplit;eauto. iFrame. 
        iApply "Hcls". iFrame. auto. 
  Qed. 
  
      
  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------- FINDB and APPEND ----------------------------------------- *)

  (* This find looks for an link address capability in the linked list which 
     is of the following form: (-,b,-,-,-), where b is the input (Z) in r_t1 *)
  Definition findb_instr :=
    [getb r_t2 r_env;
    sub_r_r r_t2 r_t2 r_t1;
    move_r r_t3 PC;
    lea_z r_t3 6;
    jnz r_t3 r_t2;
    load_r r_t1 r_env;
    move_z r_t3 0;
    jmp r_t0;
    lea_z r_env 1;
    load_r r_env r_env;
    move_r r_t2 PC;
    lea_z r_t2 (-10);
    jmp r_t2].
  
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
  
  Definition iterate_to_last_instr r temp1 temp2 :=
    [lea_z r 1;
    load_r temp1 r;
    is_ptr temp1 temp1;
    move_r temp2 PC;
    lea_z temp2 7;
    jnz temp2 temp1;
    (* if r_env+1 points to a Z, r_env contains the last node of the list *)
    lea_z r (-1);
    move_r temp2 PC;
    lea_z temp2 7;
    jmp temp2;
    (* if r_env+1 points to a cap *)
    load_r r r;
    move_r temp2 PC;
    lea_z temp2 (-11);
    jmp temp2].

  Definition iterate_to_last a r temp1 temp2 :=
    ([∗ list] a_i;w_i ∈ a;iterate_to_last_instr r temp1 temp2, a_i ↦ₐ w_i)%I.
  
  Definition appendb_instr f_m :=
    [move_r r_t6 r_t1] ++
    malloc_instrs f_m 2%nat ++
    [store_r r_t1 r_t6; (* store the input value into the first cell of the allocated region *)
    load_r r_t4 r_env;
    is_ptr r_t2 r_t4; (* r_t2 = 1 if r_t2 is cap, = 0 otherwise *)
    move_r r_t3 PC;
    lea_z r_t3 7;
    jnz r_t3 r_t2;
    (* r_env contains 0, we are done: the newly allocated capability is the head of the LL *)
    store_r r_env r_t1;
    move_z r_t3 0;
    move_z r_t6 0;
    jmp r_t0] ++
    (* otherwise we must interate to last *)
    iterate_to_last_instr r_t4 r_t2 r_t3 ++
    [lea_z r_t4 1;
    store_r r_t4 r_t1;
    move_z r_t2 0;
    move_z r_t3 0;
    move_z r_t4 0;
    move_z r_t6 0;
    jmp r_t0].

  Definition appendb a f_m :=
    ([∗ list] a_i;w_i ∈ a;appendb_instr f_m, a_i ↦ₐ w_i)%I.

  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------- SPECIFICATIONS ------------------------------------------- *)

  (* ------------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- APPEND ---------------------------------------------- *)
  
    
  Lemma iterate_to_last_spec_middle pc_p pc_b pc_e (* PC *)
        iterate_to_last_addrs (* program addresses *)
        r temp1 temp2 (* temporary registers *)
        hd d d' pbvals (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        φ (* cont *) :
    
    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between iterate_to_last_addrs a_first a_last ->

    (* linked list ptr element d *)
    (d + 2)%a = Some d' →
    d ∈ pbvals.*1 →

    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r ↦ᵣ inr (RWX,d,d',d)
       ∗ (∃ w, temp1 ↦ᵣ w)
       ∗ (∃ w, temp2 ↦ᵣ w)
       (* list predicate for d *)
       ∗ isList hd pbvals
       (* trusted code *)
       ∗ iterate_to_last iterate_to_last_addrs r temp1 temp2
       ∗ ▷ ((∃ dlast dlast', PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_last)
                        ∗ isList hd pbvals
                        ∗ ⌜list.last pbvals.*1 = Some dlast ∧ (dlast + 2)%a = Some dlast'⌝
                        ∗ r ↦ᵣ inr (RWX,dlast,dlast',dlast)
                        ∗ (∃ w, temp1 ↦ᵣ w)
                        ∗ (∃ w, temp2 ↦ᵣ w)
                        ∗ iterate_to_last iterate_to_last_addrs r temp1 temp2)
              -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iLöb as "IH" forall (d d' pbvals). (* we prove this spec by Löb induction for the case where we loop back *)
    iIntros (Hvpc Hcont Hd Hin) "(HPC & Hr_env & Htemp1 & Htemp2 & HisList & Hprog & Hφ)".
    iDestruct "Htemp1" as (w1) "Htemp1". 
    iDestruct "Htemp2" as (w2) "Htemp2".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct_list iterate_to_last_addrs. 
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a.
    (* lea r_env 1 *)
    iPrologue "Hprog".
    assert (is_Some (d + 1)%a) as [d'' Hd''];[clear -Hd;destruct (d + 1)%a eqn:Hnon;eauto;exfalso;solve_addr|].
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_env]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|apply Hd''|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_env)". 
    (* load temp1 r_env *)
    iPrologue "Hprog".
    iDestruct (isList_extract_fst with "[$HisList]") as (a' hd' w (Hincr1&Hhd')) "[Ha [Ha' Hcls'] ]";
        [eauto..|rewrite Hincr1 in Hd'';inversion Hd'';subst]. 
    iApply (wp_load_success_alt with "[$HPC $Hi $Ha' $Htemp1 $Hr_env]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 1|..]. 
    { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd Hincr1;clear;solve_addr. }
    iEpilogue "(HPC & Htemp1 & Hi & Hr_env & Hd)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* is_ptr temp1 temp2 *)
    iPrologue "Hprog".
    iApply (wp_IsPtr_success_dst with "[$HPC $Hi $Htemp1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|..].
    iEpilogue "(HPC & Hi & Htemp1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move temp2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Htemp2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|..].
    iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea temp2 7 *)
    assert (a2 + 7 = Some a9)%a as Hlea.
    { apply contiguous_between_incr_addr_middle with (i:=3) (j:=7) (ai:=a2) (aj:=a9) in Hcont;auto. }
    assert (pc_p ≠ E) as Hne.
    { apply isCorrectPC_range_perm_non_E in Hvpc;auto.
      apply contiguous_between_middle_bounds' with (ai:=a_first) in Hcont as [? ?];[auto|constructor]. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Htemp2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|apply Hlea|auto|..].
    iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* we must now diverge paths: either hd' is the tail, or it we must loop back *)
    destruct (is_cap hd') eqn:His_cap. 
    { destruct Hhd' as [ [-> Heq] | Hhd'];[inversion His_cap|]. destruct Hhd' as [p [p' [Hincr2 [-> Hin'] ] ] ]. 
      (* jnz temp2 temp1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Htemp2 $Htemp1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto| |..].
      iEpilogue "(HPC & Hi & Htemp2 & Htemp1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      rewrite updatePcPerm_cap_non_E;auto.
      do 4 (iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done").
      (* load r_env r_env *)
      iPrologue "Hprog".
      iApply (wp_load_success_same_alt with "[$HPC $Hi $Hd $Hr_env]");
        [done|apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 10|..].
      { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd Hincr1;clear;solve_addr. }
      iEpilogue "(HPC & Hr_env & Hi & Ha')"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iDestruct ("Hcls'" with "[$Ha $Ha']") as "HisList".
      (* move PC temp2 *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Htemp2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 11|..].
      iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea temp2 -10 *)
      assert (a10 + (-11) = Some a_first)%a as Hlea3. 
      { apply contiguous_between_incr_addr with (i:=11) (ai:=a10) in Hcont;auto. clear -Hcont;solve_addr. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Htemp2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 12|apply Hlea3|auto|..].
      iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp temp2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Htemp2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      rewrite updatePcPerm_cap_non_E;auto. 
      iApply ("IH" with "[] [] [] [] [$HPC $Hr_env $HisList $Hφ Htemp1 Htemp2 Hprog_done]");auto.
      iSplitL "Htemp1";eauto. iSplitL "Htemp2";eauto.
      iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$)". done. 
    }
    { destruct Hhd' as [ [-> Heq] | [? [? [? [-> ?] ] ] ] ];[|inversion His_cap].
      (* jnz temp2 temp1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Htemp2 $Htemp1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|..].
      iEpilogue "(HPC & Hi & Htemp2 & Htemp1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_env -1 *)
      assert ((d'' + -1)%a = Some d) as Hlea';[clear -Hincr1;solve_addr|].
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_env]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto|..].
      iEpilogue "(HPC & Hi & Hr_env)"; iCombine "Hi" "Hprog_done" as "Hprog_done".      
      (* move temp2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Htemp2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|..].
      iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea temp2 7 *)
      assert (a6 + 7 = Some a_last)%a as Hlea''.
      { apply contiguous_between_middle_to_end with (i:=7) (ai:=a6) (k:=7) in Hcont;auto;simpl. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Htemp2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|apply Hlea''|auto|..].
      iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp temp2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Htemp2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "(HPC & Hi & Htemp2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      rewrite updatePcPerm_cap_non_E;auto.
      iDestruct ("Hcls'" with "[$Hd $Ha]") as "HisList". 
      iApply "Hφ". 
      iExists _,_. iFrame "HPC HisList Hr_env". iSplit;auto.
      iSplitL "Htemp1";eauto. iSplitL "Htemp2";eauto.
      iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$)".
    }
  Qed. 

  Lemma iterate_to_last_spec pc_p pc_b pc_e (* PC *)
        iterate_to_last_addrs (* program addresses *)
        r temp1 temp2 (* temporary registers *)
        hd pbvals (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        φ (* cont *) :
    
    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between iterate_to_last_addrs a_first a_last ->

    (* linked list is not empty *)
    hd ≠ inl 0%Z →

    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r ↦ᵣ hd
       ∗ (∃ w, temp1 ↦ᵣ w)
       ∗ (∃ w, temp2 ↦ᵣ w)
       (* list predicate for d *)
       ∗ isList hd pbvals
       (* trusted code *)
       ∗ iterate_to_last iterate_to_last_addrs r temp1 temp2
       ∗ ▷ ((∃ dlast dlast', PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_last)
                        ∗ isList hd pbvals 
                        ∗ ⌜list.last pbvals.*1 = Some dlast ∧ (dlast + 2)%a = Some dlast'⌝
                        ∗ r ↦ᵣ inr (RWX,dlast,dlast',dlast)
                        ∗ (∃ w, temp1 ↦ᵣ w)
                        ∗ (∃ w, temp2 ↦ᵣ w)
                        ∗ iterate_to_last iterate_to_last_addrs r temp1 temp2)
              -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hne) "(HPC & Hr_env & Htemp1 & Htemp2 & HisList & Hprog & Hφ)".
    iDestruct (isList_hd_pure with "HisList") as %[ [-> ?] | [p [p' [w' [Hincr [-> Hhd] ] ] ] ] ];[congruence|]. 
    iApply iterate_to_last_spec_middle;[..|iFrame];eauto. apply elem_of_list_fmap. exists (p,w');eauto.
  Qed.
  

  Lemma appendb_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        w (* input z *)
        appendb_addrs (* program addresses *)
        ll ll' pbvals (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        rmap (* register map *)
        f_m b_m e_m (* malloc addrs *)
        b_r e_r a_r a_r' (* environment table addrs *)
        ι ι1 ι2 γ Ep φ (* invariant/gname names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between appendb_addrs a_first a_last ->

    (* linked list ptr element head *)
    (ll + 1)%a = Some ll' →

    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_env; r_t0; r_t1 ]} →

    (* environment table *)
    withinBounds (RW, b_r, e_r, a_r') = true →
    (a_r + f_m)%a = Some a_r' →

    up_close (B:=coPset) ι1 ⊆ Ep →
    up_close (B:=coPset) ι ⊆ Ep ∖ ↑ι1 →
    up_close (B:=coPset) ι2 ⊆ Ep ∖ ↑ι1 ∖ ↑ι →

    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
       ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
       ∗ r_t1 ↦ᵣ w
       ∗ r_t0 ↦ᵣ wret
       ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
       (* own token *)
       ∗ na_own logrel_nais Ep
       (* trusted code *)
       ∗ na_inv logrel_nais ι1 (appendb appendb_addrs f_m)
       (* malloc *)
       ∗ na_inv logrel_nais ι2 (malloc_inv b_m e_m)
       ∗ pc_b ↦ₐ inr (RO, b_r, e_r, a_r)
       ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)
       (* linked list invariants *)
       ∗ sealLL ι ll γ
       ∗ prefLL γ pbvals
       ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
          ∗ r_t0 ↦ᵣ wret
          ∗ pc_b ↦ₐ inr (RO, b_r, e_r, a_r)
          ∗ a_r' ↦ₐ inr (E, b_m, e_m, b_m)
          ∗ ([∗ map] r↦w ∈ <[r_t2:=inl 0%Z]> (<[r_t3:=inl 0%Z]> (<[r_t4:=inl 0%Z]>
                          (<[r_t5:=inl 0%Z]> (<[r_t6:=inl 0%Z]> rmap)))), r ↦ᵣ w)
          ∗ (∃ a a' pbvals', ⌜(a + 2 = Some a')%a⌝ ∗ prefLL γ (pbvals ++ pbvals' ++ [(a,w)]) ∗ r_t1 ↦ᵣ inr (RWX,a,a',a))
          ∗ na_own logrel_nais Ep
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hhd Hdom Hbounds Hf_m Hnclose Hnclose2 Hnclose3) "(HPC & Hr_env & Hr_t1 & Hr_t0 & Hregs & Hown 
                                             & #Happ & #Hmalloc & Hpc_b & Ha_r' & #Hseal_inv & #Hpref & Hφ)". 
    iMod (na_inv_open with "Happ Hown") as "(>Hprog & Hown & Hcls)";auto. 
    iMod (na_inv_open with "Hseal_inv Hown") as "(>HisList & Hown & Hcls')";[auto|solve_ndisj|]. 
    iDestruct "HisList" as (hd) "[Hll HisList]". iDestruct "HisList" as (pbvals') "(HisList & Hexact)".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct appendb_addrs;[inversion Hprog_length|]. 
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a.
    (* extract some registers *)
    assert (is_Some (rmap !! r_t6)) as [w6 Hw6];[rewrite elem_of_gmap_dom Hdom; set_solver|].
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]";[apply Hw6|]. 
    (* move r_t6 r_t1 *)
    destruct appendb_addrs;[inversion Hprog_length|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|..]. 
    iEpilogue "(HPC & Hprog_done & Hr_t6 & Hr_t1)". 
    (* insert registers *)
    iDestruct (big_sepM_insert _ _ r_t6 with "[$Hregs $Hr_t6]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert _ _ r_env with "[$Hregs $Hr_env]") as "Hregs".
    { rewrite !lookup_insert_ne//. rewrite elem_of_gmap_dom_none Hdom. set_solver. }
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hregs $Hr_t1]") as "Hregs".
    { rewrite !lookup_insert_ne//. rewrite elem_of_gmap_dom_none Hdom. set_solver. }
    (* apply the malloc spec *)
    assert (contiguous_between (a :: appendb_addrs) a a_last) as Hcont'.
    { do 1 (apply contiguous_between_cons_inv in Hcont as [? [? [? Hcont] ] ];
            apply contiguous_between_cons_inv_first in Hcont as ?;subst). auto. }
    iDestruct (contiguous_between_program_split with "Hprog") as (malloc_prog rest link)
                                                                   "(Hmalloc_prog & Hprog & #Hcont)";[apply Hcont'|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iApply (malloc_spec with "[- $Hmalloc $Hregs $HPC $Hr_t0 $Hown $Hpc_b $Ha_r' $Hmalloc_prog]");
      [|apply Hcont_malloc|auto..].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest.
      apply contiguous_between_incr_addr with (i:=1) (ai:=a) in Hcont;auto. 
      clear -Hcont Hcont_rest Hmid. solve_addr. }
    { rewrite !dom_insert_L Hdom. clear. set_solver. }
    iNext. iIntros "(HPC & Hmalloc_prog & Hpc_b & Ha_r' & Hreg & Hr_t0 & Hown & Hregs)". 
    rewrite delete_insert. 2: rewrite !lookup_insert_ne// elem_of_gmap_dom_none Hdom;set_solver.
    iDestruct "Hreg" as (bnew enew Hsize) "(Hr_t1 & Hbe')".
    rewrite -!(insert_commute _ r_env)//. 
    iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]";[apply lookup_insert|].
    rewrite delete_insert. 2: rewrite !lookup_insert_ne// elem_of_gmap_dom_none Hdom;set_solver.

    (* prepare for the remaining program *)
    (* the rest of the program is made up of correct PCs *)
    assert (a_first <= link)%a as Hle.
    { apply contiguous_between_bounds in Hcont_malloc.
      apply contiguous_between_incr_addr with (i:=1) (ai:=a) in Hcont;auto. 
      clear -Hcont Hcont_malloc. solve_addr. }
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc1.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. clear -Hmid Hle. solve_addr. }
    iDestruct (big_sepL2_length with "Hprog") as %Hrest_length.
    destruct rest;[inversion Hrest_length|]. apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* the newly allocated region can be split up into two points tos *)
    rewrite /region_addrs_zeroes. assert (region_size bnew enew = 2) as Hbe_length;[clear -Hsize;rewrite /region_size;solve_addr|rewrite Hbe_length].
    assert (bnew <= enew)%a as Hle';[clear -Hsize;solve_addr|]. 
    pose proof (contiguous_between_region_addrs bnew enew Hle').
    rewrite /region_mapsto. set (l:=(region_addrs bnew enew)). rewrite -/l in H.
    iDestruct (big_sepL2_length with "Hbe'") as %Hlen_eq. simpl in Hlen_eq.
    destruct l;[inversion Hlen_eq|]. apply contiguous_between_cons_inv_first in H as Heq. subst a0.
    destruct l;[inversion Hlen_eq|]. destruct l;[|inversion Hlen_eq].
    iDestruct "Hbe'" as "[Hbnew [Ha0 _] ]". 
    (* extract registers *)
    rewrite !(insert_commute _ _ r_t6)//.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]";[apply lookup_insert|rewrite delete_insert_delete]. 
    rewrite !(insert_commute _ _ r_t4)// !(delete_insert_ne _ _ r_t4)//.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[apply lookup_insert|rewrite delete_insert_delete].
    rewrite !(insert_commute _ _ r_t2)// !(delete_insert_ne _ _ r_t2)//.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[apply lookup_insert|rewrite delete_insert_delete].
    rewrite !(insert_commute _ _ r_t3)// !(delete_insert_ne _ _ r_t3)//.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[apply lookup_insert|rewrite delete_insert_delete]. 
    (* store r_t1 r_t6*)
    destruct rest;[inversion Hrest_length|].
    iPrologue "Hprog". 
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1 $Hbnew]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|..]. 
    { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hsize;clear;solve_addr. }
    iEpilogue "(HPC & Hrest_done & Hr_t6 & Hr_t1 & Hbnew)". 
    (* load r_t4 r_env *)
    destruct rest;[inversion Hrest_length|].
    iPrologue "Hprog".
    iApply (wp_load_success_alt with "[$HPC $Hi $Hr_t4 $Hr_env $Hll]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last| |iContiguous_next Hcont_rest 1|..].
    { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hhd;clear;solve_addr. }
    iEpilogue "(HPC & Hr_t4 & Hi & Hr_env & Hll)". iCombine "Hi" "Hrest_done" as "Hrest_done". 
    (* is_ptr r_t2 r_t4 *)
    destruct rest;[inversion Hrest_length|].
    iPrologue "Hprog".
    iApply (wp_IsPtr_success with "[$HPC $Hi $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hrest_done" as "Hrest_done". 
    (* move r_t3 PC *)
    destruct rest;[inversion Hrest_length|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|..].
    iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hrest_done" as "Hrest_done". 
    (* lea r_t3 8 *)
    do 6 (destruct rest;[inversion Hrest_length|]). 
    assert (a3 + 7 = Some a10)%a as Hlea. 
    { apply contiguous_between_incr_addr_middle with (i:=3) (j:=7) (ai:=a3) (aj:=a10) in Hcont_rest;auto. }
    assert (pc_p ≠ E) as Hne.
    { apply isCorrectPC_range_perm_non_E in Hvpc;auto.
      apply contiguous_between_middle_bounds' with (ai:=a_first) in Hcont as [? ?];[auto|constructor]. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|apply Hlea|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hrest_done" as "Hrest_done". 

    (* we must now consider the two cases: either the LL is empty and we store the new node at the head, 
       or the LL contains elements and we must iterate to the end of them *)
    destruct (is_cap hd) eqn:His_cap. 
    { (* Case: we iterate to the end *)
      (* jnz r_t3 r_t2 *)
      iPrologue "Hprog". 
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t3 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2)"; iCombine "Hi" "Hrest_done" as "Hrest_done".
      rewrite updatePcPerm_cap_non_E;auto.
      do 4 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hrest_done" as "Hrest_done").
      (* iterate_to_last r_t4 r_t2 r_t3 *)
      assert (contiguous_between (a10 :: rest) a10 a_last) as Hcont_rest'. 
      { do 10 (apply contiguous_between_cons_inv in Hcont_rest as [? [? [? Hcont_rest] ] ];
            apply contiguous_between_cons_inv_first in Hcont_rest as ?;subst). auto. }
      iDestruct (contiguous_between_program_split with "Hprog") as (iter_prog rest1 link1)
                                                                   "(Hiter_prog & Hprog & #Hcont)";[apply Hcont_rest'|].
      iDestruct "Hcont" as %(Hcont_iter & Hcont_rest1 & Heqapp1 & Hlink1).
      iApply (iterate_to_last_spec with "[- $HPC $HisList $Hr_t4 $Hiter_prog]");[|apply Hcont_iter|destruct hd;auto|..].
      { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
        apply contiguous_between_bounds in Hcont_rest1. 
        apply contiguous_between_incr_addr with (i:=10) (ai:=a10) in Hcont_rest;auto. 
        clear -Hcont_rest Hcont_rest1 Hmid Hle. solve_addr. }
      iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|]. 
      iNext. iIntros "Hiter".
      iDestruct "Hiter" as (dlast dlast') "(HPC & HisList & (%&%) & Hr_t4 & Hr_t2 & Hr_t3 & Hiter_prog)". 
      (* prepare rest1 *)
      assert (a_first <= link1)%a as Hle2. 
      { apply contiguous_between_bounds in Hcont_iter.
        apply contiguous_between_incr_addr with (i:=10) (ai:=a10) in Hcont_rest;auto. 
        clear -Hcont_rest Hcont_iter Hle. solve_addr. }
      assert (isCorrectPC_range pc_p pc_b pc_e link1 a_last) as Hvpc2.
      { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. clear -Hmid Hle2. solve_addr. }
      iDestruct (big_sepL2_length with "Hprog") as %Hrest_length1.
      destruct rest1;[inversion Hrest_length1|]. apply contiguous_between_cons_inv_first in Hcont_rest1 as Heq. subst a11.
      (* lea r_t4 1 *)
      destruct rest1;[inversion Hrest_length1|].
      iPrologue "Hprog".
      rewrite fmap_last in H0. apply fmap_Some in H0 as [ [plast wlast] [H0 Heq] ]. simpl in Heq; subst plast.
      iDestruct (isList_extract_and_append_last with "HisList") as (a' Hincr) "[Hdlast [Ha' Hcls''] ]";[eauto|]. 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t4]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next Hcont_rest1 0|apply Hincr|auto|..].
      iEpilogue "(HPC & Hrest_done1 & Hr_t4)". 
      (* store r_t4 r_t1 *)
      destruct rest1;[inversion Hrest_length1|].
      iPrologue "Hprog".
      iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_t4 $Ha']");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next Hcont_rest1 1|..].
      { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hincr H1;clear;solve_addr. }
      iEpilogue "(HPC & Hi & Hr_t1 & Hr_t4 & Ha')"; iCombine "Hi" "Hrest_done1" as "Hrest_done1".
      (* move r_t2 0 *)
      destruct rest1;[inversion Hrest_length1|].
      iPrologue "Hprog". iDestruct "Hr_t2" as (w2) "Hr_t2". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next Hcont_rest1 2|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hrest_done1" as "Hrest_done1".
      (* move r_t3 0 *)
      destruct rest1;[inversion Hrest_length1|].
      iPrologue "Hprog". iDestruct "Hr_t3" as (w3) "Hr_t3". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next Hcont_rest1 3|..].
      iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hrest_done1" as "Hrest_done1".
      (* move r_t3 0 *)
      destruct rest1;[inversion Hrest_length1|].
      iPrologue "Hprog". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t4]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next Hcont_rest1 4|..].
      iEpilogue "(HPC & Hi & Hr_t4)"; iCombine "Hi" "Hrest_done1" as "Hrest_done1".
      (* move r_t6 0 *)
      destruct rest1;[inversion Hrest_length1|].
      iPrologue "Hprog". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t6]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next Hcont_rest1 5|..].
      iEpilogue "(HPC & Hi & Hr_t6)"; iCombine "Hi" "Hrest_done1" as "Hrest_done1".
      (* close the list invariant *)
      iDestruct ("Hcls''" with "[$Hdlast $Ha' $Hbnew $Ha0]") as "HisList";[iSplit;auto;iPureIntro;iContiguous_next H 0|].
      iDestruct (know_pref with "Hexact Hpref") as %Hpref.
      iMod (update_ll _ _ (pbvals' ++ [(bnew,w)]) with "Hexact") as "[Hexact #Hpref']";[exists [(bnew,w)];auto|]. 
      iMod ("Hcls'" with "[HisList Hll Hexact $Hown]") as "Hown".
      { iNext. iExists _; iFrame. iExists _. iFrame. }
      (* jmp r_t0 *)
      destruct rest1;[|inversion Hrest_length1].
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|..].
      iEpilogue "(HPC & Hi & Hr_t0)";iCombine "Hi" "Hrest_done1" as "Hrest_done1". 
      (* φ *)
      iMod ("Hcls" with "[Hprog_done Hmalloc_prog Hiter_prog Hrest_done Hrest_done1 $Hown]") as "Hown".
      { iNext. iFrame "Hprog_done". rewrite Heqapp Heqapp1. 
        iApply (big_sepL2_app with "[$Hmalloc_prog]").
        iDestruct "Hrest_done" as "($&$&$&$&$&$&$&$&$&$)". 
        iApply (big_sepL2_app with "[$Hiter_prog]").
        iDestruct "Hrest_done1" as "($&$&$&$&$&$&$)". done. }
      iApply ("Hφ" with "[- $HPC $Hown $Hr_t0 $Hpc_b $Ha_r' $Hr_env]"). 
      iSplitR "Hr_t1".
      { iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        rewrite -!delete_insert_ne//.
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|rewrite insert_delete -delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        rewrite -!(insert_commute _ r_t6)// -!(insert_commute _ r_t5)// -!(insert_commute _ r_t4)// -!(insert_commute _ r_t3)// -!(insert_commute _ r_t2)//. }
      destruct Hpref.
      iExists bnew,enew,x. rewrite H2 app_assoc. iFrame "Hpref' Hr_t1". 
      auto.
    }
    { (* Case: the allocated node will become the head of the LL *)
      iDestruct (isList_hd_pure with "HisList") as %[ [-> ->] | (?&?&?&?&->&?)];[|done].
      iDestruct (know_pref with "Hexact Hpref") as %Hpre. destruct pbvals;[|by inversion Hpre]. 
      (* jnz r_t3 r_t3 *)
      iPrologue "Hprog". 
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t3 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 5|..].
      iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2)"; iCombine "Hi" "Hrest_done" as "Hrest_done".
      (* store r_env r_t1 *)
      iPrologue "Hprog". 
      iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t1 $Hr_env $Hll]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|..].
      { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hhd;clear;solve_addr. }
      iEpilogue "(HPC & Hi & Hr_t1 & Hr_env & Hll)"; iCombine "Hi" "Hrest_done" as "Hrest_done".
      (* we should now be able to close the LL invariant *)
      iMod (update_ll _ _ ([(bnew,w)]) with "Hexact") as "[Hexact #Hpref']";[exists [(bnew,w)];auto|].
      iMod ("Hcls'" with "[Hbnew Ha0 Hll Hexact $Hown]") as "Hown".
      { iNext. iExists _; iFrame. iExists [(bnew,w)]. iFrame. iExists _,_,_.
        repeat iSplit;eauto. iContiguous_next H 0. }
      (* move r_t3 0 *)
      iPrologue "Hprog". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 7|..].
      iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hrest_done" as "Hrest_done".
      (* move r_t6 0 *)
      iPrologue "Hprog". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t6]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 8|..].
      iEpilogue "(HPC & Hi & Hr_t6)"; iCombine "Hi" "Hrest_done" as "Hrest_done".
      (* jmp r_t0 *)
      iPrologue "Hprog". 
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|..].
      iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hrest_done" as "Hrest_done".
      (* Hφ *)
      iMod ("Hcls" with "[Hmalloc_prog Hprog Hrest_done Hprog_done $Hown]") as "Hown". 
      { iNext. iFrame "Hprog_done". rewrite Heqapp. 
        iApply (big_sepL2_app with "[$Hmalloc_prog]").
        iDestruct "Hrest_done" as "($&$&$&$&$&$&$&$&$&$)". iFrame. }
      iApply ("Hφ" with "[- $HPC $Hown $Hr_t0 $Hpc_b $Ha_r' $Hr_env]").
      iSplitR "Hr_t1".
      { iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        rewrite -!delete_insert_ne//.
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|rewrite insert_delete -delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
        rewrite -!(insert_commute _ r_t6)// -!(insert_commute _ r_t5)// -!(insert_commute _ r_t4)// -!(insert_commute _ r_t3)// -!(insert_commute _ r_t2)//. }
      iExists _,_,[]. iFrame. iFrame "Hpref'". auto. 
    }
  Qed. 
    
  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------------------------------------- FINDB ---------------------------------------------- *)
    
      
  (* The following describes a generalized spec for one arbitrary iteration of the find loop *)
  Lemma findb_spec_middle pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        b (* input z *)
        findb_addrs (* program addresses *)
        ll pbvals hdw (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        E γ φ (* invariant/gname names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between findb_addrs a_first a_last ->

    (* linked list ptr element d *)
    hdw = inl 0%Z ∨ (∃ d d', hdw = inr (RWX,d,d',d) ∧ (d + 2)%a = Some d' ∧ d ∈ pbvals.*1) →

    (* up_close (B:=coPset) ι ⊆ E →  *)
    
    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ hdw
      ∗ r_t1 ↦ᵣ inl b
      ∗ (∃ w, r_t2 ↦ᵣ w)
      ∗ (∃ w, r_t3 ↦ᵣ w)
      (* invariant for d *)
      ∗ (* sealLL ι ll γ *) (∃ hd, ll ↦ₐ hd ∗ isList hd pbvals ∗ Exact γ pbvals)
      (* ∗ prefLL γ pbvals *)
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais E
      (* trusted code *)
      ∗ findb_loop findb_addrs
      ∗ ▷ φ FailedV
      ∗ ▷ (findb_loop findb_addrs
          ∗ PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ inl 0%Z
          ∗ (∃ b_a b' w, ⌜z_to_addr b = Some b_a ∧ (b_a + 2)%a = Some b' ∧ (b_a,w) ∈ pbvals⌝ ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ inr (RWX,b_a,b',b_a))
          ∗ r_t3 ↦ᵣ inl 0%Z
          ∗ na_own logrel_nais E
          ∗ (∃ hd, ll ↦ₐ hd ∗ isList hd pbvals ∗ Exact γ pbvals)
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iLöb as "IH" forall (pbvals hdw). (* we prove this spec by Löb induction for the case where we loop back *)
    iIntros (Hvpc Hcont Hd (* Hnclose *)) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3
    & Hseal_inv & Hown & Hprog & Hφfailed & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    destruct_list findb_addrs. 
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a.
    (* get some general purpose registers *)
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3".

    (* Already now we must destruct on two possible cases: if this is the last element of the linked list, 
       then the search has failed, and will crash with the getb instruction. *)
    destruct Hd as [-> | (d & d' & -> & Hd & Hin)]. 
    { (* getb r_t2 r_env: FAILED INSTRUCTION *)
      iPrologue "Hprog". 
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t2 $Hr_env]");
        [apply decode_encode_instrW_inv|eauto|iCorrectPC a_first a_last|..]. 
      iEpilogue "_". iApply wp_value. iFrame. }

    (* the successful case lets us load the b bound *)
    (* getb r_t2 r_env *)
    iPrologue "Hprog". 
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t2 $Hr_env]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|..]. 
    iEpilogue "(HPC & Hprog_done & Hr_env & Hr_t2)". iSimpl in "Hr_t2". 
    (* sub r_t2 r_t2 r_t1 *)
    iPrologue "Hprog". 
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|..]. 
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)". iCombine "Hi" "Hprog_done" as "Hprog_done". iSimpl in "Hr_t2". 
    (* move r_t3 PC *)
    iPrologue "Hprog". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|..]. 
    iEpilogue "(HPC & Hi & Hr_t3)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t3 6 *)
    assert (a1 + 6 = Some a7)%a as Hlea. 
    { apply contiguous_between_incr_addr_middle with (i:=2) (j:=6) (ai:=a1) (aj:=a7) in Hcont;auto. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|..]. 
    { eapply isCorrectPC_range_perm_non_E;eauto. apply contiguous_between_length in Hcont. clear -Hcont. solve_addr. }
    iEpilogue "(HPC & Hi & Hr_t3)". iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* again we branch in two different cases: either the current word is the 
       one we are searching for, and we will return to r_t0, or we must get the next pointer 
       and start over *)

    destruct (decide (d - b = 0)%Z). 
    { rewrite e.
      (* jnz r_t3 r_t2 *)
      iPrologue "Hprog". 
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t3 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
      iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* load r_t1 r_env *)
      (* iMod (na_inv_open with "Hseal_inv Hown") as "(>Hlist & Hown & Hcls)";[auto|solve_ndisj|]. *)
      iDestruct "Hseal_inv" as (hd) "[Hll Hlist]". iDestruct "Hlist" as "[HisList Hexact]".
      apply elem_of_list_fmap in Hin as [ [dp dw] [Heq Hin] ]. simpl in Heq; subst dp. 
      iDestruct (isList_extract _ _ d with "HisList") as (a' hd' Hcond) "[Ha [Ha' Hcls'] ]"; eauto. 
      iPrologue "Hprog". 
      iApply (wp_load_success_alt with "[$HPC $Hi $Hr_t1 $Hr_env $Ha]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 5|..].
      { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd;clear;solve_addr. }
      iEpilogue "(HPC & Hr_t1 & Hi & Hr_env & Hd)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iDestruct ("Hcls'" with "[$Hd $Ha']") as "HisList".
      (* iMod ("Hcls" with "[HisList Hll Hexact $Hown]") as "Hown";[iNext;iExists _;iFrame;iExists _;iFrame|].  *)
      (* move r_t3 0 *)
      iPrologue "Hprog". 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|..].
      iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* jmp r_t0 *)
      iPrologue "Hprog". 
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* continuation *)
      iApply "Hφ".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$)". }
      iFrame. iSplitR "Hll HisList";[|iExists _;iFrame]. iExists d,d',_. iFrame. iSplit;auto. 
      iPureIntro. assert (z_of d = b)%Z as <-;[clear -e;lia|]. apply z_to_addr_z_of.  
    }
    
    (* jnz r_t3 r_t2 *)
    iPrologue "Hprog". 
    iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t3 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
    { intros Hcontr. inversion Hcontr. done. }
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* skip the instructions we jumped over *)
    do 3 (iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done"). 
    assert (updatePcPerm (inr (pc_p, pc_b, pc_e, a7)) = (inr (pc_p, pc_b, pc_e, a7))) as ->. 
    { apply isCorrectPC_range_perm_non_E in Hvpc;[|apply contiguous_between_length in Hcont;
                                                   simpl in Hcont;clear -Hcont;solve_addr].
      destruct pc_p;auto. done. }
    (* lea r_env 1 *)
    assert (is_Some (d + 1)%a) as [d'' Hd''].
    { destruct (d + 1)%a eqn:Hcontr;eauto. clear -Hcontr Hd; solve_addr. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_env]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|apply Hd''|auto|]. 
    iEpilogue "(HPC & Hi & Hr_env)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_env r_env *)
    iPrologue "Hprog".
    (* iMod (na_inv_open with "Hseal_inv Hown") as "(Hlist & Hown & Hcls')";[auto|solve_ndisj|].  *)
    iDestruct "Hseal_inv" as (hd) "[Hll Hlist]".
    iDestruct "Hlist" as "[Hlist Hexact]".
    (* iDestruct (isList_NoDup with "Hlist") as %Hdup. *)
    (* assert (list.last (hd::ptrs'') ≠ Some d) as Hn.  *)
    (* { apply rest_last with (l1:=hd::ptrs) (l2:=hd::ptrs');eauto;apply prefix_cons;auto. } *)
    apply elem_of_list_fmap in Hin as [ [dp dw] [Heq Hin] ]. simpl in Heq; subst dp. 
    iDestruct (isList_extract _ _ d with "Hlist") as (a' hd' (Hincr&Hcond)) "(Ha1 & Ha2 & Hcls'')";eauto.  
    simplify_eq.
    iApply (wp_load_success_same_alt with "[$HPC $Hi $Hr_env $Ha2]");
      [done|apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 9|..].
    { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd Hd'';clear;solve_addr. }
    iNext. iIntros "(HPC & Hr_env & Hi & Ha2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iMod (get_full_pref with "Hexact") as "[Hexact #Hpref'']". 
    iDestruct ("Hcls''" with "[$Ha1 $Ha2]") as "Hlist".
    (* iMod ("Hcls'" with "[Hexact Hlist Hll $Hown]") as "Hown";[iNext;iExists _;iFrame;iExists _;iFrame|].  *)
    iApply wp_pure_step_later;auto;iNext.
    (* move r_t2 PC *)
    iPrologue "Hprog". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 10|..]. 
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t2 -11 *)
    assert (a9 + (-10) = Some a_first)%a as Hlea'.
    { apply contiguous_between_incr_addr_middle with (i:=0) (j:=10) (ai:=a_first) (aj:=a9) in Hcont;auto. clear -Hcont; solve_addr. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 11|apply Hlea'|..].
    { apply isCorrectPC_range_perm_non_E in Hvpc;auto.
      apply contiguous_between_length in Hcont. clear-Hcont. solve_addr. }
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* jmp r_t2 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* apply IH since we have looped back *)
    assert (updatePcPerm (inr (pc_p, pc_b, pc_e, a_first)) = inr (pc_p, pc_b, pc_e, a_first)) as ->.
    { apply isCorrectPC_range_perm_non_E in Hvpc. destruct pc_p;auto. done.
      apply contiguous_between_length in Hcont. clear-Hcont. solve_addr. }
    
    iApply ("IH" with "[] [] [] [$HPC $Hr_env $Hr_t0 $Hr_t1 $Hφ $Hφfailed Hprog_done Hexact Hlist Hll Hr_t2 Hr_t3 $Hown]");auto. 
    { iPureIntro. destruct Hcond as [ (-> & _) | (p & p' & w' & Hp & -> & Hin') ];[by left|right].
      repeat eexists;auto. apply elem_of_list_fmap. exists (p,w'). eauto. }
    iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$)". iSplitL;[|done].
    iExists hd. iFrame. 
  Qed.

  (* The following describes the spec for the full program, starting at the first node of the LL *)
  (* The list of knows prefixes is arbitrary, since the proof builds up known prefixes as it goes along *)
  Lemma findb_spec pc_p pc_b pc_e (* PC *)
        wret (* return cap *)
        b (* input z *)
        findb_addrs (* program addresses *)
        ll ll' (* linked list head and pointers *)
        a_first a_last (* special adresses *)
        ι ι1 γ φ (* invariant/gname names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between findb_addrs a_first a_last ->

    (* linked list ptr element d *)
    (ll + 1)%a = Some ll' →
    
    up_close (B:=coPset) ι ⊆ ⊤ ∖ ↑ι1 → 
    
    PC ↦ᵣ inr (pc_p,pc_b,pc_e,a_first)
      ∗ r_t0 ↦ᵣ wret
      ∗ r_env ↦ᵣ inr (RWX,ll,ll',ll)
      ∗ r_t1 ↦ᵣ inl b
      ∗ (∃ w, r_t2 ↦ᵣ w)
      ∗ (∃ w, r_t3 ↦ᵣ w)
      (* invariant for d *)
      ∗ sealLL ι ll γ
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (findb findb_addrs)
      ∗ ▷ φ FailedV
      ∗ ▷ (PC ↦ᵣ updatePcPerm wret
          ∗ r_t0 ↦ᵣ wret
          ∗ r_t2 ↦ᵣ inl 0%Z
          ∗ (∃ b_a b' w pbvals, ⌜z_to_addr b = Some b_a ∧ (b_a + 2)%a = Some b' ∧ (b_a,w) ∈ pbvals⌝ ∗ prefLL γ pbvals ∗ r_t1 ↦ᵣ w ∗ r_env ↦ᵣ inr (RWX,b_a,b',b_a))
          ∗ r_t3 ↦ᵣ inl 0%Z
          ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{ φ }})
      -∗
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hd Hnclose) "(HPC & Hr_t0 & Hr_env & Hr_t1 & Hr_t2 & Hr_t3
    & #Hseal_inv & Hown & #Hfindb & Hφfailed & Hφ)".
    iMod (na_inv_open with "Hfindb Hown") as "(>Hprog & Hown & Hcls)";auto.
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    iMod (na_inv_open with "Hseal_inv Hown") as "(>HisList & Hown & Hcls')";auto.
    iDestruct "HisList" as (hd) "[Hll HisList]". iDestruct "HisList" as (pbvals') "[HisList Hexact]".
    iDestruct (isList_hd_pure with "HisList") as %Hhd. 
    iMod (get_full_pref with "Hexact") as "[Hexact #Hpref']".
    (* load r_env r_env *)
    destruct findb_addrs;[inversion Hprog_length|]. apply contiguous_between_cons_inv_first in Hcont as Heq;subst a. 
    destruct findb_addrs;[inversion Hprog_length|].
    iPrologue "Hprog".
    iApply (wp_load_success_same_alt with "[$HPC $Hi $Hr_env $Hll]");
      [done|apply decode_encode_instrW_inv|iCorrectPC a_first a_last| |iContiguous_next Hcont 0|..].
    { split;auto. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hd;clear;solve_addr. }
    iEpilogue "(HPC & Hr_env & Hi & Hll)".
    apply contiguous_between_cons_inv in Hcont as [? [? [? Hcont] ] ];
      apply contiguous_between_cons_inv_first in Hcont as ?;subst.
    iApply (findb_spec_middle with "[-]");[..|iFrame "∗ #"];eauto.
    { intros mid [Hmid Hmid']. apply isCorrectPC_inrange with a_first a_last; auto. split;auto.
      trans x;auto. clear -H0;solve_addr. }
    { destruct Hhd as [ (->&_) | (?&?&?&?&->&?) ];auto. right.
      repeat eexists;auto. apply elem_of_list_fmap. exists (x0,x2). eauto. }
    iSplitL "Hll HisList". iExists _;iFrame. 
    iNext. iIntros "(Hprog & HPC & Hr_t0 & Hr_t2 & Hres & Hr_t3 & Hna & Hlist)".
    iDestruct "Hres" as (b_a b' w (Heq&Hincr&Hin)) "[Hr_t1 Hr_env]".
    iMod ("Hcls'" with "[Hlist $Hna]") as "Hown".
    { iNext. iDestruct "Hlist" as (hd') "[? [? ?] ]".
      iExists _; iFrame. iExists _; iFrame. }
    iMod ("Hcls" with "[$Hi $Hprog $Hown]") as "Hown".
    iApply "Hφ". iFrame. iExists _,_,_,_. iFrame "∗ #". auto. 
  Qed.
  
  
End list. 

    
