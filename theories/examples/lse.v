From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec.
From cap_machine Require Import rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static region_invariants_uninitialized. 
From cap_machine.examples Require Import region_macros stack_macros stack_macros_u stack_macros_helpers scall_u awkward_example_helpers.
From stdpp Require Import countable.

Section lse.
   Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.

  Lemma create_gmap_default_lookup_is_Some {K V} `{EqDecision K, Countable K} (l: list K) (d: V) x v:
    create_gmap_default l d !! x = Some v → x ∈ l ∧ v = d.
  Proof.
    revert x v d. induction l as [| a l]; cbn.
    - done.
    - intros x v d. destruct (decide (a = x)) as [->|].
      + rewrite lookup_insert. intros; simplify_eq. repeat constructor.
      + rewrite lookup_insert_ne //. intros [? ?]%IHl. subst. repeat constructor; auto.
  Qed.

  Lemma create_gmap_default_dom {K V} `{EqDecision K, Countable K} (l: list K) (d: V):
    dom (gset K) (create_gmap_default l d) = list_to_set l.
  Proof.
    induction l as [| a l].
    - cbn. rewrite dom_empty_L //.
    - cbn [create_gmap_default list_to_set]. rewrite dom_insert_L // IHl //.
  Qed.
  
  Lemma registers_mapsto_resources pc_w stk_w rt0_w adv_w pc_w' (rmap: gmap RegName Word) :
    dom (gset RegName) rmap = all_registers_s ∖ {[PC; r_stk; r_t0; r_t30]} →
    ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z)
    -∗ r_stk ↦ᵣ stk_w
    -∗ r_t0 ↦ᵣ rt0_w
    -∗ r_t30 ↦ᵣ adv_w
    -∗ PC ↦ᵣ pc_w'
    -∗
    registers_mapsto (<[PC:=pc_w']> (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_t30:=adv_w]>
      (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z))))))).
  Proof.
    iIntros (Hdom) "Hregs Hr_stk Hr_t0 Hr_adv HPC".
    rewrite /registers_mapsto insert_insert.
    do 4 (rewrite big_sepM_insert; [iFrame|done]).
    iDestruct (big_sepM_dom with "Hregs") as "Hregs".
    iApply (big_sepM_mono (λ k _, k ↦ᵣ inl 0%Z))%I.
    { intros * [? ->]%create_gmap_default_lookup_is_Some. auto. }
    iApply big_sepM_dom. rewrite big_opS_proper'. iFrame. done.
    rewrite Hdom.
    rewrite create_gmap_default_dom list_to_set_difference -/all_registers_s.
    f_equal. clear. set_solver.
  Qed.

  Lemma r_full (pc_w stk_w rt0_w adv_w : Word) :
    full_map (Σ:=Σ) (<[PC:=pc_w]> (<[r_stk:=stk_w]> (<[r_t0:=rt0_w]> (<[r_t30:=adv_w]>
           (create_gmap_default (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
  Proof.
    rewrite /full_map. iPureIntro. intros rr. cbn beta.
    rewrite elem_of_gmap_dom 4!dom_insert_L create_gmap_default_dom list_to_set_difference.
    rewrite -/all_registers_s. generalize (all_registers_s_correct rr). clear. set_solver.
  Qed.
  
  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _ 
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end. 

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Lemma isCorrectPC_range_npE p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p ≠ E.
  Proof.
    intros HH1 HH2. 
    destruct (isCorrectPC_range_perm _ _ _ _ _ _ HH1 HH2) as [?| [?|?] ]; 
      congruence.
  Qed.

  Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; simpl; auto.

  Ltac iNotElemOfList :=
    repeat (apply not_elem_of_cons; split;[auto|]); apply not_elem_of_nil.  

  Ltac addr_succ :=
    match goal with
    | H : _ |- (?a1 + ?z)%a = Some ?a2 =>
      rewrite /incr_addr /=; do 2 f_equal; apply eq_proofs_unicity; decide equality
    end.

   (* The following ltac gets out the next general purpuse register *)
   Ltac get_genpur_reg Hr_gen wsr ptr :=
     let w := fresh "wr" in 
       destruct wsr as [? | w wsr]; first (by iApply bi.False_elim);
       iDestruct Hr_gen as ptr.

   Ltac iDestructList Hlength l :=
     (repeat (let a := fresh "a" in destruct l as [|a l];[by inversion Hlength|]));
     destruct l;[|by inversion l].

   Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

   Ltac iPrologue_pre l Hl :=
     destruct l; [inversion Hl|]; iApply (wp_bind (fill [SeqCtx])).
   
   Ltac iPrologue l Hl prog := 
     iPrologue_pre l Hl;
     iDestruct prog as "[Hinstr Hprog]".     

  Ltac iEpilogue intro_ptrn :=
    iNext; iIntros intro_ptrn; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac iLookupR Hl :=
    rewrite /= lookup_app_r;rewrite Hl /=;auto.

  (* TODO: move to region_addrs *)
  Lemma region_addrs_split2 b e a:
    region_addrs b e = region_addrs b (min a e) ++ region_addrs (max b a) e.
  Proof.
    destruct (addr_eq_dec (min a e) (max b a)).
    - rewrite e0 -region_addrs_split; auto.
      split; solve_addr.
    - destruct (Addr_le_dec (min a e) b).
      + rewrite (region_addrs_empty b (min a e)); auto.
        destruct (Addr_le_dec a b).
        * replace (max b a) with b by solve_addr. auto.
        * replace (max b a) with a in n by solve_addr.
          assert (e <= b)%a by solve_addr.
          rewrite (region_addrs_empty b e); auto.
          rewrite region_addrs_empty; auto. solve_addr.
      + replace (max b a) with a by solve_addr.
        destruct (Addr_le_dec e a).
        * rewrite (region_addrs_empty a e); auto.
          replace (min a e) with e by solve_addr; auto.
          rewrite app_nil_r. auto.
        * replace (min a e) with a by solve_addr.
          rewrite -region_addrs_split; auto. solve_addr.
  Qed.
  
  (* TODO: move to region_addrs *)
  Lemma region_addrs_split3 b e n:
    region_size b e > n ->
    exists a, region_addrs b e = region_addrs b a ++ region_addrs a e /\ region_size b a = n.
  Proof.
    intros Hsize. rewrite /region_size in Hsize.
    assert (exists a, (b + n)%a = Some a) as [a Ha].
    { rewrite /incr_addr. destruct (Z_le_dec (b + n)%Z MemNum); [|solve_addr].
      destruct (Z_le_dec 0 (b + n)%Z); [eauto|solve_addr]. }
    exists a. split; [|rewrite /region_size; solve_addr].
    eapply region_addrs_split. split; solve_addr.
  Qed.

  (* Need to update stdpp :'( *)
  Lemma list_filter_app { A: Type } (P: A -> Prop) `{ forall x, Decision (P x) } l1 l2:
    @list_filter _ P _ (l1 ++ l2) = @list_filter _ P _ l1 ++ @list_filter _ P _ l2.
  Proof.
    induction l1; simpl; auto.
    destruct (decide (P a)); auto.
    unfold filter. rewrite IHl1. auto.
  Qed.

  (* TODO: upstream to iris *)
  Lemma big_sepL2_to_big_sepM (PROP : bi) (A B : Type) `{EqDecision A} `{Countable A}
        (φ: A -> B -> PROP) (l1: list A) (l2: list B):
        NoDup l1 ->
        (([∗ list] y1;y2 ∈ l1;l2, φ y1 y2) -∗
        ([∗ map] y1↦y2 ∈ list_to_map (zip l1 l2), φ y1 y2))%I.
  Proof.
    revert l2. iInduction (l1) as [|x l1] "IH"; iIntros (l2 Hnd) "H".
    - iSimpl. iDestruct (big_sepL2_length with "H") as "%".
      destruct l2; simpl in H0; inv H0.
      iApply big_sepM_empty. auto.
    - iDestruct (big_sepL2_length with "H") as "%".
      destruct l2; simpl in H0; inv H0.
      simpl. inv Hnd. iDestruct "H" as "[A B]".
      iApply (big_sepM_insert with "[A B]").
      + eapply not_elem_of_list_to_map.
        rewrite fst_zip; auto. lia.
      + iFrame. iApply ("IH" $! l2 H4 with "B"); auto.
  Qed.
  
  (* move to iris? *)
  Lemma big_sepL_delete' {PROP: bi} {A: Type} (φ: A -> PROP) (l: list A):
        forall k, (([∗ list] k0↦y ∈ l, if decide (k0 = k) then emp else φ y) -∗
             ([∗ list] k0↦x0 ∈ delete k l, (λ (_ : nat) (x1 : A), φ x1) k0 x0))%I.
  Proof.
    iInduction (l) as [|x l] "IH"; simpl; auto; iIntros (k) "H".
    iDestruct "H" as "[H1 H2]".
    rewrite /delete /=. destruct k.
    - iApply (big_sepL_impl with "H2").
      iClear "H1". iModIntro. iIntros. destruct (decide (S k = 0)); auto. lia.
    - simpl. iFrame. iApply ("IH" with "[H2]").
      iApply (big_sepL_impl with "H2").
      iModIntro; iIntros. destruct (decide (k0 = k)); destruct (decide (S k0 = S k)); auto; lia.
  Qed.
  Lemma big_sepL_merge {PROP: bi} {A: Type} (l: list A) (HNoDup: NoDup l) (φ: A -> PROP) {Haffine: forall a, Affine (φ a)}:
    forall l1 l2, (forall a, a ∈ l -> a ∈ l1 \/ a ∈ l2) ->
             (([∗ list] a ∈ l1, φ a) -∗
              ([∗ list] a ∈ l2, φ a) -∗
              ([∗ list] a ∈ l, φ a))%I.
  Proof.
    iInduction (l) as [|x l] "IH"; iIntros (l1 l2 H) "Hl1 Hl2".
    - iApply big_sepL_nil; auto.
    - iApply big_sepL_cons. destruct (H x ltac:(eapply elem_of_list_here)) as [H'|H']; eapply elem_of_list_lookup in H'; destruct H' as [k H'].
      + iDestruct (big_sepL_delete with "Hl1") as "[$ Hl1]"; eauto.
        iAssert ([∗ list] a ∈ delete k l1, φ a)%I with "[Hl1]" as "Hl1".
        { iApply (big_sepL_impl with "[Hl1]"); auto.
          iApply (big_sepL_delete' with "Hl1"). }
        assert (Hincl: ∀ a : A, a ∈ l → a ∈ delete k l1 ∨ a ∈ l2).
        { intros. destruct (H a ltac:(eapply elem_of_list_further; eauto)).
          - left. eapply elem_of_list_lookup in H1. destruct H1.
            eapply elem_of_list_lookup. assert (x0 <> k).
            + red; intros; subst x0. rewrite H1 in H'; inv H'.
              inv HNoDup. eapply H4. auto.
            + assert  (x0 < k \/ k <= x0) by lia. destruct H3.
              * exists x0. rewrite lookup_delete_lt; auto.
              * exists (x0 - 1). rewrite lookup_delete_ge; auto; try lia.
                replace (S (x0 - 1)) with x0; auto. lia.
          - right. auto. }
        inv HNoDup. iApply ("IH" $! H3 (delete k l1) l2 Hincl with "[$Hl1] [$Hl2]").
      + iDestruct (big_sepL_delete with "Hl2") as "[$ Hl2]"; eauto.
        iAssert ([∗ list] a ∈ delete k l2, φ a)%I with "[Hl2]" as "Hl2".
        { iApply (big_sepL_impl with "[Hl2]"); auto.
          iApply (big_sepL_delete' with "Hl2"). }
        assert (Hincl: ∀ a : A, a ∈ l → a ∈ l1 ∨ a ∈ delete k l2).
        { intros. destruct (H a ltac:(eapply elem_of_list_further; eauto)).
          - left. auto.
          - right. eapply elem_of_list_lookup in H1. destruct H1.
            eapply elem_of_list_lookup. assert (x0 <> k).
            + red; intros; subst x0. rewrite H1 in H'; inv H'.
              inv HNoDup. eapply H4. auto.
            + assert  (x0 < k \/ k <= x0) by lia. destruct H3.
              * exists x0. rewrite lookup_delete_lt; auto.
              * exists (x0 - 1). rewrite lookup_delete_ge; auto; try lia.
                replace (S (x0 - 1)) with x0; auto. lia. }
        inv HNoDup. iApply ("IH" $! H3 l1 (delete k l2) Hincl with "[$Hl1] [$Hl2]").
  Qed.

  (* TODO: move *)
  Lemma contiguous_between_inj l:
    forall a1 b1 b2,
      contiguous_between l a1 b1 ->
      contiguous_between l a1 b2 ->
      b1 = b2.
  Proof.
    induction l; intros.
    - inv H; inv H0; auto.
    - inv H; inv H0. rewrite H2 in H3; inv H3.
      eapply IHl; eauto.
  Qed.

  (* TODO: move to sts.v ?*)
  Lemma rtc_rel_priv x y:
    x <> Permanent ->
    rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) x y.
  Proof.
    intros; destruct x, y; try congruence;
      repeat
        (match goal with
         | |- rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) ?X ?X => left
         | |- rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) Temporary ?X => eright; [try (left; constructor); right; constructor|left]
         | |- rtc (λ x y : region_type, Rpub x y ∨ Rpriv x y) ?X ?Y => right with Temporary; [try (left; constructor); right; constructor|]
         | _ => idtac
         end).
  Qed.
  (* TODO: move to multiple_update.v ? *)
  Lemma related_sts_priv_world_std_update_multiple W l ρ :
    Forall (λ a : Addr, ∃ ρ, (std W) !! a = Some ρ /\ ρ <> Permanent) l →
    related_sts_priv_world W (std_update_multiple W l ρ).
  Proof.
    intros Hforall.
    induction l. 
    - apply related_sts_priv_refl_world. 
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto. 
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split. 
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j x0 y Hx0 Hy.
           destruct (decide (a = j)).
           +++ subst. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (j ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in_i in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
               rewrite /revoke /std /= in Hi.
               destruct Hi as [ρ [Hi Hi'] ].
               rewrite Hi in Hx0. inversion Hx0; subst.
               eapply rtc_rel_priv; auto.
           +++ rewrite /= lookup_insert_ne in Hy;auto. rewrite Hx0 in Hy; inversion Hy; subst; left.
  Qed.

  (* TODO: move these to region.v file *)
   Lemma region_addrs_weak n a b e :
     a ∈ region_addrs_aux b (S n) ->
     (b + n)%a = Some e -> 
     a ≠ e ->
     a ∈ region_addrs_aux b n.
   Proof.
     revert b. induction n;intros b Hin Hb Hne.
     - simpl in Hin. apply elem_of_list_singleton in Hin. subst.
       rewrite addr_add_0 in Hb. inversion Hb. contradiction.
     - simpl. destruct (decide (a = b)).
       + subst. apply elem_of_cons. by left.
       + apply elem_of_cons. right.
         simpl in Hin. apply elem_of_cons in Hin.
         destruct Hin as [Hcontr | Hin];[contradiction|]. 
         apply IHn;auto. solve_addr.
   Qed. 
   
   Lemma region_addrs_elem_of_lt (a b e : Addr) n :
    a ∈ region_addrs_aux b n -> (b + n)%a = Some e -> (a < e)%a.
   Proof.
     rewrite /region_addrs. intros Hin.
     revert e. induction n; intros e.
     - inversion Hin.
     - intros He. 
       assert (exists e', (b + n)%a = Some e') as [e' He'].
       { rewrite Nat2Z.inj_succ in He. 
         assert (Z.succ n = n + 1)%Z as Heq;[lia|]. rewrite Heq in He.
         destruct (b + n)%a eqn:Hsome.
         { rewrite (addr_add_assoc _ a0) in He;auto. eauto. }
         exfalso. solve_addr.
       } 
       destruct n. 
       + rewrite addr_add_0 in He'. inversion He'. subst.
         simpl in Hin. apply elem_of_list_singleton in Hin. subst.
         solve_addr.
       + destruct (decide (a = e'));[subst;solve_addr|].
         rewrite /lt_addr. trans e';[|solve_addr]. 
         apply IHn;auto. apply region_addrs_weak with (e:=e');auto. 
   Qed.

   Lemma region_addrs_elem_of_ge (a b : Addr) n :
    a ∈ region_addrs_aux b n -> (b <= a)%a.
   Proof.
     rewrite /region_addrs.
     revert b. induction n;intros b Hin. 
     - inversion Hin.
     - simpl in Hin.
       apply elem_of_cons in Hin as [Heq | Hin]. 
       + subst. solve_addr. 
       + rewrite /le_addr. trans ^(b + 1)%a;[solve_addr|]. 
         apply IHn;auto.
   Qed.
   
   Lemma region_addrs_not_elem_of_le a (n : nat) :
     forall b a', (b + n)%a = Some a -> (a <= a')%a -> a' ∉ (region_addrs_aux b n).
   Proof.
     induction n.
     - intros b a' Ha' Hle. apply not_elem_of_nil.
     - intros b a' Ha' Hle. apply not_elem_of_cons.
       split.
       + intros Hcontr;subst. solve_addr. 
       + apply IHn;solve_addr. 
   Qed.
   
   Lemma region_addrs_xor_elem_of (a b c e : Addr) :
     (b <= c < e)%Z -> 
     a ∈ region_addrs b e ->
     (a ∈ region_addrs b c ∧ a ∉ region_addrs c e) ∨ (a ∉ region_addrs b c ∧ a ∈ region_addrs c e).
   Proof.
     intros Hbounds Ha.
     rewrite (region_addrs_split _ c) in Ha;auto.
     apply elem_of_app in Ha as [Hbc | Hce]. 
     - left. split;auto. apply region_addrs_not_elem_of.
       eapply region_addrs_elem_of_lt;eauto.
       assert (contiguous_between (region_addrs b c) b c).
       { apply contiguous_between_of_region_addrs; auto. solve_addr. }
       apply elem_of_list_lookup in Hbc as [k Hk].
       rewrite -region_addrs_length. 
       apply contiguous_between_length;auto. 
     - right. split;auto.
       assert (contiguous_between (region_addrs b c) b c).
       { apply contiguous_between_of_region_addrs; auto. solve_addr. }
       apply region_addrs_not_elem_of_le with (a:=c).
       + rewrite -region_addrs_length. 
         apply contiguous_between_length;auto. 
       + apply region_addrs_elem_of_ge with (region_size c e);auto. 
     - solve_addr. 
   Qed.        

  
        
  (* encapsulation of local state using local capabilities and scall *)
  (* assume r1 contains an executable pointer to adversarial code 
     (no linking table yet) *)
  Definition f2_instrs (r1 : RegName) epilogue_off f_a :=
     [pushU_z_instr r_stk 1] ++
     scallU_prologue_instrs epilogue_off r1 ++
     [jmp r1;
     sub_z_z r_t1 0 6;
     lea_r r_stk r_t1] ++
     popU_instrs r_stk r1 ++
     assert_r_z_instrs f_a r1 1 ++
     [halt].

  Definition f2 (a : list Addr) (p : Perm) (r1 : RegName) flag_off : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(f2_instrs r1 40 flag_off), a_i ↦ₐ[p] w_i)%I.

  (* Shorthand definition for an adress being currently temporary/revoked *)
   Definition region_type_revoked W (a : Addr) :=
     (std W) !! a = Some Revoked.
   Definition region_type_temporary W (a : Addr) :=
     (std W) !! a = Some Temporary.
   Definition region_type_uninitialized W (a : Addr) :=
     exists w, (std W) !! a = Some (Static {[a:=w]}).

   Lemma region_type_temporary_dec W a: Decision (region_type_temporary W a).
   Proof.
     rewrite /region_type_temporary. solve_decision.
   Qed.
   
   Lemma region_type_uninitialized_dec W a: Decision (region_type_uninitialized W a).
   Proof.
     rewrite /region_type_uninitialized. destruct (std W !! a); [|right; red; intros (w & A); discriminate].
     destruct r; try (right; red; intros (w & A); discriminate).
     destruct (g !! a) eqn:Hsome;[|right];[|intros [? ?];simplify_map_eq].
     destruct (decide (g = {[a:=w]}));[left|right];subst;eauto. intros [? ?]. simplify_map_eq. 
   Qed.

  
  (* We want to show encapsulation of local state, by showing that an arbitrary adv 
     cannot change what lies on top of the stack after return, i.e. we want to show
     that the last pop indeed loads the value 1 into register r1 *)
  (* to make the proof simpler, we are assuming WLOG the r1 registers is r_t30 *)
  Lemma f2_spec W rmap pc_p pc_p' pc_g pc_b pc_e (* PC *)
        f2_addrs (* f2 *)
        f_b f_e f_a b_link e_link a_link a_entry (* linking table variables *)
        f_a_first f_a_last flag_p flag_b flag_e flag_a a_env (* failure subroutine details *)
        wadv (* adversary capability *)
        a_first a_last (* special adresses *) 
        (b_r e_r : Addr) (* stack *) :
    
    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->

    (* Program adresses assumptions *)
    contiguous_between f2_addrs a_first a_last ->

    (* Linking table and failure subroutine assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (f_a_first + strings.length assert_fail_instrs)%a = Some a_env ->

    (* We assume the adversary capability is Global *)
    isLocalWord wadv = false ->
    
    (* Stack assumptions *)
    region_size b_r e_r > 8 -> (* we must assume the stack is large enough for needed local state *)

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_t30]} →
    
    {{{ r_stk ↦ᵣ inr ((URWLX,Local),b_r,e_r,b_r)
      ∗ interp W (inr ((URWLX,Local),b_r,e_r,b_r))
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* flag *)
      ∗ (∃ ι, inv ι (flag_a ↦ₐ[RW] inl 0%Z))
      (* token which states all invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv *)
      ∗ r_t30 ↦ᵣ wadv
      ∗ interp W wadv
      (* trusted *)
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ f2 f2_addrs pc_p' r_t30 f_a
      (* linking table *)
      ∗ (pc_b ↦ₐ[pc_p'] inr (RO,Global,b_link,e_link,a_link)
              ∗ a_entry ↦ₐ[RO] inr (E, Global, f_b, f_e, f_a_first))
      (* failure subroutine *)
      ∗ (∃ ι, na_inv logrel_nais ι (∃ a', ⌜contiguous_between a' f_a_first f_a_last⌝
                                           ∗ assert_fail a' RX
                                           ∗ a_env ↦ₐ[RX] inr (flag_p, Global, flag_b, flag_e, flag_a)))
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
    {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤                           
                         ∗ sts_full_world W'
                         ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hfl Hf2 Hwb_link Ha_entry Ha_env Hglobal Hsize Hrmap_dom φ)
            "(Hr_stk & #Hstk_val & Hr_gen & #Hflag & Hna & Hr_adv & #Hadv & HPC & Hf2 & Hlink & #Hfail & Hs & Hr) Hφ /=".
    (* prepare stack validity *)
    rewrite fixpoint_interp1_eq. iSimpl in "Hstk_val".
    assert (min b_r e_r = b_r) as ->.
    { revert Hsize; rewrite /region_size;clear. solve_addr. }
    assert (region_addrs b_r b_r = []) as ->;[by rewrite /region_addrs /region_size -Zminus_diag_reverse /=|].
    assert (max b_r b_r = b_r) as ->;[clear;solve_addr|].
    iDestruct "Hstk_val" as "[_ Hstk_val]".
    iAssert ([∗ list] a' ∈ region_addrs b_r e_r, read_write_cond a' RWLX (fixpoint interp1) ∧ ⌜region_state_U_pwl W a'⌝)%I
      as "#Hstk_region".
    { iApply (big_sepL_mono with "Hstk_val"). iIntros (k y Hy) "H".
      iDestruct "H" as (p Hfl') "H". destruct p;inversion Hfl'. iFrame. }

    (* next we will need to split the stack into its temporary and uninitialized parts, revoke it, and manually revoke 
       the uninitialised parts of the desired local stack frame *)
    destruct (region_addrs_split3 _ _ _ Hsize) as [asplit [Hstksplit Hspliteq] ].
    set (ltempsplit := (@list_filter Addr (region_type_temporary W) (region_type_temporary_dec W)
                                     (region_addrs b_r asplit))).
    set (ltemp := (@list_filter Addr (region_type_temporary W) (region_type_temporary_dec W)
                                (region_addrs b_r e_r))).
    set (ltemprest := (@list_filter Addr (region_type_temporary W) (region_type_temporary_dec W)
                                    (region_addrs asplit e_r))).
    assert (Hltempspliteq: ltemp = ltempsplit ++ ltemprest).
    { rewrite /ltemp /ltempsplit /ltemprest.
      rewrite Hstksplit list_filter_app. auto. }
    iAssert (⌜Forall (λ a, region_type_temporary W a) ltemp⌝)%I as %Htemp.
    { iPureIntro. eapply List.Forall_forall.
      intros. eapply elem_of_list_filter.
      eapply elem_of_list_In; eauto. }
    remember Htemp as Htemp'. clear HeqHtemp'.
    rewrite Hltempspliteq in Htemp. eapply Forall_app in Htemp.
    destruct Htemp as [Htemp Htemprest].
    set (luninitsplit := (@list_filter Addr (region_type_uninitialized W) (region_type_uninitialized_dec W)
                                       (region_addrs b_r asplit))).
    iAssert (⌜Forall (λ a, region_type_uninitialized W a) luninitsplit⌝)%I as %Huninit.
    { iPureIntro. eapply List.Forall_forall.
      intros. eapply elem_of_list_filter.
      eapply elem_of_list_In; eauto. }
    assert (Hdupuninit: NoDup luninitsplit).
    { eapply NoDup_filter, NoDup_ListNoDup. apply NoDup_ListNoDup,region_addrs_NoDup. }
    pose proof (extract_temps_split W ltemp) as [l' [Hdup Hiff] ];
      [apply NoDup_filter,NoDup_ListNoDup,NoDup_ListNoDup, region_addrs_NoDup|apply Htemp'|].

    (* we revoke all temporary regions in W *)
    iMod (monotone_revoke_keep_some W _ ltemp with "[$Hs $Hr]") as "[Hsts [Hr [Hrest Hstack] ] ]";[apply Hdup|..].
    { iSplit.
      - iApply big_sepL_forall. iPureIntro. intros n. simpl. intros x Hsome. apply Hiff. apply elem_of_app; left.
        apply elem_of_list_lookup. eauto. 
      - iApply big_sepL_forall. iIntros. iSplit.
        + iPureIntro. eapply Hiff, elem_of_app; right.
          eapply elem_of_list_lookup; eauto.
        + generalize (proj2 (elem_of_list_lookup ltemp x) ltac:(eauto)); intro Hx.
          eapply elem_of_list_filter in Hx. destruct Hx as [Hx1 Hx2].
          iDestruct (big_sepL_elem_of with "Hstk_region") as "[H _]"; eauto.
          rewrite /read_write_cond /=. iApply "H". }
    rewrite Hltempspliteq. iDestruct (big_sepL_app with "Hstack") as "[Hstack Hstackrest]".

    (* Revoke some uninitialized to get their points to *)
    iMod (region_uninitialized_to_revoked W _ _ _ Hdupuninit with "[$Hsts $Hr]") as "HHH".
    { iApply big_sepL_forall. iIntros. iSplit.
      - iPureIntro. eapply (proj1 (elem_of_list_filter (region_type_uninitialized W) _ _)).
        eapply elem_of_list_lookup. exists k. eauto.
      - generalize (proj2 (elem_of_list_lookup luninitsplit x) ltac:(eauto)); intro Hx.
        eapply elem_of_list_filter in Hx. destruct Hx as [Hx1 Hx2].
        eapply elem_of_submseteq in Hx2;
          [|eapply (submseteq_inserts_r (region_addrs asplit e_r) (region_addrs b_r asplit) (region_addrs b_r asplit));
            auto].
        rewrite -Hstksplit in Hx2.
        iDestruct (big_sepL_elem_of with "Hstk_region") as "[H _]"; eauto.
        rewrite /read_write_cond /=. iApply "H". }
    
    iDestruct "HHH" as "[Hsts [Hr Huninitstack]]".
    
    set (W' := (std_update_multiple (revoke W) luninitsplit Revoked)).
    iAssert ((▷ ∃ ws, ([∗ list] a;w ∈ region_addrs b_r asplit;ws, a ↦ₐ[RWLX] w))
               ∗ ⌜Forall (λ a : Addr, region_type_revoked W' a) ltempsplit⌝
               ∗ ⌜Forall (λ a : Addr, region_type_revoked W' a) luninitsplit⌝)%I
      with "[Hstack Huninitstack]" as "[>Hstack [#Hrevoked1 #Hrevoked2]]".
    { iDestruct (big_sepL_sep with "Hstack") as "[Hstack #Hrevoked]".
      iDestruct (big_sepL_forall with "Hrevoked") as %Hrevoked.
      rename Hrevoked into Hrevoked'.
      assert (Hrevoked: ∀ (x : nat) (x0 : Addr), ltempsplit !! x = Some x0 → std (revoke W) !! x0 = Some Revoked).
      { intros. eapply Hrevoked'. rewrite Hltempspliteq. eauto. }
      iSplit;[|iPureIntro].
      - iDestruct (big_sepL_sep with "Hstack") as "[Hstack _]". iNext.
        iApply region_addrs_exists.
        iDestruct (region_addrs_exists with "Hstack") as (ws) "Hstack".
        iDestruct (big_sepL2_sep with "Hstack") as "[_ Hstack]".
        iDestruct (big_sepL2_sep with "Hstack") as "[Hstack _]".
        iDestruct (region_addrs_exists with "[Hstack]") as "Hstack".
        { iExists ws; auto. }
        iAssert (∀ x : Addr, ⌜x ∈ region_addrs b_r asplit⌝ →
                             ⌜region_type_temporary W x ∨ region_type_uninitialized W x⌝)%I as %HHH.
        { iIntros. eapply elem_of_submseteq in a; [|eapply (submseteq_inserts_r (region_addrs asplit e_r)
                                                                                (region_addrs b_r asplit)
                                                                                (region_addrs b_r asplit)); auto].
          rewrite -Hstksplit in a.
          iDestruct (big_sepL_elem_of with "Hstk_region") as "[_ %]"; eauto. }
        iApply (big_sepL_merge with "[$Hstack] [$Huninitstack]").
        { eapply NoDup_ListNoDup,NoDup_ListNoDup,region_addrs_NoDup. }
        { intros. destruct (HHH _ H) as [HH|HH].
          - left. eapply elem_of_list_filter; auto.
          - right. eapply elem_of_list_filter; auto. }
      - split.
        + revert Htemp; repeat (rewrite Forall_forall). 
          intros Htemp x Hx. eapply elem_of_list_lookup in Hx.
          destruct Hx. rewrite /W' /region_type_revoked std_sta_update_multiple_lookup_same_i.
          eapply Hrevoked; eauto.
          red; intro. eapply elem_of_list_filter in H0. destruct H0.
          eapply Hrevoked in H. destruct H0.
          rewrite /revoke /revoke_std_sta lookup_fmap H0 /= in H.
          discriminate.
        + eapply Forall_forall. intros. rewrite /W' /region_type_revoked.
          eapply std_sta_update_multiple_lookup_in_i; auto. }
    iDestruct "Hrevoked1" as %Hrevoked1.
    iDestruct "Hrevoked2" as %Hrevoked2.
    (* we prepare the stack for storing local state *)
    (* Splitting the stack into own and adv parts *)
    assert (contiguous (region_addrs b_r e_r)) as Hcont_stack;[apply region_addrs_contiguous|].
    assert (contiguous_between (region_addrs b_r e_r) b_r e_r) as Hcontiguous.
    { apply contiguous_between_of_region_addrs; auto. revert Hsize. rewrite /region_size. clear. solve_addr. }
    iDestruct "Hstack" as (ws) "Hstack".
    iDestruct (big_sepL2_length with "Hstack") as %Hlength.
    assert (∃ ws_own ws_adv, ws = ws_own ++ ws_adv ∧ length ws_own = 8)
      as [ws_own [ws_adv [Happ Hlength'] ] ].
    { exists ws, []. split; auto. rewrite app_nil_r. auto.
      rewrite -Hlength. rewrite region_addrs_length; auto. }
    rewrite Happ. assert (Hcontiguous': contiguous_between (region_addrs b_r asplit) b_r asplit).
    { eapply contiguous_between_of_region_addrs; auto.
      rewrite /region_size in Hspliteq. revert Hspliteq; clear; solve_addr. }
    iDestruct (contiguous_between_program_split with "Hstack") as
        (stack_own stack_adv stack_own_last) "(Hstack_own & Hstack_adv & #Hcont)"; [eauto|].
    iDestruct "Hcont" as %(Hcont1 & Hcont2 & Hstack_eq1 & Hlink1).
    iDestruct (big_sepL2_length with "Hstack_own") as %Hlength_own. rewrite Hlength' in Hlength_own.
    rewrite Hstack_eq1 in Hcontiguous'.
    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hf2") as %Hlength_f2.
    iDestruct (big_sepL2_length with "Hstack_adv") as %Hlength_adv.
    (* Getting the top adress on the stack *)
    do 2 (destruct stack_own; [inversion Hlength_own|]; destruct ws_own;[inversion Hlength'|]).
    assert ((region_addrs b_r asplit) !! 0 = Some b_r) as Hfirst_stack.
    { apply region_addrs_first. revert Hspliteq; clear. rewrite /region_size. solve_addr. }
    rewrite Hstack_eq1 /= in Hfirst_stack. inversion Hfirst_stack as [Heq]. subst b_r.
    (* assert that the stack bounds are within bounds *)
    assert (withinBounds (RWLX,Local,a,e_r,a) = true
            ∧ withinBounds (RWLX,Local,a,e_r,stack_own_last) = true) as [Hwb1 Hwb2].
    { split; isWithinBounds; first lia.
      - revert Hsize. rewrite /region_size. clear. solve_addr.
      - by eapply contiguous_between_bounds.
      - apply contiguous_between_bounds in Hcont2. simplify_eq.
        revert Hlength' Hlength Hlink1 Hsize Hlength_adv Hlength_own Hcont2.
        rewrite -region_addrs_length app_length. clear.
        rewrite !region_addrs_length /region_size. solve_addr.
    }
    (* push r_stk 1 *)
    iDestruct "Hstack_own" as "[Ha Hstack_own]".
    do 2 (destruct f2_addrs;[inversion Hlength_f2|]).
    apply contiguous_between_cons_inv_first in Hf2 as Heq. subst a1. 
    iDestruct (big_sepL2_app_inv _ [a_first] (a2::f2_addrs) with "Hf2") as "[Hpush Hprog]"; [simpl;auto|].
    iDestruct "Hpush" as "[Hpush _]".
    iApply (pushU_z_spec); [..|iFrame "HPC Hr_stk Ha Hpush"];
      [iCorrectPC a_first a_last|apply Hfl|auto|iContiguous_next Hf2 0|iContiguous_next Hf2 0|auto|..].
    { done. }
    { iContiguous_next Hcont1 0. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Hb_r)".
    (* Prepare the scall prologue macro *)
    rename a0 into stack_own_b.
    (* destruct stack_own as [|stack_own_b stack_own];[inversion Hlength_own|]. *)
    assert ((stack_own_b :: stack_own) = region_addrs stack_own_b stack_own_last) as ->.
    { apply region_addrs_of_contiguous_between; auto.
      repeat (inversion Hcont1 as [|????? Hcont1']; subst; auto; clear Hcont1; rename Hcont1' into Hcont1). }
    (* assert (stack_adv = region_addrs stack_own_last e_r) as ->. *)
    (* { apply region_addrs_of_contiguous_between; auto. } *)
    assert (contiguous_between (a2 :: f2_addrs) a2 a_last) as Hcont_weak.
    { repeat (inversion Hf2 as [|????? Hf2']; subst; auto; clear Hf2; rename Hf2' into Hf2). }
    iDestruct (contiguous_between_program_split with "Hprog") as (scall_prologue rest s_last)
                                                                   "(Hscall & Hf2 & #Hcont)"; [eauto|..].
    clear Hfirst_stack Hcont_weak.
    iDestruct "Hcont" as %(Hcont_scall & Hcont_rest & Hrest_app & Hlink).
    iDestruct (big_sepL2_length with "Hscall") as %Hscall_length. simpl in Hscall_length, Hlength_f2.
    assert ((stack_own_b + 7)%a = Some stack_own_last) as Hstack_own_bound.
    { rewrite -(addr_add_assoc a _ 1). assert ((1 + 7) = 8)%Z as ->;[done|].
      rewrite Hlength_own in Hlink1. revert Hlink1; clear; solve_addr.
      apply contiguous_between_incr_addr with (i:=1) (ai:=stack_own_b) in Hcont1; auto. }
    assert (∃ a, (stack_own_b + 6)%a = Some a) as [stack_own_end Hstack_own_bound'].
    { revert Hstack_own_bound. clear. intros H. destruct (stack_own_b + 6)%a eqn:Hnone; eauto. solve_addr. }
    assert (a2 < s_last)%a as Hcontlt.
    { revert Hscall_length Hlink. clear. solve_addr. }
    assert (a_first <= a2)%a as Hcontge.
    { apply region_addrs_of_contiguous_between in Hcont_scall. simplify_eq.
      revert Hscall_length Hf2 Hcontlt. clear =>Hscall_length Hf2 Hcontlt.
      apply contiguous_between_middle_bounds with (i := 1) (ai := a2) in Hf2;[solve_addr|auto]. 
    }
    (* apply the uscall spec *)
    iApply (scallU_prologue_spec with "[- $HPC $Hr_stk $Hscall $Hstack_own $Hr_gen]");
      [ | |apply Hwb2| |apply Hcont_scall|apply Hfl|iNotElemOfList|
        iContiguous_next Hcont1 2|apply Hstack_own_bound'|apply Hstack_own_bound| |done|..].
    { assert (s_last <= a_last)%a as Hle;[by apply contiguous_between_bounds in Hcont_rest|].
      intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      revert Hle Hcontlt Hcontge Hmid. clear. intros. split; solve_addr. }
    { simplify_eq. iContiguous_bounds_withinBounds a stack_own_last. }
    { clear; split; solve_addr. }
    { assert (5 + 40 = 45)%Z as ->;[done|]. rewrite Hscall_length in Hlink. done. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hr_gen & Hstack_own & Hscall)".
    iDestruct (big_sepL2_length with "Hf2") as %Hf2_length. simpl in Hf2_length.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e s_last a_last) as Hvpc1.
    { intros mid Hmid. assert (a_first <= s_last)%a as Hle;[apply contiguous_between_bounds in Hcont_scall;
                                                           revert Hcont_scall Hcontge;clear; solve_addr|].
      apply isCorrectPC_inrange with a_first a_last; auto.
      revert Hmid Hle. clear. solve_addr. }

    (* We are now ready to set up the region invariants that we will use for the adversary call *)
    (* Since we will halt once they return, we do not mind being in a private future world *)
    (* We can therefore go the simple way and create a custom invariant for the local stack frame *)

    (* All we need to do is to uninitialize the adversary stack *)
    rewrite /W' std_update_multiple_revoke_commute; auto.
    iDestruct (big_sepL_sep with "Hstackrest") as "[Hstackrest _]".
    iDestruct (big_sepL_sep with "Hstackrest") as "[Hstackrest Hstackrest']".
    iDestruct (region_addrs_exists with "Hstackrest") as (wsrest) "Hstackrest".
    iDestruct (big_sepL2_length with "Hstackrest") as %Hlengthstackrest.
    iDestruct (big_sepL2_to_big_sepL_l with "Hstackrest'") as "Hstackrest'"; [eapply Hlengthstackrest|].
    iDestruct (big_sepL2_sep with "[$Hstackrest $Hstackrest']") as "Hstackrest".
    set m_uninit1 : gmap Addr Word := list_to_map (zip ltemprest wsrest).
    iMod (region_revoked_to_uninitialized _ m_uninit1 with "[$Hsts $Hr Hstackrest]") as "[Hsts Hr]".
    { iDestruct (big_sepL2_to_big_sepM with "Hstackrest") as "HH".
      - eapply NoDup_filter, NoDup_ListNoDup, NoDup_ListNoDup, region_addrs_NoDup.
      - rewrite /m_uninit1. iApply (big_sepM_mono with "HH").
        simpl; intros. iIntros "[(A & B & C & D) E]".
        iExists _, _. iFrame. iPureIntro. intros; eapply interp_persistent. }

    assert (Heqq: region_addrs a asplit = (a :: stack_own_b :: stack_own)).
    { rewrite -region_addrs_length Hstack_eq1 app_length Hlength_own in Hspliteq.
      rewrite Hstack_eq1. destruct stack_adv; [rewrite app_nil_r; auto|].
      simpl in Hspliteq; lia. }
    assert (Hxx: stack_own_last = asplit).
    { assert (a <= asplit)%a.
      { revert Hspliteq. clear. intros.
        rewrite /region_size in Hspliteq. solve_addr. }
      revert Hstack_own_bound Hspliteq H Heqq.
      rewrite -region_addrs_length. clear.
      simpl. intros. symmetry in Heqq.
      generalize (contiguous_between_of_region_addrs _ _ _ H Heqq).
      intro. inversion H0; subst. inv H6. 
      assert ((a + 8)%a = Some stack_own_last) by solve_addr.
      rewrite region_addrs_length in Hspliteq.
      generalize (contiguous_between_of_region_addrs_aux _ _ stack_own_last _ Heqq).
      rewrite Hspliteq. rewrite H1. intro.
      generalize (H2 eq_refl); clear H2; intro.
      revert H0 H2; clear; intros. eapply contiguous_between_inj; eauto. }
    subst asplit.
    (* Resulting world *)
    set W'' := (override_uninitializedW m_uninit1 (revoke (std_update_multiple W luninitsplit Revoked))).
    
    assert (related_sts_priv_world W W'') as HWW''.
    { eapply related_sts_priv_trans_world with W'; auto.
      - eapply related_sts_priv_trans_world;[apply revoke_related_sts_priv;auto|].
        rewrite /W'. eapply related_sts_priv_world_std_update_multiple.
        eapply Forall_forall. intros.
        eapply Forall_forall in Huninit; eauto.
        destruct Huninit. exists (Static {[x:=x0]}).
        split; auto. rewrite revoke_monotone_lookup_same'; auto.
        rewrite H0; auto.
      - rewrite /W' /W''. rewrite -std_update_multiple_revoke_commute;auto.
        apply related_sts_priv_world_override_uninitializedW.
        eapply Forall_forall. intros.
        eapply (proj1 (elem_of_elements _ _)) in H.
        eapply elem_of_dom in H. destruct H.
        eapply elem_of_list_to_map_2, elem_of_zip_l, elem_of_list_filter in H as [Htempx Hx].
        assert (x ∉ luninitsplit) as Hnin.
        { intros Hcontr. eapply Forall_forall in Huninit;eauto. destruct Huninit as [? Huninit].
          rewrite Htempx in Huninit. congruence. }
        rewrite std_sta_update_multiple_lookup_same_i;auto.
        exists Revoked. rewrite revoke_lookup_Temp;auto. 
    }

    iAssert (⌜Forall (λ a, region_type_uninitialized W a ∨ region_type_temporary W a) (region_addrs a e_r)⌝)%I as %HWstates.
    { rewrite Forall_forall. iIntros (x Hx).
      iDestruct (big_sepL_elem_of _ _ x with "Hstk_val") as (? ?) "[_ [H | H] ]";auto;[iRight;auto|iLeft;auto]. }

    assert (forall x, x ∈ region_addrs stack_own_last e_r -> region_type_uninitialized W'' x) as HrestpwlU.
    { intros x Hx.
      rewrite /W''.
      destruct (m_uninit1 !! x) eqn:Hsome. 
      - exists w1. apply override_uninitializedW_lookup_some;auto.
      - rewrite /region_type_uninitialized. rewrite override_uninitializedW_lookup_none;auto.
        apply withinBounds_le_addr in Hwb2.
        assert (x ∈ region_addrs a e_r) as Hbe.
          { rewrite (region_addrs_split _ stack_own_last);[apply elem_of_app;by right|
                                                          revert Hwb2;clear;solve_addr]. }
        assert (x ∉ luninitsplit) as Hnin.
        { intros Hcontr%elem_of_list_filter. destruct Hcontr as [_ Hcontr].
          apply (region_addrs_xor_elem_of _ _ stack_own_last) in Hbe as [ [? ?] | [? ?] ];try done. }
        rewrite -std_update_multiple_revoke_commute;auto.
        rewrite std_sta_update_multiple_lookup_same_i;auto.
        assert (W.1 !! x ≠ Some Temporary) as Hntemp.
        { intros Hcontr. apply not_elem_of_list_to_map in Hsome. apply Hsome. 
          rewrite fst_zip;[|rewrite Hlengthstackrest;clear;lia]. 
          apply elem_of_list_filter. split;auto. }
        revert HWstates. rewrite Forall_forall =>HWstate. apply HWstate in Hbe. 
        destruct Hbe as [ [? ?] | Hcontr];[|done]. 
        exists x0. rewrite revoke_monotone_lookup_same;auto.
    }
    
    (* We choose the current register state *)
    set (r := <[PC    := inl 0%Z]>
                     (<[r_stk := inr (URWLX, Local, stack_own_last, e_r, stack_own_last)]>
                     (<[r_t0  := inr (E, Local, a, stack_own_last, stack_own_b)]>
                     (<[r_t30 := wadv]>
                     (create_gmap_default
                        (list_difference all_registers [PC; r_stk; r_t0; r_t30]) (inl 0%Z)))))).
    
    (* We now want to apply the jmp or fail pattern of wadv *)
    iDestruct (jmp_or_fail_spec _ _ φ with "Hadv") as "Hadv_cont".
    
    (* jmp r_adv *)
    iDestruct (big_sepL2_length with "Hf2") as %Hrest_length; simpl in Hrest_length. 
    destruct rest;[inversion Hrest_length|].
    iPrologue rest Hrest_length "Hf2".
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0. 
    iApply (wp_jmp_success with "[$Hinstr $Hr_adv $HPC]");
      [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC s_last a_last|..].
    (* before applying the epilogue, we want to distinguish between a correct or incorrect resulting PC *)
    destruct (decide (isCorrectPC (updatePcPerm wadv))). 
    2: { iEpilogue "(HPC & _ & _)". iApply ("Hadv_cont" with "[Hφ $HPC]").
         iApply "Hφ". iIntros (Hcontr). done. }
    iDestruct "Hadv_cont" as (p g b e a0 Heq) "Hadv_cont". symmetry in Heq. simplify_eq.
    destruct g;inversion Hglobal. 
    iDestruct ("Hadv_cont" $! r _ HWW'') as "Hadv_contW''". 
    iEpilogue "(HPC & Hinstr & Hr_adv)". iSimpl in "HPC".

    (* We have now arrived at the interesting part of the proof: namely the unknown 
       adversary code. In order to reason about unknown code, we must apply the 
       fundamental theorem. To this purpose, we must first define the stsf that will 
       describe the behavior of the memory. *)

    (* We have all the resources of r *)
    iAssert (registers_mapsto (<[PC:=match p with
                                     | E => inr (RX, Global, b, e, a0)
                                     | _ => inr (p, Global, b, e, a0)
                                     end]> r))
                          with "[Hr_gen Hr_stk Hr_t0 Hr_adv HPC]" as "Hmaps".
    { iApply (registers_mapsto_resources with "[$Hr_gen] [$Hr_stk] [$Hr_t0] [$Hr_adv] [$HPC]").
      rewrite !dom_delete_L Hrmap_dom. clear. set_solver. }
    (* r contrains all registers *)
    iAssert (full_map r) as "#full";[iApply r_full|].
    (* Need to prove the validity of the continuation, the stack, as well as put
       local memory into invariant. *)
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"Hprog") with "Hprog")%I as "#Hprog".
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"Hframe") _ with "Hstack_own") as "#Hlocal".
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"Hlink") with "Hlink") as "#Hlink". 
    (* We will put the local state 1 into a separate invariant *)
    iMod (na_inv_alloc logrel_nais ⊤ (nroot.@"local") with "Hb_r")%I as "#Hlocal_one".
    iAssert (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → (fixpoint interp1) W'' (r !r! r1))%I
      with "[-Hsts Hmaps Hna Hφ Hr]" as "Hreg".
    { iIntros (r1).
      assert (r1 = PC ∨ r1 = r_stk ∨ r1 = r_t0 ∨ r1 = r_t30 ∨ (r1 ≠ PC ∧ r1 ≠ r_stk ∧ r1 ≠ r_t0 ∧ r1 ≠ r_t30)) as Hne.
      { destruct (decide (r1 = PC)); [by left|right].
        destruct (decide (r1 = r_stk)); [by left|right].
        destruct (decide (r1 = r_t0)); [by left|right].
        destruct (decide (r1 = r_t30)); [by left|right;auto].  
      }
      destruct Hne as [-> | [-> | [-> | [Hr_t30 | [Hnpc [Hnr_stk [Hnr_t0 Hnr_t30] ] ] ] ] ] ].
      - iIntros "%". contradiction.
      - (* invariant for the stack of the adversary *)
        assert (r !! r_stk = Some (inr (URWLX, Local, stack_own_last, e_r, stack_own_last))) as Hr_stk; auto. 
        rewrite /RegLocate Hr_stk !fixpoint_interp1_eq. 
        iIntros (_). iSimpl.
        assert (Hmin1: min stack_own_last e_r = stack_own_last).
        { apply withinBounds_le_addr in Hwb2. revert Hwb2. clear. solve_addr. }
        rewrite !Hmin1. replace (max stack_own_last stack_own_last) with stack_own_last by (clear; solve_addr).
        rewrite (region_addrs_empty stack_own_last stack_own_last); [|clear; solve_addr].
        rewrite big_sepL_nil. iSplitR;[auto|].
        iApply big_sepL_forall. iIntros (k x Hx).
        assert (x ∈ region_addrs a e_r) as Hin.
        { apply withinBounds_le_addr in Hwb2.
          rewrite (region_addrs_split _ stack_own_last);[|revert Hwb2;clear;solve_addr].
          apply elem_of_app. right. apply elem_of_list_lookup. eauto. }
        iDestruct (big_sepL_elem_of _ _ x with "Hstk_val") as (p' Hfl') "[Hx _]";[auto|].
        destruct p';inversion Hfl'.
        iExists RWLX. iFrame "Hx". iSplit;[auto|]. iPureIntro. right. apply HrestpwlU.
        apply elem_of_list_lookup. eauto. 
      - (* continuation *)
        iIntros (_). 
        assert (r !! r_t0 = Some (inr (E, Local, a, stack_own_last, stack_own_b))) as Hr_t0; auto. 
        rewrite /RegLocate Hr_t0 !fixpoint_interp1_eq. iSimpl. 
        (* prove continuation *)
        (* iExists _,_,_,_. iSplit;[eauto|]. *)
        iAlways.
        rewrite /enter_cond. 
        iIntros (r' W2 HWW2).
        iNext. iSimpl. 
        (* iExists _,_.  do 2 (iSplit; [eauto|]).*)
        iIntros "(#[Hfull' Hreg'] & Hmreg' & Hr & Hs & Hna)". 
        iSplit; [auto|rewrite /interp_conf].
        (* get the PC, currently pointing to the activation record *)
        iDestruct (big_sepM_delete _ _ PC with "Hmreg'") as "[HPC Hmreg']";[rewrite lookup_insert; eauto|].
        (* get a general purpose register *)
        iAssert (⌜∃ wr_t1, r' !! r_t1 = Some wr_t1⌝)%I as %[rt1w Hrt1];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t1 with "Hmreg'") as "[Hr_t1 Hmreg']".
        { rewrite lookup_delete_ne; auto.
          rewrite lookup_insert_ne; eauto. }
        (* get r_stk *)
        iAssert (⌜∃ wr_stk, r' !! r_stk = Some wr_stk⌝)%I as %[rstkw Hrstk];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_stk with "Hmreg'") as "[Hr_stk Hmreg']".
        { do 2 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* get r_t30 *)
        iAssert (⌜∃ wr30, r' !! r_t30 = Some wr30⌝)%I as %[wr30 Hr30];
          first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t30 with "Hmreg'") as "[Hr_t30 Hmreg']".
        { do 3 (rewrite lookup_delete_ne; auto).
          rewrite lookup_insert_ne; eauto. }
        (* open the na invariant for the local stack content *)
        iMod (na_inv_open logrel_nais ⊤ ⊤ with "Hlocal Hna") as "(>Hframe & Hna & Hcls)";auto. 
        assert (PermFlows RX RWLX) as Hrx;[by rewrite /PermFlows /=|].
        (* prepare the continuation *)
        let a := fresh "a" in destruct rest as [|a rest];[inversion Hf2_length|].
        (* prepare the new stack value *)
        assert (exists stack_new, (stack_new + 1)%a = Some stack_own_end) as [stack_new Hstack_new].
        { revert Hstack_own_bound'. clear. intros H. destruct (stack_own_b + 5)%a eqn:Hsome;[|solve_addr].
          exists a. solve_addr. }
        assert (withinBounds (URWLX, Local, a, e_r, stack_own_end) = true) as Hwb3.
        { isWithinBounds. 
          - assert ((a + 1)%a = Some stack_own_b) as Hincr;[apply contiguous_between_incr_addr with (i := 1) (ai := stack_own_b) in Hcont1; auto|].
            revert Hstack_own_bound' Hincr. clear. solve_addr. 
          - apply withinBounds_le_addr in Hwb2 as [_ Hwb2]. revert Hstack_own_bound Hstack_own_bound' Hwb2. clear. solve_addr. 
        }
        (* step through instructions in activation record *)
        iApply (scallU_epilogue_spec with "[-]"); last iFrame "Hframe HPC Hr_t1 Hr_stk";auto;
          [|iContiguous_next Hcont_rest 0|apply Hstack_new|..]. 
        { intros mid Hmid. split;[|auto]. apply withinBounds_le_addr in Hwb2.
          apply (contiguous_between_middle_bounds _ 1 stack_own_b) in Hcont1;[|auto]. revert Hwb2 Hcont1 Hmid. clear. solve_addr.
        }
        { revert Hstack_own_bound Hstack_own_bound';clear;solve_addr. }
        iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hframe)".
        iDestruct "Hr_t1" as (wrt1) "Hr_t1". 
        (* we don't want to close the stack invariant yet, as we will now need to pop it *)
        (* go through rest of the program. We will now need to open the invariant one instruction at a time *)
        (* sub r_t1 0 7 *)
        iPrologue_pre rest Hf2_length. 
        iMod (na_inv_open with "Hprog Hna") as "[ [>Hinstr Hprog_rest] [Hna Hcls'] ]";[solve_ndisj..|].
        iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hr_t1 $Hinstr]");
          [apply decode_encode_instrW_inv|right;left;eauto|iContiguous_next Hcont_rest 1|apply Hfl|iCorrectPC s_last a_last|..]. 
        iNext. iIntros "(HPC & Hinstr & Hr_t1)".
        iMod ("Hcls'" with "[$Hna $Hinstr $Hprog_rest]") as "Hna".
        iApply wp_pure_step_later;auto;iNext.
        (* lea r_stk r_t1 *) 
        iPrologue_pre rest Hf2_length. 
        iMod (na_inv_open with "Hprog Hna") as "[(Ha79 & >Ha80 & Hprog_rest) (Hna & Hcls')]";[solve_ndisj..|].
        assert ((stack_own_end + (0 - 6))%a = Some stack_own_b) as Hpop.
        { revert Hstack_own_bound' Hstack_new. clear. solve_addr. }
        iApply (wp_lea_success_reg with "[$HPC $Hr_t1 $Hr_stk $Ha80]");
          [apply decode_encode_instrW_inv|apply Hfl|iCorrectPC s_last a_last|iContiguous_next Hcont_rest 2|apply Hpop|auto..].
        { simpl. revert Hpop;clear;solve_addr. }
        iNext. iIntros "(HPC & Ha80 & Hr_t1 & Hr_stk)".
        iMod ("Hcls'" with "[$Hna $Ha79 $Ha80 $Hprog_rest]") as "Hna".
        iApply wp_pure_step_later;auto;iNext.
        (* pop r_stk *)
        iMod (na_inv_open with "Hprog Hna") as "[(Ha79 & Ha80 & >Hprog_rest) (Hna & Hcls')]";[solve_ndisj..|].
        iMod (na_inv_open with "Hlocal_one Hna") as "[>Hb_r [Hna Hcls''] ]";[solve_ndisj..|].
        do 2 (destruct rest;[by inversion Hlength_f2|]). 
        iDestruct (mapsto_decomposition [a4;a5;a6] _ _ (popU_instrs r_stk r_t30) with "Hprog_rest") as "[Hpop Hprog_rest]";
          [auto|]. 
        iApply (popU_spec with "[-]"); last iFrame "Hpop Hr_t30 Hr_stk HPC Hr_t1 Hb_r";
          [split; [|split]; iCorrectPC s_last a_last|apply Hfl|auto| |auto|iContiguous_next Hcont_rest 3|
           iContiguous_next Hcont_rest 4|iContiguous_next Hcont_rest 5|iContiguous_next Hcontiguous' 0|..].
        { apply le_addr_withinBounds. clear. solve_addr. revert Hsize;clear;rewrite /region_size. solve_addr. }
        iNext. iIntros "(HPC & Hpop & Hr_t30 & Hb_r & Hr_stk & Hr_t1)". 
        iMod ("Hcls''" with "[$Hna $Hb_r]") as "Hna". 
        iMod ("Hcls'" with "[$Hna $Ha79 $Ha80 Hpop Hprog_rest]") as "Hna".
        { iApply (big_sepL2_app with "Hpop [-]"). iFrame. }
        
        (* we will not use the local stack anymore, so we may close the na_inv *)
        iMod ("Hcls" with "[$Hframe $Hna]") as "Hna".

        (* we will now make the assertion that r_t30 points to 1 *)
        iAssert (⌜∃ w, r' !! r_t2 = Some w⌝)%I as %[w2 Hr2]; first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t2 with "Hmreg'") as "[Hr_t2 Hmreg']".
        { do 4 (rewrite lookup_delete_ne; auto). rewrite lookup_insert_ne; eauto. }
        iAssert (⌜∃ w, r' !! r_t3 = Some w⌝)%I as %[w3 Hr3]; first iApply "Hfull'".
        iDestruct (big_sepM_delete _ _ r_t3 with "Hmreg'") as "[Hr_t3 Hmreg']".
        { do 5 (rewrite lookup_delete_ne; auto). rewrite lookup_insert_ne; eauto. }
        iMod (na_inv_open with "Hprog Hna") as "[(Ha79 & Ha80 & >Hprog_rest) (Hna & Hcls')]";[solve_ndisj..|].
        iDestruct (mapsto_decomposition [a4;a5;a6] _ _ (popU_instrs r_stk r_t30) with "Hprog_rest") as "[Hpop Hprog_rest]";
          [auto|].
        iDestruct (big_sepL2_length with "Hprog_rest") as %Hlength_rest.
        assert (contiguous_between (a7 :: rest) a7 a_last) as Hcont_rest_weak.
        { repeat (inversion Hcont_rest as [|????? Hcont_rest']; subst; auto; clear Hcont_rest; rename Hcont_rest' into Hcont_rest). }
        iDestruct (contiguous_between_program_split with "Hprog_rest") as (rest1 rest2 link0) "(Hassert & Hhalt & #Hcont)";
          [apply Hcont_rest_weak|].
        iDestruct "Hcont" as %(Hcont_rest1 & Hcont_rest2 & Heq_app1 & Hlink0).
        iDestruct (big_sepL2_length with "Hhalt") as %Hrest2.
        destruct rest2;[inversion Hrest2|].
        apply contiguous_between_cons_inv_first in Hcont_rest2 as Heq. subst a8. 
        iMod (na_inv_open with "Hlink Hna") as "[ [>Hpc_b >Ha_entry] [Hna Hcls''] ]";[solve_ndisj..|]. 
        iApply (assert_r_z_success with "[-]");last iFrame "Hassert HPC Hr_t30 Hpc_b Ha_entry";auto;[|apply Hcont_rest1|].
        { intros mid Hmid. apply isCorrectPC_inrange with s_last a_last; auto.
          apply contiguous_between_middle_bounds with (i:=6) (ai:=a7) in Hcont_rest;auto.
          apply contiguous_between_middle_bounds with (i:=0) (ai:=link0) in Hcont_rest2;auto.
          revert Hmid Hcont_rest Hcont_rest2. clear. solve_addr. }
        iSplitL "Hr_t1";[iNext;iExists _;iFrame|].
        iSplitL "Hr_t2";[iNext;iExists _;iFrame|].
        iSplitL "Hr_t3";[iNext;iExists _;iFrame|].
        iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_t30 & HPC & Hassert & Hpc_b & Ha_entry)". 
        iMod ("Hcls''" with "[$Hna $Hpc_b $Ha_entry]") as "Hna".
        (* halt *)
        destruct rest2;[|inversion Hrest2].
        apply contiguous_between_last with (ai:=link0) in Hcont_rest2 as Hlast;auto. 
        iApply (wp_bind (fill [SeqCtx])).
        iDestruct "Hhalt" as "[Hinstr _]". 
        iApply (wp_halt with "[$HPC $Hinstr]");
          [apply decode_encode_instrW_inv|apply Hfl| |].
        { apply isCorrectPC_inrange with s_last a_last; auto.
          apply contiguous_between_middle_bounds with (i:=6) (ai:=a7) in Hcont_rest as Hle;auto.
          apply contiguous_between_bounds in Hcont_rest.
          apply contiguous_between_bounds in Hcont_rest1. 
          revert Hcont_rest Hcont_rest1 Hle Hlast. clear. solve_addr. }
        iNext. iIntros "(HPC & Hinstr)".
        iMod ("Hcls'" with "[$Hna Ha79 Ha80 Hpop Hassert Hinstr]") as "Hna".
        { iNext. iFrame "Ha79 Ha80".
          iApply (big_sepL2_app with "Hpop [-]"). rewrite Heq_app1.
          iApply (big_sepL2_app with "Hassert [-]"). iFrame. done. }
        iApply wp_pure_step_later;auto;iNext.
        (* halted: need to show post condition *)
        iApply wp_value. iIntros "_".
        evar (r'' : gmap RegName Word).
        instantiate (r'' := <[PC    := inr (pc_p, pc_g, pc_b, pc_e, link0)]>
                           (<[r_t1  := inl 0%Z]>
                           (<[r_t2  := inl 0%Z]>
                           (<[r_t3  := inl 0%Z]>
                           (<[r_t30 := inl 0%Z]>
                           (<[r_stk := inr (URWLX, Local, a, e_r, a)]> r')))))). 
        iFrame. iExists r'',_. iFrame. iSplit;[|iSplit].
        + iDestruct "Hfull'" as %Hfull'.
          iPureIntro.
          intros r0. rewrite /r''.
          destruct (decide (PC = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_t1 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_t2 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (r_t3 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (r_t30 = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto. 
          destruct (decide (r_stk = r0));first subst. 
          { rewrite lookup_insert. eauto. }
          rewrite lookup_insert_ne; auto.
        + rewrite /r''.
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I r'' PC
                       with "[-]") as "Hmreg'"; auto.
          { by rewrite lookup_insert. }
          iFrame. do 2 rewrite delete_insert_delete.
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I _ r_t1
                       with "[-]") as "Hmreg'"; auto.
          { rewrite lookup_delete_ne; auto. by rewrite lookup_insert. }
          iFrame. do 2 rewrite (delete_commute _ r_t1 PC).
          rewrite delete_insert_delete.
          do 2 rewrite (delete_commute _ PC r_t1).
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I _ r_t2
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto). by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_t2 _). rewrite delete_insert_delete. 
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I _ r_t3
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto). by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_t3 _). rewrite delete_insert_delete. 
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I _ r_t30
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto). by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_t30 _). rewrite delete_insert_delete. 
          iDestruct (big_sepM_delete (λ x y, x ↦ᵣ y)%I _ r_stk
                       with "[-]") as "Hmreg'"; auto.
          { repeat (rewrite lookup_delete_ne; auto). by rewrite lookup_insert. }
          iFrame. repeat rewrite (delete_commute _ r_stk _). rewrite delete_insert_delete. 
          iFrame.           
        + iPureIntro. apply related_sts_priv_refl_world. 
      - rewrite Hr_t30. 
        assert (r !! r_t30 = Some (inr (p, Global, b, e, a0))) as Hr_t30_some; auto.
        iIntros (_). iApply (interp_monotone_nl with "[] [] Hadv");auto. 
      - (* in this case we can infer that r1 points to 0, since it is in the list diff *)
        assert (r !r! r1 = inl 0%Z) as Hr1.
        { rewrite /RegLocate.
          destruct (r !! r1) eqn:Hsome; rewrite Hsome; last done. rewrite /r in Hsome. 
          do 4 (rewrite lookup_insert_ne in Hsome;auto). 
          assert (Some s = Some (inl 0%Z)) as Heq.
          { rewrite -Hsome. apply create_gmap_default_lookup.
            apply elem_of_list_difference. split; first apply all_registers_correct.
            repeat (apply not_elem_of_cons;split;auto).
            apply not_elem_of_nil. 
          }
          by inversion Heq. 
        }
        rewrite Hr1 !fixpoint_interp1_eq. iSimpl. auto. 
    }
    iAssert (((interp_reg interp) _ r))%I as "#HvalR";[iSimpl;auto|].
    iSpecialize ("Hadv_contW''" with "[$HvalR $Hmaps Hsts $Hna $Hr]"); iFrame. 
    iDestruct "Hadv_contW''" as "[_ Ho]". 
    rewrite /interp_conf.
    iApply wp_wand_r. iFrame.
    iIntros (v) "Htest".
    iApply "Hφ". 
    iIntros (->). 
    iSpecialize ("Htest" with "[]");[auto|]. 
    iDestruct "Htest" as (r0 W6) "(Hr0 & Hregr0 & % & Hna & Hsts)". 
    iExists _,_. iFrame.
    iPureIntro. eapply related_sts_priv_trans_world;[apply HWW''|auto].
  Qed. 


End lse.
