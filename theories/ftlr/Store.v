From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel monotone.

Section fundamental.
  Context `{memG Σ, regG Σ, STSG Σ, logrel_na_invs Σ,
            MonRef: MonRefG (leibnizO _) CapR_rtc Σ,
            Heap: heapG Σ}.

  Notation WORLD := (leibnizO (STS_states * STS_rels)).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iProp Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iProp Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Ltac option_locate_mr m r :=
    repeat match goal with
           | H : m !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
                                         assert (m !m! a = w) as Ha; [ by (unfold MemLocate; rewrite H) | clear H]
           | H : r !! ?a = Some ?w |- _ => let Ha := fresh "H"a in
                                         assert (r !r! a = w) as Ha; [ by (unfold RegLocate; rewrite H) | clear H]
           end.

  Ltac inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep Hpc_new1 :=
    match goal with
    | H : cap_lang.prim_step (Instr Executable) (r, m) _ ?e1 ?σ2 _ |- _ =>
      let σ := fresh "σ" in
      let e' := fresh "e'" in
      let σ' := fresh "σ'" in
      let Hstep' := fresh "Hstep'" in
      let He0 := fresh "He0" in
      let Ho := fresh "Ho" in
      let He' := fresh "H"e' in
      let Hσ' := fresh "H"σ' in
      let Hefs := fresh "Hefs" in
      let φ0 := fresh "φ" in
      let p0 := fresh "p" in
      let g0 := fresh "g" in
      let b0 := fresh "b" in
      let e2 := fresh "e" in
      let a0 := fresh "a" in
      let i := fresh "i" in
      let c0 := fresh "c" in
      let HregPC := fresh "HregPC" in
      let Hi := fresh "H"i in
      let Hexec := fresh "Hexec" in 
      inversion Hstep as [ σ e' σ' Hstep' He0 Hσ Ho He' Hσ' Hefs |?|?|?]; 
      inversion Hstep' as [φ0 | φ0 p0 g0 b0 e2 a0 i c0 HregPC ? Hi Hexec];
      (simpl in *; try congruence );
      subst e1 σ2 φ0 σ' e' σ; try subst c0; simpl in *;
      try (rewrite HPC in HregPC;
           inversion HregPC;
           repeat match goal with
                  | H : _ = p0 |- _ => destruct H
                  | H : _ = g0 |- _ => destruct H
                  | H : _ = b0 |- _ => destruct H
                  | H : _ = e2 |- _ => destruct H
                  | H : _ = a0 |- _ => destruct H
                  end ; destruct Hi ; clear HregPC ;
           rewrite Hpc_a Hinstr /= ;
           rewrite Hpc_a Hinstr in Hstep)
    end.
  
  Lemma wp_store_success_z_PC E pc_p pc_p' pc_g pc_b pc_e pc_a pc_a' w z :
     cap_lang.decode w = Store PC (inl z) →
     PermFlows pc_p pc_p' →
     isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w }}}
       Instr Executable @ E
       {{{ RET NextIV;
           PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a')
              ∗ pc_a ↦ₐ[pc_p'] (inl z) }}}.
   Proof.
     iIntros (Hinstr Hfl Hvpc Hpca' Hwa ϕ) "(>HPC & >Hpc_a) Hϕ".
     iApply wp_lift_atomic_head_step_no_fork; auto.
     iIntros (σ1 l1 l2 n) "Hσ1 /=". destruct σ1; simpl.
     iDestruct "Hσ1" as "[Hr Hm]".
     apply isCorrectPC_ra_wb in Hvpc as Hrawb.
     apply Is_true_eq_true, andb_true_iff in Hrawb as [Hra Hwb]. 
     assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc as [?????? Heq]; subst.
         destruct Heq as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
     iDestruct (@gen_heap_valid with "Hr HPC") as %?.
     iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?; auto. 
     option_locate_mr m r.
     iApply fupd_frame_l.
     iSplit.
     - rewrite /reducible.
       iExists [], (Instr _),(updatePC (update_mem (r,m) pc_a (inl z))).2, [].
       iPureIntro.
       constructor.
       apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                              (Store PC (inl z))
                              (NextI,_)); eauto; simpl; try congruence.
       inversion Hvpc as [????? [Hwb1 Hwb2] ]; subst.
       by rewrite HPC Hwa Hwb /= /updatePC /update_mem /= HPC Hpca'.
     - (*iMod (fupd_intro_mask' ⊤) as "H"; eauto.*)
       iModIntro. iNext.
       iIntros (e1 σ2 efs Hstep).
       inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
       rewrite HPC Hwa Hwb /= /updatePC /update_mem /update_reg HPC Hpca' /=.
       iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
       { apply PermFlows_trans with pc_p;auto. }
       iMod (@gen_heap_update with "Hr HPC") as "[$ HPC]".
       iSpecialize ("Hϕ" with "[HPC Hpc_a]"); iFrame; eauto.
   Qed.

   Lemma wp_store_fail E src dst pc_p pc_g pc_b pc_e pc_a w pc_p' :
    cap_lang.decode w = Store dst src →
    PermFlows pc_p pc_p' →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) ->
    (pc_a + 1)%a = None →

    {{{ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ pc_a ↦ₐ[pc_p'] w
           ∗ if (reg_eq_dec PC dst)
             then emp
             else ∃ p g b e a w' p', dst ↦ᵣ (inr (p,g,b,e,a))
                                         ∗ a ↦ₐ[p'] w'
                                         ∗ ⌜p' ≠ O⌝ }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    intros Hinstr Hfl Hvpc Hnext;
      (iIntros (φ) "(HPC & Hpc_a & Hdst) Hφ";
       iApply wp_lift_atomic_head_step_no_fork; auto;
       iIntros (σ1 l1 l2 n) "Hσ1 /="; destruct σ1; simpl;
       iDestruct "Hσ1" as "[Hr Hm]";
       iDestruct (@gen_heap_valid with "Hr HPC") as %?;
       iDestruct (@gen_heap_valid_cap with "Hm Hpc_a") as %?;
       option_locate_mr m r).
    { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc as [?????? Heq]; subst.
       destruct Heq as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
    iAssert (⌜if (reg_eq_dec PC dst)
              then True
              else ∃ p g b e a w', r !! dst = Some (inr (p,g,b,e,a))
                                   ∧ m !! a = Some w'⌝)%I as %?.
    { destruct (reg_eq_dec PC dst); auto.
      destruct dst; first contradiction.
      iDestruct "Hdst" as (p g b e a w' p') "[Hdst [Ha %] ]".
      iDestruct (@gen_heap_valid with "Hr Hdst") as %?.
      iDestruct (@gen_heap_valid_cap with "Hm Ha") as %?; auto.
      iExists _,_,_,_,_. eauto. 
    }
    assert (pc_p' ≠ O) as Ho.  
     { destruct pc_p'; auto. destruct pc_p; inversion Hfl.
       inversion Hvpc as [?????? Heq]; subst.
         destruct Heq as [Hcontr | [Hcontr | Hcontr] ]; inversion Hcontr. }
    iApply fupd_frame_l.
    iSplit.
    - rewrite /reducible.
      destruct (reg_eq_dec PC dst).
      + subst.  
        destruct ((writeAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a)) &&
                  (match src with
                   | inl z => true
                   | inr r0 => (negb (isLocalWord (r !r! r0)) || match pc_p with
                                                             | RWL | RWLX => true
                                                             | _ => false
                                                             end)
                   end)) eqn:Hcond.
        * apply andb_true_iff in Hcond as [Hwawb Hlocal]. 
          iExists [],(Instr Failed), (r,(update_mem (r, m) pc_a (match src with
                                                                | inl z => inl z
                                                                | inr r0 => r !r! r0
                                                                end)).2), []. 
          iPureIntro.
          constructor.
          apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC src)
                                 (Failed,_));
            eauto; simpl; try congruence.
          rewrite HPC Hwawb /updatePC /= HPC Hnext /=.
          destruct src; eauto. destruct (r !r! r0); auto. 
          destruct c,p,p,p. simpl in Hlocal.
          destruct (isLocal l); auto.
          rewrite orb_false_l in Hlocal.
          destruct pc_p; inversion Hlocal; auto.
        * iExists [],(Instr Failed), (r,m), [].
          iPureIntro. constructor.
          apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store PC src)
                                 (Failed,_));
            eauto; simpl; try congruence.
          apply andb_false_elim in Hcond as [Hwawb | Hlocal].
          ** rewrite HPC Hwawb /updatePC /=. destruct src; auto. 
          ** destruct (writeAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a)) eqn:Hwawb.
             { destruct src; inversion Hlocal. 
               rewrite HPC Hwawb.
               destruct (r !r! r0); inversion H5.
               simpl in H5. 
               destruct c,p,p,p; last inversion H6. 
               destruct (isLocal l),pc_p; try done.                
             }
             { rewrite HPC Hwawb /updatePC /=. destruct src; auto. }
      + destruct H3 as (p & g & b & e & a & w' & Hsome1 & Hsome2).
        destruct ((writeAllowed p && ((b <=? a)%a && (a <=? e)%a)) &&
                  (match src with
                   | inl z => true
                   | inr r0 => (negb (isLocalWord (r !r! r0)) || match p with
                                                  | RWL | RWLX => true
                                                  | _ => false
                                                  end)
                   end)) eqn:Hcond.
        * apply andb_true_iff in Hcond as [Hwawb Hlocal]. 
          iExists [],(Instr Failed), (r,(update_mem (r, m) a (match src with
                                                                | inl z => inl z
                                                                | inr r0 => r !r! r0
                                                                end)).2), []. 
          iPureIntro.
          constructor.
          apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a
                                 (Store dst src)
                                 (Failed,_));
            eauto; simpl; try congruence.
          option_locate_mr m r. 
          rewrite Hdst Hwawb /updatePC /= HPC Hnext. 
          destruct src; eauto. destruct (r !r! r0); auto. 
          destruct c,p0,p0,p0. simpl in Hlocal. 
          destruct (isLocal l); auto.
          rewrite orb_false_l in Hlocal.
          destruct p; inversion Hlocal; auto.
        * iExists [],(Instr Failed), (r,m), [].
          iPureIntro. constructor.
          apply (step_exec_instr (r,m) pc_p pc_g pc_b pc_e pc_a (Store dst src)
                                 (Failed,_));
            eauto; simpl; try congruence.
          option_locate_mr m r. 
          apply andb_false_elim in Hcond as [Hwawb | Hlocal].
          ** rewrite Hdst Hwawb /updatePC /=. destruct src; auto. 
          ** destruct (writeAllowed p && ((b <=? a)%a && (a <=? e)%a)) eqn:Hwawb.
             { destruct src; inversion Hlocal. 
               rewrite Hdst Hwawb.
               destruct (r !r! r0); inversion H4.
               simpl in H5. 
               destruct c,p0,p0,p0; last inversion H5. 
               destruct (isLocal l),p; try done.                
             }
             { rewrite Hdst Hwawb /updatePC /=. destruct src; auto.  }        
      - (* iMod (fupd_intro_mask' ⊤) as "H"; eauto. *)
      
      destruct (reg_eq_dec PC dst). 
      + iModIntro.
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
        subst. 
        rewrite HPC /updatePC /= HPC Hnext /=. 
        destruct src,(writeAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <=? pc_e)%a)) eqn:Hwa;
          simpl; [ |iFrame;iNext;iModIntro;iSplitR;[auto|by iApply "Hφ"]| |
                 iFrame;iNext;iModIntro;iSplitR;[auto|by iApply "Hφ"] ]. 
        * iNext.
          iMod (@gen_heap_update_cap with "Hm Hpc_a") as "[$ Hpc_a]"; auto.
          { apply PermFlows_trans with pc_p;auto. simpl.
            destruct pc_p; inversion Hwa; done. }
          iFrame. iModIntro. iSplitR;[auto|by iApply "Hφ"]. 
        * admit.
      + destruct H3 as (p & g & b & e & a & w' & Hsome1 & Hsome2).
        iModIntro.
        iIntros (e1 σ2 efs Hstep).
        inv_head_step_advanced m r HPC Hpc_a Hinstr Hstep HPC.
        option_locate_mr m r. 
        rewrite Hdst /updatePC /= HPC Hnext /=.
        destruct src,(writeAllowed p && ((b <=? a)%a && (a <=? e)%a)) eqn:Hwa;
          simpl; [ |iFrame;iNext;iModIntro;iSplitR;[auto|by iApply "Hφ"]| |
                   iFrame;iNext;iModIntro;iSplitR;[auto|by iApply "Hφ"] ].
        * iNext.
          destruct dst; first contradiction.
          iDestruct "Hdst" as (p0 g0 b0 e0 a0 w0 p0') "[Hdst [Ha %]]". 
          iMod (@gen_heap_update_cap with "Hm Ha") as "[Hm Ha]"; auto.
          { apply PermFlows_trans with pc_p;auto. simpl.
            destruct pc_p; inversion Hwa; done. }
          iFrame. iModIntro. iSplitR;[auto|by iApply "Hφ"].
          
        
        rewrite HPC. destruct HnwaHnwb as [Hnwa | Hnwb].
      + rewrite Hnwa; simpl. destruct src; simpl.
        * iFrame. iNext. iModIntro.
          iSplitR; auto. by iApply "Hφ".
        * iFrame. iNext. iModIntro. 
          iSplitR; auto. by iApply "Hφ".
      + simpl in Hnwb. rewrite Hnwb.
        rewrite andb_comm; simpl.
        destruct src; simpl.
        * iFrame. iNext. iModIntro. 
          iSplitR; auto. by iApply "Hφ".
        * iFrame. iNext. iModIntro.
          iSplitR; auto. by iApply "Hφ".
  Qed.
   
  Lemma store_case (fs : STS_states) (fr : STS_rels) (r : leibnizO Reg) (p p' : Perm) 
        (g : Locality) (b e a : Addr) (w : Word) (dst : RegName) (src : Z + RegName) :
      p = RX ∨ p = RWX ∨ p = RWLX
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a <= e)%a
    → PermFlows p p'
    → p' ≠ O
    → cap_lang.decode w = Store dst src
    -> □ ▷ (∀ a0 a1 a2 a3 a4 a5 a6 a7,
             full_map a2
          -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (a0, a1)) (a2 !r! r1))
          -∗ registers_mapsto (<[PC:=inr (a3, a4, a5, a6, a7)]> a2)
          -∗ region (a0, a1)
          -∗ sts_full a0 a1
          -∗ na_own logrel_nais ⊤
          -∗ ⌜a3 = RX ∨ a3 = RWX ∨ a3 = RWLX⌝
             → □ (∃ p'0 : Perm, ⌜PermFlows a3 p'0⌝
                    ∧ ([∗ list] a8 ∈ region_addrs a5 a6, read_write_cond a8 p'0 interp))
                 -∗ interp_conf a0 a1)
    -∗ ([∗ list] a0 ∈ region_addrs b e, read_write_cond a0 p' interp)
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) (fs, fr)) (r !r! r1))
    -∗ read_write_cond a p' interp
    -∗ ▷ future_mono (λ Wv : prodO WORLD (leibnizO Word), ((fixpoint interp1) Wv.1) Wv.2)
    -∗ ▷ ((fixpoint interp1) (fs, fr)) w
    -∗ sts_full fs fr
    -∗ na_own logrel_nais ⊤
    -∗ open_region a (fs, fr)
    -∗ a ↦ₐ[p'] w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (fs' : STS_states) (fr' : STS_rels),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv fs fs' fr fr'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full fs' fr' ∗ region (fs', fr') }} }}.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hi.
    iIntros "#IH #Hbe #Hreg #Harel #Hmono #Hw".
    iIntros "Hfull Hna Hr Ha HPC Hmap".
    rewrite delete_insert_delete.
    (* for the successful writes from PC, we want to show that 
         the region can be closed again *)
    iAssert (((fixpoint interp1) (fs, fr)) (inr ((p,g),b,e,a)))%I
        as "#HPCw".
    { (* rewrite (fixpoint_interp1_eq _ (inr _)) /=.  *)
      (* destruct Hp as [-> | [-> | ->] ]; *)
      (* (iExists _,_,_,_; iSplitR;[eauto|]; *)
      (*  iExists p';do 2 (iSplit; auto); *)
      (*  iAlways;iIntros (a' r' W' Hin) "Hfuture"; *)
      (*  iNext; destruct W' as [fs' fr'];  *)
      (*  iExists _,_; do 2 (iSplitR; [auto|]);  *)
      (*  iIntros "(#[Hfull Hreg'] & Hmap & Hr & Hsts & Hna) /=";  *)
      (*  iExists _,_,_,_,_; iSplit;[eauto|]; *)
      (*  iApply ("IH" with "Hfull Hreg' Hmap Hr Hsts Hna"); auto). *)
      admit. 
    }
    destruct (reg_eq_dec dst PC).
    - subst dst.
       destruct Hp as [-> | Hp].
       { (* if p is RX, write is not allowed *)
         iApply (wp_store_fail1' with "[$HPC $Ha]"); eauto.
         iNext. iIntros (_).
         iApply wp_pure_step_later; auto. iNext.
         iApply wp_value. iIntros. discriminate. }
      destruct src.
      + (* successful inl write into a *)
        destruct (a + 1)%a eqn:Hnext. 
        { (* successful PC increment *)
          iApply (wp_store_success_z_PC with "[$HPC $Ha]"); eauto;
            [by destruct Hp as [-> | ->]|].
          iNext. iIntros "[HPC Ha]".
          iApply wp_pure_step_later; auto; iNext.
          iDestruct (region_close with "[$Hr $Ha]") as "Hr"; iFrame "#". 
          { iSplitR;[auto|]. rewrite (fixpoint_interp1_eq _ (inl _)) /=. eauto. }
          iDestruct ((big_sepM_insert) with "[$Hmap $HPC]")
            as "Hmap"; [by rewrite lookup_delete|].
          rewrite insert_delete. 
          iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hfull] [$Hna]"); iFrame "#"; auto. 
        }
        { (* failure to increment PC *)
          
        }
      + destruct (Hsome r0) as [wdst Hsomedst].
        destruct (reg_eq_dec r0 PC).
        * simplify_eq.
          destruct Hp as [-> | ->].
          ** destruct (isLocalWord wdst) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               admit.
             *** (* successful write into a: word is not local *)
               admit.
          ** (* successful write into a: perm is local allowed *)
            admit. 
        * iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
            as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
          destruct Hp as [-> | ->]. 
          ** destruct (isLocalWord wdst) eqn:Hlocal.
             *** (* failure: trying to write a local word without perm *)
               admit.
             *** (* successful write into a: word is not local *)
               admit.
          ** (* successful write into a: perm is local allowed *)
            admit.
    - destruct (Hsome dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap")
        as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
      destruct wdst.
      { (* if dst does not contain cap, fail *)
        iApply (wp_store_fail2 with "[HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate. }
      destruct c,p0,p0,p0.
      case_eq (writeAllowed p0
               && withinBounds (p0,l,a2,a1,a0));  
        intros Hconds.
      + destruct src.
        * (* successful write into a0 *)
          admit.
        * destruct (reg_eq_dec PC r0),(reg_eq_dec dst r0);
            first congruence; subst. 
          ** (* successful store of PC into a0 *)
            admit.
          ** case_eq (negb (isLocal l) || match p with
                                         | RWL | RWLX => true
                                         | _ => false end); intros Hconds'. 
             *** (* successful write from r0 into a0 *)
               admit.
             *** (* locality failure *)
               admit.
          ** destruct (Hsome r0) as [wsrc Hsomesrc].
             assert (delete PC r !! r0 = Some wsrc).
             { rewrite lookup_delete_ne; auto. }
             iDestruct ((big_sepM_delete _ _ r0) with "Hmap")
               as "[Hsrc Hmap]"; [rewrite lookup_delete_ne; eauto|].
             destruct wsrc.
             *** (* successful write from r0 into a0 *)
               admit.
             *** case_eq (negb (isLocalWord (inr c)) || match p0 with
                                                       | RWL | RWLX => true
                                                       | _ => false end); intros Hconds'. 
                 **** (* successful write from r0 into a0 *)
                   admit.
                 **** (* locality failure *)
                   admit.
      + (* write failure, either wrong permission or not within range *)
        admit.
  Admitted. 
             
   
End fundamental.