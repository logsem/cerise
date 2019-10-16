From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

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
    { rewrite (fixpoint_interp1_eq _ (inr _)) /=. 
      destruct Hp as [-> | [-> | ->] ];
      (iExists _,_,_,_; iSplitR;[eauto|];
       iExists p';do 2 (iSplit; auto);
       iAlways;iIntros (a' r' W' Hin) "Hfuture";
       iNext; destruct W' as [fs' fr']; 
       iExists _,_; do 2 (iSplitR; [auto|]); 
       iIntros "(#[Hfull Hreg'] & Hmap & Hr & Hsts & Hna) /="; 
       iExists _,_,_,_,_; iSplit;[eauto|];
       iApply ("IH" with "Hfull Hreg' Hmap Hr Hsts Hna"); auto).
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
      + (* successful write into a *) admit.
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
      case_eq (writeAllowed p
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
             *** (* locality failure *)
               admit.
             
      destruct (writeAllowed p).
      + iApply (wp_store_success_reg_same with "[$HPC $Ha]"). 
        iApply (wp_store_fail1' with "[$HPC $Ha]"); eauto. 
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate.
    * destruct (H3 dst) as [wdst Hsomedst].
      iDestruct ((big_sepM_delete _ _ dst) with "Hmap") as "[Hdst Hmap]"; [rewrite lookup_delete_ne; eauto|].
      destruct wdst.
      { iApply (wp_store_fail2 with "[HPC Hdst Ha]"); eauto; iFrame.
        iNext. iIntros. iApply wp_pure_step_later; auto.
        iNext. iApply wp_value. iIntros. discriminate. }
      { destruct c,p,p,p. 
        case_eq (writeAllowed p); intros.
        - case_eq (withinBounds (p, l, a2, a1, a0)); intros.
          + destruct src.
            * (* need to get a0 ↦ₐ _ and stuff, todo later *)
              (* take the points to earlier, to factorize *)
              admit.
            * destruct (reg_eq_dec r0 PC).
              { subst r0. (* need to get a0 ↦ₐ _, todo later *) admit. }
              { destruct (reg_eq_dec dst r0).
                - subst r0. (* same thing *) admit.
                - destruct (H3 r0) as [wr0 Hsomer0].
                  iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hr0 Hmap]"; [repeat rewrite lookup_delete_ne; eauto|].
                  (* same thing, todo *) admit. }
          + iApply (wp_store_fail1 with "[HPC Hdst Ha]"); eauto; iFrame.
            iNext. iIntros. iApply wp_pure_step_later; auto.
            iNext. iApply wp_value. iIntros. discriminate.
        - iApply (wp_store_fail1 with "[HPC Hdst Ha]"); eauto; iFrame.
          iNext. iIntros. iApply wp_pure_step_later; auto.
          iNext. iApply wp_value. iIntros. discriminate. }
  Admitted.
*)
End fundamental.