From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel addr_reg_sample fundamental rules proofmode.

Section HashCap.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}.

  Definition hash_cap_off_end := 12%Z.
  Definition hash_cap_off_iter := 2%Z.

  Axiom hash_concat_app : forall `{MachineParameters} {A : Type} (la la' : list A),
    hash (la++la') = hash_concat (hash la) (hash la').
  Axiom hash_concat_assoc : forall `{MachineParameters}, Assoc eq hash_concat.
  Axiom hash_singleton : forall `{MachineParameters} {A : Type} (a : A),
    hash ([a]) = hash a.
  Instance hash_concat_Assoc `{MachineParameters} : Assoc eq hash_concat := hash_concat_assoc.

  (* first we will define the list of Words making up the mclear macro *)
  Definition hash_cap_instrs :=
    [
       (* r4 := (p, b, e, a) *)
        GetB r_t1 r_t4; (* r1 := b *)
        GetA r_t2 r_t4; (* r2 := a *)
        Sub r_t2 r_t1 r_t2; (* r2 := b - a *)
        Lea r_t4 r_t2; (* r4 := (p, b, e, b) *)
        GetE r_t5 r_t4; (* r5 := e *)
        Sub r_t5 r_t5 1; (* r5 := e - 1 *)
        (* init: *)
        Load r_t7 r_t4; (* r7 := mem(b) *)
        Hash r_t8 r_t7; (* r8 := hash(mem(b)) *)
        Lea r_t4 1; (* r4 := (p, b, e, b+1) *)
        Add r_t1 r_t1 1; (* r1 := b+1 *)
        (* we subtract the bound by one so that the lt check becomes a le check *)
        Mov r_t2 PC; (* r2 := PCC *)
        Lea r_t2 hash_cap_off_end; (* r2 := PCC_end *)
        Mov r_t3 PC;
        Lea r_t3 hash_cap_off_iter; (* r3 := PCC_iter *)
        (* iter: *)
        Lt r_t6 r_t5 r_t1; (* r6 := (e <= b+i) *)
        Jnz r_t2 r_t6; (* exit the loop if (e <= b+i) *)
        Load r_t7 r_t4; (* r7 := mem(b + i) *)
        Hash r_t7 r_t7; (* r7 := hash(mem(b + i)) *)
        HashConcat r_t8 r_t8 r_t7; (* r8 := hash( mem[b;b+i-1] ) || hash( mem(b+i) ) /// = hash(mem[b;b+i]) *)
        Lea r_t4 1; (* r4 := (p, b, e, b+i+1) *)
        Add r_t1 r_t1 1; (* r1 := b+i+1 *)
        Jmp r_t3; (* jmp to iter *)
        (* end: *)
        Mov r_t1 0;
        Mov r_t2 0;
        Mov r_t3 0;
        Mov r_t4 0;
        Mov r_t5 0;
        Mov r_t6 0;
        Mov r_t7 0
      ].

  Definition hash_cap_lcode : list LWord :=
    encodeInstrsLW hash_cap_instrs.

  Lemma hash_cap_spec_iter
    (pc_p : Perm) (pc_b pc_e a_first : Addr) (pc_v : Version)
    (p_r : Perm) (b_r e_r : Addr) (v_r : Version)
    (i : nat) (* iteration of the loop *)
    (wend w6 w7 : LWord)
    (ws_hd ws_tl : list LWord) φ :

    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length hash_cap_instrs)%a →
    readAllowed p_r = true ->
    (b_r < e_r)%a ->

      ▷ codefrag a_first pc_v hash_cap_lcode
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ 14)%a pc_v
    ∗ ▷ r_t1 ↦ᵣ LInt (b_r + i)
    ∗ ▷ r_t2 ↦ᵣ wend
    ∗ ▷ r_t3 ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ 14)%a pc_v (* cap to iter *)
    ∗ ▷ r_t4 ↦ᵣ LCap p_r b_r e_r (b_r ^+ i)%a v_r
    ∗ ▷ r_t5 ↦ᵣ LInt (e_r - 1%nat)
    ∗ ▷ r_t6 ↦ᵣ w6
    ∗ ▷ r_t7 ↦ᵣ w7
    ∗ ▷ r_t8 ↦ᵣ LInt (hash (lword_get_word <$> ws_hd))
    ∗ ▷ ([[ b_r , (b_r ^+ i)%a ]] ↦ₐ{v_r} [[ ws_hd ]])
    ∗ ▷ ([[ (b_r ^+ i)%a , e_r ]] ↦ₐ{v_r} [[ ws_tl ]])
    ∗ ▷ (PC ↦ᵣ updatePcPermL wend
         ∗ codefrag a_first pc_v hash_cap_lcode
         ∗ (∃ w1', r_t1 ↦ᵣ w1')
         ∗ r_t2 ↦ᵣ wend
         ∗ r_t3 ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ 14)%a pc_v (* cap to iter *)
         ∗ (∃ w4', r_t4 ↦ᵣ w4')
         ∗ r_t5 ↦ᵣ LInt (e_r - 1%nat)
         ∗ (∃ w6', r_t6 ↦ᵣ w6')
         ∗ (∃ w7', r_t7 ↦ᵣ w7')
         ∗ r_t8 ↦ᵣ LInt (hash (lword_get_word <$> (ws_hd ++ ws_tl)))
         ∗ ([[ b_r , (b_r ^+ i)%a ]] ↦ₐ{v_r} [[ ws_hd ]])
         ∗ ([[ (b_r ^+ i)%a , e_r ]] ↦ₐ{v_r} [[ ws_tl ]])
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hwb HreadAllowed Hbounds)
      "(>Hprog & >HPC & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hr_t6 & >Hr_t7 & >Hr_t8 & Hmem_hd & Hmem_tl & Hφ)".
    codefrag_facts "Hprog".
    iLöb as "IH" forall (i ws_hd ws_tl w6 w7) "Hφ".

    iInstr "Hprog".

    destruct ( decide (e_r - 1%nat < b_r + i)%Z ) as [ Hle | Hle].
    {
      iDestruct (big_sepL2_length with "Hmem_hd") as "%Hlen_hd".
      iDestruct (big_sepL2_length with "Hmem_tl") as "%Hlen_tl".
      rewrite !map_length !finz_seq_between_length in Hlen_hd, Hlen_tl.
      rewrite finz_dist_0 in Hlen_tl; last solve_addr.
      destruct ws_tl ; last done.
      apply Z.ltb_lt in Hle.
      rewrite Hle /=.
      iInstr "Hprog".
      cbn.
      iApply ("Hφ" with "[-]"); eauto; iFrame.
      iEval (rewrite app_nil_r); iFrame.
      iSplitL "Hr_t1"; first iExists _; iFrame.
      iSplitL "Hr_t4"; first iExists _; iFrame.
      iSplitL "Hr_t6"; first iExists _; iFrame.
      iExists _; iFrame.
    }

    pose proof Hle as Hle'.
    apply Z.ltb_nlt in Hle'; rewrite Hle' /=.
    iInstr "Hprog".

    iDestruct (big_sepL2_length with "Hmem_tl") as "%Hlen_tl".
    iDestruct (big_sepL2_length with "Hmem_hd") as "%Hlen_hd".
    rewrite !map_length !finz_seq_between_length in Hlen_tl,Hlen_hd.
    rewrite finz_dist_S in Hlen_tl; last solve_addr.
    destruct ws_tl ; first done.

    iDestruct ( (region_mapsto_cons _ (b_r^+(i+1))%a) with "Hmem_tl") as "[Hbr_i Hmem_tl]"
    ; [solve_addr | solve_addr |].
    iInstr "Hprog".
    { split ; [solve_pure| solve_addr]. }

    wp_instr.
    iInstr_lookup "Hprog" as "Hi" "Hprog".
    iApply (wp_hash_success_same with "[$HPC $Hr_t7 $Hi]"); try solve_pure.
    iNext. iIntros "(HPC & Hi & Hr_t7)".
    wp_pure; iInstr_close "Hprog".

    wp_instr.
    iInstr_lookup "Hprog" as "Hi" "Hprog".

    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hr_t7 $Hr_t8 $Hi]"); try solve_pure.
    { by rewrite /is_AddSubLt; do 3 right; left. }
    iNext. iIntros "(HPC & Hi & Hr_t7 & Hr_t8)".
    wp_pure; iInstr_close "Hprog".

    iInstr "Hprog".
    { transitivity (Some (b_r ^+(i + 1))%a); solve_addr. }
    { destruct p_r ; auto. }

    iInstr "Hprog".
    iInstr "Hprog".
    replace (
       match pc_p with
                | E => LCap RX pc_b pc_e (a_first ^+ 14)%a pc_v
                | _ => LCap pc_p pc_b pc_e (a_first ^+ 14)%a pc_v
                end
      ) with (LCap pc_p pc_b pc_e (a_first ^+ 14)%a pc_v).
    2: { destruct pc_p; auto. apply ExecPCPerm_not_E in Hvpc; done. }

    iDestruct ( region_mapsto_split _ (b_r ^+ (i + 1))%a _ _ _ [l] with "[$Hmem_hd Hbr_i]") as "Hmem_hd"; auto.
    { solve_addr. }
    { rewrite (region_mapsto_cons _ (b_r ^+ (i + 1))%a);[ iFrame | solve_addr | solve_addr].
      iEval (rewrite /region_mapsto).
      iFrame.
      rewrite finz_seq_between_empty; last solve_addr.
      done.
    }
    iApply ("IH" $! (i+1) (ws_hd ++ [l]) (ws_tl) with
             "[$] [$HPC] [Hr_t1] [$Hr_t2] [$Hr_t3] [Hr_t4] [$Hr_t5] [$Hr_t6] [$Hr_t7] [Hr_t8] [Hmem_hd] [Hmem_tl] [Hφ]").
    { replace (b_r + i + 1%nat)%Z with (b_r + (i + 1)%nat)%Z by lia; done. }
    { replace (b_r ^+ (i + 1))%a with (b_r ^+ (i + 1)%nat)%a by solve_addr; done. }
    { by rewrite -(hash_singleton (lword_get_word l)) -hash_concat_app fmap_app list_fmap_singleton.
    }
    { replace (b_r ^+ (i + 1))%a with (b_r ^+ (i + 1)%nat)%a by solve_addr; done. }
    { replace (b_r ^+ (i + 1))%a with (b_r ^+ (i + 1)%nat)%a by solve_addr; done. }
    iNext.
    iIntros "(HPC & Hcode & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6 & Hr7 & Hr8 & Hmem_hd & Hmem_tl)".
    iApply "Hφ"; iFrame.
    replace  ((ws_hd ++ [l]) ++ ws_tl) with ( ws_hd ++ l :: ws_tl ).
    2: { by rewrite -app_assoc cons_middle. }
    iFrame "Hr8".
    rewrite (region_mapsto_cons _ (b_r ^+ (i + 1))%a);[ iFrame | solve_addr | solve_addr].
    iDestruct ( region_mapsto_split b_r (b_r ^+ (i + 1)%nat)%a (b_r ^+ i)%a v_r ws_hd [l] with
                "Hmem_hd") as "[Hmem_hd Hbr_i]"; auto;first solve_addr.
    rewrite (region_mapsto_cons _ (b_r ^+ (i + 1))%a);[ | solve_addr | solve_addr].
    iDestruct "Hbr_i" as "[Hbr_i _]".
    replace ( (b_r ^+ (i + 1)%nat)%a ) with (b_r ^+ (i + 1))%a by solve_addr.
    iFrame.
 Qed.

  Lemma hash_cap_spec
    (pc_p : Perm) (pc_b pc_e a_first : Addr) (pc_v : Version)
    (p_r : Perm) (b_r e_r a_r : Addr) (v_r : Version)
    (w1 w2 w3 w4 w5 w6 w7 w8 : LWord)
    (ws : list LWord) φ :

    ExecPCPerm pc_p →
    SubBounds pc_b pc_e a_first (a_first ^+ length hash_cap_instrs)%a →
    readAllowed p_r = true ->
    (b_r < e_r)%a ->

      ▷ codefrag a_first pc_v hash_cap_lcode
    ∗ ▷ PC ↦ᵣ LCap pc_p pc_b pc_e a_first pc_v
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t4 ↦ᵣ LCap p_r b_r e_r a_r v_r
    ∗ ▷ r_t5 ↦ᵣ w5
    ∗ ▷ r_t6 ↦ᵣ w6
    ∗ ▷ r_t7 ↦ᵣ w7
    ∗ ▷ r_t8 ↦ᵣ w8
    ∗ ▷ ([[ b_r , e_r ]] ↦ₐ{v_r} [[ ws ]])
    ∗ ▷ (PC ↦ᵣ LCap pc_p pc_b pc_e (a_first ^+ length hash_cap_instrs)%a pc_v
         ∗ codefrag a_first pc_v hash_cap_lcode
         ∗ r_t1 ↦ᵣ LInt 0%Z
         ∗ r_t2 ↦ᵣ LInt 0%Z
         ∗ r_t3 ↦ᵣ LInt 0%Z
         ∗ r_t4 ↦ᵣ LInt 0%Z
         ∗ r_t5 ↦ᵣ LInt 0%Z
         ∗ r_t6 ↦ᵣ LInt 0%Z
         ∗ r_t7 ↦ᵣ LInt 0%Z
         ∗ r_t8 ↦ᵣ LInt (hash ( lword_get_word <$> ws ) )
         ∗ ([[ b_r , e_r ]] ↦ₐ{v_r} [[ ws ]])
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hwb HreadAllowed Hbounds)
      "(>Hprog & >HPC & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hr_t6 & >Hr_t7 & >Hr_t8 & Hmem & Hφ)".
    codefrag_facts "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    { transitivity (Some b_r); solve_addr. }
    { destruct p_r ; auto. }
    iInstr "Hprog".
    iInstr "Hprog".
    iDestruct (big_sepL2_length with "Hmem") as "%Hlen_ws".
    rewrite map_length finz_seq_between_length in Hlen_ws.
    rewrite finz_dist_S in Hlen_ws; eauto.
    destruct ws as [|ws1 ws]; first by cbn in *.
    iDestruct (region_mapsto_cons _ (b_r^+1)%a with "Hmem") as "[Hbr Hmem]"; [solve_addr|solve_addr|].
    iInstr "Hprog".
    { split ; [solve_pure| solve_addr]. }
    iInstr "Hprog".
    iInstr "Hprog".
    { transitivity (Some (b_r ^+1)%a); solve_addr. }
    { destruct p_r ; auto. }
    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".

    iApply ( (hash_cap_spec_iter _ _ _ _ _ _ _ _ _ _ _ _ _ [ws1]) with "[-]"); eauto; iFrame.
    iSplitL "Hr_t8".
    { by rewrite hash_singleton. }
    iSplitL "Hbr".
    { iNext.
      rewrite (region_mapsto_cons _ (b_r ^+ 1%nat)%a); [|solve_addr|solve_addr]; iFrame.
      rewrite /region_mapsto finz_seq_between_empty; last solve_addr.
      done.
    }
    iNext; iIntros "(HPC & Hprog & Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6 & Hr7 & Hr8 & Hmem_hd & Hmem_tl)".
    iDestruct "Hr1" as (w1') "Hr1".
    iDestruct "Hr4" as (w4') "Hr4".
    iDestruct "Hr6" as (w6') "Hr6".
    iDestruct "Hr7" as (w7') "Hr7".
    replace (updatePcPermL (LCap pc_p pc_b pc_e (a_first ^+ 22)%a pc_v))
              with (LCap pc_p pc_b pc_e (a_first ^+ 22)%a pc_v).
    2: { destruct pc_p; auto.
         apply ExecPCPerm_not_E in Hvpc;done.
    }
    iGo "Hprog".
    iApply ("Hφ" with "[-]"); eauto; iFrame.
    iDestruct (region_mapsto_split _ _ (b_r^+1%nat)%a with "[$Hmem_hd $Hmem_tl]") as "Hmem".
    { solve_addr. }
    { cbn.
      rewrite finz_dist_S; last solve_addr.
      by rewrite finz_dist_0; last solve_addr.
    }
    iFrame.
 Qed.

End HashCap.
