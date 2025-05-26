From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base sorting.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_EInit.
From cap_machine Require Import proofmode.

Lemma otype_unification (ot1 ot2 : OType) (n : ENum) :
  tid_of_otype ot1 = Some n ->
  Z.even ot1 = true ->
  finz.of_z (2 * n) = Some ot2 ->
  ot1 = ot2.
Proof.
  intros Htidx Htidx_even Hot_ec.
  rewrite /tid_of_otype in Htidx.
  rewrite Htidx_even in Htidx.
  assert (n = (Z.to_nat ot1 `div` 2)) as -> by (by injection Htidx); clear Htidx.
  assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat ot1) 2)) = (Z.to_nat ot1) ).
  {
    rewrite -(Nat2Z.inj_mul 2).
    rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
    2:{
      destruct ot1.
      rewrite /Z.even in Htidx_even.
      cbn in *.
      destruct z; cbn in *.
      + rewrite Z2Nat.inj_0.
        apply PeanoNat.Nat.divide_0_r.
      + rewrite Z2Nat.inj_pos.
        destruct p; cbn in * ; try done.
        rewrite Pos2Nat.inj_xO.
        apply Nat.divide_factor_l.
      + rewrite Z2Nat.inj_neg.
        apply PeanoNat.Nat.divide_0_r.
    }
    rewrite PeanoNat.Nat.mul_comm.
    rewrite (PeanoNat.Nat.div_mul (Z.to_nat ot1) 2); done.
  }
  solve_addr.
Qed.

(* TODO generalise *)
Lemma map_Forall_all_P (w : LWord) (la : list Addr) (lws : list LWord) (v : Version)
  (P : LWord -> Prop) :
  NoDup la ->
  length lws = length la ->
  w ∈ lws ->
  map_Forall
    (λ (a : LAddr) (lw : LWord), laddr_get_addr a ∈ la → P lw)
    (logical_region_map la lws v)
  -> P w.
Proof.
  generalize dependent lws.
  generalize dependent w.
  induction la as [|a la]; intros w lws Hnodup Hlen Hw Hall_z.
  - destruct lws ; set_solver.
  - destruct lws as [|w1 lws] ; first set_solver.
    cbn in Hlen ; simplify_eq.
    apply NoDup_cons in Hnodup as [Ha_notin_l Hnodup].
    cbn in Hall_z.
    apply map_Forall_insert in Hall_z as [Hladdr Hall_z].
    2: { rewrite -not_elem_of_list_to_map.
         intro Hcontra.
         rewrite elem_of_list_fmap in Hcontra.
         destruct Hcontra as ([x vx] & Hx & Hcontra)
         ; cbn in Hx ; simplify_eq.
         apply elem_of_zip_l in Hcontra.
         rewrite elem_of_list_fmap in Hcontra.
         destruct Hcontra as (y & Hy & Hcontra)
         ; cbn in Hy ; simplify_eq.
         set_solver.
    }
    apply elem_of_cons in Hw as [-> | Hw].
    * apply Hladdr; set_solver.
    * eapply IHla; eauto.
      eapply map_Forall_impl; eauto.
      intros [y vy] wy IH Hy; cbn in *.
      apply IH.
      set_solver.
Qed.

Section fundamental.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          {reservedaddresses : ReservedAddresses}
          `{MP: MachineParameters}
          {contract_enclaves : @CustomEnclavesMap Σ MP}.

  Notation D := ((leibnizO LWord) -n> iPropO Σ).
  Notation R := ((leibnizO LReg) -n> iPropO Σ).
  Implicit Types lw : (leibnizO LWord).
  Implicit Types interp : (D).

  Local Hint Resolve finz_seq_between_NoDup list_remove_elem_NoDup : core.

  Lemma einit_case (lregs : leibnizO LReg)
    (p_pc : Perm) (b_pc e_pc a_pc : Addr) (v_pc : Version)
    (lw_pc : LWord) (rcode rdata : RegName) (P : D):
    ftlr_instr lregs p_pc b_pc e_pc a_pc v_pc lw_pc (EInit rcode rdata) P.
  Proof.
    intros Hp Hsome i Hbae Hi.
    iIntros "[#Hcontract #Hsystem_inv] #IH #Hinv #Hinva #Hreg #(Hread & Hwrite & %HpersP) Hown Ha HP Hcls HPC Hmap".
    specialize (HpersP lw_pc).
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)) as [Hx|Hx].
      rewrite Hx lookup_insert; unfold is_Some. by eexists.
      by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hrcode now, to instantiate the existentials in step 1 *)
    assert (∃ p_code b_code e_code a_code v_code,
               read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs)
                 rcode p_code b_code e_code a_code v_code)
      as (p_code & b_code & e_code & a_code & v_code & HVrcode).
    {
      specialize Hsome' with rcode as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p_code b_code e_code a_code v_code|] | ]; try done.
      by repeat eexists.
    }
    (* Initializing the names for the values of Hrdata now, to instantiate the existentials in step 1 *)
    assert (∃ p_data b_data e_data a_data v_data,
               read_reg_inr (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs)
                 rdata p_data b_data e_data a_data v_data)
      as (p_data & b_data & e_data & a_data & v_data & HVrdata).
    {
      specialize Hsome' with rdata as Hsrc.
      destruct Hsrc as [wsrc Hsomesrc].
      unfold read_reg_inr. rewrite Hsomesrc.
      destruct wsrc as [|[ p_data b_data e_data a_data v_data|] | ]; try done.
      by repeat eexists.
    }
    name_current_mask mask_init.

    pose proof (Hsome' rcode) as [wcode Hlregs_rcode].
    iAssert (interp wcode) as "#Hinterp_wcode".
    {
      destruct (decide (rcode = PC)) as [->|Hrcode_neq_pc]; simplify_map_eq.
      + done.
      + iApply ("Hreg" $! rcode); eauto.
    }

    pose proof (Hsome' rdata) as [wdata Hlregs_rdata].
    iAssert (interp wdata) as "#Hinterp_wdata".
    {
      destruct (decide (rdata = PC)) as [->|Hrdata_neq_pc]; simplify_map_eq.
      + done.
      + iApply ("Hreg" $! rdata); eauto.
    }

    iAssert (⌜allows_einit (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) rcode⌝)%I
      as "%Hreserved_wcode".
    { iIntros (p b e a v Hrcode HreadAllowed).
      destruct (decide (rcode = PC)) as [?|Hrcode_neq_pc]; simplify_map_eq.
      all: iDestruct (readAllowed_not_reserved with "Hinterp_wcode") as "%Hreserved_code"; done.
    }
    iAssert (⌜allows_einit (<[PC:=LCap p_pc b_pc e_pc a_pc v_pc]> lregs) rdata⌝)%I
      as "%Hreserved_wdata".
    { iIntros (p b e a v Hrdata HreadAllowed).
      destruct (decide (rdata = PC)) as [?|Hrdata_neq_pc]; simplify_map_eq.
      all: iDestruct (readAllowed_not_reserved with "Hinterp_wdata") as "%Hreserved_data"; done.
    }

    (* We open the sytem invariant, necessary for apply WP EInit,
       because it contains the EC register. *)
    iInv "Hsystem_inv" as "Hsys" "Hcls_sys".
    iDestruct "Hsys" as (Ecn ot_ec) "(>HEC & >%Hot_ec & Halloc & Hfree & #Hcustom_inv)".
    name_current_mask mask_sys.

    (* The next steps consist on all deriving the failure cases,
       which are all safe because the semantics ends up failing
       at the next execution cycle.
     *)

    destruct (is_log_cap wcode) eqn:Hwcode; cycle 1.
    { (* wcode in not a capability *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hrcode Hlregs_rcode Hwcode.
        simplify_map_eq.
        rewrite Hlregs_rcode in Hrcode; simplify_eq.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
    destruct_word wcode; rewrite /read_reg_inr Hlregs_rcode in HVrcode; cbn in HVrcode, Hwcode;  simplify_eq.

    destruct (decide (p_code = RX)) as [->|Hrx]; cycle 1.
    { (* wcode in not a RX capability *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hrcode Hlregs_rcode Hrx.
        rewrite Hlregs_rcode in Hrcode; simplify_eq.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (decide (b_code < e_code)%a) as [Hb_code|Hb_code]; cycle 1.
    { (* Code capability is too small *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hrcode Hlregs_rcode Hb_code Hcode_size.
        rewrite Hlregs_rcode in Hrcode; simplify_eq; solve_addr.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (is_log_cap wdata) eqn:Hwdata; cycle 1.
    { (* wdata in not a capability *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hrdata Hlregs_rdata Hwdata.
        simplify_map_eq.
        rewrite Hlregs_rdata in Hrdata; simplify_eq.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }
    destruct_word wdata; rewrite /read_reg_inr Hlregs_rdata in HVrdata; cbn in HVrdata, Hwdata;  simplify_eq.

    destruct (decide (p_data = RW)) as [->|Hrx]; cycle 1.
    { (* wdata in not a RW capability *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hrdata Hlregs_rdata Hrx.
        rewrite Hlregs_rdata in Hrdata; simplify_eq.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (decide (b_data < e_data)%a) as [Hb_data|Hb_data]; cycle 1.
    { (* Data capability is too small *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hrdata Hlregs_rdata Hb_data Hdata_size.
        rewrite Hlregs_rdata in Hrdata; simplify_eq; solve_addr.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (decide (is_Some (a_pc + 1)%a)) as [Hpca_next | Hpca_next]; cycle 1.
    { (* The PC overflows *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        incrementLPC_inv as (p_pc'&b_pc'&e_pc'&a_pc'&v_pc'& ? & HPC & Z & Hregs'); simplify_map_eq.
        solve_addr.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (decide (PC = rcode)) as [?|Hrcode_neq_pc].
    { (* wcode in not a RX capability *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        by contradiction Hrcode_PC.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (decide (PC = rdata)) as [Heq|Hrdata_neq_pc]; first (clear -Heq Hlregs_rdata Hp; simplify_map_eq; naive_solver).
    assert (rcode ≠ rdata) as Hrcode_neq_rdata by ( intros ->; simplify_map_eq ).

    destruct ( decide (a_pc ∈ (finz.seq_between b_data e_data)))
      as [Hdata_apc_disjoint|Hdata_apc_disjoint].
    { (* data overlap with pc, the sweep will fail *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        simplify_map_eq.
        clear -Hunique_regs_data Hrdata_neq_pc Hdata_apc_disjoint Hb_data i.
        simplify_map_eq.
        apply isCorrectLPC_isCorrectPC in i; cbn in i.
        apply isCorrectPC_le_addr in i.
        eapply (map_Forall_lookup_1 _ _ PC) in Hunique_regs_data ; last by simplify_map_eq.
        rewrite decide_False in Hunique_regs_data; auto.
        apply Hunique_regs_data.
        rewrite /overlap_wordL /overlap_word /=.
        rewrite elem_of_finz_seq_between in Hdata_apc_disjoint.
        destruct (data_b <? b_pc)%a eqn:Hdata_b; solve_addr.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct ( decide ((finz.seq_between b_code e_code) ## (finz.seq_between b_data e_data)))
      as [Hcode_data_disjoint|Hcode_data_disjoint]; cycle 1.
    { (* code and data overlap, the sweep will fail *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        clear -Hunique_regs_data
                 Hrdata Hrcode
                 Hlregs_rdata Hlregs_rcode
                 Hcode_data_disjoint
                 Hrcode_neq_rdata.
        simplify_map_eq.
        rewrite Hrcode in Hlregs_rcode; simplify_eq.
        rewrite Hrdata in Hlregs_rdata; simplify_eq.
        eapply (map_Forall_lookup_1 _ _ rcode) in Hunique_regs_data ; last by simplify_map_eq.
        rewrite decide_False in Hunique_regs_data; auto.
        apply overlap_word_disjoint in Hunique_regs_data; eauto.
        apply Hcode_data_disjoint; set_solver + Hunique_regs_data.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct (ot_ec + 2)%ot as [ot_ec2|] eqn:Hot_ec2; cycle 1.
    { (* The OType overflows *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        opose proof (otype_unification ot ot_ec Ecn _ _ _) as -> ; eauto.
        rewrite Hot in Hot_ec2; done.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    destruct ( decide (a_pc ∈ (finz.seq_between b_code e_code)))
      as [Hcode_apc_disjoint|Hcode_apc_disjoint].
    { (* code overlap with pc, the sweep will fail *)
      iDestruct (memMap_resource_1 with "Ha") as "Hmem".
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        simplify_map_eq.
        clear -Hunique_regs_code Hrcode Hrdata Hrcode_neq_pc Hcode_apc_disjoint Hb_code i.
        simplify_map_eq.
        apply isCorrectLPC_isCorrectPC in i; cbn in i.
        apply isCorrectPC_le_addr in i.
        eapply (map_Forall_lookup_1 _ _ PC) in Hunique_regs_code ; last by simplify_map_eq.
        rewrite decide_False in Hunique_regs_code; auto.
        apply Hunique_regs_code.
        rewrite /overlap_wordL /overlap_word /=.
        rewrite elem_of_finz_seq_between in Hcode_apc_disjoint.
        destruct (code_b <? b_pc)%a eqn:Hcode_b; solve_addr.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec.
          iFrame "∗#%".
        }
        iDestruct (memMap_resource_1 with "Hmem") as "Ha".
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    (* We now have all the necessary information for opening all the memory invariant. *)

    (* Open the code region *)
    iDestruct (interp_open_region $ mask_sys with "Hinterp_wcode")
      as (Ps_code) "[%Hlen_Ps_code Hmod]" ; eauto.
    { eapply Forall_forall. intros a' Ha'.
      subst mask_sys mask_init.
      eapply namespaces.coPset_subseteq_difference_r; first solve_ndisj.
      assert (a' ≠ a_pc) by set_solver.
      solve_ndisj.
    }
    iMod "Hmod" as (lws_code) "(%Hlen_lws_code & %Hpers_Ps_code
      & Hcode & HPs_code & Hreadcond_Ps_code & Hcls_code)".
    name_current_mask mask_code.

    (* Open the data region *)
    iDestruct (interp_open_region $ mask_code with "Hinterp_wdata")
      as (Ps_data) "[%Hlen_Ps_data Hmod]" ; eauto.
    { eapply Forall_forall. intros a' Ha'.
      subst mask_code mask_sys mask_init.
      rewrite /compute_mask_region.
      rewrite -compute_mask_difference_namespace; [| solve_ndisj | solve_ndisj].
      rewrite -compute_mask_difference.
      2: {
        rewrite not_elem_of_list_to_set.
        intro Hcontra.
        rewrite elem_of_list_fmap in Hcontra.
        destruct Hcontra as (a'' & ? & Ha'') ; simplify_eq.
      }
      eapply namespaces.coPset_subseteq_difference_r; auto; first solve_ndisj.
      eapply namespaces.coPset_subseteq_difference_r; auto.
      + assert (a' ≠ a_pc) by set_solver.
        solve_ndisj.
      + apply compute_mask_elem_of; set_solver.
    }
    iMod "Hmod" as (lws_data) "(%Hlen_lws_data & %Hpers_Ps_data
      & Hdata & HPs_data & Hreadcond_Ps_data & Hcls_data)".
    name_current_mask mask_data.

    (* Create a single memory map with all resources, as expected by the WP rule *)
    iDestruct (big_sepM_union with "[$Hcode $Hdata]") as "Hmem".
    { rewrite /logical_region_map.
      apply map_disjoint_list_to_map_zip_r_2; auto.
      + cbn in *; f_equal; simplify_eq.
        by rewrite map_length.
      + apply Forall_forall.
        intros la Hla.
        apply not_elem_of_list_to_map_1.
        rewrite fst_zip; eauto.
        * intro Hcontra.
          rewrite !elem_of_list_fmap in Hla,Hcontra.
          destruct Hla as (la' & -> & Hla').
          destruct Hcontra as (la'' & ? & Hla''); simplify_eq.
          set_solver.
        * cbn.
          rewrite map_length.
          cbn in Hlen_lws_code; simplify_eq.
          lia.
    }
    iDestruct (big_sepM_insert with "[$Hmem $Ha]") as "Hmem".
    { rewrite lookup_union.
      rewrite !logical_region_notin; auto.
    }

    destruct (hash_lmemory_range
                (<[(a_pc, v_pc):=lw_pc]>
                   (logical_region_map (finz.seq_between b_code e_code) lws_code v_code
                      ∪ logical_region_map (finz.seq_between b_data e_data) lws_data v_data)) (b_code ^+ 1)%a e_code v_code
             ) as [|] eqn:Hhash_instrs'; cycle 1.
    { (* Computing the hash fails  *)
      iApply (wp_einit with "[$Hmap $Hmem $HEC]")
      ;eauto
      ; [ by simplify_map_eq
        | rewrite /subseteq /map_subseteq /set_subseteq_instance
          ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
        | by simplify_map_eq
        |
        ].
      iNext.
      iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC & Hspec)".
      iDestruct "Hspec" as "[Hspec | Hspec]".
      (* Contradiction *)
      + iDestruct "Hspec"
          as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
               "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".
        exfalso.
        incrementLPC_inv as (p_pc'&b_pc'&e_pc'&a_pc'&v_pc'& ? & HPC & Z & Hregs'); simplify_map_eq.
        by rewrite Hhash_instrs in Hhash_instrs'.
      + iDestruct "Hspec" as "(_ & -> & -> & ->)".
        iApply wp_pure_step_later; auto.
        (* Derive pure predicates about a_pc' *)
        iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha Hmem]".
        match goal with
        | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
            set (lmem0 := m)
        end.
        assert (
            logical_region_map (finz.seq_between (b_code)%a e_code) (lws_code) v_code
              ⊆ lmem0) as Hmem_code.
        { subst lmem0.
          eapply delete_subseteq_r.
          { eapply logical_region_notin; eauto.
          }
          eapply map_union_subseteq_l.
        }
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hcode Hmem]"
        ; first (eapply Hmem_code).
        match goal with
        | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
            set (lmem1 := m)
        end.
        assert (
            logical_region_map (finz.seq_between (b_data)%a e_data) (lws_data) v_data
              ⊆ lmem1) as Hmem_data.
        { subst lmem1.
          eapply (delete_subseteq_list_r); eauto.
          + apply logical_region_map_disjoint; auto.
            set_solver + Hcode_data_disjoint.
          + subst lmem0.
            eapply delete_subseteq_r.
            { eapply logical_region_notin; eauto.
            }
            eapply map_union_subseteq_r.
            apply logical_region_map_disjoint; auto.
        }
        iDestruct (big_sepM_insert_difference with "Hmem") as "[Hdata Hmem]"
        ; first (eapply Hmem_data).
        iMod ("Hcls_data" with "[Hdata HPs_data Hreadcond_Ps_data]") as "_".
        {
          iNext.
          iApply region_inv_construct; auto.
        }
        iModIntro.
        iMod ("Hcls_code" with "[Hcode HPs_code Hreadcond_Ps_code]") as "_".
        {
          iNext.
          iApply region_inv_construct; auto.
        }
        iModIntro.
        iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
        { iNext. iExists Ecn, ot_ec. iFrame "∗#%". }
        iMod ("Hcls" with "[HP Ha]");[iExists lw_pc;iFrame|iModIntro].
        iNext; iIntros "_".
        iApply wp_value; auto. iIntros; discriminate.
    }

    (* Apply the WP rule *)
    simplify_map_eq.
    iApply (wp_einit with "[$Hmap $Hmem $HEC]")
    ; eauto
    ; [ by simplify_map_eq
      | rewrite /subseteq /map_subseteq /set_subseteq_instance
        ; intros rr _; apply elem_of_dom; rewrite lookup_insert_is_Some'; eauto
      | by simplify_map_eq
      |
      ].
    iNext.
    iIntros (lregs' lmem' retv tidx ot) "(Hmem & Hregs & HEC  & Hspec)".
    iDestruct "Hspec" as "[Hspec | Hspec]"; cycle 1.
    {
      iDestruct "Hspec" as "(%Hspec & -> & -> & ->)".
      exfalso.
      inversion Hspec
        as [
           | wcode Hrcode Hwcode
           | p b e a v Hrcode Hrx
           | p b e a v Hrcode Hbe
           | p b e a v Hrcode Hbe Hhash
           | wdata Hrdata Hwdata
           | p b e a v Hrdata Hrx
           | p b e a v Hrdata Hbe
           | code_b code_e code_a code_v data_b data_e data_a data_v Hrcode Hrdata Hincr
           | Htidx Htidx_even Hot
        ].
      - simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rcode in Hrcode; simplify_eq.
        rewrite Hhash in Hhash_instrs'; simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rdata in Hrdata; simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rdata in Hrdata; simplify_eq.
      - rewrite lookup_insert_ne // Hlregs_rdata in Hrdata; simplify_eq.
      - incrementLPC_inv; simplify_map_eq; eauto.
        rewrite Hincr /is_Some in Hpca_next; naive_solver.
      - opose proof (otype_unification ot ot_ec Ecn _ _ _) as -> ; eauto.
        by rewrite Hot in Hot_ec2.
    }
    clear Hpca_next Hhash_instrs'.

    iDestruct "Hspec"
      as (glmem lmem'' code_b code_e code_a code_v data_b data_e data_a data_v hash_instrs eid)
           "(%Hrcode_PC & %Htidx_next & %Htidx & %Htidx_even & [%Hhash_instrs %Heid] & %Hot
               & %Hrcode & %Hrdata & %Hcode_size & %Hdata_size
               & %Hvalid_update_code & %Hvalid_update_data & %Hlmem'
               & %Hunique_regs_code & %Hunique_regs_data & %Hcode_z & %Hcode_reserved & %data_reserved
               & %Hincr & -> & Henclave_live & #Henclave_all)".

    (* Unification of the different names *)
    simplify_map_eq.
    incrementLPC_inv as (p_pc'&b_pc'&e_pc'&a_pc'&v_pc'& ? & HPC & Z & Hregs'); simplify_map_eq.
    match goal with
    | _ : _ |- context [ enclave_cur ?ECN ?I ] =>
        set (I_ECn := I)
    end.
    opose proof (otype_unification ot ot_ec Ecn _ _ _) as -> ; eauto.
    clear Hot_ec2 ot_ec2.

    rewrite (finz_seq_between_cons ot_ec); last solve_addr.
    rewrite (finz_seq_between_cons (ot_ec ^+ 1)%ot); last solve_addr.
    iEval (rewrite !list_to_set_cons) in "Hfree".
    iDestruct (big_sepS_union with "Hfree") as "[Hfree_ot_ec_0 Hfree]".
    { apply disjoint_union_r.
      split.
      + assert (ot_ec ≠ ot_ec ^+1)%f as Hneq by solve_finz+Hot.
        set_solver+Hneq.
      + apply disjoint_singleton_l.
        apply not_elem_of_list_to_set.
        apply not_elem_of_finz_seq_between.
        solve_finz+Hot.
    }
    iDestruct (big_sepS_union with "Hfree") as "[Hfree_ot_ec_1 Hfree]".
    { apply disjoint_singleton_l.
      apply not_elem_of_list_to_set.
      apply not_elem_of_finz_seq_between.
      solve_finz+Hot.
    }
    rewrite !big_sepS_singleton.

    (* Derive pure conditions on lmem and extract all the points-to resources *)
    set (lmem' :=
           <[(b_data, v_data + 1):=LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec]>
             (<[(b_code, v_code+1):=LCap RW b_data e_data a_data (v_data + 1)]> lmem'')).

    (* Derive pure predicates about a_pc' *)
    assert ( lmem'' !! (a_pc', v_pc') = Some lw_pc ) as Hmem''_pca.
    { eapply is_valid_updated_lmemory_preserves_lmem; eauto.
      by simplify_map_eq.
    }
    assert ( lmem' !! (a_pc', v_pc') = Some lw_pc ) as Hmem'_pca.
    { subst lmem'.
      rewrite lookup_insert_ne //=; cycle 1.
      { intro; simplify_eq.
        apply Hdata_apc_disjoint.
        rewrite finz_seq_between_cons //=.
        set_solver+.
      }
      rewrite lookup_insert_ne //=; cycle 1.
      { intro; simplify_eq.
        apply Hcode_apc_disjoint.
        rewrite finz_seq_between_cons //=.
        set_solver+.
      }
    }
    rewrite -(insert_id lmem' (a_pc', v_pc') lw_pc); auto.
    iDestruct (big_sepM_insert_delete with "Hmem") as "[Ha Hmem]".
    match goal with
    | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
        set (lmem0 := m)
    end.

    (* Derive pure predicates about the previous code_region*)
    assert ( logical_range_map b_code e_code (lws_code) v_code ⊆ lmem'' )
      as Hmem''_code.
    {
      eapply is_valid_updated_lmemory_lmem_incl
        with (la := (finz.seq_between b_code e_code))
             (v:= v_code)
      ; eauto.
      eapply is_valid_updated_lmemory_lmem_subset; last eassumption.
      eapply map_subseteq_trans; cycle 1.
      + eapply insert_subseteq.
        rewrite lookup_union.
        rewrite !logical_region_notin; auto.
      + eapply map_union_subseteq_l.
    }
    assert ( logical_range_map b_code e_code (lws_code) v_code ⊆ lmem' )
      as Hmem'_code.
    {
      subst lmem'.
      eapply insert_subseteq_r.
      { eapply logical_range_notin; auto.
        clear -Hb_data Hb_code Hcode_data_disjoint.
        intro.
        rewrite elem_of_disjoint in Hcode_data_disjoint.
        apply (Hcode_data_disjoint b_data); eauto.
        rewrite elem_of_finz_seq_between; solve_addr.
      }
      eapply insert_subseteq_r.
      { eapply logical_range_version_neq; auto; lia. }
      done.
    }
    assert ( logical_range_map b_code e_code (lws_code) v_code ⊆ lmem0 )
      as Hmem0_code.
    {
      subst lmem0.
      eapply delete_subseteq_r; last done.
      apply logical_range_notin; auto; done.
    }
    iDestruct (big_sepM_insert_difference with "Hmem") as "[Hcode_prev Hmem]"
    ; first (eapply Hmem0_code).
    match goal with
    | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
        set (lmem1 := m)
    end.

    (* Derive pure predicates about the new code_region*)
    rewrite finz_seq_between_cons // /= in Hlen_lws_code.
    destruct lws_code as [|lws_code1 lws_code]; first done.
    simplify_eq.
    assert (length (lws_code1 :: lws_code) = length (finz.seq_between b_code e_code))
      as Hlen_lws_code' by (rewrite finz_seq_between_cons // ; cbn ; f_equal; done).
    assert
      (logical_range_map b_code e_code (lws_code1::lws_code) (v_code + 1) ⊆ lmem'')
      as Hmem''_code_next.
    {
      clear -Hvalid_update_code
               Hlen_lws_code Hlen_lws_data
               Hlen_lws_code'
               Hcode_apc_disjoint
               Hdata_apc_disjoint Hcode_data_disjoint
               Hb_code Hb_data.
      eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
      assert (v' = v_code+1 /\ (a' ∈ (finz.seq_between b_code e_code)))
        as [-> Ha'_in_be].
      {
        eapply logical_range_map_some_inv; eauto.
      }
      destruct Hvalid_update_code as (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated).
      eapply lookup_weaken; last eapply Hcompatibility.
      rewrite update_version_region_preserves_lmem_next; eauto.
      + eapply lookup_weaken;eauto.
        rewrite lookup_insert_ne; last (intro ; simplify_eq;done).
        rewrite lookup_union.
        replace (
            logical_region_map (finz.seq_between (b_data)%a e_data) (lws_data) v_data !! (a', v_code)
          ) with (None : option LWord).
        2:{ symmetry; apply logical_region_notin; auto.
            intro.
            rewrite elem_of_disjoint in Hcode_data_disjoint.
            apply (Hcode_data_disjoint a'); eauto.
        }
        rewrite option_union_right_id.
        rewrite (logical_region_map_lookup_versions _ _ _ v_code) in Hlw'; eauto.
      + rewrite lookup_insert_ne //=; last (intro ; set_solver).
        rewrite lookup_union.
        rewrite (logical_region_notin _ _ v_data); auto; cycle 1.
        {
          intro.
          eapply elem_of_disjoint; eauto.
        }
        rewrite option_union_right_id.
        eapply logical_range_version_neq; eauto; last lia.
    }
    assert
      (logical_range_map b_code e_code (LCap RW b_data e_data a_data (v_data + 1)::lws_code) (v_code + 1) ⊆ lmem')
      as Hmem'_code_next.
    {
      clear -Hvalid_update_code Hlen_lws_code Hlen_lws_data Hcode_apc_disjoint
               Hdata_apc_disjoint Hcode_data_disjoint
               Hb_code Hb_data Hmem''_code_next.
      subst lmem'.
      eapply insert_subseteq_r.
      { eapply logical_range_notin; auto.
        + rewrite finz_seq_between_cons //; cbn; f_equal; done.
        + clear -Hb_data Hb_code Hcode_data_disjoint.
          intro.
          rewrite elem_of_disjoint in Hcode_data_disjoint.
          apply (Hcode_data_disjoint b_data); eauto.
          rewrite elem_of_finz_seq_between; solve_addr.
      }
      rewrite -(logical_range_map_insert _ _ _ lws_code1); auto.
      by apply insert_mono.
    }
    assert ( logical_range_map b_code e_code (LCap RW b_data e_data a_data (v_data + 1)::lws_code) (v_code + 1) ⊆ lmem0 )
      as Hmem0_code_next.
    {
      subst lmem0.
      eapply delete_subseteq_r; last done.
      apply logical_range_notin; auto; done.
    }
    assert ( logical_range_map b_code e_code (LCap RW b_data e_data a_data (v_data + 1)::lws_code) (v_code + 1) ⊆ lmem1 )
      as Hmem1_code_next.
    {
      subst lmem1.
      eapply (delete_subseteq_list_r); eauto.
      apply logical_range_map_disjoint_version; auto.
      lia.
    }
    iDestruct (big_sepM_insert_difference with "Hmem") as "[Hcode Hmem]"
    ; first (eapply Hmem1_code_next).
    match goal with
    | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
        set (lmem2 := m)
    end.

    (* Derive pure predicates about the previous data_region*)
    assert ( logical_range_map b_data e_data (lws_data) v_data ⊆ lmem'' )
      as Hmem''_data.
    {
      eapply is_valid_updated_lmemory_lmem_incl
        with (la := (finz.seq_between b_data e_data))
             (v:= v_data)
      ; eauto.
      eapply is_valid_updated_lmemory_lmem_subset; last eassumption.
      eapply map_subseteq_trans; cycle 1.
      + eapply insert_subseteq.
        rewrite lookup_union.
        rewrite !logical_region_notin; auto.
      + eapply map_union_subseteq_r.
        apply logical_region_map_disjoint; auto.
    }
    assert ( logical_range_map b_data e_data (lws_data) v_data ⊆ lmem' )
      as Hmem'_data.
    {
      subst lmem'.
      eapply insert_subseteq_r.
      { eapply logical_range_version_neq; auto; lia. }
      eapply insert_subseteq_r.
      { eapply logical_range_notin; auto.
        clear -Hb_data Hb_code Hcode_data_disjoint.
        intro.
        rewrite elem_of_disjoint in Hcode_data_disjoint.
        apply (Hcode_data_disjoint b_code); eauto.
        rewrite elem_of_finz_seq_between; solve_addr.
      }
      done.
    }
    assert ( logical_range_map b_data e_data (lws_data) v_data ⊆ lmem0 )
      as Hmem0_data.
    {
      subst lmem0.
      eapply delete_subseteq_r; last done.
      apply logical_range_notin; auto; done.
    }
    assert ( logical_range_map b_data e_data (lws_data) v_data ⊆ lmem1 )
      as Hmem1_data.
    {
      subst lmem1.
      eapply (delete_subseteq_list_r); eauto.
      apply logical_range_map_disjoint; auto.
      set_solver+Hcode_data_disjoint.
    }
    assert ( logical_range_map b_data e_data (lws_data) v_data ⊆ lmem2 )
      as Hmem2_data.
    {
      subst lmem2.
      eapply (delete_subseteq_list_r); eauto.
      apply logical_range_map_disjoint; auto.
      set_solver+Hcode_data_disjoint.
    }
    iDestruct (big_sepM_insert_difference with "Hmem") as "[Hdata_prev Hmem]"
    ; first (eapply Hmem2_data).
    match goal with
    | _ : _ |- context [environments.Esnoc _ (INamed "Hmem") (big_opM _ _ ?m)] =>
        set (lmem3 := m)
    end.

    (* Derive pure predicates about the new data_region*)
    rewrite finz_seq_between_cons // /= in Hlen_lws_data.
    destruct lws_data as [|lws_data1 lws_data]; first done.
    simplify_eq.
    assert (length (lws_data1 :: lws_data) = length (finz.seq_between b_data e_data))
      as Hlen_lws_data' by (rewrite finz_seq_between_cons // ; cbn ; f_equal; done).
    assert
      (logical_range_map b_data e_data (lws_data1::lws_data) (v_data + 1) ⊆ lmem'')
      as Hmem''_data_next.
    {
      clear -Hvalid_update_data Hlen_lws_code Hlen_lws_data Hdata_apc_disjoint
               Hdata_apc_disjoint Hcode_data_disjoint
               Hb_code Hb_data.
      eapply map_subseteq_spec; intros [a' v'] lw' Hlw'.
      assert (v' = v_data+1 /\ (a' ∈ (finz.seq_between b_data e_data)))
        as [-> Ha'_in_be].
      {
        eapply logical_range_map_some_inv; eauto.
        rewrite finz_seq_between_cons //=.
      }
      destruct Hvalid_update_data as (Hcompatibility & Hgl_llmem & HmaxMem & Hupdated).
      eapply lookup_weaken; last eapply Hcompatibility.
      rewrite update_version_region_preserves_lmem_next; eauto.
      + eapply lookup_weaken;eauto.
        rewrite lookup_insert_ne; last (intro ; simplify_eq;done).
        rewrite lookup_union.
        replace (
            logical_region_map (finz.seq_between (b_code)%a e_code) (lws_code1 :: lws_code) v_code !! (a', v_data)
          ) with (None : option LWord).
        2:{ symmetry; apply logical_region_notin; auto.
            + rewrite finz_seq_between_cons //.
            + intro.
              rewrite elem_of_disjoint in Hcode_data_disjoint.
              apply (Hcode_data_disjoint a'); eauto.
        }
        rewrite option_union_left_id.
        rewrite (logical_region_map_lookup_versions _ _ _ v_data) in Hlw'; eauto.
        rewrite finz_seq_between_cons //.
      + rewrite lookup_insert_ne //=; last (intro ; set_solver).
        rewrite lookup_union.
        rewrite (logical_region_notin _ _ v_code); auto; cycle 1.
        { rewrite finz_seq_between_cons //. }
        { intro.
          eapply elem_of_disjoint; eauto.
        }
        rewrite option_union_left_id.
        eapply logical_range_version_neq; eauto; last lia.
        rewrite finz_seq_between_cons //=; cbn ; by f_equal.
    }
    assert
      (logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem')
      as Hmem'_data_next.
    {
      clear -Hvalid_update_data Hlen_lws_code Hlen_lws_data
               Hcode_apc_disjoint Hdata_apc_disjoint Hcode_data_disjoint
               Hb_code Hb_data Hmem''_data_next.
      subst lmem'.
      rewrite insert_commute.
      2:{ intro ; simplify_eq.
          clear -Hcode_data_disjoint Hb_code Hb_data.
          rewrite elem_of_disjoint in Hcode_data_disjoint.
          eapply (Hcode_data_disjoint b_code).
          all: apply elem_of_finz_seq_between; solve_addr.
      }
      eapply insert_subseteq_r.
      { eapply logical_range_notin; auto.
        + rewrite finz_seq_between_cons //; cbn; f_equal; done.
        + intro.
          rewrite elem_of_disjoint in Hcode_data_disjoint.
          apply (Hcode_data_disjoint b_code); eauto.
          rewrite elem_of_finz_seq_between; solve_addr.
      }
      rewrite -(logical_range_map_insert _ _ _ lws_data1); auto.
      by apply insert_mono.
    }
    assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem0 )
      as Hmem0_data_next.
    {
      subst lmem0.
      eapply delete_subseteq_r; last done.
      apply logical_range_notin; auto; done.
    }
    assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem1 )
      as Hmem1_data_next.
    {
      subst lmem1.
      eapply (delete_subseteq_list_r); eauto.
      apply logical_range_map_disjoint; auto.
      set_solver+Hcode_data_disjoint.
    }
    assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem2 )
      as Hmem2_data_next.
    {
      subst lmem2.
      eapply (delete_subseteq_list_r); eauto.
      apply logical_range_map_disjoint; auto.
      set_solver+Hcode_data_disjoint.
    }
    assert ( logical_range_map b_data e_data (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec::lws_data) (v_data + 1) ⊆ lmem3 )
      as Hmem3_data_next.
    {
      subst lmem3.
      eapply (delete_subseteq_list_r); eauto.
      apply logical_range_map_disjoint_version; auto.
      lia.
    }
    iDestruct (big_sepM_insert_difference with "Hmem") as "[Hdata Hmem]"
    ; first (eapply Hmem3_data_next).
    iClear "Hmem".
    clear
      Hmem''_data_next Hmem'_data_next Hmem0_data_next Hmem1_data_next Hmem2_data_next Hmem3_data_next lmem3
        Hmem''_data Hmem'_data Hmem0_data Hmem1_data Hmem2_data lmem2
        Hmem''_code_next Hmem'_code_next Hmem0_code_next Hmem1_code_next lmem1
        Hmem''_code Hmem'_code Hmem0_code lmem0
        Hmem''_pca Hmem'_pca lmem'
    .
    clear Hvalid_update_code Hvalid_update_data
      Hunique_regs_data Hunique_regs_code.

    (* Close the data invariant *)
    iDestruct "HPs_data" as "#HPs_data".
    iDestruct "Hreadcond_Ps_data" as "#Hreadcond_Ps_data".
    iMod ("Hcls_data" with "[Hdata_prev HPs_data Hreadcond_Ps_data]") as "_"; [|iModIntro].
    {
      iNext.
      iApply region_inv_construct; auto.
    }
    iDestruct ( big_sepM_to_big_sepL2 with "Hdata" ) as "Hdata".
    { apply logical_region_NoDup, finz_seq_between_NoDup. }
    { rewrite logical_region_length; auto. }

    (* Close the code invariant *)
    iDestruct "HPs_code" as "#HPs_code".
    iDestruct "Hreadcond_Ps_code" as "#Hreadcond_Ps_code".
    iMod ("Hcls_code" with "[Hcode_prev HPs_code Hreadcond_Ps_code]") as "_"; [|iModIntro].
    {
      iNext.
      iApply region_inv_construct; auto.
    }
    iDestruct ( big_sepM_to_big_sepL2 with "Hcode" ) as "Hcode".
    { apply logical_region_NoDup, finz_seq_between_NoDup. }
    { rewrite logical_region_length; auto. }

    (* The next PC is safe-to-share *)
    iAssert (interp (LCap p_pc' b_pc' e_pc' x v_pc')) as "Hinterp_next_PC".
    { iApply interp_weakening_next_PC; eauto. }

    (* Two cases:
       - either the identity corresponds to one of the enclaves of interest,
       in which case we get the seal_pred from the custom map,
       and we get safe-to-share of the sentry by the contract invariant
       - or it is not an enclave of interest,
       in which case we can allocate the interp as seal predicate
     *)
    destruct (custom_enclaves !! I_ECn) as
      [ [Hcus_enclave_code Hcus_enclave_addr Hcus_enclave_enc Hcus_enclave_sign] |] eqn:HI_ECn.
    - (* CASE WHERE THE IDENTITY IS A KNOWN ENCLAVE *)
      set ( new_enclave := {| code := Hcus_enclave_code; code_region := Hcus_enclave_addr; Penc := Hcus_enclave_enc; Psign := Hcus_enclave_sign |} ).

      (* We allocate the seal predicate with the predicate given by the custom map *)
      iMod (seal_store_update_alloc _ Hcus_enclave_enc with "Hfree_ot_ec_0") as "#Hseal_pred_enc".
      iMod (seal_store_update_alloc _ Hcus_enclave_sign with "Hfree_ot_ec_1") as "#Hseal_pred_sign".
      iAssert ( custom_enclave_contract_gen ) as "Hcontract'" ; eauto.
      iSpecialize ("Hcontract'" $!
                     mask_sys I_ECn
                     b_code e_code (v_code+1)
                     b_data e_data a_data (v_data+1)
                     lws_data ot_ec new_enclave).
      pose proof custom_enclaves_wf as [Hwf_map Hwf_map_z].

      assert (I_ECn = hash_concat (hash Hcus_enclave_addr) (hash Hcus_enclave_code)) as
        HI_ECn_eq.
      {
        clear -Hwf_map HI_ECn new_enclave.
        opose proof (map_Forall_lookup_1 _ custom_enclaves I_ECn new_enclave) as H.
        apply H in Hwf_map; eauto; cbn in *.
      }

      apply hash_lmemory_range_correct with (lws:= lws_code) in Hhash_instrs as ->; auto; cycle 1.
      { apply insert_subseteq_r.
        + apply logical_range_notin; eauto.
          clear -Hcode_apc_disjoint Hb_code.
          apply not_elem_of_finz_seq_between in Hcode_apc_disjoint.
          apply not_elem_of_finz_seq_between.
          solve_addr.
        + rewrite finz_seq_between_cons //.
          apply map_subseteq_trans with
            (m2 := logical_region_map (b_code :: finz.seq_between (b_code ^+ 1)%a e_code) (lws_code1 :: lws_code) v_code)
          ; last eapply map_union_subseteq_l.
          rewrite /logical_range_map /logical_region_map /=.
          apply insert_subseteq_r; last done.
          rewrite -/(logical_range_map (b_code ^+ 1)%a e_code lws_code v_code).
          apply logical_range_notin; auto.
          apply not_elem_of_finz_seq_between; solve_addr.
      }

      (* We apply the contract to get that the sentry to the enclave is safe-to-share *)
      iMod ("Hcontract'" with
             "[] [] [] [] [] [$Hseal_pred_enc $Hseal_pred_sign Hcode Hdata]")
        as "#Hinterp_enclave"
      ; eauto.
      {
        iPureIntro.
        clear -HI_ECn_eq.
        subst I_ECn.
        apply hash_concat_inj' in HI_ECn_eq.
        destruct HI_ECn_eq as [-> ?]; simplify_eq.
        done.
      }
      {
        iPureIntro.
        clear -HI_ECn_eq.
        subst I_ECn.
        apply hash_concat_inj' in HI_ECn_eq.
        destruct HI_ECn_eq as [-> ?]; simplify_eq.
        done.
      }
      {
        iPureIntro.
        clear -HI_ECn_eq Hlen_lws_code Hb_code.
        subst I_ECn.
        apply hash_concat_inj' in HI_ECn_eq.
        destruct HI_ECn_eq as [-> ?]; simplify_eq.
        cbn.
        rewrite map_length.
        cbn in * ; simplify_eq.
        rewrite Hlen_lws_code.
        rewrite finz_seq_between_length.
        pose proof (finz_incr_iff_dist Hcus_enclave_addr e_code
                      (finz.dist Hcus_enclave_addr e_code))
          as [_ ?].
        replace
          (Hcus_enclave_addr + (finz.dist Hcus_enclave_addr e_code + 1))%a
          with (Hcus_enclave_addr + (finz.dist Hcus_enclave_addr e_code + 1)%nat)%a; last solve_addr.
        rewrite Z.add_1_r.
        replace (Hcus_enclave_addr + Z.succ (finz.dist (Hcus_enclave_addr ^+ 1)%a e_code))%a
          with (Hcus_enclave_addr + (S (finz.dist (Hcus_enclave_addr ^+ 1)%a e_code)))%a
        ; last solve_addr.
        rewrite -finz_dist_S; last solve_addr.
        apply H; solve_addr.
      }
      {
        replace ((λ w : Word, word_to_lword w (v_code + 1)) <$> code new_enclave) with lws_code
        ; first iFrame "∗#".
        subst I_ECn.
        apply hash_concat_inj' in HI_ECn_eq.
        destruct HI_ECn_eq as [-> ?]; simplify_eq.
        rewrite -list_fmap_compose.
        rewrite (Forall_fmap_ext_1 _ id); first by rewrite list_fmap_id.
        rewrite Forall_forall.
        intros w Hw; cbn.
        apply word_to_lword_get_word_int.
        apply map_Forall_insert_1_2 in Hcode_z.
        2: {
          rewrite lookup_union union_None.
          split; apply logical_region_notin; auto.
        }
        apply map_Forall_union in Hcode_z.
        2: { apply logical_region_map_disjoint; auto. }
          destruct Hcode_z as [Hcode_z _].
        cbn in Hcode_z.
        rewrite (finz_seq_between_cons Hcus_enclave_addr) // in Hcode_z.
        rewrite logical_region_map_cons in Hcode_z.
        apply map_Forall_insert_1_2 in Hcode_z.
        2: { apply logical_region_notin; auto.
             apply not_elem_of_finz_seq_between; solve_addr.
        }
        eapply (map_Forall_all_P _ _ lws_code); eauto.
      }

      (* We can close the system invariant *)
      iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_"; [|iModIntro].
      { iNext.
        iExists (Ecn +1), (ot_ec ^+ 2)%ot.
        replace ((ot_ec ^+1) ^+1)%ot with (ot_ec ^+ 2)%ot by solve_addr + Hot.
        iFrame.
        iSplitR.
        { iPureIntro; solve_addr. }
        iSplitL "Halloc".
        { rewrite (finz_seq_between_split _ ot_ec (ot_ec ^+ 2)%ot); last solve_addr + Hot.
          assert ( ot_ec ≠ (ot_ec ^+ 1)%f ) as Hot_ec1 by solve_addr.
          rewrite list_to_set_app_L.
          rewrite big_sepS_union.
          2: {
            apply list_to_set_disj.
            clear -Hot.
            rewrite elem_of_disjoint.
            intros o Ho Ho'.
            rewrite !elem_of_finz_seq_between in Ho, Ho'.
            solve_finz.
          }
          iFrame.
          rewrite (finz_seq_between_cons ot_ec); last solve_addr + Hot.
          rewrite (finz_seq_between_cons (ot_ec ^+ 1)%ot); last solve_addr + Hot.
          rewrite (finz_seq_between_empty ((ot_ec ^+ 1) ^+ 1)%ot); last solve_addr + Hot.
          rewrite !list_to_set_cons list_to_set_nil.
          rewrite big_sepS_union;last set_solver+Hot_ec1.
          rewrite big_sepS_union; last set_solver+.
          rewrite big_sepS_empty.
          rewrite !big_sepS_singleton.
          iSplit; [|iSplit]; try (iExists _ ;iFrame "#"); done.
        }
        iModIntro.
        iIntros (I tid_I ot_I ce_I) "%Htid_I (Henclave_I & %Hcustom_I & %Hhas_seal_I)".
        destruct (decide (tid_I = Ecn)) as [-> |Htid_I_ECn].
        { (* if tid_I = ECn, then it should be the predicate that had just been initialised *)
          assert (ot_ec = if Z.even ot_I then ot_I else (ot_I ^+ -1)%ot) as Hot'.
          { rewrite /has_seal in Hhas_seal_I.
            destruct (finz.of_z ot_I) eqn:Hot_I ; cbn in Hhas_seal_I; try done.
            apply finz_of_z_is_Some_spec in Hot_I.
            rewrite /tid_of_otype in Hhas_seal_I.
            destruct ( Z.even ot_I ) eqn:Hot_I_even.
            + assert (Z.even f = true) as Hf_even by (by rewrite Hot_I).
              rewrite Hf_even in Hhas_seal_I.
              assert (Ecn = (Z.to_nat f `div` 2)) as HEcn_eq by (by injection Hhas_seal_I).
              clear Hhas_seal_I.
              rewrite HEcn_eq in Hot_ec.
              clear -Hot_ec Hot_I Hf_even.
              assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat f) 2)) = (Z.to_nat f) ).
              {
                rewrite -(Nat2Z.inj_mul 2).
                rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                2:{
                  destruct f.
                  rewrite /Z.even in Hf_even.
                  cbn in *.
                  destruct z; cbn in *.
                  + rewrite Z2Nat.inj_0.
                    apply PeanoNat.Nat.divide_0_r.
                  + rewrite Z2Nat.inj_pos.
                    destruct p; cbn in * ; try done.
                    rewrite Pos2Nat.inj_xO.
                    apply Nat.divide_factor_l.
                  + rewrite Z2Nat.inj_neg.
                    apply PeanoNat.Nat.divide_0_r.
                }
                rewrite PeanoNat.Nat.mul_comm.
                rewrite (PeanoNat.Nat.div_mul (Z.to_nat f) 2); done.
              }
              solve_addr.
            + assert (Z.even f = false) as Hf_even by (by rewrite Hot_I).
              rewrite Hf_even in Hhas_seal_I.
              assert (Ecn = (Z.to_nat (f ^- 1)%f `div` 2) ) as HEcn_eq by (by injection Hhas_seal_I).
              clear Hhas_seal_I.
              rewrite HEcn_eq in Hot_ec.
              clear -Hot_ec Hot_I Hf_even.
              assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat (f ^- 1)%f) 2)) = (Z.to_nat (f ^- 1)%f) ).
              {
                rewrite -(Nat2Z.inj_mul 2).
                rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                2:{
                  destruct f.
                  rewrite /Z.even in Hf_even.
                  cbn in *.
                  destruct z; cbn in *; try done.
                  destruct p; cbn in * ; try done.
                  + remember (finz.FinZ (Z.pos p~1) finz_lt finz_nonneg) as p1.
                    destruct (p1 ^- 1)%f eqn:HP1.
                    assert (z = Z.pos p~0).
                    { solve_finz. }
                    assert (  (((Z.pos p~0) <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                    assert (  ((0 <=? (Z.pos p~0))%Z) = true ) as finz_nonneg2 by solve_finz.
                    replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                      (finz.FinZ (Z.pos p~0) finz_lt2 finz_nonneg2) by solve_finz.
                    cbn.
                    rewrite Z2Nat.inj_pos.
                    rewrite Pos2Nat.inj_xO.
                    apply Nat.divide_factor_l.
                  + remember (finz.FinZ 1 finz_lt finz_nonneg) as p1.
                    destruct (p1 ^- 1)%f eqn:HP1.
                    assert (z = 0).
                    { solve_finz. }
                    assert (  ((0 <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                    assert (  ((0 <=? 0)%Z) = true ) as finz_nonneg2 by solve_finz.
                    replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                      (finz.FinZ 0 finz_lt2 finz_nonneg2) by solve_finz.
                    cbn.
                    rewrite Z2Nat.inj_0.
                    apply PeanoNat.Nat.divide_0_r.
                }
                rewrite PeanoNat.Nat.mul_comm.
                rewrite (PeanoNat.Nat.div_mul (Z.to_nat (f ^- 1)%f) 2); done.
              }
              rewrite H in Hot_ec.
              solve_addr.
          }
          iDestruct (enclave_all_agree _ I_ECn I with "[$Henclave_all $Henclave_I]") as "->".
          rewrite Hcustom_I in HI_ECn ; simplify_eq.
          destruct (Z.even ot_I); cbn in *; iFrame "#".
          replace (((ot_I ^+ -1) ^+ 1)%f) with ot_I by solve_finz.
          iFrame "#".
        }
        { (* tid_I ≠ Ecn*)
          assert (0 <= tid_I < Ecn) as Htid_I' by lia.
          iApply ("Hcustom_inv" with "[] [$Henclave_I]"); eauto.
        }
      }

      (* We can close the pc_a invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists lw_pc;iFrame|iModIntro].
      rewrite (insert_commute _ rcode PC) // (insert_commute _ rdata PC) // insert_insert.
      iClear "Hcontract'".

      (* We finish by using the FTLR *)
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply ("IH" $! (<[rdata:=LInt 0]> (<[rcode:=LCap E b_code e_code (b_code ^+ 1)%a (v_code + 1)]> lregs)) with "[%] [] [Hregs] [$Hown]"); eauto.
      { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
      {
        iIntros (ri ? Hri Hvs).
        destruct (decide (ri = rdata)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
        destruct (decide (ri = rcode)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
        iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
      }

    - (* CASE WHERE THE IDENTITY IS NOT A KNOWN ENCLAVE *)
      (* We allocate the seal predicate with interp *)
      iMod (seal_store_update_alloc _ interp with "Hfree_ot_ec_0") as "#Hseal_pred_enc".
      iMod (seal_store_update_alloc _ interp with "Hfree_ot_ec_1") as "#Hseal_pred_sign".

      (* We can close the system invariant *)
      iMod ("Hcls_sys" with "[ HEC Hfree Halloc]") as "_".
      { iNext.
        iExists (Ecn +1), (ot_ec ^+2)%ot.
        replace ((ot_ec ^+1) ^+1)%ot with (ot_ec ^+2)%ot by solve_addr + Hot.
        iFrame.
        iSplitR.
        { iPureIntro; solve_addr. }
        iSplitL "Halloc".
        { rewrite (finz_seq_between_split _ ot_ec (ot_ec ^+2)%ot); last solve_addr + Hot.
          assert ( ot_ec ≠ (ot_ec ^+ 1)%f ) as Hot_ec1 by solve_addr.
          rewrite list_to_set_app_L.
          rewrite big_sepS_union.
          2: {
            apply list_to_set_disj.
            clear -Hot.
            rewrite elem_of_disjoint.
            intros o Ho Ho'.
            rewrite !elem_of_finz_seq_between in Ho, Ho'.
            solve_finz.
          }
          iFrame.
          rewrite (finz_seq_between_cons ot_ec); last solve_addr + Hot.
          rewrite (finz_seq_between_cons (ot_ec ^+ 1)%ot); last solve_addr + Hot.
          rewrite (finz_seq_between_empty ((ot_ec ^+ 1) ^+ 1)%ot); last solve_addr + Hot.
          rewrite !list_to_set_cons list_to_set_nil.
          rewrite big_sepS_union; last set_solver + Hot_ec1.
          rewrite big_sepS_union; last set_solver +.
          rewrite big_sepS_empty.
          rewrite !big_sepS_singleton.
          iSplit; [|iSplit]; try (iExists _ ;iFrame "#"); done.
        }
        iModIntro.
        iIntros (I tid_I ot_I ce_I) "%Htid_I (Henclave_I & %Hcustom_I & %Hhas_seal_I)".
        destruct (decide (tid_I = Ecn)) as [-> |Htid_I_ECn].
        { (* if tid_I = ECn, then it should be the predicate that had just been initialised *)
          assert (ot_ec = if Z.even ot_I then ot_I else (ot_I ^+ -1)%ot) as Hot'.
          { rewrite /has_seal in Hhas_seal_I.
            destruct (finz.of_z ot_I) eqn:Hot_I ; cbn in Hhas_seal_I; try done.
            apply finz_of_z_is_Some_spec in Hot_I.
            rewrite /tid_of_otype in Hhas_seal_I.
            destruct ( Z.even ot_I ) eqn:Hot_I_even.
            + assert (Z.even f = true) as Hf_even by (by rewrite Hot_I).
              rewrite Hf_even in Hhas_seal_I.
              assert (Ecn = (Z.to_nat f `div` 2)) as HEcn_eq by (by injection Hhas_seal_I).
              clear Hhas_seal_I.
              rewrite HEcn_eq in Hot_ec.
              clear -Hot_ec Hot_I Hf_even.
              assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat f) 2)) = (Z.to_nat f) ).
              {
                rewrite -(Nat2Z.inj_mul 2).
                rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                2:{
                  destruct f.
                  rewrite /Z.even in Hf_even.
                  cbn in *.
                  destruct z; cbn in *.
                  + rewrite Z2Nat.inj_0.
                    apply PeanoNat.Nat.divide_0_r.
                  + rewrite Z2Nat.inj_pos.
                    destruct p; cbn in * ; try done.
                    rewrite Pos2Nat.inj_xO.
                    apply Nat.divide_factor_l.
                  + rewrite Z2Nat.inj_neg.
                    apply PeanoNat.Nat.divide_0_r.
                }
                rewrite PeanoNat.Nat.mul_comm.
                rewrite (PeanoNat.Nat.div_mul (Z.to_nat f) 2); done.
              }
              solve_addr.
            + assert (Z.even f = false) as Hf_even by (by rewrite Hot_I).
              rewrite Hf_even in Hhas_seal_I.
              assert (Ecn = (Z.to_nat (f ^- 1)%f `div` 2) ) as HEcn_eq by (by injection Hhas_seal_I).
              clear Hhas_seal_I.
              rewrite HEcn_eq in Hot_ec.
              clear -Hot_ec Hot_I Hf_even.
              assert ( (Z.mul 2 (PeanoNat.Nat.div (Z.to_nat (f ^- 1)%f) 2)) = (Z.to_nat (f ^- 1)%f) ).
              {
                rewrite -(Nat2Z.inj_mul 2).
                rewrite -PeanoNat.Nat.Lcm0.divide_div_mul_exact.
                2:{
                  destruct f.
                  rewrite /Z.even in Hf_even.
                  cbn in *.
                  destruct z; cbn in *; try done.
                  destruct p; cbn in * ; try done.
                  + remember (finz.FinZ (Z.pos p~1) finz_lt finz_nonneg) as p1.
                    destruct (p1 ^- 1)%f eqn:HP1.
                    assert (z = Z.pos p~0).
                    { solve_finz. }
                    assert (  (((Z.pos p~0) <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                    assert (  ((0 <=? (Z.pos p~0))%Z) = true ) as finz_nonneg2 by solve_finz.
                    replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                      (finz.FinZ (Z.pos p~0) finz_lt2 finz_nonneg2) by solve_finz.
                    cbn.
                    rewrite Z2Nat.inj_pos.
                    rewrite Pos2Nat.inj_xO.
                    apply Nat.divide_factor_l.
                  + remember (finz.FinZ 1 finz_lt finz_nonneg) as p1.
                    destruct (p1 ^- 1)%f eqn:HP1.
                    assert (z = 0).
                    { solve_finz. }
                    assert (  ((0 <? ONum)%Z) = true ) as finz_lt2 by solve_finz.
                    assert (  ((0 <=? 0)%Z) = true ) as finz_nonneg2 by solve_finz.
                    replace (finz.FinZ z finz_lt0 finz_nonneg0) with
                      (finz.FinZ 0 finz_lt2 finz_nonneg2) by solve_finz.
                    cbn.
                    rewrite Z2Nat.inj_0.
                    apply PeanoNat.Nat.divide_0_r.
                }
                rewrite PeanoNat.Nat.mul_comm.
                rewrite (PeanoNat.Nat.div_mul (Z.to_nat (f ^- 1)%f) 2); done.
              }
              rewrite H in Hot_ec.
              solve_addr.
          }
          iDestruct (enclave_all_agree _ I_ECn I with "[$Henclave_all $Henclave_I]") as "->".
          rewrite Hcustom_I in HI_ECn ; simplify_eq.
        }
        { (* tid_I ≠ Ecn*)
          assert (0 <= tid_I < Ecn) as Htid_I' by lia.
          iApply ("Hcustom_inv" with "[] [$Henclave_I]"); eauto.
        }
      }
      iModIntro.

      (* We can close the pc_a invariant *)
      iMod ("Hcls" with "[Ha HP]") as "_";[iExists lw_pc;iFrame|iModIntro].

      (* To show that the sentry capability to enclave is safe-to-share,
         we first need to show that the new sealing capability is safe-to-share,
         which it is because the seal predicates are both interp *)
      iMod (inv_alloc (attestN.@Ecn) _ ((∃ I : EIdentity, enclave_cur Ecn I) ∨ enclave_prev Ecn) with "[Henclave_live]")
        as "#Hattest".
      { by iNext; iLeft; iExists I_ECn. }
      iAssert (interp (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec)) as "Hinterp_seal".
      { iEval (rewrite fixpoint_interp1_eq /=).
        assert (ot_ec < ot_ec ^+ 2)%ot as Hot' by solve_finz.
        assert (ot_ec ^+ 1 < ot_ec ^+ 2)%ot as Hot'' by solve_finz.
        assert (ot_ec ^+ 2 <= ot_ec ^+ 2)%ot as Hot''' by solve_finz.
        iSplit;[|iSplit].
        + rewrite /safe_to_seal.
          iEval (rewrite finz_seq_between_cons //).
          iEval (rewrite finz_seq_between_cons //).
          replace ((ot_ec ^+ 1) ^+ 1)%f with (ot_ec ^+ 2)%ot by solve_finz.
          iEval (rewrite finz_seq_between_empty //).
          rewrite 2!big_sepL_cons big_sepL_nil.
          iSplit; [|iSplit]; last done; iExists interp; iFrame "#";auto; iSplit.
          * iPureIntro; intros w; apply interp_persistent.
          * rewrite /write_cond /=; iNext ; iModIntro; iIntros (w) "$".
          * iPureIntro; intros w; apply interp_persistent.
          * rewrite /write_cond /=; iNext ; iModIntro; iIntros (w) "$".
        + rewrite /safe_to_unseal.
          iEval (rewrite finz_seq_between_cons //).
          iEval (rewrite finz_seq_between_cons //).
          replace ((ot_ec ^+ 1) ^+ 1)%f with (ot_ec ^+ 2)%ot by solve_finz.
          iEval (rewrite finz_seq_between_empty //).
          rewrite 2!big_sepL_cons big_sepL_nil.
          iSplit; [|iSplit]; last done; iExists interp; iFrame "#";auto.
          * rewrite /read_cond /=; iNext ; iModIntro; iIntros (w) "$".
          * rewrite /read_cond /=; iNext ; iModIntro; iIntros (w) "$".
        + rewrite /safe_to_attest.
          iEval (rewrite finz_seq_between_cons //).
          iEval (rewrite finz_seq_between_cons //).
          replace ((ot_ec ^+ 1) ^+ 1)%f with (ot_ec ^+ 2)%ot by solve_finz.
          iEval (rewrite finz_seq_between_empty //).
          rewrite 2!big_sepL_cons big_sepL_nil.
          iSplit; [|iSplit]; last done; iExists Ecn; iFrame "#"; iPureIntro; auto.
          rewrite /tid_of_otype in Htidx |- *.
          rewrite Htidx_even in Htidx.
          assert (Z.even (ot_ec ^+ 1)%f = false) as Heven'.
          { clear -Hot Htidx_even.
            rewrite Zeven.Zeven_odd_bool negb_false_iff.
            replace (finz.to_z (ot_ec ^+ 1)%f) with (Z.succ ot_ec) by solve_addr.
            by rewrite -Z.odd_succ in Htidx_even.
          }
          rewrite Heven'.
          by replace ( (ot_ec ^+ 1 ^- 1)%f ) with ot_ec by solve_finz.
      }

      (* We then need to show that the data capability is safe-to-share,
         which it is because the sealing cap is safe (shown above),
         and all the rest also is safe (known from hypothesis that cap comes from a register)
       *)
      iMod (region_valid_alloc _ RW b_data e_data a_data (v_data + 1)
              (LSealRange (true, true) ot_ec (ot_ec ^+ 2)%f ot_ec :: lws_data) with
             "[HPs_data] [$Hdata]")
        as "#Hinterp_data_new".
      { done. }
      { done. }
      { rewrite big_sepL_cons; iFrame "#".
        destruct Ps_data as [|Ps_data1 Ps_data]; first done.
        iEval (rewrite big_sepL_cons) in "Hreadcond_Ps_data".
        iDestruct "Hreadcond_Ps_data" as "[_ Hreadcond_Ps_data]".
        iEval (rewrite big_sepL2_cons) in "HPs_data".
        iDestruct "HPs_data" as "[_ HPs_data]".
        iApply ( list_readcond_interp with "[$HPs_data] [$Hreadcond_Ps_data]"); auto.
        clear -Hlen_Ps_data Hlen_lws_data Hb_data.
        rewrite finz_seq_between_cons // in Hlen_Ps_data; simplify_eq.
        cbn in * ; simplify_eq.
        by rewrite -Hlen_Ps_data Hlen_lws_data.
      }

      (* We then need to show that the code capability is safe-to-share,
         which it is because the data cap is safe (shown above),
         and all the rest also is safe (known from hypothesis that cap comes from a register)
       *)
      iMod (region_valid_alloc _ RX b_code e_code a_code (v_code + 1)
              (LCap RW b_data e_data a_data (v_data + 1) :: lws_code) with
             "[HPs_code] [$Hcode]")
        as "#Hinterp_code_new".
      { done. }
      { done. }
      { rewrite big_sepL_cons; iFrame "#".
        destruct Ps_code as [|Ps_code1 Ps_code]; first done.
        iEval (rewrite big_sepL_cons) in "Hreadcond_Ps_code".
        iDestruct "Hreadcond_Ps_code" as "[_ Hreadcond_Ps_code]".
        iEval (rewrite big_sepL2_cons) in "HPs_code".
        iDestruct "HPs_code" as "[_ HPs_code]".
        iApply ( list_readcond_interp with "[$HPs_code] [$Hreadcond_Ps_code]"); auto.
        clear -Hlen_Ps_code Hlen_lws_code Hb_code.
        rewrite finz_seq_between_cons // in Hlen_Ps_code; simplify_eq.
        cbn in * ; simplify_eq.
        by rewrite -Hlen_Ps_code Hlen_lws_code.
      }

      (* We can now conclude that the sentry to enclave is safe,
         because all its content is safe-to-share for RX,
         which we can weaken to E *)
      iAssert (interp (LCap E b_code e_code (b_code ^+ 1)%a (v_code + 1))) as
        "Hinterp_entry_enclave".
      { iApply (interp_weakening with "IH Hinterp_code_new"); eauto; solve_addr. }

      (* Finally, we can use the FTLR to conclude *)
      rewrite (insert_commute _ rcode PC) // (insert_commute _ rdata PC) // insert_insert.
      iApply wp_pure_step_later; auto.
      iNext; iIntros "H£'".
      iApply ("IH" $! (<[rdata:=LInt 0]> (<[rcode:=LCap E b_code e_code (b_code ^+ 1)%a (v_code + 1)]> lregs)) with "[%] [] [Hregs] [$Hown]"); eauto.
      { intro; by repeat (rewrite lookup_insert_is_Some'; right). }
      {
        iIntros (ri ? Hri Hvs).
        destruct (decide (ri = rdata)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
        destruct (decide (ri = rcode)); simplify_map_eq; first by rewrite !fixpoint_interp1_eq.
        iDestruct ("Hreg" $! ri _ Hri Hvs) as "Hinterp_dst"; eauto.
      }
  Qed.

End fundamental.
