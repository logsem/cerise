From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental.
From cap_machine.examples Require Import template_adequacy.
(* From cap_machine.examples Require Import template_adequacy macros_new. *)
From cap_machine Require Import proofmode.
From cap_machine.proofmode Require Export mkregion_helpers disjoint_regions_tactics.
Open Scope Z_scope.

Section counter.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} {sealg:sealStoreG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition N : namespace := nroot .@ "mincounter".

  (* In this example, we avoid computing offsets by hand, and instead define the
     code in two steps, computing the labels automatically (mimicking the steps
     a proper assembler would do). *)

  Definition counter_init0 (init code data secret: Z) : list Word :=
    (* init: *)
    encodeInstrsW [
        (* ; 1. store the code capability *)
        Mov r_t1 PC;
        Lea r_t1 (code-init)%Z;
        Store idc r_t1;

        (* ; 2. store the data capability *)
        Mov r_t1 idc;
        Lea r_t1 (secret-data);
        Lea idc 1;
        Store idc r_t1;

        (* ; 3. prepare the IE *)
        Lea idc (-1)%Z;
        Restrict idc (encodePerm IE);

        (* ; 4. jump to unknown code *)
        Mov r_t1 0;
        Jmp r_t31
      ].
  Definition counter_code : list Word :=
    (* code: *)
    encodeInstrsW [
        Load r_t1 idc;
        Add r_t1 r_t1 1;
        Store idc r_t1;
        Mov idc 0;
        Jmp r_t31
      ]
    (* end: *).

  Definition counter_data : list Word :=
    (* data: *)
    map WInt [
        7777 (* placeholder code cap *);
        7777 (* placeholder data cap *);
        (* secret: *)
        0 (* current value of the counter *)]
    (* data_end: *).

  Definition code_off := Eval compute in length (counter_init0 0 0 0 0).
  Definition end_off := Eval compute in (length counter_code).
  Definition secret_off := Eval compute in (length counter_data) - 1.
  Definition data_end_off := Eval compute in (length counter_data).

  Definition counter_init (init data: Z) : list Word :=
    counter_init0 init (init + code_off) data (data + secret_off).

  (* Specification for the init routine *)

  Local Ltac solve_addr' :=
    repeat match goal with x := _ |- _ => subst x end;
    unfold code_off, secret_off, end_off, data_end_off in *; solve_addr.

  Lemma counter_init_spec (a_init a_data: Addr) wadv w1 wdat0 wdat1 φ :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in
    let a_secret := (a_data ^+ secret_off)%a in
    let a_data_end := (a_data ^+ data_end_off)%a in

    ContiguousRegion a_init (code_off + end_off) →
    ContiguousRegion a_data (data_end_off) →

    ## [
        finz.seq_between a_init a_end;
        finz.seq_between a_data a_data_end
    ] ->

   ⊢ (( PC ↦ᵣ WCap RX a_init a_end a_init
      ∗ idc ↦ᵣ WCap RW a_data a_data_end a_data
      ∗ r_t1 ↦ᵣ w1
      ∗ r_t31 ↦ᵣ wadv
      ∗ a_data ↦ₐ wdat0
      ∗ (a_data ^+1)%a ↦ₐ wdat1
      (* ∗ (a_data ^+2)%a ↦ₐ wdat2 *)
      ∗ codefrag a_init (counter_init a_init a_data)
      ∗ ▷ (  PC ↦ᵣ WCap RX a_init a_end (a_code ^+ (-1))%a
           ∗ idc ↦ᵣ WCap IE a_data a_data_end a_data
           ∗ r_t1 ↦ᵣ WInt 0
           ∗ r_t31 ↦ᵣ wadv
           ∗ a_data ↦ₐ WCap RX a_init a_end a_code
           ∗ (a_data ^+1)%a ↦ₐ WCap RW a_data a_data_end a_secret
           (* ∗ (a_data ^+2)%a ↦ₐ WCap RWX a_init a_end (a_data ^+ 1)%a *)
           ∗ codefrag a_init (counter_init a_init a_data)
           -∗ WP Seq (Instr Executable) {{ φ }}))
      -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros a_code a_end a_secret a_data_end.
    iIntros (Hcont_code Hcont_data Hdis)
      "(HPC & Hidc & Hr1 & Hr31 & Hdat0 & Hdat1 & Hprog & Hφ)".
    iGo "Hprog".
    { transitivity (Some a_code); auto. solve_addr'. }
    iGo "Hprog".
    { transitivity (Some a_secret); auto. solve_addr'. }
    iGo "Hprog".
    { transitivity (Some a_data); auto. solve_addr'. }
    iGo "Hprog"; rewrite decode_encode_perm_inv //.
    iInstr "Hprog". (* stop before the jump *)
    iApply "Hφ". iFrame.
    replace (a_init ^+ 10)%a with (a_code ^+ -1)%a; solve_addr'.
  Qed.

  Lemma counter_code_spec (a_init a_data: Addr) wcont w1 φ :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in
    let a_secret := (a_data ^+ secret_off)%a in
    let a_data_end := (a_data ^+ data_end_off)%a in

    ContiguousRegion a_init (code_off + end_off) →
    ContiguousRegion a_data (data_end_off) →

    ## [
        finz.seq_between a_init a_end;
        finz.seq_between a_data a_data_end
    ] ->

  ⊢ (( inv with_adv.invN (∃ n, a_secret ↦ₐ WInt n ∗ ⌜0 ≤ n⌝)
     ∗ na_inv logrel_nais (N.@"code") (codefrag a_code counter_code)
     ∗ PC ↦ᵣ WCap RX a_init a_end a_code
     ∗ idc ↦ᵣ WCap RW a_data a_data_end a_secret
     ∗ r_t1 ↦ᵣ w1
     ∗ r_t31 ↦ᵣ wcont
     ∗ na_own logrel_nais ⊤
     ∗ ▷ (∀ (n: Z),
         PC ↦ᵣ WCap RX a_init a_end (a_end ^+ (-1))%a
           ∗ idc ↦ᵣ WInt 0
           ∗ r_t1 ↦ᵣ WInt n
           ∗ r_t31 ↦ᵣ wcont
           ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{ φ }}))
     -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros a_code a_end a_secret a_data_end.
    iIntros (Hcont_code Hcont_data Hdis)
      "(#HIv & #HIcode & HPC & Hidc & Hr1 & Hr31 & Hna & Hφ)".
    assert (Ha_code: a_code = (a_init ^+ code_off)%a) by done.
    clearbody a_code.
    (* open the invariant containing the code *)
    iMod (na_inv_acc logrel_nais with "HIcode Hna") as "(>Hcode & Hna & Hclose_code)".
    done. done.
    codefrag_facts "Hcode".

    (* load from a_data+1 *)
    wp_instr.
    iMod (inv_acc with "HIv") as "[>Hv Hclose]"; auto.
    iDestruct "Hv" as (n) "(Hn & %Hn)".
    iInstr "Hcode".
    { split; try solve_addr'. }
    { split ; solve_pure. }
    iMod ("Hclose" with "[Hn]") as "_". { iNext. iExists _. by iFrame. }
    iModIntro. wp_pure.
    (* add *)
    iInstr "Hcode".
    { split; try solve_addr'. }

    (* store to a_data+1 *)
    wp_instr.
    iMod (inv_acc with "HIv") as "[>Hv Hclose]"; auto.
    iDestruct "Hv" as (n') "(Hn' & %Hn')".
    iInstr "Hcode".
    { split; try solve_addr'. }
    iMod ("Hclose" with "[Hn']") as "_".
    { iNext. iExists _. iFrame. iPureIntro. lia. }
    iModIntro. wp_pure.
    (* cont *)
    iInstr "Hcode".
    { split; try solve_addr'. }

    (* close the invariant with the code *)
    iMod ("Hclose_code" with "[$Hcode $Hna]") as "Hna".
    iApply "Hφ".
    replace (a_code ^+ 4)%a with (a_end ^+ -1)%a by solve_addr'.
    iFrame.
  Qed.

  (* TODO ----------------------- *)
  (* TODO I think that it is worth waiting for HOCAP style  *)

  (* Lemma counter_full_run_spec (a_init: Addr) b_adv e_adv w1 w2 wdat rmap adv : *)
  (*   let a_code := (a_init ^+ code_off)%a in *)
  (*   let a_data := (a_code ^+ data_off)%a in *)
  (*   let a_end := (a_code ^+ (data_off + end_off))%a in *)
  (*   ContiguousRegion a_init (code_off + data_off + end_off) → *)
  (*   dom rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} → *)
  (*   Forall (λ w, is_z w = true \/ in_region w b_adv e_adv) adv → *)
  (*   (b_adv + length adv)%a = Some e_adv → *)

  (* ⊢ (   inv with_adv.invN (∃ n : Z, (a_data ^+ 1)%a ↦ₐ WInt n ∗ ⌜0 ≤ n⌝) *)
  (*     ∗ PC ↦ᵣ WCap RWX a_init a_end a_init *)
  (*     ∗ r_t0 ↦ᵣ WCap RWX b_adv e_adv b_adv *)
  (*     ∗ r_t1 ↦ᵣ w1 *)
  (*     ∗ r_t2 ↦ᵣ w2 *)
  (*     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_z w = true⌝) *)
  (*     ∗ codefrag a_init (counter_init a_init) *)
  (*     ∗ codefrag a_code (counter_code a_code) *)
  (*     ∗ a_data ↦ₐ wdat *)
  (*     ∗ ([∗ map] a↦w ∈ mkregion b_adv e_adv adv, a ↦ₐ w) *)
  (*     ∗ na_own logrel_nais ⊤ *)
  (*     -∗ WP Seq (Instr Executable) {{ λ _, True }})%I. *)
  (* Proof. *)
  (*   iIntros (? ? ? ? Hrdom ? ?) "(#HI & HPC & Hr0 & Hr1 & Hr2 & Hrmap & Hinit & Hcode & Hdat & Hadv & Hna)". *)

  (*   (* The capability to the adversary is safe and we can also jmp to it *) *)
  (*   iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv". done. *)
  (*   iDestruct (region_in_region_alloc' _ _ _ b_adv _ RWX with "Hadv") as ">#Hadv";auto. *)
  (*   { apply Forall_forall. intros. set_solver. } *)
  (*   iDestruct (jmp_to_unknown with "Hadv") as "#Hcont". *)

  (*   iApply (counter_init_spec a_init with "[-]"). solve_addr'. iFrame. *)
  (*   simpl. rewrite (_: a_init ^+ (_ + _ + _) = a_end)%a. 2: solve_addr'. iFrame. *)
  (*   rewrite (_: a_init ^+ (_ + _) = a_data)%a. 2: solve_addr'. iFrame. *)
  (*   iNext. iIntros "(HPC & Hr0 & Hr1 & Hr2 & Hdat & _)". *)

  (*   (* Allocate an invariant for the points-to at a_data containing the capability to a_data+1 *) *)
  (*   iMod (inv_alloc (N.@"cap") _ (a_data ↦ₐ WCap RWX a_init a_end (a_data ^+ 1)%a) *)
  (*           with "Hdat") as "#HIcap". *)

  (*   (* Allocate a non-atomic invariant for the code of the code routine *) *)
  (*   iMod (na_inv_alloc logrel_nais _ (N.@"code") (codefrag a_code (counter_code a_code)) *)
  (*          with "Hcode") as "#HIcode". *)

  (*   (* Show that the E-capability to the code: routine is safe *) *)
  (*   iAssert (interp (WCap E a_code a_end a_code)) as "#Hcode_safe". *)
  (*   { rewrite /interp /= (fixpoint_interp1_eq (WCap E _ _ _)) /=. iIntros (rr). *)
  (*     iIntros "!> !> ([%Hrfull #Hrsafe] & Hrr & Hna)". rewrite /interp_conf. *)

  (*     (* unpack the registers *) *)
  (*     destruct (Hrfull r_t0) as [w0' Hr0']. *)
  (*     destruct (Hrfull r_t1) as [w1' Hr1']. *)
  (*     destruct (Hrfull r_t2) as [w2' Hr2']. *)
  (*     unfold registers_mapsto. *)
  (*     rewrite -insert_delete_insert. *)
  (*     iDestruct (big_sepM_insert with "Hrr") as "[HPC Hrr]". *)
  (*       by rewrite lookup_delete. *)
  (*     iDestruct (big_sepM_delete _ _ r_t0 with "Hrr") as "[Hr0 Hrr]". *)
  (*       by rewrite lookup_delete_ne //. *)
  (*     iDestruct (big_sepM_delete _ _ r_t1 with "Hrr") as "[Hr1 Hrr]". *)
  (*       by rewrite !lookup_delete_ne //. *)
  (*     iDestruct (big_sepM_delete _ _ r_t2 with "Hrr") as "[Hr2 Hrr]". *)
  (*       by rewrite !lookup_delete_ne //. *)

  (*     (* the continuation is safe, and we can jump to it *) *)
  (*     iAssert (interp w0') as "Hv0". by iApply "Hrsafe"; eauto; done. *)
  (*     iDestruct (jmp_to_unknown with "[$Hv0]") as "#Hcont_prog". *)

  (*     (* apply the spec *) *)
  (*     iApply (counter_code_spec a_init with "[-]"). solve_addr'. *)
  (*     rewrite (_: (a_init ^+ _) ^+ _ = a_data)%a. 2: solve_addr'. *)
  (*     rewrite (_: (a_init ^+ _) ^+ (_ + _) = a_end)%a. 2: solve_addr'. *)
  (*     iFrame. iFrame "HIcap HIcode HI". *)
  (*     iIntros "!>" (n) "(HPC & Hr0 & Hr1 & Hr2 & Hcode)". *)

  (*     (* put the registers back together *) *)
  (*     iDestruct (big_sepM_sep _ (λ k v, interp v)%I with "[Hrr]") as "Hrr". *)
  (*     { iSplitL. by iApply "Hrr". iApply big_sepM_intro. iModIntro. *)
  (*       iIntros (r' ? HH). repeat eapply lookup_delete_Some in HH as [? HH]. *)
  (*       iApply ("Hrsafe" $! r'); auto. } *)
  (*     iDestruct (big_sepM_insert with "[$Hrr $Hr2]") as "Hrr". by rewrite lookup_delete. *)
  (*       by iApply interp_int. rewrite insert_delete_insert. *)
  (*     iDestruct (big_sepM_insert with "[$Hrr $Hr1]") as "Hrr". *)
  (*       by rewrite lookup_insert_ne // lookup_delete. *)
  (*       by iApply interp_int. rewrite insert_commute // insert_delete_insert. *)
  (*     iDestruct (big_sepM_insert with "[$Hrr $Hr0]") as "Hrr". *)
  (*       by rewrite !lookup_insert_ne // lookup_delete. *)
  (*       by iApply "Hv0". do 2 rewrite (insert_commute _ r_t0) //;[]. rewrite insert_delete_insert. *)

  (*     (* jmp to continuation *) *)
  (*     iApply "Hcont_prog". 2: iFrame. iPureIntro. *)
  (*     rewrite !dom_insert_L dom_delete_L regmap_full_dom //. } *)

  (*   (* put the registers back together *) *)
  (*   iDestruct (big_sepM_mono _ (λ k v, k ↦ᵣ v ∗ interp v)%I with "Hrmap") as "Hrmap". *)
  (*   { intros ? w ?. cbn. iIntros "[? %Hw]". iFrame. destruct w; try inversion Hw. *)
  (*     iApply interp_int. } *)
  (*   iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap". *)
  (*     by rewrite -not_elem_of_dom Hrdom; set_solver+. *)
  (*     by iApply interp_int. *)
  (*   iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap". *)
  (*     by rewrite lookup_insert_ne // -not_elem_of_dom Hrdom; set_solver+. *)
  (*     by iApply "Hcode_safe". *)
  (*   iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap". *)
  (*     by rewrite !lookup_insert_ne // -not_elem_of_dom Hrdom; set_solver+. *)
  (*     by iApply "Hadv". *)

  (*   iApply (wp_wand with "[-]"). *)
  (*   { iApply "Hcont". 2: iFrame. iPureIntro. *)
  (*     rewrite !dom_insert_L Hrdom !singleton_union_difference_L !all_registers_union_l. set_solver+. } *)
  (*   eauto. *)
  (* Qed. *)

End counter.

(* Local Ltac solve_addr' := *)
(*   repeat match goal with x := _ |- _ => subst x end; *)
(*   unfold code_off, data_off, end_off in *; solve_addr. *)

(* Program Definition counter_inv (a_init: Addr) : memory_inv := *)
(*   MkMemoryInv *)
(*     (λ m, ∃ n, m !! (a_init ^+ (code_off + data_off + 1))%a = Some (WInt n) ∧ 0 ≤ n) *)
(*     {[ (a_init ^+ (code_off + data_off + 1))%a ]} *)
(*     _. *)
(* Next Obligation. *)
(*   intros a_init m m' H. cbn in *. *)
(*   specialize (H (a_init ^+ (code_off + data_off + 1))%a). ospecialize H. by set_solver. *)
(* Qed. *)

(* Definition counterN : namespace := nroot .@ "counter". *)

(* Lemma adequacy `{MachineParameters} (P Adv: prog) (m m': Mem) (reg reg': Reg) es: *)
(*   prog_instrs P = *)
(*     counter_init (prog_start P) ++ *)
(*     counter_code (prog_start P ^+ code_off)%a ++ *)
(*     counter_data → *)
(*   with_adv.is_initial_memory P Adv m → *)
(*   with_adv.is_initial_registers P Adv reg r_t0 → *)
(*   Forall (adv_condition Adv) (prog_instrs Adv) → *)

(*   rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) → *)
(*   ∃ n, m' !! (prog_start P ^+ (code_off + data_off + 1))%a = Some (WInt n) ∧ 0 ≤ n. *)
(* Proof. *)
(*   intros HP Hm Hr HAdv Hstep. *)
(*   generalize (prog_size P). rewrite HP /=. intros. *)

(*   (* Prove the side-conditions over the memory invariant *) *)
(*   eapply (with_adv.template_adequacy P Adv (counter_inv (prog_start P)) r_t0 m m' reg reg' es); auto. *)
(*   { cbn. unfold with_adv.is_initial_memory in Hm. destruct Hm as (Hm & _ & _). *)
(*     exists 0; split; [| done]. eapply lookup_weaken; [| apply Hm]. rewrite /prog_region mkregion_lookup. *)
(*     { exists (Z.to_nat (code_off + data_off + 1)). split. done. rewrite HP; done. } *)
(*     { apply prog_size. } } *)
(*   { cbn. apply elem_of_subseteq_singleton, elem_of_list_to_set, elem_of_finz_seq_between. solve_addr'. } *)

(*   intros * Hss * Hrdom. iIntros "(#HI & Hna & HPC & Hr0 & Hrmap & Hadv & Hprog)". *)
(*   set (a_init := prog_start P) in *. *)
(*   set (a_code := (a_init ^+ code_off)%a) in *. *)
(*   set (a_data := (a_code ^+ data_off)%a) in *. *)

(*   (* Extract the code & data regions from the program resources *) *)
(*   iAssert (codefrag a_init (counter_init a_init) ∗ *)
(*            codefrag a_code (counter_code a_code) ∗ *)
(*            (∃ w, a_data ↦ₐ w))%I *)
(*     with "[Hprog]" as "(Hinit & Hcode & Hdat)". *)
(*   { rewrite /codefrag /region_mapsto. *)
(*     set M := filter _ _. *)
(*     set Minit := mkregion a_init a_code (counter_init a_init). *)
(*     set Mcode := mkregion a_code a_data (counter_code a_code). *)
(*     set Mdat := mkregion a_data (a_data ^+ 1)%a [WInt 7777]. *)

(*     assert (Mcode ##ₘ Mdat). *)
(*     { apply map_disjoint_spec. *)
(*       intros ? ? ? [? [? ?%lookup_lt_Some] ]%mkregion_lookup [? [? ?%lookup_lt_Some] ]%mkregion_lookup. *)
(*       all: solve_addr'. } *)

(*     assert (Minit ##ₘ (Mcode ∪ Mdat)). *)
(*     { apply map_disjoint_spec. *)
(*       intros ? ? ? [? [? ?%lookup_lt_Some] ]%mkregion_lookup. *)
(*       2: solve_addr'. intros [HH|HH]%lookup_union_Some; auto. *)
(*       all: apply mkregion_lookup in HH as [? [? ?%lookup_lt_Some] ]; solve_addr'. } *)

(*     assert (Minit ∪ (Mcode ∪ Mdat) ⊆ M) as HM. *)
(*     { apply map_subseteq_spec. intros a w. intros [Ha| [Ha|Ha]%lookup_union_Some]%lookup_union_Some. *)
(*       4,5: assumption. *)
(*       all: apply mkregion_lookup in Ha as [i [? HH] ]; [| solve_addr']. *)
(*       all: apply map_lookup_filter_Some_2; *)
(*         [| cbn; apply not_elem_of_singleton; apply lookup_lt_Some in HH; solve_addr']. *)
(*       all: subst; rewrite mkregion_lookup; [| rewrite HP; solve_addr']. *)
(*       { eexists. split; eauto. rewrite HP. by apply lookup_app_l_Some. } *)
(*       { exists (Z.to_nat (i+code_off)). split. solve_addr'. rewrite HP. *)
(*         apply lookup_app_Some. right. split. solve_addr'. apply lookup_app_l_Some. *)
(*         rewrite (_: _ - _ = i)%nat //. solve_addr'. } *)
(*       { exists (Z.to_nat (code_off + data_off)). destruct i; [| by inversion HH]. split. solve_addr'. *)
(*         rewrite HP. apply lookup_app_Some. right. split. solve_addr'. *)
(*         apply lookup_app_Some. right. split. solve_addr'. done. } } *)

(*     iDestruct (big_sepM_subseteq with "Hprog") as "Hprog". apply HM. *)
(*     iDestruct (big_sepM_union with "Hprog") as "[Hinit Hprog]". assumption. *)
(*     iDestruct (big_sepM_union with "Hprog") as "[Hcode Hdat]". assumption. *)
(*     iDestruct (mkregion_sepM_to_sepL2 with "Hinit") as "Hinit". solve_addr'. *)
(*     iDestruct (mkregion_sepM_to_sepL2 with "Hcode") as "Hcode". solve_addr'. *)
(*     iDestruct (mkregion_sepM_to_sepL2 with "Hdat") as "Hdat". solve_addr'. *)
(*     iFrame. iExists _. rewrite finz_seq_between_cons. cbn. by iDestruct "Hdat" as "[? ?]". *)
(*     solve_addr'. } *)
(*   iDestruct "Hdat" as (wdat) "Hdat". *)

(*   assert (is_Some (rmap !! r_t1)) as [w1 Hr1]. *)
(*   { rewrite -elem_of_dom Hrdom. set_solver+. } *)
(*   assert (is_Some (rmap !! r_t2)) as [w2 Hr2]. *)
(*   { rewrite -elem_of_dom Hrdom. set_solver+. } *)
(*   iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[[Hr1 _] Hrmap]"; eauto. *)
(*   iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[[Hr2 _] Hrmap]". *)
(*     by rewrite lookup_delete_ne //. *)

(*   iApply (counter_full_run_spec with "[$Hadv $Hr0 $Hr1 $Hr2 $Hinit $Hrmap $Hna $Hdat $Hcode HPC]"); auto. *)
(*   solve_addr'. by rewrite !dom_delete_L Hrdom; set_solver+. by apply prog_size. *)
(*   rewrite (_: _ ^+ (_ + _) = prog_end P)%a. 2: solve_addr'. iFrame. *)

(*   (* Show the invariant for the counter value using the invariant from the adequacy theorem *) *)
(*   iApply (inv_alter with "HI"). *)
(*   iIntros "!> !> H". rewrite /minv_sep. iDestruct "H" as (mι) "(Hm & %Hmιdom & %Hι)". *)
(*   cbn in Hι. destruct Hι as (n & Hι & Hn). *)
(*   rewrite (_: a_init ^+ _ = (a_data ^+ 1))%a in Hι. 2: solve_addr'. *)
(*   iDestruct (big_sepM_delete _ _ (a_data ^+ 1)%a (WInt n) with "Hm") as "[Hn Hm]". done. *)
(*   iSplitL "Hn". by eauto. iIntros "Hn'". iDestruct "Hn'" as (n') "(Hn' & %)". *)
(*   iExists (<[ (a_data ^+ 1)%a := WInt n' ]> mι). iSplitL "Hm Hn'". *)
(*   { iDestruct (big_sepM_insert with "[$Hm $Hn']") as "Hm". by apply lookup_delete. *)
(*     rewrite insert_delete_insert //. } *)
(*   iPureIntro. split. rewrite dom_insert_L Hmιdom /Hmιdom /=. 2: exists n'. *)
(*   all: rewrite (_: a_init ^+ _ = (a_data ^+ 1))%a; [| solve_addr']. set_solver+. *)
(*   rewrite lookup_insert //. *)
(* Qed. *)
