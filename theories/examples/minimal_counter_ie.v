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

        (* ; 3. prepare the IEpair *)
        Lea idc (-1)%Z;
        Restrict idc (encodePerm IEpair);

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

  Lemma counter_init_spec (a_init a_data: Addr) (wadv w1 wdat0 wdat1 : Word) φ :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in
    let a_secret := (a_data ^+ secret_off)%a in
    let a_data_end := (a_data ^+ data_end_off)%a in

    ContiguousRegion a_init (code_off + end_off) →
    ContiguousRegion a_data (data_end_off) →

   ⊢ (( PC ↦ᵣ WCap RX a_init a_end a_init
      ∗ idc ↦ᵣ WCap RW a_data a_data_end a_data
      ∗ r_t1 ↦ᵣ w1
      ∗ r_t31 ↦ᵣ wadv
      ∗ a_data ↦ₐ wdat0
      ∗ (a_data ^+1)%a ↦ₐ wdat1
      ∗ codefrag a_init (counter_init a_init a_data)
      ∗ ▷ (  PC ↦ᵣ updatePcPerm wadv
           ∗ idc ↦ᵣ WCap IEpair a_data a_data_end a_data
           ∗ r_t1 ↦ᵣ WInt 0
           ∗ r_t31 ↦ᵣ wadv
           ∗ a_data ↦ₐ WCap RX a_init a_end a_code
           ∗ (a_data ^+1)%a ↦ₐ WCap RW a_data a_data_end a_secret
           ∗ codefrag a_init (counter_init a_init a_data)
           -∗ WP Seq (Instr Executable) {{ φ }}))
      -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros a_code a_end a_secret a_data_end.
    iIntros (Hcont_code Hcont_data)
      "(HPC & Hidc & Hr1 & Hr31 & Hdat0 & Hdat1 & Hprog & Hφ)".
    iGo "Hprog".
    { transitivity (Some a_code); auto. solve_addr'. }
    iGo "Hprog".
    { transitivity (Some a_secret); auto. solve_addr'. }
    iGo "Hprog".
    { transitivity (Some a_data); auto. solve_addr'. }
    iGo "Hprog"; rewrite decode_encode_perm_inv //.
    iGo "Hprog".
    iApply "Hφ". iFrame.
  Qed.

  Lemma counter_code_spec (a_init a_data: Addr) wcont w1 φ :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in
    let a_secret := (a_data ^+ secret_off)%a in
    let a_data_end := (a_data ^+ data_end_off)%a in

    ContiguousRegion a_init (code_off + end_off) →
    ContiguousRegion a_data (data_end_off) →

    ⊢ (( inv with_adv.invN (∃ n, a_secret ↦ₐ WInt n ∗ ⌜0 ≤ n⌝)
         ∗ na_inv logrel_nais (N.@"code") (codefrag a_code counter_code)
         ∗ PC ↦ᵣ WCap RX a_init a_end a_code
         ∗ idc ↦ᵣ WCap RW a_data a_data_end a_secret
         ∗ r_t1 ↦ᵣ w1
         ∗ r_t31 ↦ᵣ wcont
         ∗ na_own logrel_nais ⊤
         ∗ ▷ (∀ (n: Z),
                PC ↦ᵣ(updatePcPerm wcont)
                ∗ idc ↦ᵣ WInt 0
                ∗ r_t1 ↦ᵣ WInt n
                ∗ r_t31 ↦ᵣ wcont
                ∗ na_own logrel_nais ⊤
                  -∗ WP Seq (Instr Executable) {{ φ }}))
       -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros a_code a_end a_secret a_data_end.
    iIntros (Hcont_code Hcont_data)
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

    (* move idc 0  *)
    iInstr "Hcode".
    { split; try solve_addr'. }

    (* jmp to cont *)
    iInstr "Hcode".
    { split; try solve_addr'. }

    (* close the invariant with the code *)
    iMod ("Hclose_code" with "[$Hcode $Hna]") as "Hna".
    iApply "Hφ"; iFrame.
  Qed.

  Lemma counter_code_spec_full (a_init a_data: Addr) (wcont w1 : Word) (rmap : Reg) :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in
    let a_secret := (a_data ^+ secret_off)%a in
    let a_data_end := (a_data ^+ data_end_off)%a in

    ContiguousRegion a_init (code_off + end_off) →
    ContiguousRegion a_data (data_end_off) →

    dom rmap = all_registers_s ∖ {[ PC; idc; r_t1; r_t31 ]} →

  ⊢ (( interp wcont
         ∗ inv with_adv.invN (∃ n, a_secret ↦ₐ WInt n ∗ ⌜0 ≤ n⌝)
         ∗ na_inv logrel_nais (N.@"code") (codefrag a_code counter_code)
         ∗ PC ↦ᵣ WCap RX a_init a_end a_code
         ∗ idc ↦ᵣ WCap RW a_data a_data_end a_secret
         ∗ r_t1 ↦ᵣ w1
         ∗ r_t31 ↦ᵣ wcont
         ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ interp w)
         ∗ na_own logrel_nais ⊤
       -∗ interp_conf)%I).
  Proof.
    intros a_code a_end a_secret a_data_end.
    iIntros (Hcont_code Hcont_data Hrmap)
      "(#Hinterp_wcont & #HIv & #HIcode & HPC & Hidc & Hr1 & Hr31 & Hrmap & Hna)".
    (* Prepare the continuation before the spec, because of the later *)
    iDestruct (jmp_to_unknown with "Hinterp_wcont") as "Hcont".

    iApply (counter_code_spec with "[-]"); eauto; iFrame "∗ #".
    iNext; iIntros (n) "(HPC & Hidc & Hr1 & Hr31 & Hna)".

    (* Show that all the registers are safe to share *)
    iAssert (idc ↦ᵣ WInt 0 ∗ interp (WInt 0))%I with "[Hidc]" as "Hidc"
    ; first (iSplit ; rewrite !fixpoint_interp1_eq //=).
    iAssert (r_t1 ↦ᵣ WInt n ∗ interp (WInt n))%I with "[Hr1]" as "Hr1"
    ; first (iSplit ; rewrite !fixpoint_interp1_eq //=).
    iAssert (r_t31 ↦ᵣ wcont ∗ interp wcont)%I with "[Hr31]" as "Hr31"
    ; first (iFrame "∗ #").
    iInsertList "Hrmap" [r_t1;r_t31;idc].

    (* Use continuation *)
    set (regs := <[ _ := _]> _).
    iApply ("Hcont" $! regs); iFrame "∗ #".
    rewrite /full_map; subst regs.
    iPureIntro.
    rewrite !dom_insert_L Hrmap; set_solver.
  Qed.

  Lemma counter_code_spec_int (a_init: Addr) w1 z :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in

    ContiguousRegion a_init (code_off + end_off) →

  ⊢ ( na_inv logrel_nais (N.@"code") (codefrag a_code counter_code)
     ∗ PC ↦ᵣ WCap RX a_init a_end a_code
     ∗ idc ↦ᵣ WInt z
     ∗ r_t1 ↦ᵣ w1
     ∗ na_own logrel_nais ⊤
     -∗ WP Seq (Instr Executable) {{ λ v, ⌜v = FailedV⌝ }})%I.
  Proof.
    intros a_code a_end.
    iIntros (Hcont_code)
      "(#HIcode & HPC & Hidc & Hr1 & Hna)".
    (* open the invariant containing the code *)
    iMod (na_inv_acc logrel_nais with "HIcode Hna") as "(>Hcode & Hna & Hclose_code)".
    done. done.
    codefrag_facts "Hcode".

    iInstr_lookup "Hcode" as "Hi" "Hcont".
    wp_instr.
    iApply (wp_Load_fail_int with "[$Hi $HPC $Hidc $Hr1]"); eauto.
    { apply decode_encode_instrW_inv. }
    { split; solve_addr'. }
    iNext; iIntros (_).
    by wp_pure; wp_end.
  Qed.

  Lemma counter_full_run_spec (a_init a_data: Addr) b_adv e_adv w1 wdat0 wdat1 rmap adv :
    let a_code := (a_init ^+ code_off)%a in
    let a_end := (a_init ^+ (code_off + end_off))%a in
    let a_secret := (a_data ^+ secret_off)%a in
    let a_data_end := (a_data ^+ data_end_off)%a in

    ContiguousRegion a_init (code_off + end_off) →
    ContiguousRegion a_data (data_end_off) →

    dom rmap = all_registers_s ∖ {[ PC; idc; r_t1; r_t31 ]} →
    Forall (λ w, is_z w = true \/ in_region w b_adv e_adv) adv →
    (b_adv + length adv)%a = Some e_adv →

  ⊢ (( inv with_adv.invN (∃ n, a_secret ↦ₐ WInt n ∗ ⌜0 ≤ n⌝)
     ∗ PC ↦ᵣ WCap RX a_init a_end a_init
     ∗ idc ↦ᵣ WCap RW a_data a_data_end a_data
     ∗ r_t1 ↦ᵣ w1
     ∗ r_t31 ↦ᵣ WCap RWX b_adv e_adv b_adv
     ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_z w = true⌝)

     ∗ codefrag a_init (counter_init a_init a_data)
     ∗ codefrag a_code counter_code

     ∗ a_data ↦ₐ wdat0
     ∗ (a_data ^+1)%a ↦ₐ wdat1
      ∗ ([∗ map] a↦w ∈ mkregion b_adv e_adv adv, a ↦ₐ w)

     ∗ na_own logrel_nais ⊤

       -∗ WP Seq (Instr Executable) {{ λ _, True }})%I).
  Proof.
    iIntros (? ? ? ? Hcont_code Hcont_data Hrdom Hadv_closed Headv)
      "(#HI & HPC & Hidc & Hr1 & Hr31 & Hrmap & Hinit & Hcode & Hdata & Hdata' & Hadv & Hna)".

    (* The capability to the adversary is safe and we can also jmp to it *)
    iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv". done.
    iDestruct (region_in_region_alloc' _ _ _ b_adv _ RWX with "Hadv") as ">#Hadv";auto.
    { apply Forall_forall. intros. set_solver. }
    iDestruct (jmp_to_unknown with "Hadv") as "#Hcont".

    iApply (counter_init_spec a_init with "[-]"); eauto; iFrame.
    iNext. iIntros "(HPC & Hidc & Hr1 & Hr31 & Hdat & Hdat' & Hinit)".

    rewrite (_: a_init ^+ (_ + _) = a_end)%a; [|solve_addr'].
    rewrite (_: a_init ^+ _ = a_code)%a; [|solve_addr'].
    rewrite (_: a_data ^+ data_end_off = a_data_end)%a; [|solve_addr'].
    rewrite (_: a_data ^+ secret_off = a_secret)%a; [|solve_addr'].
    (* Allocate an invariant for the points-to at a_data containing the capability to a_data+1 *)
    iMod (inv_alloc (logN.@a_data%a) _ (a_data ↦ₐ WCap RX a_init a_end a_code)
            with "Hdat") as "#HIcode_cap".
    iMod (inv_alloc (logN.@(a_data ^+1)%a) _ ((a_data ^+ 1)%a ↦ₐ WCap RW a_data a_data_end a_secret)
            with "Hdat'") as "#HIdata_cap".

    (* Allocate a non-atomic invariant for the code of the code routine *)
    iMod (na_inv_alloc logrel_nais _ (N.@"code") (codefrag a_code counter_code)
           with "Hcode") as "#HIcode".

    (* Show that the IEpair-capability to the code: routine is safe *)
    iAssert (interp (WCap IEpair a_data a_data_end a_data)) as "#Hcode_safe".
    { rewrite /interp /= (fixpoint_interp1_eq (WCap IEpair _ _ _)) /=.
      iIntros (Hinbounds).
      iExists (cap_eq RX a_init a_end a_code).
      iExists (cap_eq RW a_data a_data_end a_secret).
      iSplit ; first (iApply cap_eq_persistent).
      iSplit ; first (iApply cap_eq_persistent).
      iSplit; first (iApply inv_cap_eq; iFrame "#").
      iSplit; first (iApply inv_cap_eq; iFrame "#").

      iIntros (wcode wdata regs) ; iNext ; iModIntro.
      iIntros "[%Hprog %Hdata] ([%Hrfull #Hr_interp] & Hrmap & Hna)".
      simplify_eq.

      (* unpack the registers *)
      destruct (Hrfull idc) as [widc' Hridc].
      destruct (Hrfull r_t1) as [w1' Hr1'].
      destruct (Hrfull r_t31) as [w31' Hr31'].
      iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]".
      by simplify_map_eq.
      iDestruct (big_sepM_delete _ _ idc with "Hrmap") as "[Hidc Hrmap]".
      by rewrite !lookup_delete_ne //; simplify_map_eq.
      iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[Hr1 Hrmap]".
      by rewrite !lookup_delete_ne //; simplify_map_eq.
      iDestruct (big_sepM_delete _ _ r_t31 with "Hrmap") as "[Hr31 Hrmap]".
      by rewrite !lookup_delete_ne //; simplify_map_eq.

      destruct Hdata as [-> | Hdata].
      (* apply the spec *)
      + (* case wdata is the expected capability *)
        clear Hrdom rmap.
        rewrite delete_insert_ne //= !delete_insert_delete.
        set (rmap := delete r_t31 _).
        assert (Hrdom : dom rmap = all_registers_s ∖ {[PC; idc; r_t1; r_t31]}).
        { subst rmap.
          rewrite !dom_delete_L.
          simpl in Hrfull.
          rewrite regmap_full_dom; eauto.
        }
        iApply (counter_code_spec_full a_init a_data with "[-]")
        ; eauto ; iFrame "∗ #".
        iSplit.
        iApply ("Hr_interp" $! r_t31); auto.
        iApply big_sepM_sep.
        iSplit; auto.
        iApply big_sepM_intro.
        iModIntro ; iIntros (r w) "%Hr".

        iApply ("Hr_interp" $! r); auto.
        { iPureIntro; intro ; subst rmap ; simplify_map_eq. }
        { iPureIntro; intro ; subst rmap ; simplify_map_eq. }
        { iPureIntro ; subst rmap ; simplify_map_eq.
          by repeat (eapply lookup_delete_Some in Hr; destruct Hr as [_ Hr]).
        }
      + (* case wdata is an interger *)
        destruct wdata ; cbn in Hdata ; try contradiction.
        iApply (wp_wand with "[-]").
        iApply (counter_code_spec_int a_init with "[-]"); eauto; iFrame "∗ #".
        iIntros (v) "->" ; auto ; iIntros "%Hcontra" ; congruence.
    }

    (* put the registers back together *)
    iDestruct (big_sepM_mono _ (λ k v, k ↦ᵣ v ∗ interp v)%I with "Hrmap") as "Hrmap".
    { intros ? w ?. cbn. iIntros "[? %Hw]". iFrame. destruct w; try inversion Hw.
      iApply interp_int. }

    iDestruct (big_sepM_insert _ _ r_t31 with "[$Hrmap $Hr31]") as "Hrmap".
    by rewrite -not_elem_of_dom Hrdom; set_solver+.
    done.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
    by rewrite lookup_insert_ne // -not_elem_of_dom Hrdom; set_solver+.
    by iApply interp_int.
    iDestruct (big_sepM_insert _ _ idc with "[$Hrmap $Hidc]") as "Hrmap".
    by rewrite !lookup_insert_ne // -not_elem_of_dom Hrdom; set_solver+.
    by iApply "Hcode_safe".

    iApply (wp_wand with "[-]").
    { iApply "Hcont". 2: iFrame. iPureIntro.
      rewrite !dom_insert_L Hrdom !singleton_union_difference_L !all_registers_union_l. set_solver+. }
    eauto.
  Qed.

End counter.

Local Ltac solve_addr' :=
  repeat match goal with x := _ |- _ => subst x end;
  unfold code_off, secret_off, end_off, data_end_off in *; solve_addr.

Program Definition counter_inv (a_data: Addr) : memory_inv :=
  MkMemoryInv
    (λ m, ∃ n, m !! (a_data ^+ secret_off)%a = Some (WInt n) ∧ 0 ≤ n)
    {[ (a_data ^+ secret_off)%a ]}
    _.
Next Obligation.
  intros a_data m m' H. cbn in *.
  specialize (H (a_data ^+ secret_off)%a). ospecialize H. by set_solver.
Qed.

Definition counterN : namespace := nroot .@ "counter".

Lemma adequacy `{MachineParameters} (Pcode Pdata Adv: prog) (m m': Mem) (reg reg': Reg) es:
  prog_instrs Pcode =
    counter_init (prog_start Pcode) (prog_start Pdata) ++
    counter_code ->
  prog_instrs Pdata = counter_data →
  compartment_with_adv.is_initial_memory Pcode Pdata Adv m →
  compartment_with_adv.is_initial_registers Pcode Pdata Adv reg r_t31 →
  Forall (adv_condition Adv) (prog_instrs Adv) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  ∃ n, m' !! ((prog_start Pdata) ^+ secret_off)%a = Some (WInt n) ∧ 0 ≤ n.
Proof.
  intros Hcode Hdata Hm Hr HAdv Hstep.
  generalize (prog_size Pdata). rewrite Hdata /=. intros.
  generalize (prog_size Pcode). rewrite Hcode /=. intros.

  (* Prove the side-conditions over the memory invariant *)
  eapply (compartment_with_adv.template_adequacy Pcode Pdata Adv
            (counter_inv (prog_start Pdata)) r_t31 m m' reg reg' es); auto.
  { cbn. unfold compartment_with_adv.is_initial_memory in Hm. destruct Hm as (_ & Hm & _).
    exists 0; split; [| done]. eapply lookup_weaken; [| apply Hm]. rewrite /prog_region mkregion_lookup.
    { exists (Z.to_nat secret_off). split. done. rewrite /secret_off.
      rewrite Hdata; done. }
    { apply prog_size. } }
  { cbn.
    apply union_subseteq_r', elem_of_subseteq_singleton,
      elem_of_list_to_set , elem_of_finz_seq_between.
    solve_addr'. }

  intros * Hss * Hrdom. iIntros
    "(#HI & Hna & HPC & Hidc & Hradv & Hrmap & Hadv & Hprog & Hdata)".
  set (a_init := prog_start Pcode) in *.
  set (a_code := (a_init ^+ code_off)%a) in *.
  set (a_data := prog_start Pdata) in *.
  set (a_end := (a_init ^+ (code_off + end_off))%a).

  (* Extract the code & data regions from the program resources *)
  iAssert (
      codefrag a_init (counter_init a_init a_data)
        ∗ codefrag a_code counter_code)%I
    with "[Hprog]" as "(Hinit & Hcode)".
  { rewrite /codefrag /region_mapsto.
    set M := filter _ _.
    set Minit := mkregion a_init a_code (counter_init a_init a_data).
    set Mcode := mkregion a_code a_end counter_code.

    assert (Minit ##ₘ Mcode).
    { apply map_disjoint_spec.
      intros ? ? ? [? [? ?%lookup_lt_Some] ]%mkregion_lookup [? [? ?%lookup_lt_Some] ]%mkregion_lookup.
      all: solve_addr'. }

    assert (Minit ∪ Mcode ⊆ M) as HM.
    { apply map_subseteq_spec. intros a w.
      intros [Ha|Ha]%lookup_union_Some.
      3: assumption.
      all: apply mkregion_lookup in Ha as [i [? HH] ]; [| solve_addr'].
      all: apply map_lookup_filter_Some_2.
      1,3: subst; rewrite mkregion_lookup; [| rewrite Hcode; solve_addr'].
      { eexists. split; eauto. rewrite Hcode. by apply lookup_app_l_Some. }
      { exists (Z.to_nat (i+code_off)). split. solve_addr'. rewrite Hcode.
        apply lookup_app_Some. right. split. solve_addr'.
        rewrite (_: _ - _ = i)%nat //. solve_addr'. }
      all: cbn; apply not_elem_of_singleton; apply lookup_lt_Some in HH.
      all: destruct Hm as (_ & _ & _ & Hm & _); apply map_disjoint_dom_1 in Hm.
      all: assert (a ∈ dom (prog_region Pcode)).
      1,3:
        rewrite prog_region_dom
      ; apply elem_of_list_to_set, elem_of_finz_seq_between
      ; solve_addr'.
      all: assert ((a_data ^+ secret_off)%a ∈ dom (prog_region Pdata)).
      1,3:
        rewrite prog_region_dom
      ; apply elem_of_list_to_set, elem_of_finz_seq_between
      ; solve_addr'.
      all: intro; simplify_eq ; rewrite H9 in H7; set_solver.
    }

    iDestruct (big_sepM_subseteq with "Hprog") as "Hprog". apply HM.
    iDestruct (big_sepM_union with "Hprog") as "[Hinit Hprog]". assumption.
    iDestruct (mkregion_sepM_to_sepL2 with "Hinit") as "Hinit". solve_addr'.
    iDestruct (mkregion_sepM_to_sepL2 with "Hprog") as "Hprog". solve_addr'.
    replace a_end with (a_code ^+ length counter_code)%a.
    iFrame.
    solve_addr'.
    }

  iAssert (
      (prog_start Pdata) ↦ₐ WInt 7777 ∗ ((prog_start Pdata) ^+ 1)%a ↦ₐ WInt 7777
    )%I
    with "[Hdata]" as "(Hdat1 & Hdat2)".
  {
    cbn.
    rewrite /prog_region Hdata /counter_data.
    replace (filter _ _) with
     (mkregion (prog_start Pdata) (a_data ^+ secret_off)%a
                   (map WInt [7777; 7777])).
    iDestruct (mkregion_sepM_to_sepL2 with "Hdata") as "Hdata"
    ; first solve_addr'.
    rewrite finz_seq_between_cons; last solve_addr'.
    rewrite finz_seq_between_cons; last solve_addr'.
    simplify_map_eq.
    iDestruct "Hdata" as "(Hdat1 & Hdat2 & _)".
    iFrame.
    rewrite /mkregion.
    rewrite !(finz_seq_between_cons (prog_start Pdata)); try solve_addr'.
    rewrite !(finz_seq_between_cons ((prog_start Pdata) ^+ 1)%a)
    ; try solve_addr'.
    setoid_rewrite finz_seq_between_cons at 2; last solve_addr'.
    cbn.
    rewrite !finz_seq_between_empty; try solve_addr'.
    rewrite !zip_with_nil_r /=.
    rewrite map_filter_insert_True.
    2: {
      subst a_data.
      apply not_elem_of_singleton.
      solve_addr'.
    }

    rewrite map_filter_insert_True.
    2: {
      subst a_data.
      apply not_elem_of_singleton.
      solve_addr'.
    }

    rewrite map_filter_insert_False.
    2: {
      subst a_data.
      intro Hcontra ; apply Hcontra.
      apply elem_of_singleton.
      solve_addr'.
    }

    by rewrite delete_empty.
  }

  assert (is_Some (rmap !! r_t1)) as [w1 Hr1].
  { rewrite -elem_of_dom Hrdom. set_solver+. }
  iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[[Hr1 _] Hrmap]"; eauto.
  iApply (counter_full_run_spec with
           "[HPC Hidc $Hr1 $Hradv $Hrmap $Hinit $Hcode $Hadv $Hdat1 $Hdat2 $Hna]")
  ; auto.
  1,2: solve_addr'.
  by rewrite !dom_delete_L Hrdom; set_solver+.
  by apply prog_size.
  rewrite (_: _ ^+ (_ + _) = prog_end Pcode)%a; [ iFrame | solve_addr'].
  rewrite (_: _ ^+ data_end_off  = prog_end Pdata)%a; [ iFrame | solve_addr'].

  (* Show the invariant for the counter value using the invariant from the adequacy theorem *)
  iApply (inv_alter with "HI").
  iIntros "!> !> H". rewrite /minv_sep. iDestruct "H" as (mι) "(Hm & %Hmιdom & %Hι)".
  cbn in Hι. destruct Hι as (n & Hι & Hn).
  iDestruct (big_sepM_delete _ _ (a_data ^+ secret_off)%a (WInt n) with "Hm") as "[Hn Hm]". done.
  iSplitL "Hn". by eauto. iIntros "Hn'". iDestruct "Hn'" as (n') "(Hn' & %)".
  iExists (<[ (a_data ^+ secret_off)%a := WInt n' ]> mι). iSplitL "Hm Hn'".
  { iDestruct (big_sepM_insert with "[$Hm $Hn']") as "Hm". by apply lookup_delete.
    rewrite insert_delete_insert //. }
  iPureIntro. split.
  rewrite dom_insert_L Hmιdom /Hmιdom /=. set_solver+.
  exists n'. split ; simplify_map_eq; auto.
Qed.
