From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental.
From cap_machine.examples Require Import template_adequacy macros_new.
From cap_machine Require Import proofmode.
Open Scope Z_scope.

Section counter.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Definition N : namespace := nroot .@ "mincounter".

  (* In this example, we avoid computing offsets by hand, and instead define the
     code in two steps, computing the labels automatically (mimicking the steps
     a proper assembler would do). *)

  Definition counter_init0 (init code data end_: Z) : list Word :=
    (* init: *)
    encodeInstrsW [
      Mov r_t1 PC;
      Lea r_t1 (data-init)%Z;
      Mov r_t2 r_t1;
      Lea r_t2 1;
      Store r_t1 r_t2;
      Lea r_t1 (code-data)%Z;
      Subseg r_t1 code end_;
      Restrict r_t1 (encodePerm E);
      Mov r_t2 0;
      Jmp r_t0
    ].
  Definition counter_code0 (code data: Z) : list Word :=
    (* code: *)
    encodeInstrsW [
      Mov r_t1 PC;
      Lea r_t1 (data-code)%Z;
      Load r_t1 r_t1;
      Load r_t2 r_t1;
      Add r_t2 r_t2 1;
      Store r_t1 r_t2;
      Mov r_t1 0;
      Jmp r_t0
    ].
  Definition counter_data : list Word :=
    (* data: *)
    map WInt [7777 (* placeholder *); 0 (* current value of the counter *)]
    (* end: *).

  Definition code_off := Eval compute in length (counter_init0 0 0 0 0).
  Definition data_off := Eval compute in length (counter_code0 0 0).
  Definition end_off := Eval compute in length counter_data.

  Definition counter_init (init: Z) : list Word :=
    counter_init0 init (init + code_off) (init + code_off + data_off)
                  (init + code_off + data_off + end_off).

  Definition counter_code (code: Z) : list Word :=
    counter_code0 code (code + data_off).

  (* Specification for the init routine *)

  Local Ltac solve_addr' :=
    repeat match goal with x := _ |- _ => subst x end;
    unfold code_off, data_off, end_off in *; solve_addr.

  Lemma counter_init_spec (a_init: Addr) wadv w1 w2 wdat φ :
    let a_code := (a_init ^+ code_off)%a in
    let a_data := (a_init ^+ (code_off + data_off))%a in
    let a_end := (a_init ^+ (code_off + data_off + end_off))%a in
    ContiguousRegion a_init (code_off + data_off + end_off) →

   ⊢ (( PC ↦ᵣ WCap RWX a_init a_end a_init
      ∗ r_t0 ↦ᵣ wadv
      ∗ r_t1 ↦ᵣ w1
      ∗ r_t2 ↦ᵣ w2
      ∗ a_data ↦ₐ wdat
      ∗ codefrag a_init (counter_init a_init)
      ∗ ▷ (  PC ↦ᵣ updatePcPerm wadv
           ∗ r_t0 ↦ᵣ wadv
           ∗ r_t1 ↦ᵣ WCap E a_code a_end a_code
           ∗ r_t2 ↦ᵣ WInt 0
           ∗ a_data ↦ₐ WCap RWX a_init a_end (a_data ^+ 1)%a
           ∗ codefrag a_init (counter_init a_init)
           -∗ WP Seq (Instr Executable) {{ φ }}))
      -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros a_code a_data a_end.
    iIntros (Hcont) "(HPC & Hr0 & Hr1 & Hr2 & Hdat & Hprog & Hφ)".
    iGo "Hprog".
    { transitivity (Some a_data); auto. solve_addr'. }
    iGo "Hprog".
    { transitivity (Some a_code); auto. solve_addr'. }
    iGo "Hprog".
    { transitivity (Some a_code); auto. solve_addr'. }
    { transitivity (Some a_end); auto. solve_addr'. }
    solve_addr'.
    iGo "Hprog"; rewrite decode_encode_perm_inv //.
    iGo "Hprog". iApply "Hφ". iFrame.
    rewrite (_: (a_init ^+ 19) = a_data ^+ 1)%a //. solve_addr'.
  Qed.

  Lemma counter_code_spec (a_init: Addr) wcont w1 w2 φ :
    let a_code := (a_init ^+ code_off)%a in
    let a_data := (a_code ^+ data_off)%a in
    let a_end := (a_code ^+ (data_off + end_off))%a in
    ContiguousRegion a_code (data_off + end_off) →

  ⊢ (( inv (N.@"cap") (a_data ↦ₐ WCap RWX a_init a_end (a_data ^+ 1)%a)
     ∗ inv with_adv.invN (∃ n, (a_data ^+ 1)%a ↦ₐ WInt n ∗ ⌜0 ≤ n⌝)
     ∗ na_inv logrel_nais (N.@"code") (codefrag a_code (counter_code a_code))
     ∗ PC ↦ᵣ WCap RX a_code a_end a_code
     ∗ r_t0 ↦ᵣ wcont
     ∗ r_t1 ↦ᵣ w1
     ∗ r_t2 ↦ᵣ w2
     ∗ na_own logrel_nais ⊤
     ∗ ▷ (∀ (n: Z),
            PC ↦ᵣ updatePcPerm wcont
          ∗ r_t0 ↦ᵣ wcont
          ∗ r_t1 ↦ᵣ WInt 0
          ∗ r_t2 ↦ᵣ WInt n
          ∗ na_own logrel_nais ⊤
          -∗ WP Seq (Instr Executable) {{ φ }}))
     -∗ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros a_code a_data a_end.
    iIntros (Hcont) "(#HIcap & #HIv & #HIcode & HPC & Hr0 & Hr1 & Hr2 & Hna & Hφ)".
    assert (Ha_code: a_code = (a_init ^+ code_off)%a) by done. clearbody a_code.
    (* open the invariant containing the code *)
    iMod (na_inv_acc logrel_nais with "HIcode Hna") as "(>Hcode & Hna & Hclose_code)".
    done. done.

    iGo "Hcode".
    { transitivity (Some a_data); auto. solve_addr'. }
    (* load from a_data *)
    wp_instr.
    iMod (inv_acc with "HIcap") as "[>Hcap Hclose]"; auto.
    iInstr "Hcode".
    iMod ("Hclose" with "Hcap") as "_". iModIntro. wp_pure.
    (* load from a_data+1 *)
    wp_instr.
    iMod (inv_acc with "HIv") as "[>Hv Hclose]"; auto.
    iDestruct "Hv" as (n) "(Hn & %Hn)".
    iInstr "Hcode".
    { split. solve_pure. solve_addr'. }
    iMod ("Hclose" with "[Hn]") as "_". { iNext. iExists _. by iFrame. }
    iModIntro. wp_pure.
    (* add *)
    iInstr "Hcode".
    (* store to a_data+1 *)
    wp_instr.
    iMod (inv_acc with "HIv") as "[>Hv Hclose]"; auto.
    iDestruct "Hv" as (n') "(Hn' & %Hn')".
    iInstr "Hcode". solve_addr'.
    iMod ("Hclose" with "[Hn']") as "_".
    { iNext. iExists _. iFrame. iPureIntro. lia. }
    iModIntro. wp_pure.
    (* cont *)
    iGo "Hcode".

    (* close the invariant with the code *)
    iMod ("Hclose_code" with "[$Hcode $Hna]") as "Hna".
    iApply "Hφ". iFrame.
  Qed.

  Lemma counter_full_run_spec (a_init: Addr) b_adv e_adv w1 w2 wdat rmap adv :
    let a_code := (a_init ^+ code_off)%a in
    let a_data := (a_code ^+ data_off)%a in
    let a_end := (a_code ^+ (data_off + end_off))%a in
    ContiguousRegion a_init (code_off + data_off + end_off) →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    Forall (λ w, is_cap w = false) adv →
    (b_adv + length adv)%a = Some e_adv →

  ⊢ (   inv with_adv.invN (∃ n : Z, (a_data ^+ 1)%a ↦ₐ WInt n ∗ ⌜0 ≤ n⌝)
      ∗ PC ↦ᵣ WCap RWX a_init a_end a_init
      ∗ r_t0 ↦ᵣ WCap RWX b_adv e_adv b_adv
      ∗ r_t1 ↦ᵣ w1
      ∗ r_t2 ↦ᵣ w2
      ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜is_cap w = false⌝)
      ∗ codefrag a_init (counter_init a_init)
      ∗ codefrag a_code (counter_code a_code)
      ∗ a_data ↦ₐ wdat
      ∗ ([∗ map] a↦w ∈ mkregion b_adv e_adv adv, a ↦ₐ w)
      ∗ na_own logrel_nais ⊤
      -∗ WP Seq (Instr Executable) {{ λ _, True }})%I.
  Proof.
    iIntros (? ? ? ? Hrdom ? ?) "(#HI & HPC & Hr0 & Hr1 & Hr2 & Hrmap & Hinit & Hcode & Hdat & Hadv & Hna)".

    (* The capability to the adversary is safe and we can also jmp to it *)
    iDestruct (mkregion_sepM_to_sepL2 with "Hadv") as "Hadv". done.
    iDestruct (region_integers_alloc' _ _ _ b_adv _ RWX with "Hadv") as ">#Hadv". done.
    iDestruct (jmp_to_unknown with "Hadv") as "#Hcont".

    iApply (counter_init_spec a_init with "[-]"). solve_addr'. iFrame.
    simpl. rewrite (_: a_init ^+ (_ + _ + _) = a_end)%a. 2: solve_addr'. iFrame.
    rewrite (_: a_init ^+ (_ + _) = a_data)%a. 2: solve_addr'. iFrame.
    iNext. iIntros "(HPC & Hr0 & Hr1 & Hr2 & Hdat & _)".

    (* Allocate an invariant for the points-to at a_data containing the capability to a_data+1 *)
    iMod (inv_alloc (N.@"cap") _ (a_data ↦ₐ WCap RWX a_init a_end (a_data ^+ 1)%a)
            with "Hdat") as "#HIcap".

    (* Allocate a non-atomic invariant for the code of the code routine *)
    iMod (na_inv_alloc logrel_nais _ (N.@"code") (codefrag a_code (counter_code a_code))
           with "Hcode") as "#HIcode".

    (* Show that the E-capability to the code: routine is safe *)
    iAssert (interp (WCap E a_code a_end a_code)) as "#Hcode_safe".
    { rewrite /interp /= (fixpoint_interp1_eq (WCap E _ _ _)) /=. iIntros (rr).
      iIntros "!> !> ([%Hrfull #Hrsafe] & Hrr & Hna)". rewrite /interp_conf.

      (* unpack the registers *)
      destruct (Hrfull r_t0) as [w0' Hr0'].
      destruct (Hrfull r_t1) as [w1' Hr1'].
      destruct (Hrfull r_t2) as [w2' Hr2'].
      unfold registers_mapsto.
      rewrite -insert_delete.
      iDestruct (big_sepM_insert with "Hrr") as "[HPC Hrr]".
        by rewrite lookup_delete.
      iDestruct (big_sepM_delete _ _ r_t0 with "Hrr") as "[Hr0 Hrr]".
        by rewrite lookup_delete_ne //.
      iDestruct (big_sepM_delete _ _ r_t1 with "Hrr") as "[Hr1 Hrr]".
        by rewrite !lookup_delete_ne //.
      iDestruct (big_sepM_delete _ _ r_t2 with "Hrr") as "[Hr2 Hrr]".
        by rewrite !lookup_delete_ne //.

      (* the continuation is safe, and we can jump to it *)
      iAssert (interp w0') as "Hv0". by iApply "Hrsafe"; eauto; done.
      iDestruct (jmp_to_unknown with "Hv0") as "#Hcont_prog".

      (* apply the spec *)
      iApply (counter_code_spec a_init with "[-]"). solve_addr'.
      rewrite (_: (a_init ^+ _) ^+ _ = a_data)%a. 2: solve_addr'.
      rewrite (_: (a_init ^+ _) ^+ (_ + _) = a_end)%a. 2: solve_addr'.
      iFrame. iFrame "HIcap HIcode HI".
      iIntros "!>" (n) "(HPC & Hr0 & Hr1 & Hr2 & Hcode)".

      (* put the registers back together *)
      iDestruct (big_sepM_sep _ (λ k v, interp v)%I with "[Hrr]") as "Hrr".
      { iSplitL. by iApply "Hrr". iApply big_sepM_intuitionistically_forall. iModIntro.
        iIntros (r' ? HH). repeat eapply lookup_delete_Some in HH as [? HH].
        iApply ("Hrsafe" $! r'); auto. }
      iDestruct (big_sepM_insert with "[$Hrr $Hr2]") as "Hrr". by rewrite lookup_delete.
        by iApply interp_int. rewrite insert_delete.
      iDestruct (big_sepM_insert with "[$Hrr $Hr1]") as "Hrr".
        by rewrite lookup_insert_ne // lookup_delete.
        by iApply interp_int. rewrite insert_commute // insert_delete.
      iDestruct (big_sepM_insert with "[$Hrr $Hr0]") as "Hrr".
        by rewrite !lookup_insert_ne // lookup_delete.
        by iApply "Hv0". do 2 rewrite (insert_commute _ r_t0) //;[]. rewrite insert_delete.

      (* jmp to continuation *)
      iApply "Hcont_prog". 2: iFrame. iPureIntro.
      rewrite !dom_insert_L dom_delete_L regmap_full_dom //. set_solver+. }

    (* put the registers back together *)
    iDestruct (big_sepM_mono _ (λ k v, k ↦ᵣ v ∗ interp v)%I with "Hrmap") as "Hrmap".
    { intros ? w ?. cbn. iIntros "[? %Hw]". iFrame. destruct w; try inversion Hw.
      iApply interp_int. }
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hrmap $Hr2]") as "Hrmap".
      by rewrite elem_of_gmap_dom_none Hrdom; set_solver+.
      by iApply interp_int.
    iDestruct (big_sepM_insert _ _ r_t1 with "[$Hrmap $Hr1]") as "Hrmap".
      by rewrite lookup_insert_ne // elem_of_gmap_dom_none Hrdom; set_solver+.
      by iApply "Hcode_safe".
    iDestruct (big_sepM_insert _ _ r_t0 with "[$Hrmap $Hr0]") as "Hrmap".
      by rewrite !lookup_insert_ne // elem_of_gmap_dom_none Hrdom; set_solver+.
      by iApply "Hadv".

    iApply (wp_wand with "[-]").
    { iApply "Hcont". 2: iFrame. iPureIntro.
      rewrite !dom_insert_L Hrdom !singleton_union_difference_L !all_registers_union_l. set_solver+. }
    eauto.
  Qed.

End counter.

Local Ltac solve_addr' :=
  repeat match goal with x := _ |- _ => subst x end;
  unfold code_off, data_off, end_off in *; solve_addr.

Program Definition counter_inv (a_init: Addr) : memory_inv :=
  MkMemoryInv
    (λ m, ∃ n, m !! (a_init ^+ (code_off + data_off + 1))%a = Some (WInt n) ∧ 0 ≤ n)
    {[ (a_init ^+ (code_off + data_off + 1))%a ]}
    _.
Next Obligation.
  intros a_init m m' H. cbn in *.
  specialize (H (a_init ^+ (code_off + data_off + 1))%a). feed specialize H. by set_solver.
  destruct H as [w [? ?] ]. by simplify_map_eq.
Qed.

Definition counterN : namespace := nroot .@ "counter".

Lemma adequacy `{MachineParameters} (P Adv: prog) (m m': Mem) (reg reg': Reg) es:
  prog_instrs P =
    counter_init (prog_start P) ++
    counter_code (prog_start P ^+ code_off)%a ++
    counter_data →
  with_adv.is_initial_memory P Adv m →
  with_adv.is_initial_registers P Adv reg →
  Forall (λ w, is_cap w = false) (prog_instrs Adv) →

  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  ∃ n, m' !! (prog_start P ^+ (code_off + data_off + 1))%a = Some (WInt n) ∧ 0 ≤ n.
Proof.
  intros HP Hm Hr HAdv Hstep.
  generalize (prog_size P). rewrite HP /=. intros.

  (* Prove the side-conditions over the memory invariant *)
  eapply (with_adv.template_adequacy P Adv (counter_inv (prog_start P)) m m' reg reg' es); auto.
  { cbn. unfold with_adv.is_initial_memory in Hm. destruct Hm as (Hm & _ & _).
    exists 0; split; [| done]. eapply lookup_weaken; [| apply Hm]. rewrite /prog_region mkregion_lookup.
    { exists (Z.to_nat (code_off + data_off + 1)). split. done. rewrite HP; done. }
    { apply prog_size. } }
  { cbn. apply elem_of_subseteq_singleton, elem_of_list_to_set, elem_of_region_addrs. solve_addr'. }

  intros * Hrdom. iIntros "(#HI & Hna & HPC & Hr0 & Hrmap & Hadv & Hprog)".
  set (a_init := prog_start P) in *.
  set (a_code := (a_init ^+ code_off)%a) in *.
  set (a_data := (a_code ^+ data_off)%a) in *.

  (* Extract the code & data regions from the program resources *)
  iAssert (codefrag a_init (counter_init a_init) ∗
           codefrag a_code (counter_code a_code) ∗
           (∃ w, a_data ↦ₐ w))%I
    with "[Hprog]" as "(Hinit & Hcode & Hdat)".
  { rewrite /codefrag /region_mapsto.
    set M := filter _ _.
    set Minit := mkregion a_init a_code (counter_init a_init).
    set Mcode := mkregion a_code a_data (counter_code a_code).
    set Mdat := mkregion a_data (a_data ^+ 1)%a [WInt 7777].

    assert (Mcode ##ₘ Mdat).
    { apply map_disjoint_spec.
      intros ? ? ? [? [? ?%lookup_lt_Some] ]%mkregion_lookup [? [? ?%lookup_lt_Some] ]%mkregion_lookup.
      all: solve_addr'. }

    assert (Minit ##ₘ (Mcode ∪ Mdat)).
    { apply map_disjoint_spec.
      intros ? ? ? [? [? ?%lookup_lt_Some] ]%mkregion_lookup.
      2: solve_addr'. intros [HH|HH]%lookup_union_Some; auto.
      all: apply mkregion_lookup in HH as [? [? ?%lookup_lt_Some] ]; solve_addr'. }

    assert (Minit ∪ (Mcode ∪ Mdat) ⊆ M) as HM.
    { apply map_subseteq_spec. intros a w. intros [Ha| [Ha|Ha]%lookup_union_Some]%lookup_union_Some.
      4,5: assumption.
      all: apply mkregion_lookup in Ha as [i [? HH] ]; [| solve_addr'].
      all: apply map_filter_lookup_Some_2;
        [| cbn; apply not_elem_of_singleton; apply lookup_lt_Some in HH; solve_addr'].
      all: subst; rewrite mkregion_lookup; [| rewrite HP; solve_addr'].
      { eexists. split; eauto. rewrite HP. by apply lookup_app_l_Some. }
      { exists (Z.to_nat (i+code_off)). split. solve_addr'. rewrite HP.
        apply lookup_app_Some. right. split. solve_addr'. apply lookup_app_l_Some.
        rewrite (_: _ - _ = i)%nat //. solve_addr'. }
      { exists (Z.to_nat (code_off + data_off)). destruct i; [| by inversion HH]. split. solve_addr'.
        rewrite HP. apply lookup_app_Some. right. split. solve_addr'.
        apply lookup_app_Some. right. split. solve_addr'. done. } }

    iDestruct (big_sepM_subseteq with "Hprog") as "Hprog". apply HM.
    iDestruct (big_sepM_union with "Hprog") as "[Hinit Hprog]". assumption.
    iDestruct (big_sepM_union with "Hprog") as "[Hcode Hdat]". assumption.
    iDestruct (mkregion_sepM_to_sepL2 with "Hinit") as "Hinit". solve_addr'.
    iDestruct (mkregion_sepM_to_sepL2 with "Hcode") as "Hcode". solve_addr'.
    iDestruct (mkregion_sepM_to_sepL2 with "Hdat") as "Hdat". solve_addr'.
    iFrame. iExists _. rewrite region_addrs_cons. cbn. by iDestruct "Hdat" as "[? ?]".
    solve_addr'. }
  iDestruct "Hdat" as (wdat) "Hdat".

  assert (is_Some (rmap !! r_t1)) as [w1 Hr1].
  { rewrite elem_of_gmap_dom Hrdom. set_solver+. }
  assert (is_Some (rmap !! r_t2)) as [w2 Hr2].
  { rewrite elem_of_gmap_dom Hrdom. set_solver+. }
  iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[[Hr1 _] Hrmap]"; eauto.
  iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[[Hr2 _] Hrmap]".
    by rewrite lookup_delete_ne //.

  iApply (counter_full_run_spec with "[$Hadv $Hr0 $Hr1 $Hr2 $Hinit $Hrmap $Hna $Hdat $Hcode HPC]"); auto.
  solve_addr'. by rewrite !dom_delete_L Hrdom; set_solver+. by apply prog_size.
  rewrite (_: _ ^+ (_ + _) = prog_end P)%a. 2: solve_addr'. iFrame.

  (* Show the invariant for the counter value using the invariant from the adequacy theorem *)
  iApply (inv_alter with "HI").
  iIntros "!> !> H". rewrite /minv_sep. iDestruct "H" as (mι) "(Hm & %Hmιdom & %Hι)".
  cbn in Hι. destruct Hι as (n & Hι & Hn).
  rewrite (_: a_init ^+ _ = (a_data ^+ 1))%a in Hι. 2: solve_addr'.
  iDestruct (big_sepM_delete _ _ (a_data ^+ 1)%a (WInt n) with "Hm") as "[Hn Hm]". done.
  iSplitL "Hn". by eauto. iIntros "Hn'". iDestruct "Hn'" as (n') "(Hn' & %)".
  iExists (<[ (a_data ^+ 1)%a := WInt n' ]> mι). iSplitL "Hm Hn'".
  { iDestruct (big_sepM_insert with "[$Hm $Hn']") as "Hm". by apply lookup_delete.
    rewrite insert_delete //. }
  iPureIntro. split. rewrite dom_insert_L Hmιdom /Hmιdom /=. 2: exists n'.
  all: rewrite (_: a_init ^+ _ = (a_data ^+ 1))%a; [| solve_addr']. set_solver+.
  rewrite lookup_insert //.
Qed.
