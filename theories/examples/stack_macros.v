From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel monotone.
From cap_machine Require Export addr_reg_sample region_macros contiguous malloc.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MonRef: MonRefG (leibnizO _) CapR_rtc Σ} {nainv: logrel_na_invs Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS). 
  Implicit Types W : WORLD.
  
  (* ---------------------------- Helper Lemmas --------------------------------------- *)
  (* TODO: move to lang *)
  Lemma isCorrectPC_bounds_alt p g b e (a0 a1 a2 : Addr) :
    isCorrectPC (inr (p, g, b, e, a0))
    → isCorrectPC (inr (p, g, b, e, a2))
    → (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z
    → isCorrectPC (inr (p, g, b, e, a1)).
  Proof.
    intros Hvpc0 Hvpc2 [Hle0 Hle2].
    apply Z.lt_eq_cases in Hle2 as [Hlt2 | Heq2].
    - apply isCorrectPC_bounds with a0 a2; auto.
    - apply z_of_eq in Heq2. rewrite Heq2. auto.
  Qed.

  Lemma isWithinBounds_bounds_alt p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Lemma isWithinBounds_bounds_alt' p g b e (a0 a1 a2 : Addr) :
    withinBounds (p,g,b,e,a0) = true ->
    withinBounds (p,g,b,e,a2) = true ->
    (a0 ≤ a1)%Z ∧ (a1 < a2)%Z ->
    withinBounds (p,g,b,e,a1) = true.
  Proof.
    intros Hwb0 Hwb2 [Hle0 Hle2].
    rewrite /withinBounds.
    apply andb_true_iff.
    apply andb_true_iff in Hwb0 as [Hleb0 Hlea0].
    apply andb_true_iff in Hwb2 as [Hleb2 Hlea2].
    split; rewrite /leb_addr /ltb_addr; first [ apply Z.leb_le | apply Z.ltb_lt ].
    - apply Z.leb_le in Hleb0. apply Z.ltb_lt in Hlea0. lia.
    - apply Z.leb_le in Hleb2. apply Z.ltb_lt in Hlea2. lia.
  Qed.

  Lemma le_addr_withinBounds p l b e a:
    (b <= a)%a → (a < e)%a →
    withinBounds (p, l, b, e, a) = true .
  Proof.
    intros. eapply andb_true_iff. unfold ltb_addr, leb_addr.
    unfold le_addr, lt_addr in *. rewrite Z.leb_le Z.ltb_lt. lia.
  Qed.

  Definition isCorrectPC_range p g b e a0 an :=
    ∀ ai, (a0 <= ai)%a ∧ (ai < an)%a → isCorrectPC (inr (p, g, b, e, ai)).

  Lemma isCorrectPC_inrange p g b (e a0 an a: Addr) :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a < an)%Z →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    unfold isCorrectPC_range. move=> /(_ a) HH ?. apply HH. eauto.
  Qed.

  Lemma isCorrectPC_contiguous_range p g b e a0 an a l :
    isCorrectPC_range p g b e a0 an →
    contiguous_between l a0 an →
    a ∈ l →
    isCorrectPC (inr (p, g, b, e, a)).
  Proof.
    intros Hr Hc Hin.
    eapply isCorrectPC_inrange; eauto.
    eapply contiguous_between_middle_bounds'; eauto.
  Qed.

  Lemma isCorrectPC_range_perm p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    p = RX ∨ p = RWX ∨ p = RWLX.
  Proof.
    intros Hr H0n.
    assert (isCorrectPC (inr (p, g, b, e, a0))) as HH by (apply Hr; solve_addr).
    inversion HH; auto.
  Qed.

  (* Helper lemma to extract registers from a big_sepL2 *)
  Lemma big_sepL2_extract_l {A B : Type} (i : nat) (ai : A) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
    a !! i = Some ai ->
    (([∗ list] a_i;b_i ∈ a;b, φ a_i b_i) -∗
     ([∗ list] a_i;b_i ∈ (delete i a);(delete i b), φ a_i b_i) ∗ ∃ b, φ ai b)%I.
  Proof. 
    iIntros (Hsome) "Hl".
    iDestruct (big_sepL2_length with "Hl") as %Hlength.      
    assert (take i a ++ drop i a = a) as Heqa;[apply take_drop|]. 
    assert (take i b ++ drop i b = b) as Heqb;[apply take_drop|]. 
    rewrite -Heqa -Heqb.
    iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
    { apply lookup_lt_Some in Hsome.
      do 2 (rewrite take_length_le;[|lia]). done. 
    }
    apply take_drop_middle in Hsome as Hcons.
    assert (ai :: drop (S i) a = drop i a) as Hh.
    { apply app_inv_head with (take i a). congruence. }
    rewrite -Hh.
    iDestruct (big_sepL2_length with "Hdrop") as %Hlength'.      
    destruct (drop i b);[inversion Hlength'|].
    iDestruct "Hdrop" as "[Hφ Hdrop]".
    iSplitR "Hφ";[|eauto].
    rewrite Hcons. iDestruct (big_sepL2_app with "Htake Hdrop") as "Hl".
    rewrite Heqb. rewrite (delete_take_drop a).
    rewrite (delete_take_drop b).
    assert (drop (S i) b = l) as Hb.
    { apply app_inv_head with (take i b ++ [b0]). repeat rewrite -app_assoc.
      repeat rewrite -cons_middle. rewrite (drop_S _ _ _ b0 l);auto.
      apply app_inv_head with (take i b). rewrite Heqb. apply take_drop. }
    rewrite Hb. iFrame. 
  Qed.

  Lemma big_sepL2_extract {A B : Type} (i : nat) (ai : A) (bi : B) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
    a !! i = Some ai -> b !! i = Some bi ->
    (([∗ list] a_i;b_i ∈ a;b, φ a_i b_i) -∗
     ([∗ list] a_i;b_i ∈ (delete i a);(delete i b), φ a_i b_i) ∗ φ ai bi)%I.
  Proof. 
    iIntros (Hsome Hsome') "Hl".
    iDestruct (big_sepL2_length with "Hl") as %Hlength.      
    assert (take i a ++ drop i a = a) as Heqa;[apply take_drop|]. 
    assert (take i b ++ drop i b = b) as Heqb;[apply take_drop|]. 
    rewrite -Heqa -Heqb.
    iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
    { apply lookup_lt_Some in Hsome.
      do 2 (rewrite take_length_le;[|lia]). done. 
    }
    apply take_drop_middle in Hsome as Hcons.
    apply take_drop_middle in Hsome' as Hcons'.
    assert (ai :: drop (S i) a = drop i a) as Hh.
    { apply app_inv_head with (take i a). congruence. }
    assert (bi :: drop (S i) b = drop i b) as Hhb.
    { apply app_inv_head with (take i b). congruence. }
    rewrite -Hh. rewrite -Hhb.
    iDestruct "Hdrop" as "[Hφ Hdrop]".
    iSplitR "Hφ";[|eauto].
    rewrite Hcons. rewrite Hcons'. iDestruct (big_sepL2_app with "Htake Hdrop") as "Hl".
    rewrite (delete_take_drop b). rewrite (delete_take_drop a). iFrame. 
  Qed.

  Lemma delete_eq {A : Type} (a : list A) i :
    strings.length a ≤ i -> a = delete i a.
  Proof.
    revert i. induction a; intros i Hle.
    - done.
    - destruct i; [inversion Hle|].
      simpl. f_equiv. apply IHa. simpl in Hle. lia.
  Qed. 
  
  Lemma big_sepL2_close_l {A B : Type} (i : nat) (ai : A) (bi : B) (a : list A) (b : list B) (φ : A -> B -> iProp Σ) :
    length a = length b ->
    a !! i = Some ai ->
    (([∗ list] a_i;b_i ∈ (delete i a);(delete i b), φ a_i b_i) ∗ φ ai bi -∗
                                                               ([∗ list] a_i;b_i ∈ a;<[i:= bi]> b, φ a_i b_i) )%I.
  Proof. 
    iIntros (Hlen Hsome) "[Hl Hb]".
    iDestruct (big_sepL2_length with "Hl") as %Hlength.
    repeat rewrite delete_take_drop.
    apply lookup_lt_Some in Hsome as Hlt.
    assert (i < strings.length b) as Hlt';[lia|].
    iDestruct (big_sepL2_app_inv with "Hl") as "[Htake Hdrop]". 
    { repeat rewrite take_length. lia. }
    apply take_drop_middle in Hsome as Hcons.
    assert (ai :: drop (S i) a = drop i a) as Hh.
    { apply app_inv_head with (take i a). rewrite Hcons. by rewrite take_drop. }
    iAssert ([∗ list] y1;y2 ∈ ai :: drop (S i) a;bi :: drop (S i) b, φ y1 y2)%I
      with "[Hb Hdrop]" as "Hdrop";[iFrame|].
    rewrite Hh.
    iDestruct (big_sepL2_app with "Htake Hdrop") as "Hab".
    rewrite take_drop.
    assert (take i b ++ bi :: drop (S i) b = <[i:=bi]> b) as ->;[|iFrame].
    assert (<[i:=bi]> b !! i = Some bi) as Hsome'.
    { apply list_lookup_insert. lia. }
    apply take_drop_middle in Hsome'. rewrite -Hsome'.
    rewrite take_insert;[|lia]. rewrite drop_insert;[|lia]. done. 
  Qed.

  Lemma delete_insert_list {A : Type} i (l : list A) (a : A) :
    <[i := a]> (delete 0 l) = delete 0 (<[S i := a]> l).
  Proof.
    induction l.
    - done.
    - simpl in *. destruct l; auto. 
  Qed.

  Lemma insert_delete_list {A : Type} (l : list A) (a : A) :
    delete 0 (<[0 := a]> l) = delete 0 l.
  Proof.
    induction l; done.
  Qed.

  Lemma big_sepL2_split_at {A B: Type} `{EqDecision A} `{Countable A}
        (k: nat) (l1: list A) (l2: list B) (φ : A → B → iProp Σ):
    ([∗ list] a;b ∈ l1;l2, φ a b) -∗
    ([∗ list] a;b ∈ (take k l1);(take k l2), φ a b) ∗ ([∗ list] a;b ∈ (drop k l1);(drop k l2), φ a b).
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_length with "H") as %?.
    rewrite -{1}(take_drop k l1) -{1}(take_drop k l2).
    iDestruct (big_sepL2_app' with "H") as "[? ?]".
    { rewrite !take_length. lia. }
    iFrame.
  Qed.

  (* -------------------------------- LTACS ------------------------------------------- *)
  Ltac iPrologue_pre :=
    match goal with
    | Hlen : length ?a = ?n |- _ =>
      let a' := fresh "a" in
      destruct a as [| a' a]; inversion Hlen; simpl
    end.

  Ltac iPrologue prog :=
    (try iPrologue_pre);
    iDestruct prog as "[Hi Hprog]";
    iApply (wp_bind (fill [SeqCtx])).

  Ltac iEpilogue prog :=
    iNext; iIntros prog; iSimpl;
    iApply wp_pure_step_later;auto;iNext.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end.

  Ltac iCorrectPC i j :=
    eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
    cbn; solve [ repeat constructor ].

  Ltac iContiguous_next Ha index :=
    apply contiguous_of_contiguous_between in Ha;
    generalize (contiguous_spec _ Ha index); auto.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_instrs (f : Z) :=
    [move_r r_t1 PC;
    getb r_t2 r_t1;
    geta r_t3 r_t1;
    sub_r_r r_t2 r_t2 r_t3;
    lea_r r_t1 r_t2;
    load_r r_t1 r_t1;
    lea_z r_t1 f;
    move_z r_t2 0;
    move_z r_t3 0;
    load_r r_t1 r_t1]. 

  Definition fetch f a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(fetch_instrs f), a_i ↦ₐ[p] w_i)%I. 

  (* fetch spec *)
  Lemma fetch_spec f a pc_p pc_p' pc_g pc_b pc_e a_first a_last b_link e_link a_link entry_a wentry φ w1 w2 w3:
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->
    contiguous_between a a_first a_last ->
    withinBounds (RW, Global, b_link, e_link, entry_a) = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ fetch f a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
    ∗ ▷ entry_a ↦ₐ[RW] wentry
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ fetch f a pc_p'
            (* the newly allocated region *)
            ∗ r_t1 ↦ᵣ wentry ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z
            ∗ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
            ∗ entry_a ↦ₐ[RW] wentry
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb Hentry) "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* move r_t1 PC *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t1)".
    (* getb r_t2 r_t1 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply getb_i|auto|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* geta r_t3 r_t1 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply geta_i|auto|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* sub r_t2 r_t2 r_t3 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t3 $Hr_t2]");
      [apply sub_r_r_i|auto|iContiguous_next Hcont 3|apply Hfl|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t1 r_t2 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    assert ((a_first + (pc_b - a_first))%a = Some pc_b) as Hlea;[solve_addr|]. 
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply lea_r_i|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* load r_t1 r_t1 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iAssert (⌜(pc_b ≠ a3)%Z⌝)%I as %Hneq.
    { iIntros (Hcontr);subst.
      iDestruct (cap_duplicate_false with "[$Hi $Hpc_b]") as %Hne; auto.
      apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      destruct Hvpc as [Hcontr | [Hcontr | Hcontr] ]; done.
    }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Hpc_b]");
      [|apply load_r_i|auto|iCorrectPC a_first a_last| |iContiguous_next Hcont 5|..].
    { exact (inr (RW, Global, b_link, e_link, a_link)). }
    { apply contiguous_between_length in Hcont as Hlen.
      assert (pc_b < pc_e)%Z as Hle.
      { eapply isCorrectPC_contiguous_range in Hvpc as Hwb';[|eauto|apply elem_of_cons;left;eauto].
        inversion Hwb'. solve_addr. }
      apply isCorrectPC_range_perm in Hvpc as Heq; [|revert Hlen; clear; solve_addr].      
      split;[destruct Heq as [-> | [-> | ->] ]; auto|].
      apply andb_true_intro. split;[apply Z.leb_le;solve_addr|apply Z.ltb_lt;auto].
    }
    { destruct (pc_b =? a3)%a; [done|iFrame]. auto. }
    destruct ((pc_b =? a3)%a) eqn:Hcontr;[apply Z.eqb_eq in Hcontr;apply z_of_eq in Hcontr;congruence|clear Hcontr]. 
    iEpilogue "(HPC & Hr_t1 & Hi & Hpc_b)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 f *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hentry|auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply move_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 7|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 0 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
      [apply move_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 8|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    destruct l;[|inversion Hlength].
    apply contiguous_between_last with (ai:=a7) in Hcont as Hlink;[|auto]. 
    iPrologue "Hprog".
    iAssert (⌜(entry_a ≠ a7)%Z⌝)%I as %Hneq'.
    { iIntros (Hcontr);subst.
      iDestruct (cap_duplicate_false with "[$Hi $Ha_entry]") as %Hne; auto.
      apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct pc_p'; auto. destruct pc_p; inversion Hfl.
      destruct Hvpc as [Hcontr | [Hcontr | Hcontr] ]; done.
    }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Ha_entry]");
      [exact wentry|apply load_r_i|auto|iCorrectPC a_first a_last|auto|apply Hlink|..].
    { destruct (entry_a =? a7)%a; auto. }
    destruct ((entry_a =? a7)%a) eqn:Hcontr;[apply Z.eqb_eq in Hcontr;apply z_of_eq in Hcontr;congruence|clear Hcontr]. 
    iEpilogue "(HPC & Hr_t1 & Hi & Hentry_a)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame. 
    repeat iDestruct "Hprog_done" as "[$ Hprog_done]". 
    iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* The assert macro relies on a convention for the failure flag. This file contains the 
     failure subroutine *)

  (* The convention for the failure flag: one address after the last instruction of the failure subroutine *)
  (* failing the assert will set the flag to 1 and then crash the program to a Failed configuration. The flag 
     capability is at one address after the instructions *)
  Definition assert_fail_instrs :=
    [move_r r_t1 PC;
    lea_z r_t1 6;
    load_r r_t1 r_t1; 
    store_z r_t1 1;
    move_z r_t1 0;
    fail_end].

  Definition assert_fail a p :=
    ([∗ list] a_i;w_i ∈ a;(assert_fail_instrs), a_i ↦ₐ[p] w_i)%I. 

  (* f_a is the offset of the failure subroutine in the linking table *)
  (* assert r z asserts that the register r contains the integer z *)
  (* r is assumed not to be r_t1 *)
  Definition assert_r_z_instrs f_a r z :=
    fetch_instrs f_a ++ 
    [sub_r_z r r z;
    jnz r_t1 r;
    move_z r_t1 0].

  Definition assert_r_z a f_a r z p :=
    ([∗ list] a_i;w_i ∈ a;(assert_r_z_instrs f_a r z), a_i ↦ₐ[p] w_i)%I. 

  (* Spec for assertion success *)
  (* Since we are not jumping to the failure subroutine, we do not need any assumptions 
     about the failure subroutine *)
  Lemma assert_r_z_success a f_a r z pc_p pc_p' pc_g pc_b pc_e a_first a_last
        b_link e_link a_link a_entry fail_cap w_r φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    PermFlows pc_p pc_p' →
    contiguous_between a a_first a_last →
    (* linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (* condition for assertion success *)
    (w_r = inl z) ->

    ▷ assert_r_z a f_a r z pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ[RW] fail_cap
    ∗ ▷ r ↦ᵣ w_r
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t3 ↦ᵣ w)
    ∗ ▷ (r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ r ↦ᵣ inl 0%Z
         ∗ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ assert_r_z a f_a r z pc_p'
         ∗ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ[RW] fail_cap
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb Htable Hsuccess)
            "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
     (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3". 
    iApply (fetch_spec with "[$HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b Hφ Hprog Hr]");
      [|apply Hfl|apply Hcont_fetch|apply Hwb|apply Htable|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a0 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* sub_r_z r r z *)
    destruct l';[inversion Hlength_rest|].
    inversion Hsuccess. subst w_r.  
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr]");
      [apply sub_r_z_i|right;left;eauto|iContiguous_next Hcont_rest 0|apply Hfl|iCorrectPC link a_last|..]. 
    iEpilogue "(HPC & Hi & Hr)"; iCombine "Hfetch" "Hi" as "Hprog_done". 
    (* jnz r_t1 r *)
    rewrite /= Z.sub_diag. 
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply jnz_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|].
    iEpilogue "(HPC & Hinstr & Hr_t1 & Hr)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
    (* move r_t1 0 *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=a1) in Hcont_rest as Hlink';[|auto].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply move_z_i|apply Hfl|iCorrectPC link a_last|apply Hlink'|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Continuation *)
    iApply "Hφ". iFrame.
    rewrite Heqapp /=. iDestruct "Hprog_done" as "(?&?&?&?)". iFrame. done.
  Qed.

  (* Spec for assertion failure *)
  (* When the assertion fails, the program jumps to the failure subroutine, sets the 
     flag (which by convention is one address after subroutine) and Fails *)
  Lemma assert_r_z_fail a f_a r z pc_p pc_p' pc_g pc_b pc_e a_first a_last z_r
        b_link e_link a_link a_entry
        f_b f_e f_a_first f_a_last a' a_env (* fail subroutine *)
        flag_p flag_p' flag_b flag_e flag_a (* flag capability *) :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    PermFlows pc_p pc_p' → 
    contiguous_between a a_first a_last →
    (* linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (* failure subroutine assumptions *)
    isCorrectPC_range RX Global f_b f_e f_a_first f_a_last →
    contiguous_between a' f_a_first f_a_last →
    (f_a_first + (length a'))%a = Some a_env ->
    withinBounds (RX,Global,f_b,f_e,a_env) = true ->
    (* flag assumptions *)
    PermFlows flag_p flag_p' →
    withinBounds (flag_p,Global,flag_b,flag_e,flag_a) = true ∧ writeAllowed flag_p = true ->
    (* condition for assertion success *)
    (z_r ≠ z) ->

    (* the assert and assert failure subroutine programs *)
    {{{ ▷ assert_r_z a f_a r z pc_p'
    ∗ ▷ assert_fail a' RX
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    (* linking table and assertion flag *)
    ∗ ▷ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link) (* the linking table capability *)
    ∗ ▷ a_entry ↦ₐ[RW] inr (E,Global,f_b,f_e,f_a_first) (* the capability to the failure subroutine *)
    ∗ ▷ a_env ↦ₐ[RX] inr (flag_p,Global,flag_b,flag_e,flag_a) (* the assertion flag capability *)
    ∗ ▷ (∃ w, flag_a ↦ₐ[flag_p'] w) (* the assertion flag *)
    (* registers *)
    ∗ ▷ r ↦ᵣ inl z_r
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t3 ↦ᵣ w) }}}
      
      Seq (Instr Executable)
      
    {{{ RET FailedV; r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ (∃ z, r ↦ᵣ inl z ∧ ⌜z ≠ 0⌝)
         ∗ PC ↦ᵣ inr (RX, Global, f_b, f_e,^(f_a_last + (-1))%a)
         ∗ assert_r_z a f_a r z pc_p' ∗ assert_fail a' RX
         ∗ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ[RW] inr (E,Global,f_b,f_e,f_a_first)
         ∗ a_env ↦ₐ[RX] inr (flag_p,Global,flag_b,flag_e,flag_a) ∗ flag_a ↦ₐ[flag_p'] inl 1%Z }}}. 
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb Htable Hvpc' Hcont' Henv Henvwb Hfl' [Hwb' Hwa] Hfailure φ) 
            "(>Hprog & >Hprog' & >HPC & >Hpc_b & >Ha_entry & >Ha_env & >Hflag & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3) Hφ".
    iDestruct "Hflag" as (flag_w) "Hflag". 
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3". 
    iApply (fetch_spec with "[$HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b Hφ Hprog Hr Hprog' Ha_env Hflag]");
      [|apply Hfl|apply Hcont_fetch|apply Hwb|apply Htable|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a0 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* sub_r_z r r z *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr]");
      [apply sub_r_z_i|right;left;eauto|iContiguous_next Hcont_rest 0|apply Hfl|iCorrectPC link a_last|..]. 
    iEpilogue "(HPC & Hi & Hr)"; iCombine "Hi" "Hfetch" as "Hprog_done". 
    (* jnz r_t1 r *)
    iPrologue "Hprog".
    iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply jnz_i|apply Hfl|iCorrectPC link a_last|simpl;revert Hfailure;clear;intros Hne Hcontr;simplify_eq;lia|..]. 
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iSimpl in "HPC"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hprog" "Hprog_done" as "Hprog_done".
    (* FAILURE SUBROUTINE *)
    iDestruct (big_sepL2_length with "Hprog'") as %Hlength'. 
    destruct a';[inversion Hlength'|].
    apply contiguous_between_cons_inv_first in Hcont' as Heq. subst a1.
    (* move r_t1 PC *)
    destruct a';[inversion Hlength'|].
    iAssert (⌜r_t1 ≠ PC⌝)%I as %Hne. 
    { iIntros (Hcontr). rewrite Hcontr. iDestruct (regname_dupl_false with "Hr_t1 HPC") as "H". done. }
    iPrologue "Hprog'".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply move_r_i|apply PermFlows_refl|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 0|auto|..]. 
    iEpilogue "(HPC & Hi & Hr_t1)". iRename "Hi" into "Hprog_done'". 
    (* lea r_t1 5 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog".
    assert ((f_a_first + 6)%a = Some a_env) as Hlea.
    { simpl in Henv. inversion Hlength' as [Heq]. rewrite Heq in Henv. auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply PermFlows_refl|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 1|apply Hlea|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done'" as "Hprog_done'".
    (* load r_t1 r_t1 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog".
    iAssert (⌜(a_env =? a2)%a = false⌝)%I as %Hne'.
    { destruct (decide (a_env = a2)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
      iDestruct (cap_duplicate_false with "[$Hi $Ha_env]") as "H";auto. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Ha_env]");
      [|apply load_r_i|apply PermFlows_refl|iCorrectPC f_a_first f_a_last|split;auto|iContiguous_next Hcont' 2|
       rewrite Hne';iFrame|rewrite Hne'];auto. 
    iEpilogue "(HPC & Hr_t1 & Hi & Ha_env)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t1 1 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hflag]");
      [apply store_z_i|apply PermFlows_refl|apply Hfl'|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 3|
       split;auto|].    
    iEpilogue "(HPC & Hi & Hr_t1 & Hflag)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 0 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply move_z_i|apply PermFlows_refl|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 4|auto|].     
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Fail *)
    destruct a';[|inversion Hlength'].
    apply contiguous_between_last with (ai:=a5) in Hcont' as Hlink';[|auto].
    iPrologue "Hprog".
    iApply (wp_fail with "[$HPC $Hi]");
      [apply fail_end_i|apply PermFlows_refl|iCorrectPC f_a_first f_a_last|].
    iEpilogue "(HPC & Hi)".
    iApply wp_value. iApply "Hφ".
    iFrame. iSplitL "Hr".
    { simpl. iExists _. iFrame. iPureIntro. revert Hfailure. clear. lia. }
    assert ((f_a_last + (-1))%a = Some a5) as ->;[|simpl].
    { eapply contiguous_between_last in Hcont';[|eauto]. revert Hlink' Hcont'. clear. solve_addr. }
    iFrame. rewrite Heqapp. iDestruct "Hprog_done'" as "(?&?)". iDestruct "Hprog_done" as "(?&?&?&?&?&?&?)".
    iFrame.
  Qed. 
    
  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* malloc stores the result in r_t1, rather than a user chosen destination. 
     f_m is the offset of the malloc capability *)
  Definition malloc_instrs f_m size :=
    fetch_instrs f_m ++ 
    [move_r r_t2 r_t0;
    move_r r_t3 r_t1;
    move_z r_t1 size;
    move_r r_t0 PC;
    lea_z r_t0 3;
    jmp r_t3;
    move_r r_t0 r_t2;
    move_z r_t2 0;
    move_z r_t3 0].

  Definition malloc f_m size a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(malloc_instrs f_m size), a_i ↦ₐ[p] w_i)%I. 

  (* malloc spec *)
  Lemma malloc_spec W size cont a pc_p pc_p' pc_g pc_b pc_e a_first a_last b_link e_link a_link f_m a_entry rmap φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    PermFlows pc_p pc_p' →
    contiguous_between a a_first a_last →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a pc_p'
    ∗ inv malloc_γ ([[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine]])
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ[RW] inr (E,Global,b_m,e_m,a_m)
    (* register state *)
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* current world *)
    ∗ ▷ region W
    ∗ ▷ sts_full_world W
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ malloc f_m size a pc_p'
            ∗ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
            ∗ a_entry ↦ₐ[RW] inr (E,Global,b_m,e_m,a_m)
            (* the newly allocated region *)
            ∗ (∃ (b e : Addr), ⌜(e - b = size)%Z⌝ ∧ r_t1 ↦ᵣ inr (RWX,Global,b,e,b)
            ∗ [[b,e]] ↦ₐ[RWX] [[region_addrs_zeroes b e]]
            ∗ r_t0 ↦ᵣ cont
            ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=inl 0%Z]> (<[r_t3:=inl 0%Z]> (delete r_t1 rmap))), r_i ↦ᵣ w_i)
            (* the newly allocated region is fresh in the current world *)
            ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝
            ∗ region W
            ∗ sts_full_world W)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb Ha_entry Hrmap_dom)
            "(>Hprog & #Hmalloc & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hr & Hsts & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[$HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b Hφ Hprog Hr_t0 Hregs Hr Hsts]");
      [|apply Hfl|apply Hcont_fetch|apply Hwb|apply Ha_entry|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst.
    (* move r_t2 r_t0 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t2 $Hr_t0]");
      [apply move_r_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t2 & Hr_t0)". iCombine "Hprog_done" "Hfetch" as "Hprog_done". 
    (* move r_t3 r_t1 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply move_r_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 size *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply move_z_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply move_r_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|]. destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert ((a1 + 3)%a = Some a4) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 a1 a4) in Hcont_rest; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply lea_z_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* jmp r_t3 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t3]");
      [apply jmp_i|apply Hfl|iCorrectPC link a_last|]. 
    iEpilogue "(HPC & Hi & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      by rewrite lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete.
    rewrite (insert_delete _ r_t3) (insert_commute _ r_t2 r_t3) // (insert_delete _ r_t2).
    iApply (malloc_subroutine_spec W). iFrame "Hr_t0 HPC Hr_t1 Hregs". iSplitR;[done|].
    iSplitR.
    { iPureIntro. rewrite !dom_insert_L dom_delete_L Hrmap_dom difference_difference_L.
      rewrite singleton_union_difference_L all_registers_union_l.
      rewrite singleton_union_difference_L all_registers_union_l.
      f_equal. set_solver. }
    iNext. iIntros "(Hregs & Hr_t0 & HPC & Hbe) /=".
    iDestruct "Hbe" as (b e Hbe) "(Hr_t1 & Hbe & %)".
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]".
      by rewrite lookup_insert_ne // lookup_insert //.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]".
      by rewrite lookup_delete_ne // lookup_insert //.
    rewrite (insert_commute _ r_t3 r_t2) // !delete_insert_delete
            delete_commute // delete_insert_delete.
    (* move r_t0 r_t2 *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t2]");
      [apply move_r_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply move_z_i|apply Hfl|iCorrectPC link a_last|iContiguous_next Hcont_rest 7|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 0 *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=a6) in Hcont_rest as Hlast;[|auto]. 
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
      [apply move_z_i|apply Hfl|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iFrame "Hpc_b Ha_entry".
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite lookup_delete //. rewrite insert_delete.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete.
    rewrite insert_commute // insert_delete.
    iExists b,e. iFrame "Hbe Hr_t0 Hr_t1 Hr Hsts". iSplitR;[auto|]. iSplitL;[|auto]. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- STACK MACROS AND THEIR SPECS -------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  (* -------------------------------------- PUSH ------------------------------------- *)

  Definition push_r_instrs r_stk r := [lea_z r_stk 1 ; store_r r_stk r].

  Definition push_r (a1 a2 : Addr) (p : Perm) (r_stk r : RegName) : iProp Σ :=
    ([∗ list] a;i ∈ [a1;a2];(push_r_instrs r_stk r), a ↦ₐ[p] i)%I.

  Lemma push_r_spec a1 a2 a3 w w' r p p' g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) →
    PermFlows p p' ->
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a') = true →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ push_r a1 a2 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ stk_a' ↦ₐ[RWLX] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a3) ∗ push_r a1 a2 p' r_stk r ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ r ↦ᵣ w' ∗ stk_a' ↦ₐ[RWLX] w'
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ([Hvpc1 Hvpc2] Hfl Hwb Hsuc Hlea Hstk)
            "([Ha1 [Ha2 _] ] & HPC & Hr_stk & Hr & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a1 a2 _ r_stk RWLX with "[HPC Ha1 Hr_stk]");
      eauto; try apply lea_z_i; iFrame.
    iNext. iIntros "(HPC & Ha1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_reg _ _ _ _ _ a2 a3 _ r_stk r _ RWLX Local
              with "[HPC Ha2 Hr_stk Hr Hstk_a']"); eauto; try apply store_r_i;
      first apply PermFlows_refl; iFrame.
    iNext. iIntros "(HPC & Ha2 & Hr & Hr_stk & Hstk_a') /=".
    iApply wp_pure_step_later; auto. iNext. iApply "Hφ". iFrame. done.
  Qed.


  Definition push_z_instrs r_stk z := [lea_z r_stk 1; store_z r_stk z].

  Definition push_z (a1 a2 : Addr) (p : Perm) (r_stk : RegName) (z : Z) : iProp Σ :=
    ([∗ list] a;i ∈ [a1;a2];(push_z_instrs r_stk z), a ↦ₐ[p] i)%I.

  Lemma push_z_spec a1 a2 a3 w z p p' g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) →
    PermFlows p p' ->
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a') = true →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (stk_a + 1)%a = Some stk_a' →

      ▷ push_z a1 a2 p' r_stk z
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a' ↦ₐ[RWLX] w
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a3) ∗ push_z a1 a2 p' r_stk z ∗
            r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a') ∗ stk_a' ↦ₐ[RWLX] inl z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ([Hvpc1 Hvpc2] Hfl Hwb Hsuc Hlea Hstk)
            "([Ha1 [Ha2 _] ] & HPC & Hr_stk & Hstk_a' & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_z _ _ _ _ _ a1 a2 _ r_stk RWLX with "[HPC Ha1 Hr_stk]");
      eauto; first apply lea_z_i;iFrame.
    iNext. iIntros "(HPC & Ha1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_store_success_z _ _ _ _ _ a2 a3 _ r_stk _ _ RWLX
              with "[HPC Ha2 Hr_stk Hstk_a']"); eauto; first apply store_z_i;
      first apply PermFlows_refl; iFrame.
    iNext. iIntros "(HPC & Ha2 & Hr_stk & Hstk_a') /=".
    iApply wp_pure_step_later; auto. iNext. iApply "Hφ". iFrame. done.
  Qed.


  (* -------------------------------------- POP -------------------------------------- *)
  Definition pop_instrs r_stk r := [load_r r r_stk; sub_z_z r_t1 0 1; lea_r r_stk r_t1].

  Definition pop (a1 a2 a3 : Addr) (p : Perm) (r_stk r : RegName) : iProp Σ :=
    ([∗ list] a;i ∈ [a1;a2;a3];(pop_instrs r_stk r), a ↦ₐ[p] i)%I.

  Lemma pop_spec a1 a2 a3 a4 r w w' wt1 p p' g b e stk_b stk_e stk_a stk_a' φ :
    isCorrectPC (inr ((p,g),b,e,a1)) ∧ isCorrectPC (inr ((p,g),b,e,a2)) ∧
    isCorrectPC (inr ((p,g),b,e,a3)) →
    PermFlows p p' ->
    withinBounds ((RWLX,Local),stk_b,stk_e,stk_a) = true →
    r ≠ PC →
    (a1 + 1)%a = Some a2 →
    (a2 + 1)%a = Some a3 →
    (a3 + 1)%a = Some a4 →
    (stk_a + (-1))%a = Some stk_a' →

      ▷ pop a1 a2 a3 p' r_stk r
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a)
    ∗ ▷ stk_a ↦ₐ[RWLX] w
    ∗ ▷ r_t1 ↦ᵣ wt1
    ∗ ▷ r ↦ᵣ w'
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a4)
            ∗ pop a1 a2 a3 p' r_stk r
            ∗ r ↦ᵣ w
            ∗ stk_a ↦ₐ[RWLX] w
            ∗ r_stk ↦ᵣ inr ((RWLX,Local),stk_b,stk_e,stk_a')
            ∗ r_t1 ↦ᵣ (inl (-1)%Z)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ((Hvpc1 & Hvpc2 & Hvpc3) Hfl Hwb Hne Ha1' Ha2' Ha3' Hstk_a')
            "((>Ha1 & >Ha2 & >Ha3 & _) & >HPC & >Hr_stk & >Hstk_a & >Hr_t1 & >Hr & Hφ)".
    iApply (wp_bind (fill [SeqCtx])).
    iAssert (⌜(stk_a =? a1)%a = false⌝)%I as %Hne'.
    { rewrite Z.eqb_neq. iIntros (Hcontr); apply z_of_eq in Hcontr; subst.
      iApply (cap_duplicate_false with "[$Ha1 $Hstk_a]").
      split; auto. destruct p'; auto. destruct p; inversion Hfl. 
      inversion Hvpc1 as [?????? [Hcontr | [Hcontr | Hcontr] ] ];inversion Hcontr. }
    iApply (wp_load_success _ _ _ _ _ _ _ a1 _ _ _ RWLX
              with "[HPC Ha1 Hr_stk Hr Hstk_a]"); eauto; first apply load_r_i; rewrite Hne'; iFrame. iPureIntro. eapply PermFlows_refl.
    iNext. iIntros "(HPC & Hr & Ha1 & Hr_stk & Hstk_a) /=".
    iApply wp_pure_step_later; auto; iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_z_z _ r_t1 _ _ _ _ a2 with "[HPC Ha2 Hr_t1]");
      first apply sub_z_z_i; eauto; iFrame; simpl.
    iNext.
    (* rewrite sub_z_z_i Ha2'. *)
    iIntros "(HPC & Ha2 & Hr_t1) /=".
    iApply wp_pure_step_later; auto; iNext.
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_stk _ RWLX
              with "[HPC Ha3 Hr_stk Hr_t1]"); eauto; first apply lea_r_i; iFrame.
    iNext. iIntros "(HPC & Ha3 & Hr_t1 & Hr_stk) /=".
    iApply wp_pure_step_later; auto; iNext.
    iApply "Hφ". iFrame. done.
  Qed.

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) := map (λ r_i, move_z r_i 0) r.

  Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = move_z rr 0 :: rclear_instrs r.
  Proof. reflexivity. Qed.

  Definition rclear (a : list Addr) (p : Perm) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↦ₐ[p] w_i)%I.

  Lemma rclear_spec (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p p' g b e a1 an φ :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p g b e a1 an →
    PermFlows p p' →
    list_to_set r = dom (gset RegName) rmap →

      ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
    ∗ ▷ rclear a p' r
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,an) ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z)
            ∗ rclear a p' r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hfl Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha Hrdom).
    iInduction (a) as [| a1'] "IH" forall (r rmap a1 an).
    { iIntros (Hne Har Hhd Hvpc Ha Hrdom). by inversion Hhd; simplify_eq. }
    iIntros (Hne Har Hhd Hvpc Ha Hrdom).
    iApply (wp_bind (fill [SeqCtx])). rewrite /rclear /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    rewrite rclear_instrs_cons.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    rewrite list_to_set_cons in Hrdom.
    assert (is_Some (rmap !! r)) as [rv ?].
    { rewrite elem_of_gmap_dom -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hreg") as "[Hr Hreg]". eauto.
    pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
    iApply (wp_move_success_z with "[$HPC $Hr $Ha1]");
      [apply move_z_i|apply Hfl|iCorrectPC a1 an|eauto|..].
    { apply (not_elem_of_cons) in Hne as [Hne _]. apply Hne. }
    iNext. iIntros "(HPC & Ha1 & Hr)". iApply wp_pure_step_later; auto. iNext.
    destruct a.
    { iApply "Hφ". iFrame. inversion Hcont'; subst. iFrame.
      destruct r0; inversion Har. simpl in Hrdom.
      iApply (big_sepM_delete _ _ r). eauto.
      rewrite (_: delete r rmap = ∅). rewrite !big_sepM_empty. eauto.
      apply map_empty. intro. eapply (@not_elem_of_dom _ _ (gset RegName)).
      typeclasses eauto. rewrite dom_delete_L -Hrdom. set_solver. }

    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont') as ->.
    assert (PC ∉ r0). { apply not_elem_of_cons in Hne as [? ?]. auto. }

    destruct (decide (r ∈ r0)).
    { iDestruct (big_sepM_insert with "[$Hreg $Hr]") as "Hreg".
        by rewrite lookup_delete. rewrite insert_delete.
      iApply ("IH" with "Hreg HPC Hrclear [Hφ Ha1]"); eauto.
      { iNext. iIntros "(? & Hreg & ?)". iApply "Hφ". iFrame.
        iApply (big_sepM_delete _ _ r). eauto.
        iDestruct (big_sepM_delete _ _ r with "Hreg") as "[? ?]".
        rewrite lookup_insert //. iFrame. rewrite delete_insert_delete //. }
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_insert_L -Hrdom. set_solver. } }
    { iApply ("IH" with "Hreg HPC Hrclear [Hφ Ha1 Hr]"); eauto.
      { iNext. iIntros "(? & ? & ?)". iApply "Hφ". iFrame.
        iApply (big_sepM_delete _ _ r). eauto. iFrame. }
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_delete_L -Hrdom. set_solver. } }
  Qed.

  (* -------------------------------------- MCLEAR ----------------------------------- *)
   (* the following macro clears the region of memory a capability govers over. a denotes
     the list of adresses containing the instructions for the clear. |a| = 23 *)

  (* first we will define the list of Words making up the mclear macro *)
  Definition mclear_instrs r_stk off_end off_iter :=
    [ move_r r_t4 r_stk;
      getb r_t1 r_t4;
      geta r_t2 r_t4;
      sub_r_r r_t2 r_t1 r_t2;
      lea_r r_t4 r_t2;
      gete r_t5 r_t4;
      sub_r_z r_t5 r_t5 1; (* we subtract the bound by one so that the lt check becomes a le check *)
      move_r r_t2 PC;
      lea_z r_t2 off_end; (* offset to "end" *)
      move_r r_t3 PC;
      lea_z r_t3 off_iter; (* offset to "iter" *)
    (* iter: *)
      lt_r_r r_t6 r_t5 r_t1;
      jnz r_t2 r_t6;
      store_z r_t4 0;
      lea_z r_t4 1;
      add_r_z r_t1 r_t1 1;
      jmp r_t3;
    (* end: *)
      move_z r_t4 0;
      move_z r_t1 0;
      move_z r_t2 0;
      move_z r_t3 0;
      move_z r_t5 0;
      move_z r_t6 0].

  (* Next we define mclear in memory, using a list of addresses of size 23 *)
  Definition mclear (a : list Addr) (p : Perm) (r : RegName) (off_end off_iter : Z) : iProp Σ :=
    if ((length a) =? (length (mclear_instrs r off_end off_iter)))%nat then
      ([∗ list] k↦a_i;w_i ∈ a;(mclear_instrs r off_end off_iter), a_i ↦ₐ[p] w_i)%I
    else
      False%I.

  Lemma mclear_iter_spec (a1 a2 a3 a4 a5 a6 b_r e_r a_r (* e_r' *) : Addr) ws (z : nat)
        p p' g b e rt rt1 rt2 rt3 rt4 rt5 a_end (p_r p_r' : Perm) (g_r : Locality) φ :
        isCorrectPC (inr ((p,g),b,e,a1))
      ∧ isCorrectPC (inr ((p,g),b,e,a2))
      ∧ isCorrectPC (inr ((p,g),b,e,a3))
      ∧ isCorrectPC (inr ((p,g),b,e,a4))
      ∧ isCorrectPC (inr ((p,g),b,e,a5))
      ∧ isCorrectPC (inr ((p,g),b,e,a6)) →
        (a1 + 1)%a = Some a2
      ∧ (a2 + 1)%a = Some a3
      ∧ (a3 + 1)%a = Some a4
      ∧ (a4 + 1)%a = Some a5
      ∧ (a5 + 1)%a = Some a6 →
        ((b_r + z < e_r)%Z → withinBounds ((p_r,g_r),b_r,e_r,a_r) = true) →
        writeAllowed p_r = true →
        (* (e_r + 1)%a = Some e_r' → *)
        (b_r + z)%a = Some a_r →
        PermFlows p p' ->
        PermFlows p_r p_r' ->
      ([[a_r,e_r]] ↦ₐ[p_r'] [[ws]]
     ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
     ∗ ▷ rt ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
     ∗ ▷ rt1 ↦ᵣ inl (b_r + z)%Z
     ∗ ▷ rt2 ↦ᵣ inl ((z_of e_r) - 1)%Z
     ∗ ▷ (∃ w, rt3 ↦ᵣ w)
     ∗ ▷ rt4 ↦ᵣ inr (p, g, b, e, a_end)
     ∗ ▷ rt5 ↦ᵣ inr (p, g, b, e, a1)
     ∗ ▷ ([∗ list] a_i;w_i ∈ [a1;a2;a3;a4;a5;a6];[lt_r_r rt3 rt2 rt1;
                                                  jnz rt4 rt3;
                                                  store_z rt 0;
                                                  lea_z rt 1;
                                                  add_r_z rt1 rt1 1;
                                                  jmp rt5], a_i ↦ₐ[p'] w_i)
     ∗ ▷ (PC ↦ᵣ updatePcPerm (inr ((p,g),b,e,a_end))
             ∗ [[ a_r , e_r ]] ↦ₐ[p_r'] [[ region_addrs_zeroes a_r e_r ]]
             ∗ (∃ a_r, rt ↦ᵣ inr (p_r, g_r, b_r, e_r, a_r))
             ∗ rt5 ↦ᵣ inr (p, g, b, e, a1)
             ∗ a3 ↦ₐ[p'] store_z rt 0
             ∗ a4 ↦ₐ[p'] lea_z rt 1
             ∗ a5 ↦ₐ[p'] add_r_z rt1 rt1 1
             ∗ a6 ↦ₐ[p'] jmp rt5
             ∗ a1 ↦ₐ[p'] lt_r_r rt3 rt2 rt1
             ∗ rt2 ↦ᵣ inl ((z_of e_r) - 1)%Z
             ∗ (∃ z, rt1 ↦ᵣ inl (b_r + z)%Z)
             ∗ a2 ↦ₐ[p'] jnz rt4 rt3
             ∗ rt4 ↦ᵣ inr (p, g, b, e, a_end)
             ∗ rt3 ↦ᵣ inl 1%Z
              -∗ WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hnext Hwb Hwa (* Her' *) Hprogress Hfl1 Hfl2)
            "(Hbe & >HPC & >Hrt & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & >Hprog & Hφ)".
    iRevert (Hwb Hprogress).
    iLöb as "IH" forall (a_r ws z).
    iIntros (Hwb Hprogress).
    iDestruct "Hr_t3" as (w) "Hr_t3".
    destruct Hvpc as (Hvpc1 & Hvpc2 & Hvpc3 & Hvpc4 & Hvpc5 & Hvpc6).
    destruct Hnext as (Hnext1 & Hnext2 & Hnext3 & Hnext4 & Hnext5).
    iAssert (⌜rt1 ≠ PC⌝)%I as %Hne1.
    { destruct (reg_eq_dec rt1 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 HPC") as "Hfalse". }
    iAssert (⌜rt3 ≠ PC⌝)%I as %Hne2.
    { destruct (reg_eq_dec rt3 PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t3 HPC") as "Hfalse". }
    iAssert (⌜rt ≠ PC⌝)%I as %Hne3.
    { destruct (reg_eq_dec rt PC); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hrt HPC") as "Hfalse". }
    iAssert (⌜rt2 ≠ rt3⌝)%I as %Hne4.
    { destruct (reg_eq_dec rt2 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t2 Hr_t3") as "Hfalse". }
    iAssert (⌜rt1 ≠ rt3⌝)%I as %Hne5.
    { destruct (reg_eq_dec rt1 rt3); auto. rewrite e0.
        by iDestruct (regname_dupl_false with "Hr_t1 Hr_t3") as "Hfalse". }
    (* lt rt3 rt2 rt1 *)
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_r_r _ rt3 _ _ _ _ a1 _ _ _ rt2 _ rt1 _ _
      with "[Hi HPC Hr_t3 Hr_t1 Hr_t2]"); [apply lt_r_r_i | | | apply Hfl1 | ..]; eauto.
    iFrame.
    iEpilogue "(HPC & Ha1 & Hr_t2 & Hr_t1 & Hr_t3)".
    rewrite /region_mapsto /region_addrs.
    destruct (Z_le_dec (b_r + z) (e_r - 1))%Z; simpl.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 0%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_lt in HH. lia. }
      rewrite Heq0.
      (* jnz rt4 rt3 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jnz_success_next _ rt4 rt3 _ _ _ _ a2 a3 with "[HPC Hi Hr_t3 Hr_t4]");
        first apply jnz_i; first apply Hfl1;eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      (* store rt 0 *)
      rewrite/ withinBounds in Hwb.
      apply andb_prop in Hwb as [Hwb_b%Z.leb_le Hwb_e%Z.ltb_lt].
      rewrite {1}region_size_S /=.
      destruct ws as [| w1 ws]; simpl; [by iApply bi.False_elim|].
      iDestruct "Hbe" as "[Ha_r Hbe]".
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_store_success_z _ _ _ _ _ a3 a4 _ rt 0 _ p_r g_r b_r e_r a_r with "[HPC Hi Hrt Ha_r]"); first apply store_z_i; first apply Hfl1; eauto.
      { split;[auto|]. rewrite /withinBounds andb_true_iff; split;[auto|].
          by apply Z.leb_le. by apply Z.ltb_lt. }
      iFrame. iEpilogue "(HPC & Ha3 & Hrt & Ha_r)".
      (* lea rt 1 *)
      assert (∃ a_r', (a_r + 1)%a = Some a_r') as [a_r' Ha_r'].
      { apply addr_next_lt with e_r. apply incr_addr_of_z_i in Hprogress. lia. }
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_lea_success_z _ _ _ _ _ a4 a5 _ rt p_r _ _ _ a_r 1 a_r' with "[HPC Hi Hrt]"); first apply lea_z_i; first apply Hfl1; eauto.
      { destruct p_r; auto. }
      iFrame. iEpilogue "(HPC & Ha4 & Hrt)".
      (* add rt1 rt1 1 *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_add_sub_lt_success_dst_z _ rt1 _ _ _ _ a5 _ _ _ with "[HPC Hi Hr_t1]");
        [ apply add_r_z_i | | | apply Hfl1 | ..]; eauto.
      iFrame. iEpilogue "(HPC & Ha5 & Hr_t1)".
      (* jmp rt5 *)
      iDestruct "Hprog" as "[Hi _]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jmp_success _ _ _ _ _ a6 with "[HPC Hi Hr_t5]");
        first apply jmp_i; first apply Hfl1; eauto.
      iFrame. iEpilogue "(HPC & Ha6 & Hr_t5)".
      iApply ("IH" $! a_r' ws (z + 1)%nat with
                  "[Hbe] [HPC] [Hrt] [Hr_t1] [Hr_t2] [Hr_t3] [Hr_t4] [Hr_t5] [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6] [Hφ Ha_r]")
      ; iFrame. all: auto.
      + by rewrite Ha_r'.
      + assert (updatePcPerm (inr (p, g, b, e, a1)) = (inr (p, g, b, e, a1))).
        { rewrite /updatePcPerm. destruct p; auto.
          inversion Hvpc1; destruct H5 as [Hc | [Hc | Hc] ]; inversion Hc. }
        rewrite H. iFrame.
      + cbn. assert (b_r + z + 1 = b_r + (z + 1)%nat)%Z as ->;[lia|]. iFrame.
      + iNext.
        iIntros "(HPC & Hregion & Hrt & Hrt5 & Ha3 & Ha4 & Ha5 & Ha6 & Ha1 & Hrt2 & Hrt1 & Ha2 & Hrt4 & Hrt3)".
        iApply "Hφ".
        iFrame.
        rewrite /region_addrs_zeroes.
        rewrite (region_size_S a_r e_r) //= (_: (^(a_r+1))%a = a_r'); [| solve_addr].
        iFrame.
      + iPureIntro. intro.
        rewrite andb_true_iff -Zle_is_le_bool -Zlt_is_lt_bool. solve_addr.
      + iPureIntro. solve_addr.
      + solve_addr.
    - assert (Z.b2z (e_r - 1 <? b_r + z)%Z = 1%Z) as Heq0.
      { rewrite /Z.b2z. destruct (e_r - 1 <? b_r + z)%Z eqn:HH; auto.
        apply Z.ltb_nlt in HH. lia. }
      rewrite Heq0.
      assert (e_r <= a_r)%Z by solve_addr.
      (* destruct (Z_le_dec a_r e_r). *)
      rewrite region_size_0 //=.
      destruct ws;[|by iApply bi.False_elim].
      (* jnz *)
      iDestruct "Hprog" as "[Hi Hprog]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_jnz_success_jmp _ rt4 rt3 _ _ _ _ a2 _ _ (inl 1%Z) with "[HPC Hi Hr_t3 Hr_t4]"); first apply jnz_i; first apply Hfl1; eauto.
      iFrame. iEpilogue "(HPC & Ha2 & Hr_t4 & Hr_t3)".
      iApply "Hφ". iDestruct "Hprog" as "(Ha3 & Ha4 & Ha5 & Ha6 & _)".
      rewrite /region_addrs_zeroes region_size_0 //=. iFrame.
      iSplitL "Hrt"; eauto.
  Qed.

  Lemma mclear_spec (a : list Addr) (r : RegName)
        (a_first a6' a_end : Addr) p p' g b e p_r p_r' g_r (b_r e_r a_r : Addr) a'
        w1 w2 w3 w4 w5 w6 ws φ :
    contiguous_between a a_first a' →
    (* We will assume that we are not trying to clear memory in a *)
    r ≠ PC ∧ writeAllowed p_r = true →
    (a !! 7 = Some a6' ∧ (a6' + 10)%a = Some a_end ∧ a !! 17 = Some a_end) →

    isCorrectPC_range p g b e a_first a' →
    PermFlows p p' → PermFlows p_r p_r' ->

    (* We will also assume the region to clear is non empty *)
    (b_r ≤ e_r)%Z →

     (mclear a p' r 10 2
    ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
    ∗ ▷ r ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
    ∗ ▷ r_t4 ↦ᵣ w4
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t5 ↦ᵣ w5
    ∗ ▷ r_t6 ↦ᵣ w6
    ∗ ▷ ([[ b_r , e_r ]] ↦ₐ[p_r'] [[ ws ]])
    ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,a')
            ∗ r_t1 ↦ᵣ inl 0%Z
            ∗ r_t2 ↦ᵣ inl 0%Z
            ∗ r_t3 ↦ᵣ inl 0%Z
            ∗ r_t4 ↦ᵣ inl 0%Z
            ∗ r_t5 ↦ᵣ inl 0%Z
            ∗ r_t6 ↦ᵣ inl 0%Z
            ∗ r ↦ᵣ inr ((p_r,g_r),b_r,e_r,a_r)
            ∗ [[ b_r , e_r ]] ↦ₐ[p_r'] [[region_addrs_zeroes b_r e_r]]
            ∗ mclear a p' r 10 2 -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hnext [Hne Hwa] Hjnz_off Hvpc Hfl1 Hfl2 Hle)
            "(Hmclear & >HPC & >Hr & >Hr_t4 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t5 & >Hr_t6 & >Hregion & Hφ)".
    iAssert (⌜((length a) =? (length (mclear_instrs r _ _)) = true)%nat⌝)%I as %Hlen.
    { destruct (((length a) =? (length (mclear_instrs r _ _)))%nat) eqn:Hlen; auto.
      rewrite /mclear Hlen. by iApply bi.False_elim. }
    rewrite /mclear Hlen /mclear_instrs; simpl in Hlen. apply beq_nat_true in Hlen.
    destruct a as [| a1 a]; inversion Hlen; simpl.
    move: (contiguous_between_cons_inv_first _ _ _ _ Hnext).
    match goal with |- (?a = _) -> _ => intro; subst a end.
    iPrologue "Hmclear".
    iApply (wp_move_success_reg _ _ _ _ _ a_first _ _ r_t4 _ r with "[HPC Hr Hr_t4 Hi]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 0. }
    iFrame. iEpilogue "(HPC & Ha_first & Hr_t4 & Hr)".
    (* getb r_t1 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t1 r_t4 _ _ _ _ a0 _ _ _ a1 with "[$HPC $Hi $Hr_t1 $Hr_t4]");
      first eapply getb_i; first eauto; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 1. }
    iFrame. iEpilogue "(HPC & Ha0 & Hr_t4 & Hr_t1)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha0 Ha_first" as "Hprog_done".
    (* geta r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t2 r_t4 _ _ _ _ a1 _ _ _ a2 with "[HPC Hi Hr_t2 Hr_t4]");
      first eapply geta_i; first eauto; first eapply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 2. }
    iFrame. iEpilogue "(HPC & Ha1 & Hr_t4 & Hr_t2)".
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    iCombine "Ha1 Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t1 r_t2 *)
    iPrologue "Hprog".
    (* destruct b_r eqn:Hb_r. *)
    iApply (wp_add_sub_lt_success_r_dst _ _ _ _ _ _ a2 _ _ r_t1 with "[HPC Hi Hr_t1 Hr_t2]");
      [ apply sub_r_r_i | | | apply Hfl1 | ..]; eauto. 2: by iCorrectPC a_first a'. 
    assert ((a2 + 1) = Some a3)%a as ->. { iContiguous_next Hnext 3. } by eauto. by iFrame.
    iEpilogue "(HPC & Ha2 & Hr_t1 & Hr_t2)".
    iCombine "Ha2 Hprog_done" as "Hprog_done".
    (* lea r_t4 r_t2 *)
    iPrologue "Hprog".
    assert (a_r + (b_r - a_r) = b_r)%Z as Haddmin; first lia.
    assert ((a_r + (b_r - a_r))%a = Some b_r) as Ha_rb_r by solve_addr.
    iApply (wp_lea_success_reg _ _ _ _ _ a3 a4 _ r_t4 r_t2 p_r _ _ _ a_r (b_r - a_r) with "[HPC Hi Hr_t4 Hr_t2]");
      first apply lea_r_i; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 4. }
    { destruct p_r; inversion Hwa; auto. }
    by iFrame. iEpilogue "(HPC & Ha3 & Hr_t2 & Hr_t4)".
    iCombine "Ha3 Hprog_done" as "Hprog_done".
    (* gete r_t2 r_t4 *)
    iPrologue "Hprog".
    iApply (wp_Get_success _ _ r_t5 r_t4 _ _ _ _ a4 _ _ _ a5 with "[HPC Hi Hr_t5 Hr_t4]");
      first apply gete_i; first eauto; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 5. }
    do 2 iFrame.
    destruct (reg_eq_dec PC r_t4) as [Hcontr | _]; [inversion Hcontr|].
    destruct (reg_eq_dec r_t4 r_t5) as [Hcontr | _]; [inversion Hcontr|].
    iEpilogue "(HPC & Ha4 & Hr_t4 & Hr_t5)".
    iCombine "Ha4 Hprog_done" as "Hprog_done".
    (* sub r_t5 r_t5 1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi Hr_t5]");
      [apply sub_r_z_i| | | apply Hfl1|iCorrectPC a_first a'|..]; eauto.
    assert ((a5 + 1)%a = Some a6) as ->. { iContiguous_next Hnext 6. } eauto.
    iEpilogue "(HPC & Ha5 & Hr_t5)".
    iCombine "Ha5 Hprog_done" as "Hprog_done".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a6 a7 _ r_t2 with "[HPC Hi Hr_t2]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC a_first a'; eauto.
    { iContiguous_next Hnext 7. }
    iFrame. iEpilogue "(HPC & Ha6 & Hr_t2)".
    iCombine "Ha6 Hprog_done" as "Hprog_done".
    (* lea r_t2 off_end *)
    iPrologue "Hprog".
    assert (p ≠ E) as Hpne.
    { have: (isCorrectPC (inr (p, g, b, e, a_first))).
      { apply Hvpc. eapply contiguous_between_middle_bounds'; eauto. constructor. }
      inversion 1; subst.
      destruct H15 as [? | [? | ?] ]; subst; auto. }
    iApply (wp_lea_success_z _ _ _ _ _ a7 a8 _ r_t2 p _ _ _ a6 10 a_end with "[HPC Hi Hr_t2]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 8. }
    { destruct Hjnz_off as (Ha7' & Hoff_end & Ha_end). simpl in Ha7'. congruence. }
    iFrame. iEpilogue "(HPC & Ha7 & Hr_t2)".
    iCombine "Ha7 Hprog_done" as "Hprog_done".
    (* move r_t3 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC _ _ _ _ _ a8 a9 _ r_t3 with "[HPC Hi Hr_t3]");
      first apply move_r_i; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 9. }
    iFrame. iEpilogue "(HPC & Ha8 & Hr_t3)".
    iCombine "Ha8 Hprog_done" as "Hprog_done".
    (* lea r_t3 off_iter *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ a9 a10 _ r_t3 p _ _ _ a8 2 a10 with "[HPC Hi Hr_t3]");
      first apply lea_z_i; first apply Hfl1; first iCorrectPC a_first a'; auto.
    { iContiguous_next Hnext 10. }
    { assert (2 = 1 + 1)%Z as ->; auto.
      apply incr_addr_trans with a9. iContiguous_next Hnext 9.
      iContiguous_next Hnext 10. }
    iFrame. iEpilogue "(HPC & Ha9 & Hr_t3)".
    iCombine "Ha9 Hprog_done" as "Hprog_done".
    (* iter *)
    clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    do 5 iPrologue_pre. clear H0 H1 H2 H3.
    iDestruct "Hprog" as "[Hi1 Hprog]".
    iDestruct "Hprog" as "[Hi2 Hprog]".
    iDestruct "Hprog" as "[Hi3 Hprog]".
    iDestruct "Hprog" as "[Hi4 Hprog]".
    iDestruct "Hprog" as "[Hi5 Hprog]".
    iDestruct "Hprog" as "[Hi6 Hprog]".
    iApply (mclear_iter_spec a10 a11 a12 a13 a14 a15 b_r e_r b_r _
                        0 p p' g b e r_t4 r_t1 r_t5 r_t6 r_t2 r_t3 _ p_r p_r' g_r
              with "[-]"); auto.
    - repeat apply conj; iCorrectPC a_first a'.
    - repeat split; solve [
        iContiguous_next Hnext 11; auto
      | iContiguous_next Hnext 12; auto
      | iContiguous_next Hnext 13; auto
      | iContiguous_next Hnext 14; auto
      | iContiguous_next Hnext 15; auto ].
    - (* rewrite Z.add_0_r. intros Hle. *)
      rewrite /withinBounds. intro.
      rewrite andb_true_iff Z.leb_le Z.ltb_lt. lia.
    - apply addr_add_0.
    - rewrite Z.add_0_r.
      iFrame.
      iSplitL "Hr_t6". iNext. iExists w6. iFrame.
      iSplitR; auto.
      iNext.
      iIntros "(HPC & Hbe & Hr_t4 & Hr_t3 & Ha11 & Ha12 & Ha13 & Ha14 &
      Ha9 & Hr_t5 & Hr_t1 & Ha10 & Hr_t2 & Hr_t6)".
      iCombine "Ha9 Ha10 Ha11 Ha12 Ha13 Ha14 Hprog_done" as "Hprog_done".
      iDestruct "Hr_t4" as (a_r0) "Hr_t4".
      iDestruct "Hr_t1" as (z0) "Hr_t1".
      iPrologue "Hprog".
      assert (a16 = a_end)%a as Ha16.
      { simpl in Hjnz_off.
        destruct Hjnz_off as (Ha16 & Ha16' & Hend).
        by inversion Hend.
      }
      destruct a as [| a17 a]; inversion Hlen.
      iApply (wp_move_success_z _ _ _ _ _ a16 a17 _ r_t4 _ 0 with "[HPC Hi Hr_t4]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 17; auto. }
      { rewrite Ha16. destruct p; iFrame. contradiction. }
      iEpilogue "(HPC & Ha16 & Hr_t4)".
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a17 a18 _ r_t1 _ 0 with "[HPC Hi Hr_t1]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 18. }
      iFrame. iEpilogue "(HPC & Ha17 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a18 a19 _ r_t2 _ 0 with "[HPC Hi Hr_t2]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 19. }
      iFrame. iEpilogue "(HPC & Ha18 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a19 a20 _ r_t3 _ 0 with "[HPC Hi Hr_t3]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 20. }
      iFrame. iEpilogue "(HPC & Ha19 & Hr_t3)".
      (* move r_t5 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a20 a21 _ r_t5 _ 0 with "[HPC Hi Hr_t5]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { iContiguous_next Hnext 21. }
      iFrame. iEpilogue "(HPC & Ha20 & Hr_t5)".
      (* move r_t6 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z _ _ _ _ _ a21 a' _ r_t6 _ 0 with "[HPC Hi Hr_t6]");
        first apply move_z_i; first apply Hfl1;
        first iCorrectPC a_first a'; auto.
      { eapply contiguous_between_last. eapply Hnext. reflexivity. }
      iFrame. iEpilogue "(HPC & Ha21 & Hr_t6)".
      iApply "Hφ".
      iDestruct "Hprog_done" as "(Ha_iter & Ha10 & Ha12 & Ha11 & Ha13 & Ha14 & Ha15 & Ha8 & Ha7
      & Ha6 & Ha5 & Ha4 & Ha3 & Ha2 & Ha1 & Ha0 & Ha_first)".
      iFrame. Unshelve. exact 0. exact 0.
  Qed.        (* ??? *)


  (* -------------------------------------- REQGLOB ----------------------------------- *)
  (* the following macro requires that a given registers contains a global capability. If 
     this is not the case, the macro goes to fail, otherwise it continues               *)

  Definition reqglob_instrs r :=
    [getl r_t1 r;
    sub_r_z r_t1 r_t1 (encodeLoc Global);
    move_r r_t2 PC;
    lea_z r_t2 6;
    jnz r_t2 r_t1;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jmp r_t2;
    fail_end;
    move_z r_t1 0;
    move_z r_t2 0].

  (* TODO: move this to the rules_Get.v file. small issue with the spec of failure: it does not actually 
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Get_fail E get_i dst src pc_p pc_g pc_b pc_e pc_a w zsrc wdst pc_p' :
    cap_lang.decode w = get_i →
    is_Get get_i dst src →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
      ∗ ▷ pc_a ↦ₐ[pc_p'] w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ inl zsrc }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hfl Hvpc φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  (* TODO: move the following into lang. *)
  Definition isGlobal (l: Locality): bool :=
    match l with
    | Global => true
    | _ => false
    end.

  Definition isGlobalWord (w : Word): bool :=
    match w with
    | inl _ => false
    | inr ((_,l),_,_,_) => isGlobal l
    end.

  Lemma isGlobalWord_cap_isGlobal (w0:Word):
    isGlobalWord w0 = true →
    ∃ p g b e a, w0 = inr (p,g,b,e,a) ∧ isGlobal g = true.
  Proof.
    intros. destruct w0;[done|].
    destruct c, p, p, p.
    cbv in H. destruct l; last done. 
    eexists _, _, _, _, _. split; eauto.
  Qed.

  Global Axiom encodeLoc_inj : Inj eq eq encodeLoc.
  (* ------------------------------- *)
  
  Definition reqglob r a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqglob_instrs r), a_i ↦ₐ[p] w_i)%I.

  Lemma reqglob_spec r a w pc_p pc_p' pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->
    contiguous_between a a_first a_last ->

      ▷ reqglob r a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (if isGlobalWord w then
           ∃ g b e a', ⌜w = inr (g,Global,b,e,a')⌝ ∧
          (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ reqglob r a pc_p' ∗
            r ↦ᵣ inr (g,Global,b,e,a') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iPrologue "Hprog".
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    destruct w. 
    { (* if w is an integer, the getL will fail *)
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply getl_i|auto|apply Hfl|iCorrectPC a_first a_last|..].
      iEpilogue "_ /=". 
      iApply wp_value. done. 
    }
    (* if w is a capability, the getL will succeed *)
    destruct a as [|a l];[done|]. 
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply getl_i|auto|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iRename "Hi" into "Hprog_done".
    destruct c,p,p,p. iSimpl in "Hr_t1". 
    (* sub r_t1 r_t1 (encodeLoc Global) *)
    destruct l;[done|].
    iPrologue "Hprog". 
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply sub_r_z_i|auto|iContiguous_next Hcont 1|apply Hfl|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done". 
    iSimpl in "Hr_t1".
    (* move r_t2 PC *)
    destruct l;[done|]. 
    iPrologue "Hprog".
    iDestruct "Hr_t2" as (w2) "Hr_t2". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t2 6 *)
    do 7 (destruct l;[done|]). destruct l; [|done]. 
    assert ((a3 + 6)%a = Some a9) as Hlea. 
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 6 a3 a9) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE.
    { apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply lea_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    destruct (decide (encodeLoc l0 - encodeLoc Global = 0))%Z.
    - (* l is Global *)
      rewrite e. assert (l0 = Global);[apply encodeLoc_inj;lia|subst]. 
      iSimpl in "Hcont". iDestruct "Hcont" as (g b e0 a' Heq) "Hφ". inversion Heq; subst.
      iPrologue "Hprog". 
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply jnz_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move_r r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* lea r_t2 3 *)
      assert ((a6 + 4)%a = Some a10) as Hlea'. 
      { apply (contiguous_between_incr_addr_middle _ _ _ 5 4 a6 a10) in Hcont; auto. }
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply lea_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto..]. 
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* jmp r_t2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
        [apply jmp_i|apply Hfl|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      assert (updatePcPerm (inr (pc_p, pc_g, pc_b, pc_e, a10)) = (inr (pc_p, pc_g, pc_b, pc_e, a10))) as ->.
      { destruct pc_p; auto. congruence. }
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
        [apply move_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 9|auto|..].
      iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t2 0 *)
      iPrologue "Hprog".
      apply contiguous_between_last with (ai:=a11) in Hcont as Hnext;[|auto]. 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
        [apply move_z_i|apply Hfl|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      iApply "Hφ". iFrame "HPC Hr Hr_t1 Hr_t2".
      repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi"). 
      iFrame.
    - destruct l0;[lia|iSimpl in "Hcont"]. 
      (* jnz r_t2 r_t1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply jnz_i|apply Hfl|iCorrectPC a_first a_last|..].
      { intros Hcontr. inversion Hcontr. done. }
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done"). 
      (* fail *)
      iPrologue "Hprog".
      assert (updatePcPerm (inr (pc_p, pc_g, pc_b, pc_e, a9)) = (inr (pc_p, pc_g, pc_b, pc_e, a9))) as ->.
      { destruct pc_p; auto. congruence. }
      iApply (wp_fail with "[$HPC $Hi]");
        [apply fail_end_i|apply Hfl|iCorrectPC a_first a_last|]. 
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". 
  Qed.

  (* -------------------------------------- REQPERM ----------------------------------- *)
  (* the following macro requires that a given registers contains a capability with a 
     given (encoded) permission. If this is not the case, the macro goes to fail,
     otherwise it continues *)  

  Definition reqperm_instrs r z :=
    [getp r_t1 r;
    sub_r_z r_t1 r_t1 z;
    move_r r_t2 PC;
    lea_z r_t2 6;
    jnz r_t2 r_t1;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jmp r_t2;
    fail_end;
    move_z r_t1 0;
    move_z r_t2 0].


  (* TODO: move the following into lang. *)
  Definition isPerm p p' :=
    match p with
    | RWX => match p' with
            | RWX => true
            | _ => false
            end
    | RWLX => match p' with
            | RWLX => true
            | _ => false
            end
    | RX => match p' with
            | RX => true
            | _ => false
            end
    | RW => match p' with
            | RW => true
            | _ => false
            end
    | RWL => match p' with
            | RWL => true
            | _ => false
            end
    | RO => match p' with
            | RO => true
            | _ => false
           end
    | O => match p' with
            | O => true
            | _ => false
          end
    | E => match p' with
          | E => true
          | _ => false
          end
    end.

  Lemma isPerm_refl p : isPerm p p = true.
  Proof. destruct p; auto. Qed.
  Lemma isPerm_ne p p' : p ≠ p' -> isPerm p p' = false.
  Proof. intros Hne. destruct p,p'; auto; congruence. Qed. 

  Definition isPermWord (w : Word) (p : Perm): bool :=
    match w with
    | inl _ => false
    | inr ((p',_),_,_,_) => isPerm p p'
    end.

  Lemma isPermWord_cap_isPerm (w0:Word) p:
    isPermWord w0 p = true →
    ∃ p' g b e a, w0 = inr (p',g,b,e,a) ∧ isPerm p p' = true.
  Proof.
    intros. destruct w0;[done|].
    destruct c,p0,p0,p0. 
    cbv in H. destruct p; try done; 
    eexists _, _, _, _, _; split; eauto.
  Qed.
  
  Global Axiom encodePerm_inj : Inj eq eq encodePerm.
  (* ------------------------------- *)
  
  Definition reqperm r z a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqperm_instrs r z), a_i ↦ₐ[p] w_i)%I.

  Lemma reqperm_spec r perm a w pc_p pc_p' pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->
    contiguous_between a a_first a_last ->

      ▷ reqperm r (encodePerm perm) a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (if isPermWord w perm then
           ∃ l b e a', ⌜w = inr (perm,l,b,e,a')⌝ ∧
          (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ reqperm r (encodePerm perm) a pc_p' ∗
            r ↦ᵣ inr (perm,l,b,e,a') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iPrologue "Hprog".
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    destruct w. 
    { (* if w is an integer, the getL will fail *)
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply getp_i|auto|apply Hfl|iCorrectPC a_first a_last|..].
      iEpilogue "_ /=". 
      iApply wp_value. done. 
    }
    (* if w is a capability, the getL will succeed *)
    destruct a as [|a l];[done|]. 
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply getp_i|auto|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iRename "Hi" into "Hprog_done".
    destruct c,p,p,p. iSimpl in "Hr_t1". 
    (* sub r_t1 r_t1 (encodeLoc Global) *)
    destruct l;[done|].
    iPrologue "Hprog". 
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply sub_r_z_i|auto|iContiguous_next Hcont 1|apply Hfl|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done". 
    iSimpl in "Hr_t1".
    (* move r_t2 PC *)
    destruct l;[done|]. 
    iPrologue "Hprog".
    iDestruct "Hr_t2" as (w2) "Hr_t2". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t2 6 *)
    do 7 (destruct l;[done|]). destruct l; [|done]. 
    assert ((a3 + 6)%a = Some a9) as Hlea. 
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 6 a3 a9) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE.
    { apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply lea_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    destruct (decide (encodePerm p - encodePerm perm = 0))%Z.
    - (* p is perm *)
      rewrite e. assert (p = perm);[apply encodePerm_inj;lia|subst]. 
      iSimpl in "Hcont". rewrite isPerm_refl. iDestruct "Hcont" as (l b e0 a' Heq) "Hφ". inversion Heq; subst.
      iPrologue "Hprog". 
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply jnz_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move_r r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* lea r_t2 3 *)
      assert ((a6 + 4)%a = Some a10) as Hlea'. 
      { apply (contiguous_between_incr_addr_middle _ _ _ 5 4 a6 a10) in Hcont; auto. }
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply lea_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto..]. 
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* jmp r_t2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
        [apply jmp_i|apply Hfl|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      assert (updatePcPerm (inr (pc_p, pc_g, pc_b, pc_e, a10)) = (inr (pc_p, pc_g, pc_b, pc_e, a10))) as ->.
      { destruct pc_p; auto. congruence. }
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
        [apply move_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 9|auto|..].
      iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t2 0 *)
      iPrologue "Hprog".
      apply contiguous_between_last with (ai:=a11) in Hcont as Hnext;[|auto]. 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
        [apply move_z_i|apply Hfl|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      iApply "Hφ". iFrame "HPC Hr Hr_t1 Hr_t2".
      repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi"). 
      iFrame.
    - assert (p ≠ perm) as HneP.
      { intros Hcontr. subst. lia. }
      iSimpl in "Hcont". rewrite isPerm_ne;[|auto]. 
      (* jnz r_t2 r_t1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply jnz_i|apply Hfl|iCorrectPC a_first a_last|..].
      { intros Hcontr. inversion Hcontr. done. }
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done"). 
      (* fail *)
      iPrologue "Hprog".
      assert (updatePcPerm (inr (pc_p, pc_g, pc_b, pc_e, a9)) = (inr (pc_p, pc_g, pc_b, pc_e, a9))) as ->.
      { destruct pc_p; auto. congruence. }
      iApply (wp_fail with "[$HPC $Hi]");
        [apply fail_end_i|apply Hfl|iCorrectPC a_first a_last|]. 
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". 
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) greater than [minsize]. *)

  Definition reqsize_instrs r (minsize: Z) :=
    [getb r_t1 r;
     gete r_t2 r;
     sub_r_r r_t1 r_t2 r_t1;
     lt_z_r r_t1 minsize r_t1;
     move_r r_t2 PC;
     lea_z r_t2 4;
     jnz r_t2 r_t1;
     fail_end].

  Definition reqsize r minsize a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqsize_instrs r minsize), a_i ↦ₐ[p] w_i)%I.

  Lemma reqsize_spec r minsize a pc_p pc_p' pc_g pc_b pc_e a_first a_last r_p r_g r_b r_e r_a w1 w2 φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    PermFlows pc_p pc_p' →
    contiguous_between a a_first a_last →

      ▷ reqsize r minsize a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ inr (r_p, r_g, r_b, r_e, r_a)
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if (minsize <? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
            reqsize r minsize a pc_p'
            ∗ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last)
            ∗ r ↦ᵣ inr (r_p, r_g, r_b, r_e, r_a)
            ∗ r_t1 ↦ᵣ w1
            ∗ r_t2 ↦ᵣ w2)
           -∗ WP Seq (Instr Executable) {{ φ }}
        else φ FailedV)
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont) "(>Hprog & >HPC & >Hr & >Hr1 & >Hr2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { iIntros (->). iApply (regname_dupl_false with "HPC Hr"). }
    destruct a as [| a l];[done|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont) as ->.
    assert (pc_p ≠ E).
    { (* FIXME: hackish *)
      assert (isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, a_first))) as HH.
      iCorrectPC a_first a_last. inversion HH; subst. intros ->.
      repeat match goal with H: _ ∨ _ |- _ => destruct H end; congruence. }
    (* getb r_t1 r *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr1]");
      [apply getb_i|auto|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr1)". iRename "Hi" into "Hprog_done".
    (* gete r_t2 r *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr2]");
      [apply gete_i|auto|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub_r_r r_t1 r_t2 r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_dst with "[$HPC $Hi $Hr2 $Hr1]");
      [apply sub_r_r_i|done|iContiguous_next Hcont 2|apply Hfl|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lt_z_r r_t1 minsize r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_z_dst with "[$HPC $Hi $Hr1]");
      [apply lt_z_r_i|done|iContiguous_next Hcont 3|apply Hfl|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t2 PC *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t2 4 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply lea_z_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 5|try done..].
    { change 4%Z with (Z.of_nat (4%nat)).
      (* FIXME: a bit annoying to have to specify the index manually *)
      eapply (contiguous_between_middle_to_end _ _ _ 4); eauto. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t2 r_t1 *)
    destruct l as [| ? l];[done|].
    iPrologue "Hprog".
    destruct (minsize <? r_e - r_b)%Z eqn:Htest; simpl.
    { iApply (wp_jnz_success_jmp with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply jnz_i|apply Hfl|iCorrectPC a_first a_last|done|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iApply "Hcont". iExists _,_.
      rewrite updatePcPerm_cap_non_E //. iFrame.
      iDestruct "Hprog_done" as "(?&?&?&?&?&?)". iFrame. }
    { iApply (wp_jnz_success_next with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply jnz_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 6|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail_end *)
      iPrologue "Hprog".
      iApply (wp_fail with "[$HPC $Hi]");
        [apply fail_end_i|apply Hfl|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". }
  Qed.

  (* -------------------------------------- PREPSTACK ---------------------------------- *)
  (* The following macro first checks whether r is a capability with permission RWLX. Next
     if it is, it will move the pointer to the bottom of its range *)

  Definition prepstack_instrs r (minsize: Z) :=
    reqperm_instrs r (encodePerm RWLX) ++
    reqsize_instrs r minsize ++
    [getb r_t1 r;
    geta r_t2 r;
    sub_r_r r_t1 r_t1 r_t2;
    lea_r r r_t1;
    sub_z_z r_t1 0 1;
    lea_r r r_t1;
    move_z r_t1 0;
    move_z r_t2 0].

  Definition prepstack r minsize a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(prepstack_instrs r minsize), a_i ↦ₐ[p] w_i)%I.

  Definition cap_size (w : Word) : Z :=
    match w with
    | inr (_,_,b,e,_) => (e - b)%Z
    | _ => 0%Z
    end.

  Definition bound_check (w : Word) : option Addr :=
    match w with 
    | inr (_,_,b,_,_) => (b + (-1))%a
    | _ => None
    end. 

  (* TODO: move this to the rules_Lea.v file. *)
  Lemma wp_Lea_fail_none Ep pc_p pc_g pc_b pc_e pc_a w r1 rv p g b e a z pc_p' :
    cap_lang.decode w = Lea r1 (inr rv) →
    PermFlows pc_p pc_p' → isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + z)%a = None ->
     
     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ[pc_p'] w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
     {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hfl Hvpc Hz φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.
  
  Lemma prepstack_spec r minsize a w pc_p pc_p' pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    PermFlows pc_p pc_p' ->
    contiguous_between a a_first a_last ->

      ▷ prepstack r minsize a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (if isPermWord w RWLX then
           if (minsize <? cap_size w)%Z then
             if (decide (is_Some (bound_check w))) then 
               (∃ l b e a' b', ⌜w = inr (RWLX,l,b,e,a')⌝ ∧ ⌜(b' + 1)%a = Some b⌝ ∧
                PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ prepstack r minsize a pc_p' ∗
                   r ↦ᵣ inr (RWLX,l,b,e,b') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z)
                 -∗ WP Seq (Instr Executable) {{ φ }}
             else φ FailedV
           else φ FailedV
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    (* reqperm *)
    iDestruct (contiguous_between_program_split with "Hprog") as (reqperm_prog rest link)
                                                                   "(Hreqperm & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_reqperm & Hcont_rest & Heqapp & Hlink).
    iApply (reqperm_spec with "[$HPC $Hreqperm $Hr $Hr_t1 $Hr_t2 Hφ Hprog]"); [|apply Hfl|apply Hcont_reqperm|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. solve_addr. }
    iNext. destruct (isPermWord w RWLX) eqn:Hperm; auto.
    destruct w as [z | [ [ [ [p g] b] e] a'] ];[inversion Hperm|].
    destruct p;inversion Hperm.
    iExists _,_,_,_;iSplit;[eauto|]. 
    iIntros "(HPC & Hprog_done & Hr & Hr_t1 & Hr_t2)".
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. solve_addr. }
    (* reqsize *)
    iDestruct (contiguous_between_program_split with "Hprog")
      as (reqsize_prog rest' link') "(Hreqsize & Hprog & #Hcont)";[apply Hcont_rest|].
    iDestruct "Hcont" as %(Hcont_reqsize & Hcont_rest' & Heqapp' & Hlink').
    iApply (reqsize_spec with "[- $HPC $Hreqsize $Hr $Hr_t1 $Hr_t2]");
      [|apply Hfl|eauto|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest'. solve_addr. }
    iNext. simpl. destruct (minsize <? e - b)%Z; auto.
    iIntros "H". iDestruct "H" as (w1 w2) "(Hreqsize & HPC & Hr & Hr_t1 & Hr_t2)".
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link' a_last) as Hvpc_rest'.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. solve_addr. }
    (* getb r_t1 r *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength'.
    do 2 (destruct rest';[inversion Hlength'|]). 
    iPrologue "Hprog".
    apply contiguous_between_cons_inv_first in Hcont_rest' as Heq; subst.
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply getb_i|auto|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* geta r_t2 r *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t2]");
      [apply geta_i|auto|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 1|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* sub r_t1 r_t1 r_t2 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply sub_r_r_i|auto|iContiguous_next Hcont_rest' 2|apply Hfl|iCorrectPC link' a_last|..].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r r_t1 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    assert ((a' + (b - a'))%a = Some b) as Hlea;[solve_addr|].
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply lea_r_i|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 3|apply Hlea|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* sub r_t1 0 1 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_z_z with "[$HPC $Hi $Hr_t1]");
      [apply sub_z_z_i|auto|iContiguous_next Hcont_rest' 4|apply Hfl|iCorrectPC link' a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r r_t1 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    (* if lea fails we go to φ FailedV *)
    destruct (b + -1)%a as [b'|] eqn:Hb; simpl.
    2: { iApply (wp_Lea_fail_none with "[$HPC $Hi $Hr_t1 $Hr]");
           [apply lea_r_i|apply Hfl|iCorrectPC link' a_last|apply Hb|..].
         iEpilogue "_". iApply wp_value. iApply "Hφ". }
    assert ((b + (0 - 1))%a = Some b') as Hlea';[revert Hb;clear;solve_addr|].
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply lea_r_i|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 5|apply Hlea'|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move r_t1 0 *)
    destruct rest';[inversion Hlength'|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
      [apply move_z_i|apply Hfl|iCorrectPC link' a_last|iContiguous_next Hcont_rest' 6|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* move r_t2 0 *)
    destruct rest';[|inversion Hlength'].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=a12) in Hcont_rest' as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
      [apply move_z_i|apply Hfl|iCorrectPC link' a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    assert ((b' + 1)%a = Some b) as Hb';[revert Hlea';clear;solve_addr|]. 
    iApply "Hφ". iExists _,_,_,_,_. iSplit;[eauto|]. iSplit;[iPureIntro;apply Hb'|]. 
    iFrame. rewrite Heqapp. 
    repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi"). 
    iFrame "Hprog_done". iFrame. done.
  Qed.

  (* ---------------------------------------- CRTCLS ------------------------------------ *)
  (* The following macro creates a closure with one variable. A more general create closure would 
     allow for more than one variable in the closure, but this is so far not necessary for our 
     examples. The closure allocates a new region with a capability to the closure code, the closure 
     variable, and the closure activation *)

  (* encodings of closure activation code *)
  Parameter v1 : Z.
  Parameter v2 : Z.
  Parameter v3 : Z.
  Parameter v4 : Z.
  Parameter v5 : Z.
  Parameter v6 : Z. 
  Axiom j_1 : cap_lang.encode (Mov r_t1 (inr PC)) = inl v1.
  Axiom j_2 : cap_lang.encode (Lea r_t1 (inl 7%Z)) = inl v2.
  Axiom j_3 : cap_lang.encode (Load r_env r_t1) = inl v3.
  Axiom j_4 : cap_lang.encode (Lea r_t1 (inl (-1)%Z)) = inl v4.
  Axiom j_5 : cap_lang.encode (Load r_t1 r_t1) = inl v5.
  Axiom j_6 : cap_lang.encode (Jmp r_t1) = inl v6.
  (* encodings of enter capability permission pair *)
  Parameter global_e : Z. 
  Axiom epp_global_e : cap_lang.decodePermPair global_e = (E,Global).

  (* crtcls instructions *)
  (* f_m denotes the offset to the malloc capability in the lookup table *)
  (* crtcls assumes that the code lies in register r_t1 and the variable lies in r_t2 *)
  Definition crtcls_instrs f_m :=
    [move_r r_t4 r_t1;
    move_r r_t5 r_t2] ++ 
    malloc_instrs f_m 8 ++ 
    [store_z r_t1 v1;
    lea_z r_t1 1;
    store_z r_t1 v2;
    lea_z r_t1 1;
    store_z r_t1 v3;
    lea_z r_t1 1;
    store_z r_t1 v4;
    lea_z r_t1 1;
    store_z r_t1 v5;
    lea_z r_t1 1;
    store_z r_t1 v6;
    lea_z r_t1 1;
    store_r r_t1 r_t4;
    move_z r_t4 0;
    lea_z r_t1 1;
    store_r r_t1 r_t5;
    move_z r_t5 0;
    lea_z r_t1 (-7)%Z;
    restrict_z r_t1 global_e].

  Definition crtcls f_m a p : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(crtcls_instrs f_m), a_i ↦ₐ[p] w_i)%I.

  (* crtcls spec *)
  Lemma crtcls_spec W f_m wvar wcode a pc_p pc_p' pc_g pc_b pc_e
        a_first a_last b_link a_link e_link a_entry rmap cont φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    PermFlows pc_p pc_p' →
    contiguous_between a a_first a_last →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    isLocalWord wcode = false → (* the closure must be a Global Word! *)
    isLocalWord wvar = false → (* the closure must be a Global Word! *)


      ▷ crtcls f_m a pc_p'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ inv malloc_γ ([[b_m,e_m]] ↦ₐ[p_m] [[malloc_subroutine]])
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ[RW] inr (E,Global,b_m,e_m,a_m)
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ r_t1 ↦ᵣ wcode
    ∗ ▷ r_t2 ↦ᵣ wvar
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* current world *)
    ∗ ▷ region W
    ∗ ▷ sts_full_world W
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ crtcls f_m a pc_p'
            ∗ pc_b ↦ₐ[pc_p'] inr (RW,Global,b_link,e_link,a_link)
            ∗ a_entry ↦ₐ[RW] inr (E,Global,b_m,e_m,a_m)
            (* the newly allocated region *)
            ∗ (∃ (b e : Addr), ⌜(e - b = 8)%Z⌝ ∧ r_t1 ↦ᵣ inr (E,Global,b,e,b)
            ∗ [[b,e]] ↦ₐ[RWX] [[ [inl v1;inl v2;inl v3;inl v4;inl v5;inl v6;wcode;wvar] ]]
            ∗ r_t0 ↦ᵣ cont
            ∗ r_t2 ↦ᵣ inl 0%Z
            ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=inl 0%Z]> (<[r_t4:=inl 0%Z]> (<[r_t5:=inl 0%Z]> rmap)), r_i ↦ᵣ w_i)
            (* the newly allocated region is fresh in the current world *)
            ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝
            ∗ region W
            ∗ sts_full_world W)
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hfl Hcont Hwb Ha_entry Hrmap_dom Hlocal Hlocal')
            "(>Hprog & >HPC & #Hmalloc & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hr & Hsts & Hφ)".
    (* get some registers out of regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t4)) as [rv4 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* move r_t4 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t4 $Hr_t1]");
      [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|].
    iEpilogue "(HPC & Hprog_done & Hr_t4 & Hr_t1)".
    (* move r_t5 r_t2 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t2]");
      [apply move_r_i|apply Hfl|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto|].
    iEpilogue "(HPC & Hi & Hr_t5 & Hr_t2)"; iCombine "Hi Hprog_done" as "Hprog_done".
    assert (contiguous_between (a0 :: l) a0 a_last) as Hcont'.
    { apply contiguous_between_cons_inv in Hcont as [_ (? & ? & Hcont)].
      apply contiguous_between_cons_inv in Hcont as [_ (? & ? & Hcont)].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst. apply Hcont. }
    (* malloc 8 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog rest link) "(Hmalloc_prog & Hprog & #Hcont)";[apply Hcont'|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    (* we start by putting the registers back together *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs".
      by rewrite lookup_delete_ne // lookup_delete.
      rewrite delete_commute // insert_delete.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t5]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete.
      rewrite insert_commute // insert_delete.
    assert (∀ (r:RegName), r ∈ ({[PC;r_t0;r_t1;r_t2]} : gset RegName) → rmap !! r = None) as Hnotin_rmap.
    { intros r Hr. eapply (@not_elem_of_dom _ _ (gset RegName)). typeclasses eauto.
      rewrite Hrmap_dom. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite !lookup_insert_ne //; apply Hnotin_rmap; set_solver.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
      by rewrite !lookup_insert_ne //; apply Hnotin_rmap; set_solver.
    (* apply the malloc spec *)
    iApply (malloc_spec with "[$HPC $Hmalloc_prog $Hpc_b $Ha_entry $Hr_t0 $Hregs Hr Hsts Hprog Hφ Hprog_done]");
      [|apply Hfl|apply Hcont_fetch|apply Hwb|apply Ha_entry|..].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest.
      apply contiguous_between_incr_addr with (i:=2) (ai:=a0) in Hcont;auto.
      revert Hcont Hcont_rest Hmid; clear. solve_addr. }
    { rewrite !dom_insert_L. rewrite Hrmap_dom.
      repeat (rewrite singleton_union_difference_L all_registers_union_l).
      f_equal. set_solver. }
    iSplitR;[auto|]. iFrame "Hr Hsts".
    iNext. iIntros "(HPC & Hmalloc_prog & Hpc_b & Ha_entry & Hbe)".
    iDestruct "Hbe" as (b e Hbe) "(Hr_t1& Hbe & Hr_t0 & Hregs & % & Hr & Hsts)".
    rewrite delete_insert_delete (insert_commute _ r_t2 r_t3) //.
    rewrite (delete_insert_ne _ r_t1 r_t2) // insert_insert.
    (* we now want to infer a list of contiguous addresses between b and e *)
    assert (b < e)%a as Hlt;[solve_addr|]. 
    assert (contiguous (region_addrs b e)) as Hcontbe';[apply region_addrs_contiguous|].
    apply contiguous_iff_contiguous_between in Hcontbe'. destruct Hcontbe' as [b' [e' Hcontbe] ].
    assert (exists l, l = region_addrs b e) as [h Heqh];[eauto|].
    rewrite -Heqh in Hcontbe.
    rewrite /region_mapsto /region_addrs_zeroes -Heqh. 
    assert (region_size b e = 8) as ->;[rewrite /region_size;lia|simpl]. 
    (* prepare the execution of the rest of the program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_incr_addr with (i:=2) (ai:=a0) in Hcont;auto.
      revert Hcont Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a1 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst link. 
    iDestruct (big_sepL2_length with "Hbe") as %Hlengthbe. 
    destruct h;[inversion Hlengthbe|]. 
    apply region_addrs_first in Hlt as Hfirst. rewrite -Heqh in Hfirst; inversion Hfirst. subst a2.
    apply contiguous_between_cons_inv_first in Hcontbe as Heq. subst b'. 
    assert (∀ i a', (b :: h) !! i = Some a' -> withinBounds (RWX, Global, b, e, a') = true) as Hwbbe.
    { intros i a' Hsome. apply andb_true_intro.
      apply contiguous_between_incr_addr with (i:=i) (ai:=a') in Hcontbe;[|congruence].
      apply lookup_lt_Some in Hsome. rewrite Heqh region_addrs_length in Hsome. 
      revert Hsome Hcontbe Hbe. rewrite /region_size. clear; intros. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr.
    }
    iCombine "Hmalloc_prog" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v1 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 0|..]. 
    { split;auto. apply Hwbbe with 0. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Heb)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 1|iContiguous_next Hcontbe 0|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v2 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 2|..]. 
    { split;auto. apply Hwbbe with 1. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 3|iContiguous_next Hcontbe 1|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v3 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 4|..]. 
    { split;auto. apply Hwbbe with 2. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 5|iContiguous_next Hcontbe 2|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v4 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 6|..]. 
    { split;auto. apply Hwbbe with 3. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 7|iContiguous_next Hcontbe 3|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v5 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 8|..]. 
    { split;auto. apply Hwbbe with 4. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 9|iContiguous_next Hcontbe 4|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v6 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply store_z_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 10|..]. 
    { split;auto. apply Hwbbe with 5. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 11|iContiguous_next Hcontbe 5|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 r_t4 *)
    (* first we must extract r_t4 *)
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]".
      by rewrite !lookup_insert_ne // lookup_delete_ne // lookup_insert //.
    (* then we can store *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t4 $Hr_t1 $Hb]"); 
      [apply store_r_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 12|..]. 
    { split;auto. apply Hwbbe with 6. auto. }
    { auto. }
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb".
    (* move r_t4 0 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t4]");
      [apply move_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 13|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t4)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 14|iContiguous_next Hcontbe 6|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 r_t5 *)
    (* first we must extract r_t5 *)
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]".
      rewrite lookup_delete_ne // !lookup_insert_ne // lookup_delete_ne //
              lookup_insert_ne // lookup_insert //.
    (* then we can store *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t1 $Hb]"); 
      [apply store_r_i|apply Hfl|apply PermFlows_refl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 15|..]. 
    { split;auto. apply Hwbbe with 7. auto. }
    { auto. }
    iEpilogue "(HPC & Hi & Hr_t5 & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb".
    (* move r_t4 0 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply move_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 16|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* put r_t4 and r_t5 back *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t5]") as "Hregs". by rewrite lookup_delete.
    rewrite insert_delete.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs". by rewrite lookup_insert_ne // lookup_delete.
    rewrite -(delete_insert_ne _ r_t4) // insert_delete.
    iClear "Hbe".
    (* lea r_t1 -7 *)
    destruct h;[|inversion Hlengthbe]. 
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=a23) in Hcontbe as Hnext; auto.
    assert ((a23 + (-7))%a = Some b) as Hlea.
    { apply contiguous_between_length in Hcontbe. revert Hbe Hnext Hcontbe; clear. solve_addr. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply lea_z_i|apply Hfl|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 17|apply Hlea|auto..]. 
    iEpilogue "(HPC & Hi & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* restrict r_t1 (Global,E) *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=a26) in Hcont_rest as Hlast; auto.
    iPrologue "Hprog". iClear "Hprog". 
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t1]");
      [apply restrict_r_z|apply Hfl|iCorrectPC a1 a_last|apply Hlast|auto..].
    { rewrite epp_global_e. auto. }
    rewrite epp_global_e.
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC Hpc_b Ha_entry". iSplitL "Hprog_done".
    { rewrite Heqapp.
      repeat iDestruct "Hprog_done" as "[$ Hprog_done]". iFrame. done. 
    }
    iExists b,e. iSplitR;auto.
    iFrame "Hr_t1 Hr_t0".
    iSplitL "Heb".
    { rewrite -Heqh. repeat iDestruct "Heb" as "[$ Heb]". iFrame. done. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]".
      by do 3 (rewrite lookup_insert_ne //); rewrite lookup_insert //.
    iFrame "Hr Hsts Hr_t2". iSplitL;[|auto].
    repeat (rewrite delete_insert_ne //; []). rewrite delete_insert_delete.
    rewrite !delete_insert_ne // !delete_notin; [| apply Hnotin_rmap; set_solver ..].
    do 2 (rewrite (insert_commute _ r_t4) //). rewrite insert_insert.
    do 2 (rewrite (insert_commute _ r_t5) //). rewrite insert_insert. eauto.
  Qed.

  (* ------------------------------- Closure Activation --------------------------------- *)

  Lemma closure_activation_spec pc_p pc_g b_cls e_cls r1v renvv wcode wenv φ :
    PermFlows pc_p RWX →
    readAllowed pc_p = true →
    isCorrectPC_range pc_p pc_g b_cls e_cls b_cls e_cls →
    pc_p ≠ E →
    PC ↦ᵣ inr (pc_p, pc_g, b_cls, e_cls, b_cls)
    ∗ r_t1 ↦ᵣ r1v
    ∗ r_env ↦ᵣ renvv
    ∗ [[b_cls, e_cls]]↦ₐ[RWX][[ [inl v1; inl v2; inl v3; inl v4; inl v5; inl v6; wcode; wenv] ]]
    ∗ (  PC ↦ᵣ updatePcPerm wcode
       ∗ r_t1 ↦ᵣ wcode
       ∗ r_env ↦ᵣ wenv
       ∗ [[b_cls, e_cls]]↦ₐ[RWX][[ [inl v1; inl v2; inl v3; inl v4; inl v5; inl v6; wcode; wenv] ]]
       -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hfl Hrpc Hvpc HnpcE) "(HPC & Hr1 & Hrenv & Hcls & Hcont)".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hcls") as %Hcls_len. simpl in Hcls_len.
    assert (b_cls + 8 = Some e_cls)%a as Hbe.
    { rewrite region_addrs_length /region_size in Hcls_len.
      revert Hcls_len; clear; solve_addr. }
    assert (contiguous_between (region_addrs b_cls e_cls) b_cls e_cls) as Hcont_cls.
    { apply contiguous_between_of_region_addrs; auto. revert Hbe; clear; solve_addr. }
    pose proof (region_addrs_NoDup b_cls e_cls) as Hcls_nodup.
    iDestruct (big_sepL2_split_at 6 with "Hcls") as "[Hcls_code Hcls_data]".
    cbn [take drop].
    destruct (region_addrs b_cls e_cls) as [| ? ll]; [by inversion Hcls_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_cls). subst.
    do 7 (destruct ll as [| ? ll]; [by inversion Hcls_len|]).
    destruct ll;[| by inversion Hcls_len]. cbn [take drop].
    iDestruct "Hcls_data" as "(Hcls_ptr & Hcls_env & _)".
    (* move r_t1 PC *)
    iPrologue "Hcls_code". rewrite -j_1.
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 0 | done | ..].
    iEpilogue "(HPC & Hprog_done & Hr1)".
    (* lea r_t1 7 *)
    iPrologue "Hprog". rewrite -j_2.
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
      [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 1 | | done | done | ..].
    { eapply contiguous_between_incr_addr_middle' with (i:=0); eauto.
      cbn. clear. lia. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done".
    (* load r_env r_t1 *)
    apply NoDup_ListNoDup in Hcls_nodup.
    iPrologue "Hprog". rewrite -j_3.
    (* FIXME: tedious & fragile *)
    assert ((a5 =? a0)%a = false) as H_5_0.
    { apply Z.eqb_neq. intros Heqb. assert (a5 = a0) as ->. revert Heqb; clear; solve_addr.
      exfalso. by pose proof (NoDup_lookup _ 2 7 _ Hcls_nodup eq_refl eq_refl). }
    iApply (wp_load_success with "[$HPC $Hi $Hrenv $Hr1 Hcls_env]");
      [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
       split;[done|] | iContiguous_next Hcont_cls 2 | ..].
    { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
      by eapply le_addr_withinBounds; eauto. repeat constructor. }
    { rewrite H_5_0. iFrame. eauto. }
    iEpilogue "(HPC & Hrenv & Hi & Hr1 & Hcls_env)". rewrite H_5_0.
    iCombine "Hi Hprog_done" as "Hprog_done".
    (* lea r_t1 (-1) *)
    iPrologue "Hprog". rewrite -j_4.
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
      [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 3 | | done | done | ..].
    { assert ((a4 + 1)%a = Some a5) as HH. by iContiguous_next Hcont_cls 6.
      instantiate (1 := a4). revert HH. clear; solve_addr. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    iPrologue "Hprog". rewrite -j_5.
    (* FIXME: tedious & fragile *)
    assert ((a4 =? a2)%a = false) as H_4_2.
    { apply Z.eqb_neq. intros Heqb. assert (a4 = a2) as ->. revert Heqb; clear; solve_addr.
      exfalso. by pose proof (NoDup_lookup _ 4 6 _ Hcls_nodup eq_refl eq_refl). }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr1 Hcls_ptr]");
      [(* FIXME *) auto | rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls |
       split;[done|] | iContiguous_next Hcont_cls 4 | ..].
    { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
      by eapply le_addr_withinBounds; eauto. repeat constructor. }
    { rewrite H_4_2. iFrame. eauto. }
    iEpilogue "(HPC & Hr1 & Hi & Hcls_ptr)". rewrite H_4_2.
    iCombine "Hi Hprog_done" as "Hprog_done".
    (* jmp r_t1 *)
    iPrologue "Hprog". rewrite -j_6.
    iApply (wp_jmp_success with "[$HPC $Hi $Hr1]");
      [rewrite decode_encode_inv // | done | iCorrectPC b_cls e_cls | .. ].
    iEpilogue "(HPC & Hi & Hr1)".

    iApply "Hcont". repeat (iDestruct "Hprog_done" as "(? & Hprog_done)"). iFrame.
  Qed.

End stack_macros.
