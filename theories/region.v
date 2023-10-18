From cap_machine Require Export stdpp_extra cap_lang rules_base.
(* From cap_machine Require Import rules_binary_base. *)
From iris.proofmode Require Import tactics.
From machine_utils Require Import finz_interval.
From cap_machine Require Import addr_reg. (* Required because of a weird Coq bug related to imports *)

Section region.
  Context `{MachineParameters, memG Σ, regG Σ, cfg: cfgSG Σ}.

  Lemma isWithin_finz_seq_between_decomposition {z} (a0 a1 b e : finz z):
    (b <= a0 /\ a1 <= e /\ a0 <= a1)%f ->
    finz.seq_between b e = finz.seq_between b a0 ++
                           finz.seq_between a0 a1 ++
                           finz.seq_between a1 e.
  Proof with try (unfold finz.dist; solve_addr) using.
    intros (Hba0 & Ha1e & Ha0a1).
    rewrite (finz_seq_between_split b a0 e)... f_equal.
    rewrite (finz_seq_between_split a0 a1 e)...
  Qed.

  (*--------------------------------------------------------------------------*)
  (* `region_mapsto` is a contiguous region of memory for one given version *)

  Definition region_mapsto (b e : Addr)  (v : Version) (ws : list LWord) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (map (fun a => (a,v)) (finz.seq_between b e));ws, y1 ↦ₐ y2)%I.

  Definition included (b' e' : Addr) (b e : Addr) : iProp Σ :=
    (⌜(b <= b')%a⌝ ∧ (⌜e' <= e⌝)%a)%I.

  Definition in_range (a b e : Addr) : Prop :=
    (b <= a)%a ∧ (a < e)%a.

  Lemma mapsto_decomposition:
    forall l1 l2 ws1 ws2,
      length l1 = length ws1 ->
      ([∗ list] k ↦ y1;y2 ∈ (l1 ++ l2);(ws1 ++ ws2), y1 ↦ₐ y2)%I ⊣⊢
      ([∗ list] k ↦ y1;y2 ∈ l1;ws1, y1 ↦ₐ y2)%I ∗ ([∗ list] k ↦ y1;y2 ∈ l2;ws2, y1 ↦ₐ y2)%I.
  Proof. intros. rewrite big_sepL2_app' //. Qed.

  Lemma extract_from_region b e v a ws φ :
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    (region_mapsto b e v ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ region_mapsto b a v (take n ws)
        ∗ ([∗ list] w ∈ (take n ws), φ w)
        ∗ (a, v) ↦ₐ w ∗ φ w
        ∗ region_mapsto ((a^+1))%a e v (drop (S n) ws)
        ∗ ([∗ list] w ∈ (drop (S n) ws), φ w)%I).
  Proof.
    intros. iSplit.
    - iIntros "[A B]". unfold region_mapsto.
      iDestruct (big_sepL2_length with "A") as %Hlen.
      rewrite (finz_seq_between_decomposition b a e) //.
      assert (Hlnws: n = length (take n ws)).
      { rewrite take_length. rewrite Nat.min_l; auto.
        rewrite <- Hlen. subst n.
        rewrite map_length !finz_seq_between_length /finz.dist.
        solve_addr. }
      rewrite map_length in Hlen.
      generalize (take_drop n ws). intros HWS.
      rewrite <- HWS. simpl.
      iDestruct "B" as "[HB1 HB2]".
    (*   iDestruct (mapsto_decomposition _ _ _ _ Hlnws with "A") as "[HA1 HA2]". *)
    (*   case_eq (drop n ws); intros. *)
    (*   + auto. *)
    (*   + iDestruct "HA2" as "[HA2 HA3]". *)
    (*     iDestruct "HB2" as "[HB2 HB3]". *)
    (*     generalize (drop_S' _ _ _ _ _ H3). intros Hdws. *)
    (*     rewrite <- H3. rewrite HWS. rewrite Hdws. *)
    (*     iExists w. iFrame. by rewrite <- H3. *)
    (* - iIntros "A". iDestruct "A" as (w Hws) "[A1 [B1 [A2 [B2 AB]]]]". *)
    (*   unfold region_mapsto. rewrite (finz_seq_between_decomposition b a e) //. *)
    (*   iDestruct "AB" as "[A3 B3]". *)
    (*   rewrite {5}Hws. iFrame. rewrite {3}Hws. iFrame. *)
  (* Qed. *)
  Admitted.

  Lemma extract_from_region' b e a v ws φ `{!∀ x, Persistent (φ x)}:
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    (region_mapsto b e v ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ region_mapsto b a v (take n ws)
        ∗ ([∗ list] w ∈ ws, φ w)
        ∗ (a, v) ↦ₐ w ∗ φ w
        ∗ region_mapsto (a^+1)%a e v (drop (S n) ws))%I.
  Proof.
    intros. iSplit.
    - iIntros "H".
      iDestruct (extract_from_region with "H") as (w Hws) "(?&?&?&#Hφ&?&?)"; eauto.
      iExists _. iFrame. iSplitR. iPureIntro. by rewrite {1}Hws //.
      rewrite {3}Hws. iFrame. iSplit; iApply "Hφ".
    - iIntros "H". iApply (extract_from_region with "[H]"); eauto.
      iDestruct "H" as (w Hws) "(?&Hl&?&#Hφ&?)". iExists _. iFrame.
      iSplitR. iPureIntro. by rewrite {1}Hws //.
      rewrite {1}Hws. iDestruct (big_sepL_app with "Hl") as "[? ?]".
      cbn. iFrame.
  Qed.

  Lemma extract_from_region_inv b e a (φ : Addr → iProp Σ) `{!∀ x, Persistent (φ x)}:
    (b <= a ∧ a < e)%a →
    ⊢ (([∗ list] a' ∈ (finz.seq_between b e), φ a') →
     φ a)%I.
  Proof.
    iIntros (Ha) "#Hreg".
    generalize (finz_seq_between_decomposition _ _ _ Ha); intro HRA. rewrite HRA.
    iDestruct (big_sepL_app with "Hreg") as "[Hlo Hhi] /=".
    iDestruct "Hhi" as "[$ _]".
  Qed.

  Lemma extract_from_region_inv_2 b e a ws (φ : Addr → Word → iProp Σ)
        `{!∀ x y, Persistent (φ x y)}:
    let n := length (finz.seq_between b a) in
    (b <= a ∧ a < e)%a →
    ⊢ (([∗ list] a';w' ∈ (finz.seq_between b e);ws, φ a' w') →
     ∃ w, φ a w ∗ ⌜ws = (take n ws) ++ w :: (drop (S n) ws)⌝)%I.
  Proof.
    iIntros (n Ha) "#Hreg".
    iDestruct (big_sepL2_length with "Hreg") as %Hlen.
    rewrite (finz_seq_between_decomposition b a e) //.
    assert (Hlnws: n = length (take n ws)).
    { rewrite take_length. rewrite Nat.min_l; auto.
      rewrite <- Hlen. subst n. rewrite !finz_seq_between_length /finz.dist.
      solve_addr. }
    generalize (take_drop n ws). intros HWS.
    rewrite <- HWS.
    iDestruct (big_sepL2_app_inv_l _ (finz.seq_between b a) (a :: finz.seq_between _ e)
                 with "Hreg") as (l1 l2 Hws2) "[Hl1 Hl2]".
    destruct l2; auto.
    simpl. iDestruct "Hl2" as "[Ha Hl2]".
    iExists w. iFrame "#".
    iDestruct (big_sepL2_length with "Hl1") as %Hlenl1.
    iDestruct (big_sepL2_length with "Hl2") as %Hlenl2.
    iPureIntro.
    rewrite take_app_alt //.
    assert (drop n ws = w :: l2) as Heql2.
    { apply app_inj_1 in Hws2 as [_ Heq]; auto.
        by rewrite -Hlnws. }
    rewrite (drop_S' _ (take n ws ++ drop n ws) n w (l2)); try congruence.
  Qed.

  Notation "[[ b , e ]] ↦ₐ{ v } [[ ws ]]" := (region_mapsto b e v ws)
            (at level 50, format "[[ b , e ]] ↦ₐ{ v } [[ ws ]]") : bi_scope.

  Lemma region_mapsto_cons
      (b b' e : Addr) (v : Version) (w : LWord) (ws : list LWord) :
    (b + 1)%a = Some b' → (b' <= e)%a →
    [[b, e]] ↦ₐ{ v } [[ w :: ws ]] ⊣⊢ (b,v) ↦ₐ w ∗ [[b', e]] ↦ₐ{ v } [[ ws ]].
  Proof.
    intros Hb' Hb'e.
    rewrite /region_mapsto.
    rewrite (finz_seq_between_decomposition b b e).
    2: revert Hb' Hb'e; clear; intros; split; solve_addr.
    rewrite finz_seq_between_empty /=.
    2: clear; solve_addr.
    rewrite (_: (b ^+ 1) = b')%a.
    2: revert Hb' Hb'e; clear; intros; solve_addr.
    eauto.
  Qed.

  Lemma region_mapsto_single b e v l:
    (b+1)%a = Some e →
    [[b,e]] ↦ₐ{v}  [[l]] -∗
    ∃ lw, (b,v) ↦ₐ lw ∗ ⌜l = [lw]⌝.
  Proof.
    iIntros (Hbe) "H". rewrite /region_mapsto finz_seq_between_singleton //.
    iDestruct (big_sepL2_length with "H") as %Hlen.
    cbn in Hlen. destruct l as [|x l']; [by inversion Hlen|].
    destruct l'; [| by inversion Hlen]. iExists x. cbn.
    iDestruct "H" as "(H & _)". eauto.
  Qed.

  Lemma region_mapsto_split  (b e a : Addr) (v : Version) (w1 w2 : list LWord) :
     (b ≤ a ≤ e)%Z →
     (length w1) = (finz.dist b a) →
     ([[b,e]]↦ₐ{v}[[w1 ++ w2]] ⊣⊢ [[b,a]]↦ₐ{v}[[w1]] ∗ [[a,e]]↦ₐ{v}[[w2]])%I.
   Proof with try (rewrite /finz.dist; solve_addr).
     intros [Hba Hae] Hsize.
     iSplit.
     - iIntros "Hbe".
       rewrite /region_mapsto /finz.seq_between.
       rewrite (finz_seq_decomposition _ _ (finz.dist b a))...
       rewrite map_app.
       iDestruct (big_sepL2_app' with "Hbe") as "[Hba Ha'b]".
       + by rewrite map_length finz_seq_length.
       + iFrame.
         rewrite (_: (b ^+ finz.dist b a)%a = a)...
         rewrite (_: finz.dist a e = finz.dist b e - finz.dist b a)...
         (* todo: turn these two into lemmas *)
     - iIntros "[Hba Hae]".
       rewrite /region_mapsto /finz.seq_between. (* todo: use a proper region splitting lemma *)
       rewrite (finz_seq_decomposition (finz.dist b e) _ (finz.dist b a))...
       rewrite map_app.
       iApply (big_sepL2_app with "Hba [Hae]"); cbn.
       rewrite (_: (b ^+ finz.dist b a)%a = a)...
       rewrite (_: finz.dist b e - finz.dist b a = finz.dist a e)...
   Qed.

   (*--------------------------------------------------------------------------*)

  (* Definition region_mapsto_spec (b e : Addr) (ws : list Word) : iProp Σ := *)
  (*   ([∗ list] k↦y1;y2 ∈ (finz.seq_between b e);ws, y1 ↣ₐ y2)%I. *)

  (* Lemma mapsto_decomposition_spec: *)
  (*   forall l1 l2 ws1 ws2, *)
  (*     length l1 = length ws1 -> *)
  (*     ([∗ list] k ↦ y1;y2 ∈ (l1 ++ l2);(ws1 ++ ws2), y1 ↣ₐ y2)%I ⊣⊢ *)
  (*     ([∗ list] k ↦ y1;y2 ∈ l1;ws1, y1 ↣ₐ y2)%I ∗ ([∗ list] k ↦ y1;y2 ∈ l2;ws2, y1 ↣ₐ y2)%I. *)
  (* Proof. intros. rewrite big_sepL2_app' //. Qed. *)

  (* Lemma extract_from_region_spec b e a ws φ : *)
  (*   let n := length (finz.seq_between b a) in *)
  (*   (b <= a ∧ a < e)%a → *)
  (*   (region_mapsto_spec b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢ *)
  (*    (∃ w, *)
  (*       ⌜ws = take n ws ++ (w::drop (S n) ws)⌝ *)
  (*       ∗ region_mapsto_spec b a (take n ws) *)
  (*       ∗ ([∗ list] w ∈ (take n ws), φ w) *)
  (*       ∗ a ↣ₐ w ∗ φ w *)
  (*       ∗ region_mapsto_spec (a^+1)%a e (drop (S n) ws) *)
  (*       ∗ ([∗ list] w ∈ (drop (S n) ws), φ w)%I). *)
  (* Proof. *)
  (*   intros. iSplit. *)
  (*   - iIntros "[A B]". unfold region_mapsto_spec. *)
  (*     iDestruct (big_sepL2_length with "A") as %Hlen. *)
  (*     rewrite (finz_seq_between_decomposition b a e) //. *)
  (*     assert (Hlnws: n = length (take n ws)). *)
  (*     { rewrite take_length. rewrite Nat.min_l; auto. *)
  (*       rewrite <- Hlen. subst n. rewrite !finz_seq_between_length /finz.dist. *)
  (*       solve_addr. } *)
  (*     generalize (take_drop n ws). intros HWS. *)
  (*     rewrite <- HWS. simpl. *)
  (*     iDestruct "B" as "[HB1 HB2]". *)
  (*     iDestruct (mapsto_decomposition_spec _ _ _ _ Hlnws with "A") as "[HA1 HA2]". *)
  (*     case_eq (drop n ws); intros. *)
  (*     + auto. *)
  (*     + iDestruct "HA2" as "[HA2 HA3]". *)
  (*       iDestruct "HB2" as "[HB2 HB3]". *)
  (*       generalize (drop_S' _ _ _ _ _ H3). intros Hdws. *)
  (*       rewrite <- H3. rewrite HWS. rewrite Hdws. *)
  (*       iExists w. iFrame. by rewrite <- H3. *)
  (*   - iIntros "A". iDestruct "A" as (w Hws) "[A1 [B1 [A2 [B2 AB]]]]". *)
  (*     unfold region_mapsto_spec. rewrite (finz_seq_between_decomposition b a e) //. *)
  (*     iDestruct "AB" as "[A3 B3]". *)
  (*     rewrite {5}Hws. iFrame. rewrite {3}Hws. iFrame. *)
  (* Qed. *)

  (* Lemma extract_from_region_spec' b e a ws φ `{!∀ x, Persistent (φ x)}: *)
  (*   let n := length (finz.seq_between b a) in *)
  (*   (b <= a ∧ a < e)%a → *)
  (*   (region_mapsto_spec b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢ *)
  (*    (∃ w, *)
  (*       ⌜ws = take n ws ++ (w::drop (S n) ws)⌝ *)
  (*       ∗ region_mapsto_spec b a (take n ws) *)
  (*       ∗ ([∗ list] w ∈ ws, φ w) *)
  (*       ∗ a ↣ₐ w ∗ φ w *)
  (*       ∗ region_mapsto_spec (a^+1)%a e (drop (S n) ws))%I. *)
  (* Proof. *)
  (*   intros. iSplit. *)
  (*   - iIntros "H". *)
  (*     iDestruct (extract_from_region_spec with "H") as (w Hws) "(?&?&?&#Hφ&?&?)"; eauto. *)
  (*     iExists _. iFrame. iSplitR. iPureIntro. by rewrite {1}Hws //. *)
  (*     rewrite {3}Hws. iFrame. iSplit; iApply "Hφ". *)
  (*   - iIntros "H". iApply (extract_from_region_spec with "[H]"); eauto. *)
  (*     iDestruct "H" as (w Hws) "(?&Hl&?&#Hφ&?)". iExists _. iFrame. *)
  (*     iSplitR. iPureIntro. by rewrite {1}Hws //. *)
  (*     rewrite {1}Hws. iDestruct (big_sepL_app with "Hl") as "[? ?]". *)
  (*     cbn. iFrame. *)
  (* Qed. *)

  (* Notation "[[ b , e ]] ↣ₐ [[ ws ]]" := (region_mapsto_spec b e ws) *)
  (*           (at level 50, format "[[ b , e ]] ↣ₐ [[ ws ]]") : bi_scope. *)

  (* Lemma region_mapsto_cons_spec *)
  (*     (b b' e : Addr) (w : Word) (ws : list Word) : *)
  (*   (b + 1)%a = Some b' → (b' <= e)%a → *)
  (*   [[b, e]] ↣ₐ [[ w :: ws ]] ⊣⊢ b ↣ₐ w ∗ [[b', e]] ↣ₐ [[ ws ]]. *)
  (* Proof. *)
  (*   intros Hb' Hb'e. *)
  (*   rewrite /region_mapsto_spec. *)
  (*   rewrite (finz_seq_between_decomposition b b e). *)
  (*   2: revert Hb' Hb'e; clear; intros; split; solve_addr. *)
  (*   rewrite finz_seq_between_empty /=. *)
  (*   2: clear; solve_addr. *)
  (*   rewrite (_: (b ^+ 1) = b')%a. *)
  (*   2: revert Hb' Hb'e; clear; intros; solve_addr. *)
  (*   eauto. *)
  (* Qed. *)

  (* Lemma region_mapsto_single_spec b e l: *)
  (*   (b+1)%a = Some e → *)
  (*   [[b,e]] ↣ₐ [[l]] -∗ *)
  (*   ∃ v, b ↣ₐ v ∗ ⌜l = [v]⌝. *)
  (* Proof. *)
  (*   iIntros (Hbe) "H". rewrite /region_mapsto_spec finz_seq_between_singleton //. *)
  (*   iDestruct (big_sepL2_length with "H") as %Hlen. *)
  (*   cbn in Hlen. destruct l as [|x l']; [by inversion Hlen|]. *)
  (*   destruct l'; [| by inversion Hlen]. iExists x. cbn. *)
  (*   iDestruct "H" as "(H & _)". eauto. *)
  (* Qed. *)

  (* Lemma region_mapsto_split_spec  (b e a : Addr) (w1 w2 : list Word) : *)
  (*    (b ≤ a ≤ e)%Z → *)
  (*    (length w1) = (finz.dist b a) → *)
  (*    ([[b,e]]↣ₐ[[w1 ++ w2]] ⊣⊢ [[b,a]]↣ₐ[[w1]] ∗ [[a,e]]↣ₐ[[w2]])%I. *)
  (*  Proof with try (rewrite /finz.dist; solve_addr). *)
  (*    intros [Hba Hae] Hsize. *)
  (*    iSplit. *)
  (*    - iIntros "Hbe". *)
  (*      rewrite /region_mapsto_spec /finz.seq_between. *)
  (*      rewrite (finz_seq_decomposition _ _ (finz.dist b a))... *)
  (*      iDestruct (big_sepL2_app' with "Hbe") as "[Hba Ha'b]". *)
  (*      + by rewrite finz_seq_length. *)
  (*      + iFrame. *)
  (*        rewrite (_: (b ^+ finz.dist b a)%a = a)... *)
  (*        rewrite (_: finz.dist a e = finz.dist b e - finz.dist b a)... *)
  (*        (* todo: turn these two into lemmas *) *)
  (*    - iIntros "[Hba Hae]". *)
  (*      rewrite /region_mapsto_spec /finz.seq_between. (* todo: use a proper region splitting lemma *) *)
  (*      rewrite (finz_seq_decomposition (finz.dist b e) _ (finz.dist b a))... *)
  (*      iApply (big_sepL2_app with "Hba [Hae]"); cbn. *)
  (*      rewrite (_: (b ^+ finz.dist b a)%a = a)... *)
  (*      rewrite (_: finz.dist b e - finz.dist b a = finz.dist a e)... *)
  (*  Qed. *)


End region.

(* TODO included and in_range might need to be defined in terms of logical addresses instead *)
Global Notation "[[ b , e ]] ↦ₐ{ v } [[ ws ]]" := (region_mapsto b e v ws)
            (at level 50, format "[[ b , e ]] ↦ₐ{ v } [[ ws ]]") : bi_scope.

Global Notation "[[ b , e ]] ⊂ₐ [[ b' , e' ]]" := (included b e b' e')
            (at level 50, format "[[ b , e ]] ⊂ₐ [[ b' , e' ]]") : bi_scope.

Global Notation "a ∈ₐ [[ b , e ]]" := (in_range a b e)
            (at level 50, format "a ∈ₐ [[ b , e ]]") : bi_scope.

(* Global Notation "[[ b , e ]] ↣ₐ [[ ws ]]" := (region_mapsto_spec b e ws) *)
(*             (at level 50, format "[[ b , e ]] ↣ₐ [[ ws ]]") : bi_scope. *)


Section codefrag.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

Definition codefrag (a: Addr) (v : Version) (cs: list LWord) :=
  ([[ a, (a ^+ length cs)%a ]] ↦ₐ{ v } [[ cs ]])%I.

Lemma codefrag_contiguous_region a v cs :
  codefrag a v cs -∗
  ⌜ContiguousRegion a (length cs)⌝.
Proof using.
  iIntros "Hcs". unfold codefrag.
  iDestruct (big_sepL2_length with "Hcs") as %Hl.
  set an := (a + length cs)%a in Hl |- *.
  unfold ContiguousRegion.
  destruct an eqn:Han; subst an; [ by eauto |]. cbn.
  exfalso. rewrite map_length finz_seq_between_length /finz.dist in Hl.
  solve_addr.
Qed.

End codefrag.
