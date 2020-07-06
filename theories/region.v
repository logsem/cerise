From cap_machine Require Export cap_lang rules_base.
From cap_machine Require Import addr_reg. (* Required because of a weird Coq bug related to imports *)
From iris.proofmode Require Import tactics.

Section region.
  Context `{MachineParameters, memG Σ, regG Σ, MonRef: MonRefG (leibnizO _) CapR_rtc Σ}.

  (*------------------------- region_size ------------------------------------*)

  Definition region_size : Addr → Addr → nat :=
    λ b e, Z.to_nat (e - b).

  Lemma region_size_S a b :
    (a < b)%a ->
    region_size a b = S (region_size (^(a+1))%a b).
  Proof. rewrite /region_size. solve_addr. Qed.

  Lemma region_size_0 a b :
    (b <= a)%a ->
    region_size a b = 0.
  Proof. rewrite /region_size. solve_addr. Qed.

  Lemma region_size_split (a b e : Addr) :
    (b ≤ a ≤ e)%Z →
    region_size b e = region_size b a + region_size a e.
  Proof. intros [? ?]. rewrite /region_size. solve_addr. Qed.

  Lemma get_addr_from_option_addr_region_size (a b : Addr) :
    (b ≤ a)%Z →
    (^(b + region_size b a) = a)%a.
  Proof. intros Hle. rewrite /region_size. solve_addr. Qed.

  Lemma incr_addr_region_size (a b : Addr) :
    (b <= a)%a →
    (b + region_size b a)%a = Some a.
  Proof. intros. unfold region_size. solve_addr. Qed.

  Lemma incr_addr_region_size_iff (a b : Addr) (i : nat) :
    (a + i)%a = Some b ↔ (a <= b)%a ∧ region_size a b = i.
  Proof.
    rewrite /region_size. split; [ intros | intros [? ?] ]; solve_addr.
  Qed.

  (*-------------------------- region_addrs_aux ------------------------------*)

  Fixpoint region_addrs_aux (b: Addr) (n: nat): list Addr :=
    match n with
    | 0 => nil
    | S n => b :: (region_addrs_aux (^(b + 1)%a) n)
    end.

  Lemma region_addrs_aux_length:
    forall n b,
      length (region_addrs_aux b n) = n.
  Proof. induction n; intros; simpl; auto. Qed.

  Definition region_addrs_aux_singleton (a : Addr) :
    [a] = region_addrs_aux a 1. Proof. done. Qed.

  Lemma region_addrs_aux_decomposition n b k :
    (k <= n)%nat ->
    region_addrs_aux b n = region_addrs_aux b k ++ (region_addrs_aux (^(b + k)%a) (n - k)).
  Proof.
    revert b k. induction n.
    - intros. assert ((k = 0)%nat) by lia; subst k. reflexivity.
    - intros * HH. inv HH.
      + rewrite Nat.sub_diag. simpl. rewrite app_nil_r //.
      + simpl. destruct k; simpl. by rewrite addr_add_0.
        rewrite (IHn (^(b+1))%a k); [|lia]. do 3 f_equal. solve_addr.
  Qed.

  Lemma region_addrs_aux_spec n b k :
    (k < n)%nat ->
    nth_error (region_addrs_aux b n) k = Some (^(b + k)%a).
  Proof.
    revert b k. induction n; intros.
    - lia.
    - assert (X: k = n \/ k < n) by omega; destruct X as [X | X].
      + subst k. destruct n; simpl.
        * f_equal. solve_addr.
        * rewrite IHn; [| lia]. f_equal. solve_addr.
      + rewrite <- IHn; auto.
        rewrite (region_addrs_aux_decomposition (S n) b n); [| lia].
        rewrite nth_error_app1; auto.
        rewrite region_addrs_aux_length. auto.
  Qed.

  Lemma not_elem_of_region_addrs_aux a n (i : Z) :
     (i > 0)%Z →
     a ≠ addr_reg.top →
     a ∉ region_addrs_aux (^(a + i)%a) n.
   Proof.
     intros Hi Hne.
     revert i Hi; induction n; intros i Hi.
     - apply not_elem_of_nil.
     - simpl. apply not_elem_of_cons; split.
       + intro. apply Hne. solve_addr.
       + rewrite get_addrs_from_option_addr_comm.
         apply IHn; omega. omega. omega. 
   Qed.

   Lemma region_addrs_not_elem_of a n :
     forall a', (a < a')%a -> a ∉ (region_addrs_aux a' n).
   Proof.
     induction n.
     - intros a' Ha'. apply not_elem_of_nil.
     - intros a' Ha'. apply not_elem_of_cons.
       split.
       + intros Hcontr; subst. rewrite /lt_addr in Ha'. lia.
       + apply IHn. rewrite /lt_addr in Ha'. rewrite /lt_addr.
         destruct (a' + 1)%a eqn:Hsome; simpl.
         ++ apply next_lt in Hsome. lia.
         ++ destruct a,a'. simpl in *. apply Z.leb_le in fin0 as Hle. lia.
   Qed.

  Lemma region_addrs_aux_next_head a (a0 a1 : Addr) n :
    ((region_addrs_aux (^a)%a n) !! 0) = Some a0 →
    ((region_addrs_aux (^a)%a n) !! (1)) = Some a1 →
    (^(a0 + 1)%a = a1).
  Proof.
    intros Ha0 Ha1.
    destruct n as [| n]; cbn in *; [ by inversion Ha0 |].
    destruct n as [| n]; cbn in *; [ by inversion Ha1 |].
    solve_addr.
  Qed.

  Lemma region_addrs_aux_next a n i ai aj :
    ((region_addrs_aux a n) !! i) = Some ai → ((region_addrs_aux a n) !! (i + 1)) = Some aj →
    ^(ai + 1)%a = aj.
  Proof.
    intros Hai Haj.
    assert (i + 1 < n).
    { rewrite -(region_addrs_aux_length n a).
      apply lookup_lt_is_Some_1. eauto. }
    assert (i < n).
    { rewrite -(region_addrs_aux_length n a).
      apply lookup_lt_is_Some_1. eauto. }
    rewrite (region_addrs_aux_decomposition n a i) in Hai; last lia.
    rewrite lookup_app_r region_addrs_aux_length in Hai |- *; last lia.
    rewrite (region_addrs_aux_decomposition n a i) in Haj; last lia.
    rewrite lookup_app_r region_addrs_aux_length in Haj |- *; last lia.
    rewrite minus_plus in Haj. rewrite Nat.sub_diag in Hai.
    eapply region_addrs_aux_next_head; eauto.
  Qed.

  Lemma region_addrs_lt_top (a: Addr) n i ai :
    (a + (Z.of_nat i) < MemNum)%Z →
    region_addrs_aux a n !! i = Some ai → ai ≠ top.
  Proof.
    intros Ha Hai.
    assert (length (region_addrs_aux a n) = n) as Hlen.
    { apply region_addrs_aux_length. }
    assert (length (region_addrs_aux a i) = i) as Hleni.
    { apply region_addrs_aux_length. }
    assert (i < n) as Hi.
    { rewrite -Hlen. by apply lookup_lt_Some with ai. }
    rewrite (region_addrs_aux_decomposition n a i) in Hai; last lia.
    rewrite lookup_app_r in Hai; last lia.
    rewrite Hleni Nat.sub_diag in Hai.
    destruct (n - i) eqn:Hni; cbn in Hai; [ congruence |].
    inversion Hai; subst ai. intro. solve_addr.
  Qed.

  Lemma region_addrs_aux_NoDup (a: Addr) (n: nat) :
    is_Some (a + n)%a →
    NoDup (region_addrs_aux a n).
  Proof.
    generalize a. clear a. induction n; intros a Hsome.
    - apply NoDup_nil; auto.
    - cbn. apply NoDup_cons; split.
      + eapply not_elem_of_region_addrs_aux; first lia.
        destruct Hsome as [? ?]. intros ->. solve_addr.
      + eapply IHn. destruct Hsome as [? ?]. unfold is_Some.
        zify_addr; first [ by eauto | lia ].
  Qed.

  (*---------------------------- region_addrs --------------------------------*)

  Definition region_addrs (b e: Addr): list Addr :=
    region_addrs_aux b (region_size b e).

  Lemma region_addrs_length:
    forall b e,
      length (region_addrs b e) = region_size b e.
  Proof.
    intros; unfold region_addrs. by rewrite region_addrs_aux_length.
  Qed.

  Lemma region_addrs_spec:
    forall b e k,
      (b <= e)%a ->
      (k < region_size b e)%nat ->
      nth_error (region_addrs b e) k = Some (^(b + k)%a).
  Proof.
    intros; unfold region_addrs.
    destruct (Z_le_dec b e).
    - apply region_addrs_aux_spec; auto.
    - elim n. solve_addr.
  Qed.

  Lemma region_addrs_empty b e:
    (e <= b)%a ->
    region_addrs b e = nil.
  Proof.
    intros. rewrite /region_addrs /region_size /=.
    replace (Z.to_nat (e - b)) with 0 by solve_addr.
    reflexivity.
  Qed.

  Lemma region_addrs_decomposition b a e :
    (b <= a /\ a < e)%a ->
    region_addrs b e = region_addrs b a ++ (a :: region_addrs ^(a+1)%a e).
  Proof with try (unfold region_size; solve_addr).
    intros [? ?]. unfold region_addrs at 1.
    rewrite (region_addrs_aux_decomposition _ _ (region_size b a))...
    rewrite (_ : region_size b e - region_size b a = region_size a e)...
    rewrite -/(region_addrs b a). f_equal.
    rewrite (_ : region_size a e = S (region_size ^(a+1)%a e))...
    cbn. f_equal... rewrite /region_addrs. f_equal...
  Qed.

  Lemma region_addrs_split b a e :
    (b <= a ∧ a <= e)%a →
    region_addrs b e = region_addrs b a ++ region_addrs a e.
  Proof with try (unfold region_size; solve_addr).
    intros [? ?]. unfold region_addrs at 1.
    rewrite (region_addrs_aux_decomposition _ _ (region_size b a))...
    rewrite (_: region_size b e - region_size b a = region_size a e)...
    rewrite (_: ^(b + region_size b a)%a = a)...
    rewrite -/(region_addrs _ _) //.
  Qed.

  Lemma isWithin_region_addrs_decomposition a0 a1 b e:
    (b <= a0 /\ a1 <= e /\ a0 <= a1)%a ->
    region_addrs b e = region_addrs b a0 ++
                       region_addrs a0 a1 ++
                       region_addrs a1 e.
  Proof with try (unfold region_size; solve_addr).
    intros (Hba0 & Ha1e & Ha0a1).
    rewrite (region_addrs_split b a0 e)... f_equal.
    rewrite (region_addrs_split a0 a1 e)...
  Qed.

  Lemma region_addrs_first a b :
    (a < b)%a ->
    (region_addrs a b) !! 0 = Some a.
  Proof.
    intros Hle.
    rewrite /region_addrs.
    rewrite (_: region_size a b = S (region_size a b - 1)).
    2: by (unfold region_size; solve_addr). done.
  Qed.

  Lemma region_addrs_NoDup a b :
    NoDup (region_addrs a b).
  Proof.
    rewrite /region_addrs. destruct (Z_le_dec a b).
    - apply region_addrs_aux_NoDup.
      rewrite incr_addr_region_size; eauto.
    - rewrite /region_size Z_to_nat_nonpos; [| lia]. by apply NoDup_nil.
  Qed.

  Lemma region_addrs_cons a e :
    (a < e)%a →
    region_addrs a e = a :: region_addrs (^(a+1))%a e.
  Proof.
    intros. rewrite (region_addrs_decomposition a a). 2: solve_addr.
    rewrite /region_addrs region_size_0 //. solve_addr.
  Qed.

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

  Lemma elem_of_region_addrs (a b e: Addr):
    a ∈ region_addrs b e ↔ (b <= a)%a ∧ (a < e)%a.
  Proof.
    rewrite /region_addrs /region_size.
    set n := Z.to_nat (e - b). have: (n = Z.to_nat (e - b)) by reflexivity.
    clearbody n. revert n a b e. induction n.
    { intros. cbn. rewrite elem_of_nil. solve_addr. }
    { intros. cbn. rewrite elem_of_cons (IHn a _ e). 2: solve_addr.
      split. intros [ -> | ]; solve_addr. intros [Hba ?].
      apply Zle_lt_or_eq in Hba. destruct Hba; [| subst]. solve_addr.
      assert (b = a) by solve_addr. subst. solve_addr. }
  Qed.

  Lemma not_elem_of_region_addrs (a b e: Addr):
    a ∉ region_addrs b e ↔ (a < b)%a ∨ (e <= a)%a.
  Proof.
    destruct (decide ((a < b)%a ∨ (e <= a)%a)) as [X1|X1];
    destruct (decide (a ∈ region_addrs b e)) as [X2|X2].
    - rewrite -> elem_of_region_addrs in *. solve_addr.
    - split; auto.
    - rewrite -> elem_of_region_addrs in *. solve_addr.
    - split; auto. intros _. exfalso. apply X2, elem_of_region_addrs. solve_addr.
  Qed.

  Lemma region_addrs_not_elem_of_le a (n : nat) b a' :
    (b + n)%a = Some a -> (a <= a')%a -> a' ∉ (region_addrs_aux b n).
  Proof.
    revert b a'. induction n.
    - intros * Ha' Hle. apply not_elem_of_nil.
    - intros * Ha' Hle. apply not_elem_of_cons.
      split.
      + intros Hcontr;subst. solve_addr.
      + apply IHn; solve_addr.
  Qed.

   Lemma region_addrs_xor_elem_of (a b c e : Addr) :
     (b <= c < e)%Z ->
     a ∈ region_addrs b e ->
     (a ∈ region_addrs b c ∧ a ∉ region_addrs c e) ∨ (a ∉ region_addrs b c ∧ a ∈ region_addrs c e).
   Proof.
     intros Hbounds Ha.
     rewrite (region_addrs_split _ c) in Ha;auto. 2: solve_addr.
     apply elem_of_app in Ha. rewrite ->!elem_of_region_addrs in *. solve_addr.
   Qed.

  Lemma region_addrs_single b e:
    (b+1)%a = Some e →
    region_addrs b e = [b].
  Proof.
    intros. rewrite /region_addrs.
    rewrite (_: region_size b e = 1) //= /region_size.
    solve_addr.
  Qed.

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

  Lemma region_addrs_submseteq b b' e e':
    (b' <= b)%a ->
    (e <= e')%a ->
    region_addrs b e ⊆+ region_addrs b' e'.
  Proof.
    intros. destruct (Addr_le_dec b e).
    - rewrite (region_addrs_split b' b e'); [|solve_addr].
      rewrite (region_addrs_split b e e'); [|solve_addr].
      eapply submseteq_middle.
    - rewrite region_addrs_empty; [|solve_addr].
      eapply submseteq_nil_l.
  Qed.

  (*--------------------------------------------------------------------------*)

  Definition region_mapsto (b e : Addr) (p : Perm) (ws : list Word) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (region_addrs b e);ws, y1 ↦ₐ[p] y2)%I.

  Definition included (b' e' : Addr) (b e : Addr) : iProp Σ :=
    (⌜(b <= b')%a⌝ ∧ (⌜e' <= e⌝)%a)%I.

  Definition in_range (a b e : Addr) : Prop :=
    (b <= a)%a ∧ (a < e)%a.

  Lemma mapsto_decomposition:
    forall l1 l2 p ws1 ws2,
      length l1 = length ws1 ->
      ([∗ list] k ↦ y1;y2 ∈ (l1 ++ l2);(ws1 ++ ws2), y1 ↦ₐ[p] y2)%I ⊣⊢
      ([∗ list] k ↦ y1;y2 ∈ l1;ws1, y1 ↦ₐ[p] y2)%I ∗ ([∗ list] k ↦ y1;y2 ∈ l2;ws2, y1 ↦ₐ[p] y2)%I.
  Proof.
    induction l1; intros * Hlen.
    - iSplit; iIntros "A".
      + simpl. destruct ws1; simpl in Hlen; try congruence.
        simpl. auto.
      + simpl. destruct ws1; simpl in Hlen; try congruence.
        simpl. iDestruct "A" as "[A B]". auto.
    - iSplit; iIntros "A".
      + destruct ws1; simpl in H1; try congruence. inv Hlen.
        simpl. iDestruct "A" as "[A B]".
        iFrame.
        iApply IHl1; auto.
      + destruct ws1; simpl in H1; try congruence. inv Hlen.
        simpl. iDestruct "A" as "[A B]".
        iFrame.
  Qed.

  Lemma mapsto_length:
    forall l p ws,
      ([∗ list] k ↦ y1;y2 ∈ l;ws, y1 ↦ₐ[p] y2)%I -∗
      ⌜length l = length ws⌝.
  Proof.
    induction l; intros.
    - destruct ws; auto.
    - destruct ws; simpl; auto.
      iIntros "[A B]". iDestruct (IHl p ws with "B") as "%".
      iPureIntro. auto.
  Qed.

  Lemma drop_S:
    forall A l n (a: A) l',
      drop n l = a::l' ->
      drop (S n) l = l'.
  Proof.
    induction l; intros * HH.
    - rewrite drop_nil in HH. inv HH.
    - simpl. destruct n.
      + rewrite drop_0 in HH. inv HH.
        reflexivity.
      + simpl in HH. eapply IHl; eauto.
  Qed.

  Lemma extract_from_region b e p a ws φ :
    let n := length (region_addrs b a) in
    (b <= a ∧ a < e)%a →
    (region_mapsto b e p ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ region_mapsto b a p (take n ws)
        ∗ ([∗ list] w ∈ (take n ws), φ w)
        ∗ a ↦ₐ[p] w ∗ φ w
        ∗ region_mapsto (^(a+1))%a e p (drop (S n) ws)
        ∗ ([∗ list] w ∈ (drop (S n) ws), φ w)%I).
  Proof.
    intros. iSplit.
    - iIntros "[A B]". unfold region_mapsto.
      iDestruct (mapsto_length with "A") as %Hlen.
      rewrite (region_addrs_decomposition b a e) //.
      assert (Hlnws: n = length (take n ws)).
      { rewrite take_length. rewrite Min.min_l; auto.
        rewrite <- Hlen. subst n. rewrite !region_addrs_length /region_size.
        solve_addr. }
      generalize (take_drop n ws). intros HWS.
      rewrite <- HWS. simpl.
      iDestruct "B" as "[HB1 HB2]".
      iDestruct (mapsto_decomposition _ _ _ _ _ Hlnws with "A") as "[HA1 HA2]".
      case_eq (drop n ws); intros.
      + auto.
      + iDestruct "HA2" as "[HA2 HA3]".
        iDestruct "HB2" as "[HB2 HB3]".
        generalize (drop_S _ _ _ _ _ H3). intros Hdws.
        rewrite <- H3. rewrite HWS. rewrite Hdws.
        iExists w. iFrame. by rewrite <- H3.
    - iIntros "A". iDestruct "A" as (w Hws) "[A1 [B1 [A2 [B2 AB]]]]".
      unfold region_mapsto. rewrite (region_addrs_decomposition b a e) //.
      iDestruct "AB" as "[A3 B3]".
      rewrite {5}Hws. iFrame. rewrite {3}Hws. iFrame.
  Qed.

  Lemma extract_from_region' b e a p ws φ `{!∀ x, Persistent (φ x)}:
    let n := length (region_addrs b a) in
    (b <= a ∧ a < e)%a →
    (region_mapsto b e p ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ w,
        ⌜ws = take n ws ++ (w::drop (S n) ws)⌝
        ∗ region_mapsto b a p (take n ws)
        ∗ ([∗ list] w ∈ ws, φ w)
        ∗ a ↦ₐ[p] w ∗ φ w
        ∗ region_mapsto (^(a+1))%a e p (drop (S n) ws))%I.
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
    (([∗ list] a' ∈ (region_addrs b e), φ a') →
     φ a)%I.
  Proof.
    iIntros (Ha) "#Hreg".
    generalize (region_addrs_decomposition _ _ _ Ha); intro HRA. rewrite HRA.
    iDestruct (big_sepL_app with "Hreg") as "[Hlo Hhi] /=".
    iDestruct "Hhi" as "[$ _]".
  Qed.

  Lemma extract_from_region_inv_2 b e a ws (φ : Addr → Word → iProp Σ)
        `{!∀ x y, Persistent (φ x y)}:
    let n := length (region_addrs b a) in
    (b <= a ∧ a < e)%a →
    (([∗ list] a';w' ∈ (region_addrs b e);ws, φ a' w') →
     ∃ w, φ a w ∗ ⌜ws = (take n ws) ++ w :: (drop (S n) ws)⌝)%I.
  Proof.
    iIntros (n Ha) "#Hreg".
    iDestruct (big_sepL2_length with "Hreg") as %Hlen.
    rewrite (region_addrs_decomposition b a e) //.
    assert (Hlnws: n = length (take n ws)).
    { rewrite take_length. rewrite Min.min_l; auto.
      rewrite <- Hlen. subst n. rewrite !region_addrs_length /region_size.
      solve_addr. }
    generalize (take_drop n ws). intros HWS.
    rewrite <- HWS.
    iDestruct (big_sepL2_app_inv_l _ (region_addrs b a) (a :: region_addrs _ e)
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
    rewrite (drop_S _ (take n ws ++ drop n ws) n w (l2)); try congruence.
  Qed.

  Notation "[[ b , e ]] ↦ₐ [ p ] [[ ws ]]" := (region_mapsto b e p ws)
            (at level 50, format "[[ b , e ]] ↦ₐ [ p ] [[ ws ]]") : bi_scope.

  Lemma region_mapsto_cons
      (b b' e : Addr) (w : Word) (ws : list Word) (p : Perm) :
    (b + 1)%a = Some b' → (b' <= e)%a →
    [[b, e]] ↦ₐ [p] [[ w :: ws ]] ⊣⊢ b ↦ₐ[p] w ∗ [[b', e]] ↦ₐ [p] [[ ws ]].
  Proof.
    intros Hb' Hb'e.
    rewrite /region_mapsto.
    rewrite (region_addrs_decomposition b b e).
    2: revert Hb' Hb'e; clear; intros; split; solve_addr.
    rewrite region_addrs_empty /=.
    2: clear; solve_addr.
    rewrite (_: ^(b + 1) = b')%a.
    2: revert Hb' Hb'e; clear; intros; solve_addr.
    eauto.
  Qed.

End region.

Global Notation "[[ b , e ]] ↦ₐ [ p ] [[ ws ]]" := (region_mapsto b e p ws)
            (at level 50, format "[[ b , e ]] ↦ₐ [ p ] [[ ws ]]") : bi_scope.

Global Notation "[[ b , e ]] ⊂ₐ [[ b' , e' ]]" := (included b e b' e')
            (at level 50, format "[[ b , e ]] ⊂ₐ [[ b' , e' ]]") : bi_scope.

Global Notation "a ∈ₐ [[ b , e ]]" := (in_range a b e)
            (at level 50, format "a ∈ₐ [[ b , e ]]") : bi_scope.
