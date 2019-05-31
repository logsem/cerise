From cap_machine Require Export lang rules.
From iris.proofmode Require Import tactics.
(*Require Import Coq.Program.Wf.*)

Section region.
  Context `{memG Σ, regG Σ}.

  (* Not usable without proving some sort of rewriting rule, and can't manage to prove it *)
  (* Program Fixpoint region_addrs (b e: Addr) { measure (Z.to_nat (e - b)%Z) }: list Addr := *)
  (*   if Z.eq_dec b e then b::nil else *)
  (*     if Z_lt_dec b e then  *)
  (*       match (b + 1)%a with *)
  (*       | Some b' => b::region_addrs b' e *)
  (*       | None => False_rect _ _  *)
  (*       end *)
  (*     else nil. *)
  (* Next Obligation. *)
  (*   intros. unfold incr_addr in *. *)
  (*   destruct (Z_le_dec (b + 1)%Z MemNum); try discriminate. *)
  (*   inv Heq_anonymous. simpl. destruct e; simpl. *)
  (*   destruct b; simpl in *. assert (z - z0 = Z.succ (z - (z0 + 1)))%Z by omega. *)
  (*   rewrite H3. rewrite Z2Nat.inj_succ; omega. Defined. *)
  (* Next Obligation. *)
  (*   intros. unfold incr_addr in *. *)
  (*   destruct (Z_le_dec (b + 1)%Z MemNum); try discriminate. *)
  (*   destruct b; destruct e; simpl in *. *)
  (*   apply Z.leb_le in fin. apply Z.leb_le in fin0. *)
  (*   omega. Defined. *)
  (* Next Obligation. apply measure_wf. apply lt_wf. Defined. *)

  Fixpoint region_addrs_aux (b: Addr) (n: nat): list Addr :=
    match n with
    | 0 => nil
    | S n => b :: (region_addrs_aux (get_addr_from_option_addr (b + 1)%a) n)
    end.

  Lemma region_addrs_aux_length:
    forall n b,
      length (region_addrs_aux b n) = n.
  Proof. induction n; intros; simpl; auto. Qed.

  Lemma region_addrs_aux_decomposition:
    forall n b k,
      (k <= n)%nat ->
      region_addrs_aux b n = region_addrs_aux b k ++ (region_addrs_aux (get_addr_from_option_addr (b + Z.of_nat k)%a) (n - k)).
  Proof.
    induction n; intros.
    - assert ((k = 0)%nat) by Lia.lia; subst k.
      reflexivity.
    - inv H1.
      + rewrite Nat.sub_diag. simpl.
        rewrite app_nil_r. auto.
      + simpl. destruct k; simpl.
        * assert (b = get_addr_from_option_addr (b + 0%nat)%a).
          { destruct b; unfold incr_addr; simpl.
            generalize (Zle_bool_imp_le _ _ fin). intro Y.
            destruct (Z_le_dec (z + 0%nat)%Z MemNum); try Lia.lia.
            simpl. apply z_of_eq; simpl. Lia.lia. }
          rewrite <- H1. reflexivity.
        * generalize (IHn (get_addr_from_option_addr (b + 1)%a) k ltac:(omega)). intros A.
          rewrite A. do 3 (f_equal; auto). destruct b; unfold incr_addr; simpl.
          generalize (Zle_bool_imp_le _ _ fin). intro Y.
          destruct (Z_le_dec (z + 1)%Z MemNum); simpl.
          { destruct (Z_le_dec (z + 1 + k)%Z MemNum); simpl.
            - destruct (Z_le_dec (z + S k)%Z MemNum); simpl.
              + apply z_of_eq; simpl. Lia.lia.
              + elim n0. Lia.lia.
            - destruct (Z_le_dec (z + S k)%Z MemNum); simpl.
              + elim n0. Lia.lia.
              + reflexivity. }
          { assert (z = MemNum) by Lia.lia. subst z.
            destruct (Z_le_dec (MemNum + S k)%Z MemNum).
            - exfalso. Lia.lia.
            - simpl. destruct (Z_le_dec (MemNum + k)%Z MemNum); simpl; auto.
              apply z_of_eq. simpl. Lia.lia. }
  Qed.

  Lemma region_addrs_aux_spec:
    forall n b k,
      (k < n)%nat ->
      nth_error (region_addrs_aux b n) k = Some (get_addr_from_option_addr (b + (Z.of_nat k))%a).
  Proof.
    induction n; intros.
    - inv H1.
    - assert (X: k = n \/ k < n) by omega; destruct X as [X | X].
      + subst k. simpl. destruct n.
        * simpl. f_equal.
          unfold incr_addr; destruct b; simpl.
          generalize (Zle_bool_imp_le _ _ fin). intro Y.
          destruct (Z_le_dec (z + 0%nat)%Z MemNum); try omega.
          { simpl. apply z_of_eq; simpl. rewrite Z.add_0_r. reflexivity. }
          { elim n. rewrite Z.add_0_r. exact Y. }
        * replace (nth_error (b :: region_addrs_aux (get_addr_from_option_addr (b + 1)%a) (S n)) (S n)) with (nth_error (region_addrs_aux (get_addr_from_option_addr (b + 1)%a) (S n)) n) by reflexivity.
          rewrite IHn; try omega.
          f_equal. unfold incr_addr; destruct b; simpl.
          generalize (Zle_bool_imp_le _ _ fin). intro Y.
          destruct (Z_le_dec (z + 1)%Z MemNum).
          { simpl. f_equal. assert (Z: (z + 1 + n)%Z = (z + S n)%Z) by (rewrite Nat2Z.inj_succ; omega).
            destruct (Z_le_dec (z + 1 + n)%Z MemNum); destruct (Z_le_dec (z + S n)%Z MemNum); try omega; auto.
            f_equal. apply z_of_eq. simpl.
            rewrite Nat2Z.inj_succ. omega. }
          { assert (z = MemNum) by omega. subst z. simpl.
            rewrite Nat2Z.inj_succ.
            destruct (Z_le_dec (MemNum + Z.succ n)%Z MemNum); try omega.
            simpl. destruct (Z_le_dec (MemNum + n)%Z MemNum).
            - simpl. apply z_of_eq. simpl. omega.
            - simpl. reflexivity. }
      + rewrite <- IHn; auto.
        generalize (region_addrs_aux_decomposition (S n) b n ltac:(omega)).
        intros A. rewrite A.
        rewrite nth_error_app1; auto.
        rewrite region_addrs_aux_length. auto.
  Qed.

  Definition region_addrs (b e: Addr): list Addr :=
    if Z_le_dec b e then region_addrs_aux b (region_size b e) else nil.

  Lemma region_addrs_length:
    forall b e,
      (b <= e)%a ->
      length (region_addrs b e) = region_size b e.
  Proof.
    intros; unfold region_addrs.
    destruct (Z_le_dec b e).
    - apply region_addrs_aux_length.
    - elim n. exact H1.
  Qed.

  Lemma region_addrs_spec:
    forall b e k,
      (b <= e)%a ->
      (k < region_size b e)%nat ->
      nth_error (region_addrs b e) k = Some (get_addr_from_option_addr (b + (Z.of_nat k))%a).
  Proof.
    intros; unfold region_addrs.
    destruct (Z_le_dec b e).
    - apply region_addrs_aux_spec; auto.
    - elim n. exact H1.
  Qed.

  Lemma list_nth_eq:
    forall A (l1 l2: list A),
      (forall n, nth_error l1 n = nth_error l2 n) ->
      l1 = l2.
  Proof.
    induction l1; intros.
    - destruct l2; auto.
      generalize (H1 0). simpl. discriminate.
    - destruct l2.
      + generalize (H1 0); simpl; discriminate.
      + generalize (H1 0); simpl; intros.
        inv H2. f_equal.
        apply IHl1. intros.
        generalize (H1 (S n)); simpl; auto.
  Qed.
  
  Lemma addr_conv:
    forall (b a: Addr),
      (b + (a - b)%Z)%a = Some a.
  Proof.
    intros. unfold incr_addr; destruct a; destruct b; simpl.
    generalize (Zle_bool_imp_le _ _ fin). generalize (Zle_bool_imp_le _ _ fin0). intros A B.
    destruct (Z_le_dec (z0 + (z - z0))%Z MemNum); try omega.
    f_equal. apply z_of_eq; simpl. omega.
  Qed.

  Lemma region_addrs_decomposition:
    forall b a e,
      (b <= a /\ a <= e)%a ->
      region_addrs b e = region_addrs b (get_addr_from_option_addr (a + (-1))%a)
                         ++ (a :: match (a + 1)%a with
                                  | Some y => region_addrs y e
                                  | _ => nil
                                  end).
  Proof.
    intros. unfold region_addrs at 1.
    assert (b <= e)%Z by (unfold le_addr in H1; omega).
    destruct (Z_le_dec b e); try omega.
    assert (X: length (region_addrs b (get_addr_from_option_addr (a + -1)%a)) <= region_size b e).
    { unfold region_addrs. destruct (Z_le_dec b (get_addr_from_option_addr (a + -1)%a)).
      - rewrite region_addrs_aux_length. unfold region_size.
        apply le_n_S. apply Zabs_nat_le; split.
        + omega.
        + destruct a; destruct b; destruct e; unfold incr_addr; unfold le_addr in *; simpl in *.
          generalize (Zle_bool_imp_le _ _ fin). intro X1.
          destruct (Z_le_dec (z + -1)%Z MemNum); try omega.
          simpl. omega.
      - simpl; Lia.lia. }
    erewrite region_addrs_aux_decomposition; eauto. f_equal.
    { unfold region_addrs.
      destruct (Z_le_dec b (get_addr_from_option_addr (a + -1)%a)).
      - rewrite region_addrs_aux_length. reflexivity.
      - reflexivity. }
    assert ((get_addr_from_option_addr (b + length (region_addrs b (get_addr_from_option_addr (a + -1))))%a) = a).
    { unfold region_addrs. destruct (Z_le_dec b (get_addr_from_option_addr (a + -1)%a)).
      - rewrite region_addrs_aux_length.
        unfold region_size; destruct b; destruct a; unfold le_addr in *; unfold incr_addr in *; simpl in *.
        generalize (Zle_bool_imp_le _ _ fin). intro X1.
        generalize (Zle_bool_imp_le _ _ fin0). intro X2.
        destruct (Z_le_dec (z0 + -1)%Z MemNum); try omega.
        simpl. destruct H1.
        assert ((z + S (Z.abs_nat (z0 + -1 - z)))%Z = z0).
        { simpl in l0. Lia.lia. }
        destruct (Z_le_dec (z + S (Z.abs_nat (z0 + -1 - z)))%Z MemNum); try omega.
        simpl. apply z_of_eq; auto.
      - simpl. destruct b; destruct a; unfold le_addr in *; unfold incr_addr in *; simpl in *.
        generalize (Zle_bool_imp_le _ _ fin). intro X1.
        generalize (Zle_bool_imp_le _ _ fin0). intro X2.
        destruct (Z_le_dec (z + 0%nat)%Z MemNum); try Lia.lia.
        simpl. apply z_of_eq; simpl. destruct (Z_le_dec (z0 + -1)%Z MemNum); try omega.
        simpl in n. Lia.lia. }
    rewrite H3.
    assert ((region_size b e - length (region_addrs b (get_addr_from_option_addr (a + -1)%a))) = S (length (match (a + 1)%a with
       | Some y => region_addrs y e
       | None => []
       end))).
    { unfold region_addrs. destruct (Z_le_dec b (get_addr_from_option_addr (a + -1)%a)).
      - rewrite region_addrs_aux_length. case_eq (a + 1)%a; intros.
        + destruct (Z_le_dec a0 e).
          * rewrite region_addrs_aux_length.
            unfold region_size; destruct b; destruct a; destruct e; unfold le_addr in *; unfold incr_addr in *; simpl in *.
            generalize (Zle_bool_imp_le _ _ fin). intro X1.
            generalize (Zle_bool_imp_le _ _ fin0). intro X2.
            generalize (Zle_bool_imp_le _ _ fin1). intro X3.
            destruct (Z_le_dec (z0 + -1)%Z MemNum); try omega; simpl in *.
            destruct (Z_le_dec (z0 + 1)%Z MemNum); inv H4; simpl in *.
            repeat (rewrite Zabs2Nat.abs_nat_nonneg; try omega).
            rewrite <- Z2Nat.inj_sub; try omega.
            replace (z1 - z - (z0 + -1 - z))%Z with (z1 - z0 + 1)%Z by omega.
            do 2 (rewrite <- Z2Nat.inj_succ; try omega).
            f_equal; omega.
          * destruct H1; unfold region_size; destruct b; destruct a; destruct e; unfold le_addr in *; unfold incr_addr in *; simpl in *.
            generalize (Zle_bool_imp_le _ _ fin). intro X1.
            generalize (Zle_bool_imp_le _ _ fin0). intro X2.
            generalize (Zle_bool_imp_le _ _ fin1). intro X3.
            destruct (Z_le_dec (z0 + -1)%Z MemNum); try omega; simpl in *.
            destruct (Z_le_dec (z0 + 1)%Z MemNum); inv H4; simpl in *.
            assert (z0 = z1) by omega. subst z0.
            repeat (rewrite Zabs2Nat.abs_nat_nonneg; try omega).
            rewrite <- Z2Nat.inj_sub; try omega.
            replace ((z1 - z - (z1 + -1 - z))%Z) with 1%Z by omega.
            reflexivity.
        + simpl. generalize (incr_addr_one_none _ H4). intro; subst a.
          unfold addr_reg.top in *. destruct e; destruct b; unfold le_addr in *; unfold incr_addr in *; simpl in *.
          generalize (Zle_bool_imp_le _ _ fin). intro X1.
          generalize (Zle_bool_imp_le _ _ fin0). intro X2.
          destruct H1. assert (z = MemNum) by omega. subst z.
          repeat (rewrite Zabs2Nat.abs_nat_nonneg; try omega).
          rewrite <- Z2Nat.inj_sub; try omega.
          assert (MemNum - z0 - (MemNum + -1 - z0) = 1)%Z by omega.
          rewrite H6. reflexivity.
      - simpl. assert (a = b).
        { destruct H1. destruct a; destruct b; unfold le_addr in *; unfold incr_addr in *; simpl in *.
          generalize (Zle_bool_imp_le _ _ fin). intro X1.
          generalize (Zle_bool_imp_le _ _ fin0). intro X2.
          apply z_of_eq; simpl.
          destruct (Z_le_dec (z + -1)%Z MemNum); try omega.
          simpl in n. omega. } subst a. case_eq (b + 1)%a; intros.
        + destruct (Z_le_dec a e).
          * simpl. rewrite region_addrs_aux_length.
            destruct H1. destruct e; destruct b; unfold le_addr in *; unfold incr_addr in *; simpl in *.
            generalize (Zle_bool_imp_le _ _ fin). intro X1.
            generalize (Zle_bool_imp_le _ _ fin0). intro X2.
            destruct (Z_le_dec (z0 + 1)%Z MemNum); try congruence. inv H4. simpl.
            f_equal. simpl in l0. rewrite <- Zabs2Nat.inj_succ; try omega.
            f_equal. omega.
          * simpl. destruct b; destruct a; destruct e; unfold le_addr in *; unfold incr_addr in *; simpl in *.
          generalize (Zle_bool_imp_le _ _ fin). intro X1.
          generalize (Zle_bool_imp_le _ _ fin0). intro X2.
          generalize (Zle_bool_imp_le _ _ fin1). intro X3.
          destruct (Z_le_dec (z + 1)%Z MemNum); try congruence.
          inv H4. assert (z1 = z) by omega. subst z1. Lia.lia.
        + simpl. generalize (incr_addr_one_none _ H4). intro; subst b.
          unfold addr_reg.top in *. destruct H1; destruct e; unfold le_addr in *; unfold incr_addr in *; simpl in *.
          generalize (Zle_bool_imp_le _ _ fin). intro X1.
          assert (z = MemNum) by omega; subst z. Lia.lia. }
    rewrite H4. simpl. f_equal.
    unfold region_addrs. destruct (a + 1)%a.
    { simpl. destruct (Z_le_dec a0 e); simpl; auto.
      rewrite region_addrs_aux_length. reflexivity. }
    { simpl. auto. }
  Qed.



  (*Fixpoint region_addrs (b e : Addr) (n : nat) {struct n} : list Addr :=
    if (b <=? e)%a && ((region_size b e) =? n)%nat then
      match n with
      | 0 => [b]
      | S n => b :: (region_addrs (get_addr_from_option_addr (b + 1)%a) e n)
      end
    else [].*)

  Definition region_mapsto (b e : Addr) (ws : list Word) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (region_addrs b e);ws, y1 ↦ₐ y2)%I. 
  
  Definition included (b' e' : Addr) (b e : Addr) : iProp Σ :=
    (⌜(b <= b')%a⌝ ∧ (⌜e' <= e⌝)%a)%I.
  
  Fixpoint in_range (a b e : Addr) : iProp Σ :=
    (⌜(b <= a)%a⌝ ∧ ⌜(a < e)%a⌝)%I.

  (* Fixpoint region_mapsto_sub (b e : Addr) ws : iProp Σ :=  *)
  (*   ([∗ list] k↦y1;y2 ∈ (region_addrs b e);take (region_size b e) ws, y1 ↦ₐ y2)%I.  *)

  Lemma extract_from_region b e a ws φ : 
    (b <= a ∧ a <= e)%a →
    (region_mapsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     (∃ al w ah, (⌜(a + (-1) = Some al)%a⌝ ∨ ⌜a = al⌝)%I ∧
                 (⌜(a + 1 = Some ah)%a⌝ ∨ ⌜a = ah⌝)
        ∗ region_mapsto b al (take (region_size b al) ws)
        ∗ ([∗ list] w ∈ (take (region_size b al) ws), φ w) 
        ∗ a ↦ₐ w ∗ φ w
        ∗ region_mapsto ah e (drop (region_size b a) ws)
        ∗ ([∗ list] w ∈ (drop (region_size b a) ws), φ w))%I.
  Proof. Admitted.
    
  (* Lemma extract_from_region b e a al ah ws φ :   *)
  (*   (b <= a ∧ a <= e)%a → *)
  (*   (a + (Zneg 1))%a = Some al → *)
  (*   (a + (Zpos 1))%a = Some ah → *)
  (*   (region_mapsto b e ws ∗ ([∗ list] w ∈ ws, φ w)  ⊣⊢ *)
  (*    (∃ w, region_mapsto b al (take (region_size b al) ws) *)
  (*       ∗ ([∗ list] w ∈ (take (region_size b al) ws), φ w)  *)
  (*       ∗ a ↦ₐ w ∗ φ w *)
  (*       ∗ region_mapsto ah e (drop (region_size b a) ws) *)
  (*       ∗ ([∗ list] w ∈ (drop (region_size b a) ws), φ w)))%I. *)
  (* Proof. Admitted.  *)

  Lemma extract_from_listmap ws w n (φ : Word → iProp Σ) :
    n ≤ length ws →
    ws !! n = Some w →
    (([∗ list] w ∈ ws, φ w) ⊣⊢
       ([∗ list] w ∈ take (n - 1) ws, φ w)
        ∗ φ w
        ∗ ([∗ list] w ∈ drop n ws, φ w))%I.
  Proof. Admitted. 

  Lemma extract_from_region_exists b e a al ah φ :
    (b <= a ∧ a <= e)%a →
    (a + (Zneg 1))%a = Some al →
    (a + (Zpos 1))%a = Some ah →
    ((∃ ws, region_mapsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     ((∃ ws1, region_mapsto b al ws1 ∗ ([∗ list] w ∈ ws1, φ w)) 
        ∗ (∃ w, a ↦ₐ w ∗ φ w) 
        ∗ (∃ ws2, region_mapsto ah e ws2 ∗ ([∗ list] w ∈ ws2, φ w))))%I.
  Proof. Admitted.

  Lemma in_range_is_correctPC p l b e a b' e' :
    isCorrectPC (inr ((p,l),b,e,a)) →
    (b' <= b)%a ∧ (e <= e')%a →
    (b' <= a)%a ∧ (a <= e')%a. 
  Proof.
    intros Hvpc [Hb He]. 
    inversion Hvpc; simplify_eq. 
    - destruct H3; rewrite /leb_addr in Hb;
      rewrite /le_addr. split.
      + apply (Z.le_trans b' b a); eauto.
      + simpl in He.
        apply (Z.le_trans a e e'); eauto.
        by apply Z.lt_le_incl. 
    - simpl in He.
      apply top_le_eq in He. 
      split.
      + apply (Z.le_trans b' b a); eauto.
      + rewrite He.
        destruct a. rewrite /le_addr. simpl. 
        by apply Z.leb_le. 
  Qed. 
  
End region.

Global Notation "[[ b , e ]] ↦ₐ [[ ws ]]" := (region_mapsto b e ws)
            (at level 50, format "[[ b , e ]] ↦ₐ [[ ws ]]") : bi_scope.

Global Notation "[[ b , e ]] ⊂ₐ [[ b' , e' ]]" := (included b e b' e')
            (at level 50, format "[[ b , e ]] ⊂ₐ [[ b' , e' ]]") : bi_scope.

Global Notation "a ∈ₐ [[ b , e ]]" := (in_range a b e)
            (at level 50, format "a ∈ₐ [[ b , e ]]") : bi_scope.
