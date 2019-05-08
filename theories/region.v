From cap_machine Require Export lang rules.
From iris.proofmode Require Import tactics.

Section region.
  Context `{memG Σ, regG Σ}.

  Fixpoint region_addrs (b e : Addr) (n : nat) {struct n} : list Addr :=
    if (b <=? e)%a && ((region_size b e) =? n)%nat then
      match n with
      | 0 => [b]
      | S n => b :: (region_addrs (get_addr_from_option_addr (b + 1)%a) e n)
      end
    else [].

  Definition region_mapsto (b e : Addr) (ws : list Word) : iProp Σ :=
    ([∗ list] k↦y1;y2 ∈ (region_addrs b e (region_size b e));ws, y1 ↦ₐ y2)%I. 
  

  Definition included (b' : Addr) (e' : option Addr)
             (b : Addr) (e : option Addr) : iProp Σ :=
    (⌜(b' <=? b)%a⌝ ∧ ((⌜e = None⌝ ∧ ⌜e' = None⌝) ∨
                  (∃ a a', ⌜e = Some a⌝ ∧ ⌜e' = Some a'⌝ ∧ ⌜(a <=? a')%a⌝)))%I.
  

  Fixpoint in_range (a b : Addr) (e : option Addr) : iProp Σ :=
    match e with
    | None => (⌜(b <=? a)%a⌝)%I
    | Some e' => (⌜(b <=? a)%a⌝ ∧ ⌜(a <? e')%a⌝)%I
    end.

  Fixpoint region_mapsto_sub (b e : Addr) ws : iProp Σ := 
    ([∗ list] k↦y1;y2 ∈ (region_addrs b e (region_size b e));take (region_size b e) ws,
                                                             y1 ↦ₐ y2)%I. 
  
  Lemma extract_from_region b e a ws φ :  
    (b < a ∧ a < e)%a →
    (region_mapsto b e ws ∗ ([∗ list] w ∈ ws, φ w)  ⊣⊢
     (∃ w, region_mapsto b (a -- 1)%a (take (region_size b (a -- 1)%a) ws)
        ∗ ([∗ list] w ∈ (take (region_size b (a -- 1)%a) ws), φ w) 
        ∗ a ↦ₐ w ∗ φ w
        ∗ region_mapsto (a ++ 1)%a e (drop (region_size b a) ws)
        ∗ ([∗ list] w ∈ (drop (region_size b a) ws), φ w)))%I.
  Proof. Admitted. 
    (* iIntros ([Hb He] Hw) "Hbe". *)
    (* iNext. rewrite /region_mapsto /region_addrs /region_size /=. *)
    (* destruct b,e,(a ++ 1)%a,(a -- 1)%a;simpl. *)
    (* assert (z <=? z0 = true)%Z as Hle.  *)
    (* { apply (addr_lt_trans (A z fin) a (A z0 fin0)) in Hb as Ha; eauto. *)
    (*   simpl in Ha. apply Zle_imp_le_bool. omega. } *)
    (* assert (true = (Z.abs_nat (z0 - z) =? Z.abs_nat (z0 - z)))%nat as Heq.  *)
    (* { apply (beq_nat_refl (Z.abs_nat (z0 - z))). } *)
  (* rewrite Hle -Heq /=. *)

  Lemma extract_from_listmap ws w n (φ : Word → iProp Σ) :
    n ≤ length ws →
    ws !! n = Some w →
    (([∗ list] w ∈ ws, φ w) ⊣⊢
       ([∗ list] w ∈ take (n - 1) ws, φ w)
        ∗ φ w
        ∗ ([∗ list] w ∈ drop n ws, φ w))%I.
  Proof. Admitted. 

  Lemma extract_from_region_exists b e a φ :
    (b < a ∧ a < e)%a →
    ((∃ ws, region_mapsto b e ws ∗ ([∗ list] w ∈ ws, φ w)) ⊣⊢
     ((∃ ws1, region_mapsto b (a -- 1)%a ws1 ∗ ([∗ list] w ∈ ws1, φ w)) 
        ∗ (∃ w, a ↦ₐ w ∗ φ w) 
        ∗ (∃ ws2, region_mapsto (a ++ 1)%a e ws2 ∗ ([∗ list] w ∈ ws2, φ w))))%I.
  Proof. Admitted.
  
End region.

Global Notation "{[ b , e ]} ↦ₐ {[ ws ]}" := (region_mapsto b e ws)
            (at level 50, format "{[ b , e ]} ↦ₐ {[ ws ]}") : bi_scope.

Global Notation "{[ b , e ]} ⊂ₐ {[ b' , e' ]}" := (included b e b' e')
            (at level 50, format "{[ b , e ]} ⊂ₐ {[ b' , e' ]}") : bi_scope.

Global Notation "a ∈ₐ {[ b , e ]}" := (in_range a b e)
            (at level 50, format "a ∈ₐ {[ b , e ]}") : bi_scope.




(* class_instances_bi.from_sep_big_sepL2_cons: *)
(*   ∀ (PROP : bi) (A B : Type) (Φ : nat → A → B → PROP) (l1 : list A)  *)
(*     (x1 : A) (l1' : list A) (l2 : list B) (x2 : B) (l2' : list B), *)
(*     IsCons l1 x1 l1' *)
(*     → IsCons l2 x2 l2' *)
(*       → FromSep ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) (Φ 0 x1 x2) *)
(*                 ([∗ list] k↦y1;y2 ∈ l1';l2', Φ (S k) y1 y2) *)

(*                 big_sepL2_app: *)
(*   ∀ (PROP : bi) (A B : Type) (Φ : nat → A → B → PROP) (l1 l2 : list A)  *)
(*     (l1' l2' : list B), *)
(*     ([∗ list] k↦y1;y2 ∈ l1;l1', Φ k y1 y2) *)
(*     -∗ ([∗ list] k↦y1;y2 ∈ l2;l2', Φ (length l1 + k) y1 y2) *)
(*        -∗ [∗ list] k↦y1;y2 ∈ (l1 ++ l2);(l1' ++ l2'), Φ k y1 y2 *)