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
  

  Definition included (b' e' : Addr) (b e : Addr) : iProp Σ :=
    (⌜(b <= b')%a⌝ ∧ (⌜e' <= e⌝)%a)%I.
  

  Fixpoint in_range (a b e : Addr) : iProp Σ :=
    (⌜(b <= a)%a⌝ ∧ ⌜(a < e)%a⌝)%I.

  Fixpoint region_mapsto_sub (b e : Addr) ws : iProp Σ := 
    ([∗ list] k↦y1;y2 ∈ (region_addrs b e (region_size b e));take (region_size b e) ws,
                                                             y1 ↦ₐ y2)%I. 
  
  Lemma extract_from_region b e a al ah ws φ :  
    (b <= a ∧ a <= e)%a →
    (a + (Zneg 1))%a = Some al →
    (a + (Zpos 1))%a = Some ah →
    (region_mapsto b e ws ∗ ([∗ list] w ∈ ws, φ w)  ⊣⊢
     (∃ w, region_mapsto b al (take (region_size b al) ws)
        ∗ ([∗ list] w ∈ (take (region_size b al) ws), φ w) 
        ∗ a ↦ₐ w ∗ φ w
        ∗ region_mapsto ah e (drop (region_size b a) ws)
        ∗ ([∗ list] w ∈ (drop (region_size b a) ws), φ w)))%I.
  Proof. Admitted. 

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

Global Notation "{[ b , e ]} ↦ₐ {[ ws ]}" := (region_mapsto b e ws)
            (at level 50, format "{[ b , e ]} ↦ₐ {[ ws ]}") : bi_scope.

Global Notation "{[ b , e ]} ⊂ₐ {[ b' , e' ]}" := (included b e b' e')
            (at level 50, format "{[ b , e ]} ⊂ₐ {[ b' , e' ]}") : bi_scope.

Global Notation "a ∈ₐ {[ b , e ]}" := (in_range a b e)
            (at level 50, format "a ∈ₐ {[ b , e ]}") : bi_scope.
