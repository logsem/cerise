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
  
End region.

Global Notation "{[ b , e ]} ↦ₐ {[ ws ]}" := (region_mapsto b e ws)
            (at level 50, format "{[ b , e ]} ↦ₐ {[ ws ]}") : bi_scope.

Global Notation "{[ b , e ]} ⊂ₐ {[ b' , e' ]}" := (included b e b' e')
            (at level 50, format "{[ b , e ]} ⊂ₐ {[ b' , e' ]}") : bi_scope.

Global Notation "a ∈ₐ {[ b , e ]}" := (in_range a b e)
            (at level 50, format "a ∈ₐ {[ b , e ]}") : bi_scope.
