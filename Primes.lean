-- This module serves as the root of the `Primes` library.
-- Import modules here that should be built as part of the library.
import «Primes».Basic

import Init.Classical

import Init.Data.Nat

import Init.WF

import Init.Data.List

theorem lt_of_divides {n m k: Nat} (h₁: n = m * k) (h₂: m ≥ 2) (h₃: k > 0): k < n := by
  rw [h₁]
  calc
    k < k + k := by rw ( config := {occs := .pos [1] }) [← Nat.zero_add k]; apply Nat.add_lt_add_right; assumption
    _ = 2*k := by rw [Nat.succ_mul]; simp
    _ ≤ m*k := by apply Nat.mul_le_mul_right; assumption

theorem le_of_dvd {n m: Nat} (h: n ∣ m) (h₀: m > 0): n ≤ m := by
  cases h with
  | intro k hk =>
    cases k with
    | zero => omega
    | succ l => rw [hk, Nat.mul_add]; simp;

theorem eq_one_of_mul (n m: Nat) (h: n * m = 1): n = 1 ∧ m = 1 := by
  match n, m with
  | 0, m => rw [Nat.zero_mul] at h; contradiction
  | n, 0 => contradiction
  | 1, 1 => constructor <;> rfl
  | n + 2, m + 2 =>
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, ← Nat.add_assoc] at h
    simp at h

theorem eq_div (n m: Nat) (h: 0 < n): n ∣ m ∧ m ∣ n ↔ m = n := by
  constructor
  . intro ⟨hn, hm⟩
    . cases hn with
      | intro l hl =>
        cases hm with
        | intro k hk =>
          rw [←Nat.mul_one n, hl, Nat.mul_assoc, Nat.mul_comm l] at hk
          have h': k*l = 1 := by exact Nat.eq_of_mul_eq_mul_left h (Eq.symm hk)
          have hl' := eq_one_of_mul k l h'
          rw [hl'.right, Nat.mul_one] at hl
          assumption

  . intro hnm; rw [hnm]; constructor <;> exact Nat.dvd_refl n

theorem div_mul (n m k: Nat) (h: m * k ∣ n): k ∣ n ∧ m ∣ n := by
  cases h with
  | intro l hl =>
    constructor
    . exists m * l; rw [← Nat.mul_assoc, Nat.mul_comm k m]; assumption
    . exists k * l; rw [← Nat.mul_assoc]; assumption

theorem mul_extend (n m k: Nat) (h: m ∣ n): m ∣ k * n := by
  cases h with
  | intro l hl =>
    exists (k * l)
    rw [Nat.mul_comm m, Nat.mul_assoc, Nat.mul_comm l, hl]

theorem extend_mul (n m k: Nat) (h: m ∣ n): m ∣ n * k := by
  rw [Nat.mul_comm]; exact mul_extend n m k h

def Prime (p: Nat): Prop := p ≥ 2 ∧ ∀m, m ≥ 2 ∧ m ≠ p → ¬m ∣ p

theorem one_or_prime_of_dvd_prime {n p: Nat} (hp: Prime p) (h: n ∣ p): n = 1 ∨ n = p := by
  have hp₀ := hp.left
  have hn := hp.right n
  have hn₁ := Nat.pos_of_dvd_of_pos h (by omega)

  -- Make a case distinction. If `n = p`, we are directly done. Otherwise we
  -- have to show that 0 and values larger than 1 lead to a contradiction.
  by_cases heq: n = p
  . exact Or.inr heq
  . by_cases hge: n ≥ 2
    . exfalso; exact hn ⟨hge, heq⟩ h
    . exact match n with
      | 0 => False.elim ((Nat.not_lt_zero 0) hn₁)
      | 1 => Or.inl (Eq.refl 1)
      | n+2 => False.elim (hn ⟨by omega, heq⟩ h)

def Coprime (n m: Nat): Prop := ∀d, d ∣ n → d ∣ m → d = 1

theorem coprime_iff_gcd {n m: Nat}: Coprime n m ↔ n.gcd m = 1 := by
  constructor
  . intro h
    have ⟨hdn, hdm⟩ := Nat.gcd_dvd n m
    exact h (n.gcd m) hdn hdm
  . intros hgcd d hdn hdm
    have hd := Nat.dvd_gcd hdn hdm
    rw [hgcd] at hd
    rwa [←Nat.dvd_one]

theorem coprime_symm {n m: Nat} (h: Coprime n m): Coprime m n :=
  fun d hdn hdm => h d hdm hdn

theorem coprime_n_sub_m {n m: Nat} (hn₁: 0 < n) (hnm: n ≤ m) (hc: Coprime n m): Coprime n (m - n) := by
  intro d hdp hdn
  exact match d with
  | 0 => by have blubb := Nat.pos_of_dvd_of_pos hdp hn₁; contradiction
  | 1 => rfl
  | d + 2 => by
    have blubb := Nat.dvd_add hdn hdp
    rw [Nat.sub_add_cancel (by omega)] at blubb
    exact hc (d + 2) hdp blubb

def pos_or_pos_of_coprime {n m: Nat} (h: Coprime n m): (n = 1 ∧ m = 0) ∨ (n = 0 ∧ m = 1) ∨ (0 < n ∧ 0 < m) :=
  match n, m with
  | 0, 0 => False.elim (Nat.zero_ne_one (h 0 (Nat.dvd_zero 0) (Nat.dvd_zero 0)))
  | 1, 0 => Or.inl ⟨Eq.refl 1, Eq.refl 0⟩
  | 0, 1 => Or.inr (Or.inl ⟨Eq.refl 0, Eq.refl 1⟩)
  | n + 2, 0 => by
    have tmp := h (n + 2) (Nat.dvd_refl (n + 2)) (Nat.dvd_zero (n + 2))
    omega
  | 0, m + 2 => by
    have tmp := h (m + 2) (Nat.dvd_zero (m + 2)) (Nat.dvd_refl (m + 2))
    omega
  | n + 1, m + 1 => Or.inr (Or.inr ⟨Nat.succ_pos n, Nat.succ_pos m⟩)

def sum (t: List Nat) := List.foldl (· + ·) 0 t
def prod: List Nat → Nat
  | [] => 1
  | t::ts => t * prod ts

theorem forall_empty {α : Type} (p: α → Prop) : ∀x, x ∈ [] → p x := by
  intro x hx
  contradiction

@[simp]
theorem one_of_prod_nil : prod [] = 1 := rfl

@[simp]
theorem self_of_prod_singleton : prod [a] = a := by
  unfold prod
  unfold prod
  rw [Nat.mul_one]

theorem mul_head_of_prod_cons : prod (a :: as) = a * prod as := rfl

theorem dvd_mul_left_or_right {n m l: Nat} (h: n ∣ m ∨ n ∣ l): n ∣ m * l := by
  cases h with
  | inl hm => cases hm with
    | intro c hc =>
      rw [hc]
      exists (c * l)
      rw [Nat.mul_assoc]
  | inr hl => cases hl with
    | intro c hc =>
      rw [hc]
      exists (c * m)
      rw [Nat.mul_comm, Nat.mul_assoc]

theorem de_morgan_not_and (p q: Prop): ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  . intro h
    cases Classical.em p with
    | inl hp => cases Classical.em q with
      | inl hq =>
        have h': p ∧ q := ⟨hp, hq⟩
        contradiction
      | inr hnq => exact Or.inr hnq
    | inr hnp => exact Or.inl hnp
  . intro h hn
    cases h with
    | inl hp => exact hp hn.left
    | inr hq => exact hq hn.right

theorem de_morgan_not_or {p q: Prop}: ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro hpq
    constructor
    . intro hp
      exact hpq (Or.inl hp)
    . intro hq
      exact hpq (Or.inr hq)
  . intro ⟨hnp, hnq⟩ hpq
    cases hpq with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq

theorem mul_head_of_prod_dvd {a: Nat} {as: List Nat} (h: a ∈ as): a ∣ prod as := by
  induction as with
  | nil => exfalso; exact (List.not_mem_nil a h)
  | cons x xs ih =>
    rw [mul_head_of_prod_cons]
    apply dvd_mul_left_or_right
    cases h with
    | head a => exact Or.inl (Nat.dvd_refl a)
    | tail a ib => exact Or.inr (ih (h:=ib))

theorem prime_not_dvd {a: Nat} {as: List Nat} (ha: a ≥ 2) (has: ∀x,x∈as → Prime x) (hnin: a ∉ as): ∀x,x∈as → ¬(a ∣ x) := by
  intros x hx hdvd
  have ⟨hl, hr⟩ := (has x hx)
  have bla := hr a ⟨ha, by apply Classical.byContradiction; simp; intro heq; rw [heq] at hnin; contradiction⟩
  exact bla hdvd

theorem prod_of_gt_zero_gt_zero {s: List Nat} (h: ∀x, x ∈ s → 0 < x): 0 < prod s := by
  induction s with
  | nil => rw [one_of_prod_nil]; exact Nat.zero_lt_one
  | cons a as ih =>
      rw [mul_head_of_prod_cons]
      have ⟨hl, hr⟩ := (List.forall_mem_cons.mp h)
      exact Nat.mul_pos hl (ih hr)

theorem zero_is_not_prime : ¬Prime 0 := by
  intro ⟨hl, _⟩
  contradiction

theorem one_is_not_prime : ¬Prime 1 := by
  intro ⟨hl, _⟩
  contradiction


theorem two_is_prime : Prime 2 := by
  constructor
  . exact Nat.le_refl 2
  . intro m hm hdvd
    have bla := Nat.le_of_dvd (by omega) hdvd
    omega

theorem three_is_prime : Prime 3 := by
  constructor
  . apply Nat.le_of_lt; exact Nat.lt_succ_self 2
  . intro m hm hdiv
    cases hdiv with
    | intro k hk =>
      match k with
      | 0 => contradiction
      | 1 => rw [Nat.mul_one] at hk; exact hm.right (Eq.symm hk)
      | n + 2 => rw [Nat.mul_add] at hk; omega;

theorem mul_dvd {n m k: Nat} (h: n = m * k): m ∣ n ∧ k ∣ n := by
  constructor
  . exists k
  . exists m; rw [Nat.mul_comm]; assumption;

def IsOdd (n: Nat) := ∃k, n = 2*k + 1
def IsEven (n: Nat) := ∃k, n = 2*k

theorem odd_is_not_even (n: Nat) (h_odd: IsOdd n): ¬IsEven n := by
  intro h_even
  cases h_odd with
  | intro k hk => cases h_even with
    | intro l hl => omega

theorem even_is_not_odd (n: Nat) (h_even: IsEven n): ¬IsOdd n := by
  intro h_odd
  cases h_odd with
  | intro k hk => cases h_even with
    | intro l hl => omega

theorem even_eq_dvd_two {n: Nat}: IsEven n ↔ 2 ∣ n := by
  constructor
  . intros h
    cases h with
    | intro k hk =>
      rw [hk]
      apply Nat.dvd_mul_right
  . intros h
    cases h with
    | intro k hk =>
      rw [hk]
      exists k

theorem even_not_dvd_odd {n m: Nat} (hn: IsEven n) (hm: IsOdd m): ¬n ∣ m := by
  intro hnm
  have bla := even_eq_dvd_two.mpr (Nat.dvd_trans (even_eq_dvd_two.mp hn) hnm)
  exact odd_is_not_even m hm bla


theorem even_of_succ_odd {n: Nat} (hn: IsOdd (n + 1)): IsEven n := by
  rcases hn with ⟨l, hl⟩
  exists l
  exact Nat.add_right_cancel hl

theorem even_not_prime (p: Nat) (hp: IsEven p) (h2: p > 2): ¬Prime p := by
  intro h
  cases hp with
  | intro k hk =>
    unfold Prime at h
    have hd: 2 ∣ p := by exact (mul_dvd hk).left
    have hnd: ¬ 2 ∣ p := by exact ((h.right 2) ⟨Nat.le_refl 2, by omega⟩)
    contradiction

theorem not_even_is_odd (p: Nat) (hp: ¬IsEven p): IsOdd p := by
  match p with
  | 0      => exfalso; apply hp; exists 0
  | p' + 1 =>
    rw [even_eq_dvd_two] at hp
    exists p' / 2
    have h2: 2 ∣ p' := by
      omega
    rw [Nat.mul_div_cancel' h2]

theorem odd_of_not_two_dvd {n: Nat} (h: ¬2 ∣ n): IsOdd n := by
  rw [← even_eq_dvd_two] at h
  exact not_even_is_odd n h

theorem primes_are_odd (p: Nat) (hp: Prime p) (h2: 2 < p): IsOdd p := by
  apply not_even_is_odd
  intro h_even
  cases h_even with
  | intro k hk =>
    apply hp.right 2 ⟨Nat.le_refl 2, Nat.ne_of_lt h2⟩
    exists k

theorem not_for_all {α: Type} (p: α -> Prop): (¬∀x, p x) ↔ ∃x, ¬p x := by
  constructor
  . intro h₁
    exact Classical.byContradiction (by
      intro h₂
      apply h₁
      intro x
      cases Classical.em (p x) with
      | inl hpx => exact hpx
      | inr hnpx =>
        have h := h₂ ⟨x, hnpx⟩
        contradiction
    )
  . intro h₁ h₂
    cases h₁ with
    | intro x hx => exact hx (h₂ x)

theorem double_not_elim {p: Prop}: ¬¬p ↔ p := by
  constructor
  . intro hnnp
    cases Classical.em p with
    | inl hp => assumption
    | inr hnp => contradiction
  . intro hp hnnp
    contradiction

theorem imp (p q: Prop): (p → q) ↔ ¬ p ∨ q := by
  constructor
  . intro h
    cases Classical.em p with
    | inl hp => exact Or.inr (h hp)
    | inr hnp => exact Or.inl hnp
  . intro h hp
    cases h with
    | inl hnp => contradiction
    | inr hq => assumption

theorem imp_neg {p q: Prop}: ¬(p → q) ↔ p ∧ ¬q := by
  constructor
  . rw [imp p q, de_morgan_not_or]
    intro ⟨hnnp, hnq⟩
    constructor
    . exact double_not_elim.mp hnnp
    . assumption
  . intro ⟨hp, hnq⟩ hnp
    exact hnq (hnp hp)

theorem gt_zero_of_prime {n: Nat} (h: Prime n): n > 0 := by
  unfold Prime at h
  omega

theorem divider_if_not_prime {n: Nat} (hn: n ≥ 2) (h: ¬Prime n): ∃k, k ≥ 2 ∧ k < n ∧ k ∣ n := by
  unfold Prime at h
  rw [de_morgan_not_and, not_for_all] at h
  cases h with
  | inl hl => contradiction
  | inr hr => cases hr with
    | intro k hk =>
      rw [imp_neg] at hk
      exists k
      rw [double_not_elim, and_assoc] at hk
      have ⟨hgt, hkn, hdvd⟩ := hk
      cases Nat.eq_or_lt_of_le (Nat.le_of_dvd (by omega) hdvd) with
      | inl heq' => exfalso; exact hkn heq'
      | inr hlt' => exact ⟨hgt, hlt', hdvd⟩

theorem exists_prime_factor {n: Nat} (hn: n ≥ 2): ∃p, Prime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n hi => cases Classical.em (Prime n) with
    | inl h => exists n; exact ⟨h, Nat.dvd_refl n⟩
    | inr h =>
      cases divider_if_not_prime hn h with
      | intro k hk => cases hi k hk.right.left hk.left with
        | intro p hp =>
          exists p
          exact ⟨hp.left, Nat.dvd_trans hp.right hk.right.right⟩

theorem element_singleton {α: Type} (x : α) (a : α) : (x ∈ [a] → x = a) := by
  intro h
  cases h with
  | head => rfl
  | tail a has => contradiction

theorem finset_extensionality {α: Type} (p: α → Prop) (a : α) (h₁: p a) (as : List α) (h₂: ∀x, x ∈ as → p x) : ∀x, x ∈ a::as → p x := by
  intro x hx
  cases hx with
  | head => exact h₁
  | tail a has => exact h₂ x has

def PrimeDecomposition (n: Nat) (s: List Nat) :=
  (∀x, x ∈ s → Prime x) ∧ n = prod s

theorem not_prime_dvd (n: Nat) (h: ¬Prime n) (hn: n ≥ 2): ∃ p, p ∣ n := by
  unfold Prime at h
  rw [not_and, Classical.not_forall] at h
  simp only [not_imp, Decidable.not_not] at h
  have h' := h hn
  cases h' with
  | intro p hp =>
    exists p
    exact hp.right

theorem prime_decomposition (n : Nat) (hn: 0 < n): ∃ s, PrimeDecomposition n s := by
  induction n using Nat.strongRecOn with
  | ind n hi => match n with
    | 0 => contradiction
    | 1 =>
      exists []
      constructor
      . exact forall_empty Prime
      . apply Eq.symm; exact one_of_prod_nil
    | n + 2 =>
      have hn': 2 ≤ n + 2 := Nat.le_add_left 2 n
      cases exists_prime_factor hn' with
      | intro p hp =>
        have hpg: p ≥ 2 := hp.left.left
        cases hp.right with
        | intro k hk =>
          have hkgt: k > 0 := by
            rw [hk] at hn
            match k with
            | 0 => simp at hn
            | i+1 => apply Nat.zero_lt_succ;
          have bla: k < n + 2 := lt_of_divides hk hpg hkgt
          cases hi k bla hkgt with
          | intro s' hs' =>
            exists p :: s'
            constructor
            . exact finset_extensionality Prime p hp.left s' hs'.left
            . rw [hk, hs'.right]; exact mul_head_of_prod_cons


theorem prod_append_mul {ns ms: List Nat}: prod ns * prod ms = prod (ns ++ ms) := by
  induction ns with
  | nil => simp
  | cons x xs ih =>
    rw [mul_head_of_prod_cons, List.cons_append, mul_head_of_prod_cons, Nat.mul_assoc, ←ih]


theorem prime_decomposition_of_mul {n m: Nat} {ns ms: List Nat} (hn: PrimeDecomposition n ns) (hm: PrimeDecomposition m ms): PrimeDecomposition (n*m) (ns ++ ms) := by
  constructor
  . intros x hmem
    rw [List.mem_append] at hmem
    cases hmem with
    | inl hleft => exact hn.left x hleft
    | inr hright => exact hm.left x hright
  . rw [hn.right, hm.right, prod_append_mul]

theorem prime_decomposition_of_prime (p: Nat) {hp: Prime p}: PrimeDecomposition p [p] := by
  constructor
  . intros x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    assumption
  . rw [self_of_prod_singleton]


structure FinMultiSet (α: Type) where
  elements: List α

instance : Membership α (FinMultiSet α) where
  mem l a := List.Mem a l.elements


def Sorted: List Nat → Prop
  | [] => True
  | [_] => True
  | x::y::ys => x < y ∧ Sorted (y::ys)

theorem sorted_nil: Sorted [] := True.intro

theorem sorted_tail_of_sorted {xs: List Nat} (h: Sorted xs): Sorted xs.tail :=
  match xs with
  | [] => by rwa [List.tail_nil]
  | [x] => by rw [List.tail_cons]; exact sorted_nil
  | (x::y::ys) => by simp [Sorted] at h; exact h.right

theorem is_sorted_tail {x: Nat} {xs: List Nat} (h: Sorted (x :: xs)): Sorted xs :=
  match xs with
  | [] => sorted_nil
  | [_] => sorted_nil
  | _ :: _ :: _ => h.right

theorem euclid_lemma {p n m: Nat} (h: p ∣ n * m) (hc: Coprime p n): p ∣ m := by
  -- We first have to deal with the cases in which p and n are 0 and 1 and vice-versa
  -- in both cases, the statement is trivially true based on simple arithmetics.
  cases pos_or_pos_of_coprime hc with
  | inl hy => rw [hy.left]; exact Nat.one_dvd m
  | inr hx => cases hx with
    | inl hzero => rwa [hzero.right, Nat.one_mul] at h
    | inr hpos => cases h with | intro l hl =>
      have ⟨hp₁, hn₁⟩ := hpos
      by_cases heq: n = p
      . rw [←heq] at hc
        have hone: n = 1 := hc n (Nat.dvd_refl n) (Nat.dvd_refl n)
        rw [hone, Nat.one_mul] at hl
        exists l
      . cases Nat.lt_or_gt.mp heq with
        | inr hgt =>
          have hl': p ∣ (n - p) * m := by
            exists l - m
            rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
            congr

          have hc' := coprime_n_sub_m hp₁ (by omega) hc

          exact euclid_lemma hl' hc'
        | inl hlt =>
          have hl': n*(m - l) = (p - n)*l := by
            rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
            congr

          have hc': Coprime (p - n) n :=
            coprime_symm (coprime_n_sub_m hn₁ (Nat.le_of_lt hlt) (coprime_symm hc))

          cases euclid_lemma (by exists l) hc' with
          | intro r hr =>
            rw [hr, Nat.mul_comm, Nat.mul_assoc] at hl'
            have sadsd := Nat.mul_left_cancel (by omega) hl'
            rw [←sadsd, ←Nat.mul_assoc, Nat.mul_comm] at hl
            have tmp := Nat.mul_right_cancel hn₁ hl
            exists r

theorem dvd_or_dvd {p n m: Nat} (hp: Prime p) (h: p ∣ n*m): p ∣ n ∨ p ∣ m :=
  Classical.byCases
    Or.inl
    (fun hndvd: ¬p ∣ n => by
      have hc: Coprime p n := by
        intro d hdp hdn
        cases one_or_prime_of_dvd_prime hp hdp with
        | inl hone => exact hone
        | inr hp => rw [hp] at hdn; contradiction
      exact Or.inr (euclid_lemma h hc)
    )

theorem mem_of_tail_mem_of_list (x: α) (s: List α) (h: x ∈ s.tail): x ∈ s := by
  match s with
  | [] => rw [List.tail_nil] at h; assumption
  | y::ys => rw [List.tail_cons] at h; rw [List.mem_cons]; right; assumption

theorem forall_tail {s: List α} {p: α → Prop} (h: ∀x, x ∈ s → p x): ∀x, x ∈ s.tail → p x := by
  intros x helem
  exact h x (mem_of_tail_mem_of_list x s helem)


theorem reducible_pd {s: List Nat} (hs: PrimeDecomposition (prod s) s): PrimeDecomposition (prod s.tail) s.tail := by
  cases s with
    | nil => rw [List.tail_nil]; assumption
    | cons a as =>
      rw [List.tail];
      constructor
      . intros x hx
        exact hs.left x (List.mem_cons_of_mem a hx)
      . rfl


theorem prod_gt_zero (s: List Nat) (h: ∀x, x ∈ s → x > 0): 0 < prod s := by
  induction s with
  | nil => rw [one_of_prod_nil]; exact Nat.zero_lt_one
  | cons a as ih =>
    rw [mul_head_of_prod_cons]
    exact Nat.mul_pos (h a (List.mem_cons_self a as)) (ih (List.forall_mem_cons.mp h).right)

theorem prime_prod_eq_len (a: Nat) (as: List Nat) (n: Nat) (hn₁: n = prod []) (hn₂: n = prod (a::as)) (hs₂ : (∀ (x : Nat), x ∈ a :: as → Prime x)) (hgt₂: ∀x, x ∈ (a::as) → x > 0): False := by
  rw [one_of_prod_nil] at hn₁
  rw [hn₁, mul_head_of_prod_cons] at hn₂
  have ha: 1 < a := (hs₂ a (List.mem_cons_self a as)).left
  have has: 0 < prod as := prod_gt_zero as (forall_tail hgt₂)
  have tmp: 1 < a * prod as := by calc
    1 < a           := ha
    _ = a * 1       := by rw [Nat.mul_one]
    _ ≤ a * prod as := Nat.mul_le_mul_left a has
  rw [←hn₂] at tmp
  exact Nat.lt_irrefl 1 tmp

theorem sorted_head_le_tail (a: Nat) (as: List Nat) (h: Sorted (a::as)): ∀x, x ∈ as → a ≤ x := by
  intro y hy
  induction as with
  | nil => exfalso; exact List.not_mem_nil y hy
  | cons b bs ih =>
    unfold Sorted at h;
    have h': Sorted (a::bs) := by
      have hbs: Sorted bs := is_sorted_tail h.right
      exact match bs with
      | [] => True.intro
      | c::cs => by unfold Sorted at h; have hac: a ≤ c := Nat.le_trans (Nat.le_succ_of_le (Nat.le_of_lt h.left)) h.right.left; simp [Sorted]; exact ⟨by omega, h.right.right⟩
    cases List.mem_cons.mp hy with
    | inl hb => rw [hb]; exact (Nat.le_of_lt h.left)
    | inr hbs => exact ih h' hbs

theorem eq_of_dvd {p q: Nat} (hp: Prime p) (hq: Prime q) (hpq: p ∣ q): p = q := by
  apply Classical.byContradiction
  intro hnpq
  exact hq.right p ⟨hp.left, hnpq⟩ hpq

theorem dvd_prod_dvd_mem {p: Nat} {qs: List Nat} (hp: Prime p) (hqs: ∀q, q ∈ qs → Prime q) (hdvd: p ∣ prod qs): p ∈ qs := by
  induction qs with
  | nil =>
    exfalso
    rw [one_of_prod_nil, Nat.dvd_one] at hdvd
    have h:=hp.left
    omega
  | cons x xs ih =>
    rw [mul_head_of_prod_cons] at hdvd
    cases dvd_or_dvd hp hdvd with
    | inl hpx =>
      have hprime_x := hqs x (List.mem_cons_self x xs)
      cases Classical.em (p = x) with
      | inl hpeqx => rw [hpeqx]; apply List.mem_cons_self
      | inr hpneqx => exfalso; exact hprime_x.right p ⟨hp.left, hpneqx⟩ hpx
    | inr hpps => exact List.mem_cons_of_mem x (ih (forall_tail hqs) hpps)


theorem unique_pd {n : Nat} (s₁ s₂: List Nat) (hs₁: PrimeDecomposition n s₁) (hs₂: PrimeDecomposition n s₂) (h₁: Sorted s₁) (h₂: Sorted s₂): s₁ = s₂ := by
  have hn₁ := hs₁.right
  have hn₂ := hs₂.right

  have hgt₁: ∀x, x ∈ s₁ → x > 0 := by
    unfold PrimeDecomposition at hs₁
    intros x helem
    exact gt_zero_of_prime (hs₁.left x helem)

  have hgt₂: ∀x, x ∈ s₂ → x > 0 := by
    unfold PrimeDecomposition at hs₂
    intros x helem
    exact gt_zero_of_prime (hs₂.left x helem)

  rw [hn₁] at hs₁
  rw [hn₂] at hs₂

  exact match s₁, s₂ with
  | [], [] => by rfl
  | [], (b::bs) => by exfalso; exact prime_prod_eq_len b bs n hn₁ hn₂ hs₂.left hgt₂
  | (a::as), [] => by exfalso; exact prime_prod_eq_len a as n hn₂ hn₁ hs₁.left hgt₁
  | (a::as), (b::bs) => by
    have ha: Prime a := hs₁.left a (List.mem_cons.mpr (Or.inl (Eq.refl a)))
    have hb: Prime b := hs₂.left b (List.mem_cons.mpr (Or.inl (Eq.refl b)))
    rw [List.cons_eq_cons]
    have haeqb: a=b := by
      have hdvda: a ∣ prod (b::bs) := by
        have tmp := mul_head_of_prod_dvd (List.mem_cons_self a as)
        rw [←hn₁, hn₂] at tmp
        assumption
      have hdvdb: b ∣ prod (a::as) := by
        have tmp := mul_head_of_prod_dvd (List.mem_cons_self b bs)
        rw [←hn₂, hn₁] at tmp
        assumption
      have hab: a ∣ b ∨ a ∣ prod bs := by
        apply dvd_or_dvd ha
        assumption
      cases hab with
      | inl simple => exact eq_of_dvd ha hb simple
      | inr hard =>
        have hamem: a ∈ bs := dvd_prod_dvd_mem ha (forall_tail hs₂.left) hard
        have hle := sorted_head_le_tail b bs h₂ a hamem
        cases Nat.eq_or_lt_of_le hle with
        | inl heq => rw [heq]
        | inr hlt =>
          have hxxxx: b ∣ prod (as) := by
            rw [mul_head_of_prod_cons] at hdvdb;
            cases dvd_or_dvd hb hdvdb with
            | inl heq' => exfalso; exact ha.right b ⟨hb.left, Nat.ne_of_lt hlt⟩ heq'
            | inr hlt' => assumption
          have hbmem: b ∈ as := dvd_prod_dvd_mem hb (forall_tail hs₁.left) hxxxx
          have hble := sorted_head_le_tail a as h₁ b hbmem
          exfalso
          omega

    have hprod_as_eq_prod_bs: prod as = prod bs := by
      rw [←haeqb, hn₁] at hn₂
      apply Nat.eq_of_mul_eq_mul_left
      exact hgt₁ a (List.mem_cons_self a as)
      assumption

    have haseqbs := unique_pd as bs (reducible_pd hs₁) ⟨forall_tail hs₂.left, hprod_as_eq_prod_bs⟩ (is_sorted_tail h₁) (is_sorted_tail h₂)

    exact ⟨haeqb, haseqbs⟩

def factorial (n: Nat) := Nat.fold (fun n => ((n+1) * .)) n 1

theorem factorial_0_is_1: factorial 0 = 1 :=
  rfl

theorem factorial_1_is_1: factorial 1 = 1 :=
  rfl

theorem factorial_2_is_2: factorial 2 = 2 :=
  rfl

theorem factorial_3_is_6: factorial 3 = 6 :=
  rfl

theorem factorial_mul {n: Nat}: factorial (n + 1) = (n + 1) * factorial n := by
  simp only [factorial, Nat.fold]

theorem zero_lt_factorial {n: Nat}: 0 < factorial n := by
  induction n with
  | zero => rw [factorial_0_is_1]; apply Nat.lt_add_one
  | succ n ih => rw [factorial_mul]; exact Nat.mul_pos (Nat.zero_lt_succ n) ih

theorem le_factorial {n: Nat}: n ≤ factorial n := by
  match n with
  | 0 => rw [factorial_0_is_1]; exact Nat.zero_le 1
  | i + 1 =>
    rw [factorial_mul]
    exact Nat.le_mul_of_pos_right (i + 1) zero_lt_factorial

theorem lt_factorial {n: Nat} (h: 2 < n): n < factorial n := by
  match n with
  | 0 | 1 | 2 => contradiction
  | i + 3 =>
    rw [factorial_mul, Nat.add_assoc]
    conv =>
      left; rw [← Nat.mul_one (i + 3)]
    apply Nat.mul_lt_mul_of_pos_left
    case hk => omega
    case h => induction i with
      | zero => simp only [Nat.zero_add, factorial_2_is_2, Nat.lt_add_one]
      | succ i hi =>
        rw [factorial_mul]
        calc
          1 < factorial (i + 2) := hi (by omega)
          _ < (i + 2) * factorial (i + 2) + factorial (i + 2) := by
            apply Nat.lt_add_of_pos_left
            exact Nat.mul_pos (by omega) (zero_lt_factorial)
          _ = (i + 3) * factorial (i + 2) := by rw [←Nat.succ_mul]

theorem dvd_factorial_of_le {n m: Nat} (h: m ≤ n) (hm: 0 < m): m ∣ factorial n := by
  induction n with
  | zero => rw [Nat.eq_zero_of_le_zero h] at hm; contradiction
  | succ n hi =>
    rw [factorial_mul]
    cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      rcases hi (Nat.le_of_lt_succ hlt) with ⟨l, hl⟩
      exists l * (n + 1)
      rw [Nat.mul_comm, hl, Nat.mul_assoc]
    | inr heq =>
      rw [heq]
      exists factorial n

def minFacAux (n k: Nat) (h: 1 < k):=
  if k ∣ n then k
  else if n < k*k then n
  else minFacAux n (k + 2) (by omega)
termination_by n - k
decreasing_by
  have : k < k * k := by
    conv => lhs; rw [←Nat.mul_one k]
    rwa [Nat.mul_lt_mul_left (by omega)]
  omega

def minFac (n: Nat) :=
  if 2 ∣ n then 2
  else minFacAux n 3 (by omega)

theorem minFac_0_is_2: minFac 0 = 2 := by
  rfl

theorem minFac_1_is_1: minFac 1 = 1 := by
  simp [minFac, minFacAux]

theorem minFac_2_is_2: minFac 2 = 2 := by
  simp [minFac, minFacAux]
  intro h
  exfalso
  apply h
  apply Nat.dvd_refl

theorem minFac_3_is_3: minFac 3 = 3 := by
  simp [minFac, minFacAux]
  omega

theorem minFac_35_is_5: minFac 35 = 5 := by
  simp [minFac, minFacAux]
  repeat first | split | omega


theorem min_fac_aux_pos {n k: Nat} (h: 1 < k): 0 < minFacAux n k h := by
  unfold minFacAux
  split
  . omega
  . split
    case isFalse.isTrue hndiv _ =>
      by_cases h₀: n = 0
      . exfalso; apply hndiv; rw [h₀]; apply Nat.dvd_zero
      . omega
    . apply min_fac_aux_pos
termination_by n - k
decreasing_by
  -- This seems somewhat crude ...
  have : k < k * k := by
    conv => lhs; rw [←Nat.mul_one k]
    rwa [Nat.mul_lt_mul_left (by omega)]
  omega

theorem min_fac_pos {n: Nat}: 0 < minFac n := by
  unfold minFac
  split
  . apply Nat.succ_pos
  . apply min_fac_aux_pos

theorem min_fac_aux_gt_2 {n k: Nat} (hk: 1 < k) (hn: 1 < n): 1 < minFacAux n k hk := by
  unfold minFacAux
  split
  . assumption
  . split
    . assumption
    . apply min_fac_aux_gt_2
      exact hn
termination_by n - k
decreasing_by
  -- This seems somewhat crude ...
  have : k < k * k := by
    conv => lhs; rw [←Nat.mul_one k]
    rwa [Nat.mul_lt_mul_left (by omega)]
  omega

theorem min_fac_gt_2 {n: Nat} (h: 1 < n): 1 < minFac n := by
  unfold minFac
  split
  . omega
  . apply min_fac_aux_gt_2 (by omega) h

theorem min_fac_aux_dvd {n k: Nat} (hk: 1 < k): minFacAux n k hk ∣ n := by
  unfold minFacAux
  split
  . assumption
  . split
    . apply Nat.dvd_refl
    . exact min_fac_aux_dvd (by omega)
termination_by n - k
decreasing_by
  -- This seems somewhat crude ...
  have : k < k * k := by
    conv => lhs; rw [←Nat.mul_one k]
    rwa [Nat.mul_lt_mul_left (by omega)]
  omega

theorem min_fac_dvd {n: Nat}: minFac n ∣ n := by
  unfold minFac
  split
  . assumption
  . exact min_fac_aux_dvd (by omega)

theorem odd_of_odd_plus_2 {n: Nat} (h: IsOdd n): IsOdd (n + 2) := by
  rcases h with ⟨k, hk⟩
  exists k + 1
  omega

theorem not_dvd_of_sq_lt {n k: Nat} (hn: 0 < n) (h: n < k * k) (hall: ∀i, 1 < i → i < k → ¬i ∣ n): ∀m, m < n → k < m → ¬ m ∣ n := by
  rintro m hltm hgt ⟨l, hl⟩
  have hk_pos: 0 < k := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt h)
  have hlt: l < k := by
    false_or_by_contra
    rename ¬l < k => hge'
    replace hgt' := Nat.le_of_not_lt hge'
    have hl_pos: 0 < l := by omega
    rw [hl] at h
    have h_contra: m * l < m * l := by calc
      m * l < k * k := h
      _ ≤ k * l := Nat.mul_le_mul_left k hgt'
      _ < m * l := (Nat.mul_lt_mul_right hl_pos).mpr hgt
    exact Nat.lt_irrefl (m * l) h_contra
  have hl: 1 < l := by
    match l with
    | 0 => rw [hl, Nat.mul_zero] at hn; contradiction;
    | 1 => rw [hl, Nat.mul_one] at hltm; exfalso; exact Nat.lt_irrefl m hltm
    | l + 2 => omega
  apply hall l hl hlt
  exists m
  rwa [Nat.mul_comm]

theorem min_fac_le_n {n: Nat} (h: 0 < n): minFac n ≤ n :=
  Nat.le_of_dvd h min_fac_dvd

theorem min_fac_aux_is_min {n m: Nat} (hn: 1 < n) (hm: 1 < m) (hk: 3 ≤ k) (hodd: IsOdd k) (hind: ∀i, 1 < i → i < k → ¬i∣n) (h2n: ¬ 2 ∣ n) (hlt: m < minFacAux n k (by omega)) (hmn: m ∣ n): False := by
  unfold minFacAux at hlt
  split at hlt
  case isTrue => exact hind m hm hlt hmn
  case isFalse hndvd =>
    by_cases hmk: m < k
    . exact hind m hm hmk hmn
    . replace hmk: k < m := by
        have tmp: k ≠ m := by
          intro heq
          rw [←heq] at hmn
          exact hndvd hmn
        exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hmk) tmp
      split at hlt
      case neg.isTrue hnk2 =>
        exact not_dvd_of_sq_lt (Nat.lt_of_succ_lt hn) hnk2 hind m hlt hmk hmn
      case neg.isFalse =>
        have hk': 3 ≤ k + 2 := by omega
        have hodd': IsOdd (k + 2) := odd_of_odd_plus_2 hodd
        have hind': ∀i, 1 < i → i < k + 2 → ¬ i∣n := by
          have hndvd1: ¬k+1∣n := even_not_dvd_odd (even_of_succ_odd hodd') (odd_of_not_two_dvd h2n)
          intro i hi hik2 hin
          cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hik2)
          case inr heq => rw [heq] at hin; contradiction
          case inl hlt' =>
            cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt')
            case inr heq => rw [heq] at hin; contradiction
            case inl hlt'' => exact hind i hi hlt'' hin
        exact min_fac_aux_is_min hn hm hk' hodd' hind' h2n hlt hmn
termination_by n - k
decreasing_by
  rename ¬ n < k * k  => hk2
  replace hk2 := Nat.le_of_not_lt hk2
  have : k < k * k := by
    conv => lhs; rw [←Nat.mul_one k]
    rw [Nat.mul_lt_mul_left (by omega)]
    omega
  omega

theorem min_fac_is_min {n m: Nat} (hn: 0 < n) (hm: 1 < m) (hlt: m < minFac n): ¬ m ∣ n := by
  -- Argue that n actually needs to be larger or equal to two
  replace hn: 1 < n :=
    Nat.lt_trans hm (Nat.lt_of_lt_of_le hlt (min_fac_le_n hn))

  -- Now unroll minFac and prove the base cases
  unfold minFac at hlt
  split at hlt
  -- The even case follows from simple arithmetics as m needs to be less than 2
  -- but is assumed to be larger or equal.
  case isTrue => omega

  -- In the odd case, we construct our hypothesis that no number less than 3 and larger
  -- than 1 divides n.
  case isFalse h2n =>
    -- We do this by case distinction. Everything other than 2 runs into some contradiction.
    have hind: ∀i, 1 < i → i < 3 → ¬i∣n := by
      intro i hi hin
      match i with
      | 2 => exact h2n
      | 0 | 1 | i + 3 => contradiction
    -- And then we simply need to call the min_fac_aux_is_min proof with k = 3
    exact min_fac_aux_is_min hn hm (Nat.le_refl 3) (by exists 1) hind h2n hlt

theorem min_fac_is_prime {n: Nat} (h: 1 < n): Prime (minFac n) := by
  constructor
  -- Proof that the min prime factor needs to be at least 2
  . exact min_fac_gt_2 h
  -- Show that the prime factor is not divisible by any other number
  . rintro m ⟨hm2, hmr⟩ hmd
    have hm': m < minFac n :=
      Nat.lt_of_le_of_ne (Nat.le_of_dvd min_fac_pos hmd) hmr

    -- Apply the proof that the minimum prime factor is indeed the minimum prime factor.
    -- To show a contradiction we then need to proof that m ∣ n, which follows from the fact
    -- that the min prime factor of n divides n.
    apply min_fac_is_min (Nat.lt_of_succ_lt h) hm2 hm'
    exact Nat.dvd_trans hmd min_fac_dvd

-- If a product of two factors equals one, then both factors themselves need to be one
theorem mul_one_one_of_eq_one {n m: Nat}: n * m = 1 ↔ n = 1 ∧ m = 1 := by
  constructor
  -- By case distinction all cases other than (1,1) lead to contradictions
  . intro h
    match n, m with
      | 0, _ => rw [Nat.zero_mul] at h; contradiction
      | _, 0 => rw [Nat.mul_zero] at h; contradiction
      | 1, 1 => exact ⟨rfl, rfl⟩
      | n + 2, m + 2 =>
        rw [Nat.add_mul] at h
        simp_arith only at h
  -- If we know the value of the factors the result follows trivially.
  . rintro ⟨hn, hm⟩
    rw [hn, hm]


-- A positive number that is divided by a non-trivial factor does not share that factor with its
-- successor. This is used for showing that we can construct a new prime number by multiplying
-- all known prime numbers together.
theorem not_dvd_succ_of_dvd {n m: Nat} (hm: 0 < m) (hn2: 1 < n) (h: n ∣ m): ¬ n ∣ m + 1 := by
  rintro ⟨l, hl⟩
  rcases h with ⟨k, hk⟩
  match n with
  | 0 | 1 => contradiction
  | n + 2 =>
    -- Kowing that n is positive, we can create a contradiction. This mainly exploits the
    -- fact that m + 1 - m = 1 and that we have representations as factors. Can likely
    -- be simplified.
    have hm_lt: m < m + 1 := by omega

    have hlt: k < l := by
      rw [hl, hk] at hm_lt
      exact Nat.lt_of_mul_lt_mul_left hm_lt

    have hk_pos: 0 < k := by
      rw [hk] at hm;
      exact Nat.pos_of_mul_pos_left hm

    have hl_pos: 0 < l := by
      replace h_pos := Nat.lt_succ_of_lt hm
      rw [Nat.succ_eq_add_one, hl] at h_pos;
      exact Nat.pos_of_mul_pos_left h_pos

    have hkl: 0 < l - k := Nat.sub_pos_iff_lt.mpr hlt

    have hx: 0 = (n + 2) * (l - k) - 1 := calc
      0 = (n + 2) * l - (m + 1) := by rw [hl, Nat.sub_self]
      _ = (n + 2) * l - ((n + 2) * k + 1) := by rw [hk]
      _ = (n + 2) * l - (n + 2) * k - 1 := by rw [Nat.sub_add_eq]
      _ = (n + 2) * (l - k) - 1 := by rw [Nat.mul_sub_left_distrib]

    replace hx: 1 = (n + 2) * (l - k) := by
      have bla := Nat.sub_eq_zero_iff_le.mp (Eq.symm hx)
      cases Nat.lt_or_eq_of_le bla with
      | inl hlt =>
        rw [Nat.lt_one_iff] at hlt
        exfalso
        have tmp := Nat.mul_pos (Nat.succ_pos (n + 1)) hkl
        rw [hlt] at tmp
        contradiction
      | inr heq => rw [heq]

    replace hx := (mul_one_one_of_eq_one.mp (Eq.symm hx)).left
    rw [hx] at hn2
    exact Nat.lt_irrefl 1 hn2


theorem exists_infinite_primes: (∀n, ∃p, n ≤ p ∧ Prime p) := by
  intro n
  exists minFac (factorial n + 1)
  constructor
  . false_or_by_contra
    rename _ => hgt
    replace hgt := Nat.gt_of_not_le hgt
    have h_dvd_0: minFac (factorial n + 1) ∣ factorial n := dvd_factorial_of_le (Nat.le_of_lt hgt) min_fac_pos
    have h_dvd_1: minFac (factorial n + 1) ∣ factorial n + 1 := min_fac_dvd
    exact not_dvd_succ_of_dvd zero_lt_factorial (min_fac_gt_2 (by apply Nat.succ_lt_succ; exact zero_lt_factorial)) h_dvd_0 h_dvd_1
  . apply min_fac_is_prime
    exact Nat.succ_lt_succ_iff.mpr (zero_lt_factorial)
