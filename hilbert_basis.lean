import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.RingTheory.Noetherian.Defs


/- main theorem does not need lemmas from laurent series.
it's here just to give a corollary. -/
import Mathlib.RingTheory.LaurentSeries


namespace PowerSeries

variable {R : Type*}


section Semiring

variable [Semiring R] {p q : R⟦X⟧} {r : R}

section Basic

theorem C_mul_X_pow_eq_monomial {n : ℕ} :
  C R r * X ^ n = monomial R n r := by
  ext i
  simp [coeff_monomial, coeff_X_pow]


end Basic



section Order

/- if ca ≠ 0, where a is leading coefficient of p, then order of cp equal p. -/
theorem order_C_mul_of_mul_ne_zero {k : ℕ} (h1 : p.order = k)
  (h2 : r * coeff R k p ≠ 0) :
  ((C R r) * p).order = k := by
  rw [← h1]
  apply le_antisymm ?_ ?_
  · have : (C R r) * p ≠ 0 := by
      suffices coeff R k ((C R r) * p) ≠ 0 by
        rintro hh
        simp [hh] at this
      simp [h2]
    have pnz: p ≠ 0 := by
      rintro hh
      simp [hh] at h1
    delta order
    simp only [this, ↓reduceDIte, coeff_C_mul, ne_eq, pnz,
      Nat.cast_le, Nat.le_find_iff, Nat.lt_find_iff, not_not]
    intro i h3
    by_contra! h4
    have: k ≤ i := by
      by_contra!
      absurd h4
      rw [coeff_of_lt_order_toNat]
      simp [h1, this]
    apply h2 (h3 k this)
  · refine le_trans ?_ (le_order_mul (C R r) p)
    simp

@[simp]
lemma order_le_order_mul_left : p.order ≤ (q * p).order := by
  apply le_trans ?_ (le_order_mul q p)
  simp

@[simp]
lemma order_le_order_mul_right : p.order ≤ (p * q).order := by
  apply le_trans ?_ (le_order_mul p q)
  simp


theorem order_X_pow_mul {k : ℕ} :
  (X ^ k * p).order = k + p.order := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← coe_toNat_order hp]
  norm_cast
  apply le_antisymm ?_ ?_
  · apply order_le _ ?_
    rw [add_comm k _, coeff_X_pow_mul]
    exact coeff_order hp
  · apply le_order _ _ ?_
    intro i
    norm_cast
    intro hi
    rw [coeff_X_pow_mul']
    by_cases h : k ≤ i
    · simp only [h, ↓reduceIte]
      rw [coeff_of_lt_order]
      rw [← coe_toNat_order hp]
      norm_cast
      exact Nat.sub_lt_left_of_lt_add h hi
    · simp [h]



theorem order_add_of_coeff_ne_zero {k : ℕ}
  (hp : p.order = k) (hq : q.order = k)
  (h : coeff R k (p + q) ≠ 0) :
  (p + q).order = k := by
  apply le_antisymm ?_ ?_
  · by_contra! hh
    absurd h
    rw [coeff_of_lt_order _ hh]
  · apply le_trans ?_ (min_order_le_order_add _ _)
    simp only [le_inf_iff]
    simp [hp, hq]


theorem le_order_C_mul_finset_sum {n k : ℕ} {r : ℕ → R} {p : ℕ → R⟦X⟧}
  (h : ∀ i ∈ Finset.range n, (p i).order = k) :
  k ≤ (∑ i ∈ Finset.range n, (C R (r i)) * (p i)).order := by
  induction' n with n ih
  · simp
  · have: ∀ i ∈ Finset.range n, (p i).order = k := by
      refine (fun i hi => h i ?_)
      simp only [Finset.mem_range] at hi ⊢
      exact hi.trans (lt_add_one n)
    simp only [Finset.sum_range_succ]
    apply le_trans _ (min_order_le_order_add _ _)
    simp only [le_inf_iff, ih this, true_and]
    nth_rw 1 [← h n (Finset.self_mem_range_succ n)]
    exact order_le_order_mul_left

theorem le_order_C_mul_finsum {n k : ℕ} {r : Fin n → R} {p : Fin n → R⟦X⟧}
  (h : ∀ i, (p i).order = k) :
  k ≤ (∑ i, (C R (r i)) * p i).order := by
  let r' : ℕ → R := fun i => if h : i < n then r ⟨i,h⟩  else 0
  let p' : ℕ → R⟦X⟧ := fun i => if h : i < n then p ⟨i,h⟩ else 0
  have: ∑ i, (C R (r i)) * (p i) =
    ∑ i ∈ Finset.range n, (C R (r' i)) * (p' i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [r', p']
  rw [this]
  apply le_order_C_mul_finset_sum ?_
  intro i
  simp only [Finset.mem_range]
  intro hi
  simp only [hi, ↓reduceDIte, h, p']


theorem ne_order_of_coeff_eq_zero {k : ℕ}
  (h : coeff R k p = 0) : ¬ k = p.order := by
  by_cases hp : p = 0
  · simp [hp]
  rintro heq
  absurd h
  have: k = p.order.toNat := by simp [← heq]
  rw [this]
  exact coeff_order hp


theorem order_C_mul_finset_sum {n k : ℕ} {r : ℕ → R} {p : ℕ → R⟦X⟧}
  (h1 : coeff R k (∑ i ∈ Finset.range n, (C R (r i)) * (p i)) ≠ 0)
  (h2 : ∀ i ∈ Finset.range n, (p i).order = k) (hn : n ≥ 1) :
  (∑ i ∈ Finset.range n, (C R (r i)) * (p i)).order = k := by
  induction' n,hn using Nat.le_induction with n hn ih
  · simp only [Finset.range_one, Finset.sum_singleton]
    simp only [Finset.range_one, Finset.sum_singleton, coeff_C_mul, ne_eq] at h1
    specialize h2 0 (by simp)
    rw [order_C_mul_of_mul_ne_zero h2 h1]
  · simp only [Finset.sum_range_succ]
    have hh : ∀ i ∈ Finset.range n, (p i).order = k := by
      refine (fun i hi => h2 i ?_)
      simp at hi ⊢
      exact hi.trans (lt_add_one n)
    specialize h2 n (by simp)
    by_cases h3: coeff R k (∑ i ∈ Finset.range n, (C R (r i)) * p i) = 0
    · simp only [Finset.sum_range_succ, map_add,
        h3, zero_add, coeff_C_mul] at h1
      have: (∑ i ∈ Finset.range n, (C R (r i)) * p i).order > k := by
        apply lt_of_le_of_ne ?_ ?_
        · apply le_order_C_mul_finset_sum hh
        · apply ne_order_of_coeff_eq_zero h3
      have h4: ((C R (r n)) * (p n)).order = k :=
        order_C_mul_of_mul_ne_zero h2 h1
      rw [← h4] at this ⊢
      rw [order_add_of_order_eq _ _ this.ne']
      simp [this.le]
    · specialize ih h3 hh
      simp only [Finset.sum_range_succ] at h1
      by_cases h4 : r n * coeff R k (p n) = 0
      · suffices k < (C R (r n) * (p n)).order by
          rw [← ih] at this ⊢
          rw [order_add_of_order_eq _ _ this.ne]
          simp [this.le]
        apply lt_of_le_of_ne ?_ ?_
        · simp [← h2, order_le_order_mul_left]
        · apply ne_order_of_coeff_eq_zero (by simp [h4])
      · apply order_add_of_coeff_ne_zero ih ?_ h1
        apply order_C_mul_of_mul_ne_zero h2 h4

theorem order_C_mul_finsum {n k : ℕ} {r : Fin n → R} {p : Fin n → R⟦X⟧}
  (h1 : coeff R k (∑ i, (C R (r i)) * (p i)) ≠ 0)
  (h2 : ∀ i, (p i).order = k) (hn : n ≥ 1) :
  (∑ i, (C R (r i)) * (p i)).order = k := by
  let r' : ℕ → R := fun i => if h : i < n then r ⟨i,h⟩  else 0
  let p' : ℕ → R⟦X⟧ := fun i => if h : i < n then p ⟨i,h⟩ else 0
  have: ∑ i, (C R (r i)) * (p i) =
    ∑ i ∈ Finset.range n, (C R (r' i)) * (p' i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [r', p']
  rw [this]
  apply order_C_mul_finset_sum ?_ ?_ hn
  · rw [← Fin.sum_univ_eq_sum_range]
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, r', p']
    exact h1
  · simp only [Finset.mem_range]
    intro i hi
    simp [p', hi, h2 ⟨i,hi⟩]

end Order


section Trunc

/- Notice : most of trunc lemmas in this section depend on order lemmas above
and api from mathlib Order file. To put these lemmas in a single file,
the imports should include both Trunc file and Order file. -/

/- if i ≤ order of p, then its truncate at i is 0.   -/
theorem trunc_eq_zero_of_le_order {i : ℕ}
  (hi : i ≤ p.order) : p.trunc i = 0 := by
  simp only [trunc, Nat.Ico_zero_eq_range]
  apply Finset.sum_eq_zero ?_
  intro j
  simp only [Finset.mem_range, Polynomial.monomial_eq_zero_iff]
  intro jlt
  apply coeff_of_lt_order _ (lt_of_lt_of_le ?_ hi)
  simp [jlt]


theorem trunc_ne_zero_of_order_lt {i : ℕ}
  (hi : p.order < i) : p.trunc i ≠ 0 := by
  suffices coeff R p.order.toNat (p.trunc i).toPowerSeries ≠ 0 by
    contrapose! this
    simp [this]
  simp only [Polynomial.coeff_coe, ne_eq]
  have pnz: p ≠ 0 := by
    contrapose! hi
    simp [hi]
  rw [← coe_toNat_order pnz, Nat.cast_lt] at hi
  rw [coeff_trunc, if_pos hi]
  exact coeff_order pnz


@[simp]
lemma trunc_toNat_order : p.trunc p.order.toNat = 0 := by
  apply trunc_eq_zero_of_le_order
  exact ENat.coe_toNat_le_self p.order

lemma trunc_order_succ {k : ℕ} (hk : p.order = k) :
  p.trunc (k + 1) = Polynomial.monomial k (coeff R k p) := by
  rw [trunc_succ, trunc_eq_zero_of_le_order (by simp [hk])]
  simp

theorem trunc_monomial_of_le {i j : ℕ} (hij : i ≤ j) :
  trunc i (monomial R j r) = 0 := by
  simp only [trunc, Nat.Ico_zero_eq_range]
  apply Finset.sum_eq_zero ?_
  intro k
  simp only [Finset.mem_range, Polynomial.monomial_eq_zero_iff]
  intro klt
  have := lt_of_lt_of_le klt hij
  simp [monomial_eq_mk, this.ne]

theorem eq_iff_forall_trunc : p = q ↔
  ∀ i : ℕ, p.trunc (i+1) = q.trunc (i+1) := by
  constructor
  · intro h
    simp [h]
  · intro h
    ext j
    specialize h j
    have: (trunc (j+1) p ).coeff j = (trunc (j+1) q).coeff j := by
      rw [h]
    simp only [coeff_trunc,
      lt_add_iff_pos_right, zero_lt_one, ↓reduceIte] at this
    exact this

@[simp]
theorem trunc_finset_sum {n m : ℕ} {f : ℕ → R⟦X⟧} :
  trunc n (∑ i ∈ Finset.range m, f i) =
  ∑ i ∈ Finset.range m, trunc n (f i) := by
  induction' m with m ih
  · simp
  · simp [Finset.sum_range_succ, ih]

@[simp]
theorem trunc_finsum {n m : ℕ} {f : Fin m → R⟦X⟧} :
  trunc n (∑ i, f i) = ∑ i, trunc n (f i) := by
  let f' : ℕ → R⟦X⟧ := fun i => if h : i < m then f ⟨i,h⟩ else 0
  have: ∑ i, f i = ∑ (i : Fin m), f' i := by
    simp [f']
  rw [this, Fin.sum_univ_eq_sum_range,
    trunc_finset_sum, ← Fin.sum_univ_eq_sum_range]
  simp [f']

theorem trunc_down (m : ℕ) {n : ℕ} (h : p.trunc (m + n) = q.trunc (m + n)) :
  p.trunc n = q.trunc n := by
  ext i
  have hh: (p.trunc (m + n)).coeff i = (q.trunc (m + n)).coeff i := by
    rw [h]
  simp only [coeff_trunc] at hh ⊢
  by_cases hi : i < n
  · have : i < m + n := lt_of_lt_of_le hi (by simp)
    simp only [this, ↓reduceIte] at hh
    simp [hi, hh]
  · simp [hi]


theorem trunc_trunc_mul_of_order_eq {m n : ℕ}
  (hq : q.order = n) :
  trunc (m + n) ((trunc m p) * q : R⟦X⟧) = trunc (m + n) (p * q) := by
  ext i
  rw [coeff_trunc, coeff_trunc]
  split_ifs with h
  · rw [coeff_mul, coeff_mul, Finset.sum_congr rfl ?_]
    intro j hj
    simp only [Finset.mem_antidiagonal] at hj
    rw [Polynomial.coeff_coe]
    by_cases h2 : j.1 < m
    · rw [coeff_trunc, if_pos h2]
    · rw [coeff_trunc, if_neg h2]
      push_neg at h2
      have : j.2 < q.order := by
        simp only [hq, Nat.cast_lt]
        omega
      rw [coeff_of_lt_order _ this]
      simp
  · rfl

theorem trunc_X_pow_mul {m n : ℕ} :
  trunc (m + n) (X^m * p) = Polynomial.X^m * trunc n p := by
  induction' n with n ih
  · simp only [add_zero, trunc_zero', mul_zero]
    rw [trunc_eq_zero_of_le_order]
    simp [order_X_pow_mul]
  · rw [← add_assoc, trunc_succ, ih, trunc_succ, mul_add]
    simp only [Polynomial.X_pow_mul_monomial, add_comm n m]
    suffices coeff R (m+n) (X^m * p) = coeff R n p by rw [this]
    rw [add_comm m n, coeff_X_pow_mul]



theorem cast_trunc_mk_eq_finset_sum {f : ℕ → R} {n : ℕ} :
  (trunc n (mk f) : R⟦X⟧) = ∑ i ∈ Finset.range n, X^i * C R (f i) := by
  induction' n with n ih
  · simp
  · rw [trunc_succ, Finset.sum_range_succ, ← ih]
    simp only [coeff_mk, Polynomial.coe_add, Polynomial.coe_monomial]
    rw [X_pow_mul, C_mul_X_pow_eq_monomial]


end Trunc

section Ideal

variable {I : Ideal R⟦X⟧}

theorem mem_ideal_of_mem_subset_span {S : Set R⟦X⟧}
  (hS : ∀ q ∈ S, q ∈ I) (h : p ∈ Ideal.span S) : p ∈ I := by
  suffices Ideal.span S ≤ I by exact this h
  rw [← Ideal.span_eq I]
  exact Ideal.span_mono hS


/- for p a power series, a its leading coefficient,
if a is linear combination of a0, a1, ..., a_{n-1},
f maps each a_i to its "representative power series" f_i,
then p can be written as some form of lienar combination of f_0, f_1, ..., f_{n-1},
such that they have same leading coefficient and order. -/
theorem exists_coeff_order_eq_mem_span_image_of_coeff_mem_span
  {k : ℕ} {S : Finset R} {f : R → R⟦X⟧} (hp : p.order = k)
  (hS : coeff R k p ∈ Ideal.span S)
  (hf : ∀ a ∈ S, (f a).order = k ∧ coeff R k (f a) = a ∧ f a ∈ I) :
  ∃ q ∈ Ideal.span (f '' S),
    q.order = k ∧ coeff R k q = coeff R k p ∧ q ∈ I := by
  have pnz : p ≠ 0 := by
    contrapose! hp
    simp [hp]
  have pnz' : coeff R k p ≠ 0 := by
    rw [← coe_toNat_order pnz, Nat.cast_inj] at hp
    rw [← hp]
    exact coeff_order pnz
  have: S.toSet.Finite := by simp
  rcases this.fin_embedding with ⟨n, a, ha⟩
  have hn : n ≥ 1 := by
    suffices n ≠ 0 by omega
    rintro hn
    have: S.toSet = ∅ := by
      rw [← ha]
      simp only [Set.range_eq_empty_iff, hn]
      exact Fin.isEmpty'
    simp only [this, Ideal.span_empty, Ideal.mem_bot] at hS
    exact pnz' hS
  rw [← ha, Ideal.mem_span_range_iff_exists_fun] at hS
  rcases hS with ⟨c, hc⟩
  use ∑ i, (C R (c i)) * f (a i)
  have h1 : ∑ i, (C R (c i)) * f (a i) ∈ Ideal.span (f '' S) := by
    letI := Classical.decEq R⟦X⟧
    delta Ideal.span
    rw [Submodule.mem_span_set']
    use n, (fun i => C R (c i))
    simp only [smul_eq_mul]
    have: ∀ i : Fin n, f (a i) ∈ f '' S := by
      intro i
      rw [← ha]
      simp
    use (fun i => ⟨(f (a i)), this i⟩)
  have h2 : ∀ q ∈ f '' S, q ∈ I := by
    simp only [Set.mem_image, Finset.mem_coe, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro b hb
    exact (hf b hb).right.right
  have a_mem : ∀ i, a i ∈ S := by
    intro i
    suffices a i ∈ S.toSet by
      rwa [Finset.mem_coe] at this
    simp [← ha]
  have hfa: ∀ i, coeff R k (f (a i)) = a i := by
    intro i
    exact (hf (a i) (a_mem i)).right.left
  refine ⟨h1, ?_, ?_, mem_ideal_of_mem_subset_span h2 h1⟩
  · apply order_C_mul_finsum ?_ ?_ hn
    · simp [hfa, hc, pnz']
    · intro i
      apply (hf (a i) (a_mem i)).left
  · simp [← hc, hfa]

variable (I)

/- given an ideal I of R⟦X⟧, make the ideal of leading coefficients
of power series in I with order ≥ k. -/
def coeffOrderGE (k : ℕ) : Ideal R where
  carrier := {a | ∃ p ∈ I, a = coeff R k p ∧ p.order ≥ k}
  add_mem' := by
    intro a b
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro p1 p1_mem p1_coeff p1_order p2 p2_mem p2_coeff p2_order
    use (p1 + p2)
    suffices k ≤ (p1 + p2).order by
      simp [I.add_mem p1_mem p2_mem, p1_coeff, p2_coeff, this]
    refine le_trans ?_ (min_order_le_order_add p1 p2)
    exact le_min p1_order p2_order
  zero_mem' := by
    simp only [ge_iff_le, Set.mem_setOf_eq]
    use C R 0
    simp
  smul_mem' := by
    intro c a
    simp only [Set.mem_setOf_eq, smul_eq_mul, forall_exists_index, and_imp]
    intro p p_mem p_coeff p_order
    use (C R c) * p
    suffices k ≤ ((C R c) * p).order by
      simp [I.mul_mem_left _ p_mem, coeff_C_mul, p_coeff, this]
    refine p_order.trans ?_
    refine le_trans ?_ (le_order_mul _ p)
    simp

/- ideal I k defined by leading coefficients of p with order ≥ k is monotone. -/
lemma coeffOrderGE_le_succ (k : ℕ) [Nontrivial R] :
  coeffOrderGE I k ≤ coeffOrderGE I (k+1) := by
  intro a
  delta coeffOrderGE
  simp only [ge_iff_le, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    Nat.cast_add, Nat.cast_one, forall_exists_index, and_imp]
  intro p p_mem p_coeff p_order
  use X * p
  suffices (k: ENat) + 1 ≤ (X * p).order by
    simp [I.mul_mem_left X p_mem, p_coeff, this]
  rw [X_mul]
  refine le_trans ?_ (le_order_mul p X)
  refine add_le_add p_order ?_
  simp

theorem coeffOrderGE_mono [Nontrivial R] :
  Monotone (coeffOrderGE I) := by
  intro i j hij
  induction' j,hij using Nat.le_induction with j hij ih
  · simp
  · refine ih.trans ?_
    apply coeffOrderGE_le_succ

/- if coefficient a is member of the above ideal,
then we can find the corresponding power series p. -/
theorem mem_coeffOrderGE_iff_exists
  {I : Ideal R⟦X⟧} {k : ℕ} {a : R} (ha : a ≠ 0) :
  a ∈ coeffOrderGE I k ↔
  ∃ p ∈ I, a = coeff R k p ∧ p.order = k := by
  constructor <;> intro h
  · simp only [coeffOrderGE, ge_iff_le, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at h
    rcases h with ⟨p, p_mem, p_coeff, p_order⟩
    have pnz: p ≠ 0 := by
      rintro peq
      simp only [peq, map_zero] at p_coeff
      exact ha p_coeff
    use p, p_mem
    refine ⟨p_coeff, ?_⟩
    apply le_antisymm ?_ p_order
    contrapose! ha
    rw [p_coeff]
    exact coeff_of_lt_order _ ha
  · simp only [coeffOrderGE, ge_iff_le, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    rcases h with ⟨p, p_mem, p_coeff, p_order⟩
    use p, p_mem, p_coeff, p_order.symm.le


end Ideal

end Semiring


section Ring

variable [Ring R]

section Order

variable {p q : R⟦X⟧}

/- order of p equal order of -p.  -/
@[simp]
lemma order_neg : (-p).order = p.order := by
  by_cases hp: p = 0
  · simp [hp]
  · have: ¬ -p = 0 := by simp [hp]
    simp only [order, this, ↓reduceDIte, map_neg,
      ne_eq, neg_eq_zero, hp, Nat.cast_inj]
    congr 1
    simp

lemma order_sub_comm : (p - q).order = (q - p).order := by
  rw [show p - q = - (q - p) by simp, order_neg]

/- order of p-q ≥ min of them. -/
theorem min_order_le_order_sub : min p.order q.order ≤ (p - q).order := by
  rw [sub_eq_add_neg]
  convert min_order_le_order_add p (-q) using 2
  simp

end Order

section Trunc

variable {p q : R⟦X⟧}

@[simp]
lemma trunc_neg {k : ℕ} : (-p).trunc k = - (p.trunc k) := by
  delta trunc
  simp

@[simp]
lemma trunc_sub {k : ℕ} : (p-q).trunc k = p.trunc k - q.trunc k := by
  rw [sub_eq_add_neg, trunc_add]
  simp [← sub_eq_add_neg]

theorem trunc_succ_eq_of_trunc_sub_eq {n : ℕ} {p q pp : R⟦X⟧}
  (h : trunc (n + 1) pp = trunc (n + 1) (q - p)) :
  trunc (n+1) (p + pp) = trunc (n+1) q := by
  rw [show q = (q - p) + p by simp]
  simp [trunc_add, h]

theorem trunc_eq_trunc_of_lt_sub_order {n : ℕ} (hn : n < (p - q).order) :
  trunc (n + 1) p = trunc (n + 1) q := by
  rw [← sub_eq_zero, ← trunc_sub, trunc_eq_zero_of_le_order]
  simp only [Nat.cast_add, Nat.cast_one]
  exact Order.add_one_le_of_lt hn


/- if p,q has same first n terms, then order of p-q is at least n. -/
theorem le_order_of_trunc_eq {n : ℕ} (h : p.trunc n = q.trunc n) :
  n ≤ (p-q).order := by
  rw [← sub_eq_zero, ← trunc_sub] at h
  contrapose! h
  exact trunc_ne_zero_of_order_lt h

end Trunc


section Ideal

variable {I : Ideal R⟦X⟧}

/- if span S 0, span S 1, ... is ideal such that it collects all leading ceofficients
of power series with order 0, 1,...,
f maps coefficients from S to its "representative power series",
then power series can be written as linear combination of those f_i,
such that they have same first n terms, for any finite n. -/
theorem exists_trunc_eq_mem_span_biUnion_of_forall_coeff_mem_span
  (k : ℕ) (S : ℕ → Finset R) (f : ℕ → R → R⟦X⟧)
  (hS : ∀ p ∈ I, coeff R p.order.toNat p ∈ Ideal.span (S p.order.toNat))
  (hf : ∀ j : ℕ, ∀ a ∈ S j,
    (f j a).order = j ∧ coeff R j (f j a) = a ∧ f j a ∈ I) :
  letI := Classical.decEq R⟦X⟧
  ∀ p ∈ I, ∃ q ∈ I, p.trunc (k+1) = q.trunc (k+1) ∧
    q ∈ Ideal.span (Finset.biUnion (Finset.range (k+1))
      (fun i => Finset.image (f i) (S i) ) ) := by
  induction' k with k ih
  · intro p p_mem
    by_cases hp : 0 < p.order
    · use 0
      suffices coeff R 0 p = 0 by
        simp [this]
      apply coeff_of_lt_order _ (by simp [hp])
    simp only [not_lt, nonpos_iff_eq_zero] at hp
    specialize hS p p_mem
    simp only [hp, ENat.toNat_zero] at hS
    have := exists_coeff_order_eq_mem_span_image_of_coeff_mem_span hp hS (hf 0)
    simp only [zero_add, trunc_one_left, Polynomial.C_inj,
      Finset.range_one, Finset.singleton_biUnion, Finset.coe_image]
    rcases this with ⟨q, hq1, _, hq2, hq3⟩
    use q, hq3, hq2.symm, hq1
  · intro p p_mem
    rcases (ih p p_mem) with ⟨q, q_mem, q_trunc, hq⟩
    letI := Classical.decEq R⟦X⟧
    have h1: Finset.biUnion (Finset.range (k+1))
      (fun i => Finset.image (f i) (S i) ) ⊆
      Finset.biUnion (Finset.range (k+1+1))
        (fun i => Finset.image (f i) (S i) ) := by
      simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_range]
      intro j hj
      apply Finset.subset_biUnion_of_mem (fun i => Finset.image (f i) (S i))
      simp only [Finset.mem_range]
      exact hj.trans (lt_add_one (k + 1))
    by_cases hpq : (p - q).order > k + 1
    · use q, q_mem
      constructor
      · rw [← sub_eq_zero, ← trunc_sub]
        replace hpq: k+1+1 ≤ (p-q).order := by
          exact Order.add_one_le_of_lt hpq
        apply trunc_eq_zero_of_le_order ?_
        simp [hpq]
      · exact (Ideal.span_mono h1) hq
    replace hpq : (p-q).order = ↑(k + 1) := by
      push_neg at hpq
      refine le_antisymm hpq ?_
      contrapose! q_trunc
      rw [ne_eq, ← sub_eq_zero, ← trunc_sub]
      apply trunc_ne_zero_of_order_lt q_trunc
    specialize hS (p-q) (I.sub_mem p_mem q_mem)
    specialize hf (k+1)
    have: (p-q).order.toNat = k + 1 := by simp [hpq]
    rw [this] at hS
    replace := exists_coeff_order_eq_mem_span_image_of_coeff_mem_span hpq hS hf
    rcases this with ⟨q', hq', q_order', q_coeff', q_mem'⟩
    use q + q', (I.add_mem q_mem q_mem')
    constructor
    · simp only [trunc_succ _ (k+1), trunc_add]
      rw [trunc_eq_zero_of_le_order q_order'.symm.le]
      simp [q_trunc, q_coeff']
    · apply Ideal.add_mem _ ?_ ?_
      · apply (Ideal.span_mono h1) hq
      · refine (Ideal.span_mono ?_) hq'
        norm_cast
        refine Finset.subset_biUnion_of_mem (fun i ↦ Finset.image (f i) (S i)) ?_
        simp

end Ideal





/- Hilbert basis theorem for power series:
a power series ring over a Noetherian ring is Noetherian ring. -/
protected theorem isNoetherianRing' [inst : IsNoetherianRing R] :
  IsNoetherianRing R⟦X⟧ := by
  rw [isNoetherianRing_iff_ideal_fg]
  -- suppose we are given some arbitrary ideal I,
  -- we need prove I is finitely generated.
  intro I
  -- if R only contains 0, then obviously elements from I are all 0.
  by_cases inst': ¬Nontrivial R
  · use {0}
    simp only [Finset.coe_singleton]
    apply le_antisymm ?_ ?_
    · rw [← Ideal.span_eq I]
      apply Ideal.span_mono
      simp
    · intro p hp
      have: p = 0 := by
        ext i
        by_contra!
        absurd inst'
        use (coeff R i) p, 0, this
      simp [this]
  push_neg at inst'

  -- otherwise, consider coefficient of those power series from I with order ≥ k for some k.
  -- we claim such set is indeed an ideal of R, and it is monotone.
  -- since R is Noetherian ring, this ascending chain I0, I1, I2, ... must stop at some m.
  have := isNoetherianRing_iff.mp inst
  rw [← monotone_stabilizes_iff_noetherian] at this
  specialize this ⟨coeffOrderGE I, coeffOrderGE_mono I⟩
  rcases this with ⟨m, hm⟩
  simp only [OrderHom.coe_mk] at hm
  -- therefore I m can be seen as a maximal of this ideal chain.
  replace hm: ∀ k, coeffOrderGE I k ≤ coeffOrderGE I m := by
    intro k
    by_cases hk: k ≥ m
    · simp [hm k hk]
    · push_neg at hk
      apply coeffOrderGE_mono I hk.le

  -- R is Noetherian ring, I 0 to I m are ideals of R, so they are finitely generated.
  -- say, generated by S0, S1, ..., Sm.
  -- further more, we can take out 0.
  have: ∀ k : ℕ, ∃ S : Finset R, Ideal.span S = coeffOrderGE I k
    ∧ ∀a ∈ S, a ≠ 0 := by
    intro k
    rw [isNoetherianRing_iff_ideal_fg] at inst
    specialize inst (coeffOrderGE I k)
    rcases inst with ⟨S, hS⟩
    letI := Classical.decEq R
    use (S.erase 0)
    by_cases hh: 0 ∈ S
    · rw [← Finset.insert_erase hh] at hS
      push_cast at hS
      constructor
      · apply le_antisymm ?_ ?_
        · rw [← hS]
          apply Ideal.span_mono
          simp
        · intro p hp
          rw [← hS, Ideal.mem_span_insert] at hp
          simpa only [Finset.coe_erase, mul_zero, zero_add,
            exists_eq_right', exists_const] using hp
      · intro a
        simp only [Finset.mem_erase, ne_eq, and_imp]
        exact fun h _ => h
    · have: S.erase 0 = S := by simp [hh]
      simp [hS, hh]
  choose! S hS using this

  -- choose representative power series for each coefficient in the ideal.
  -- since elements from S k are non-zero for any k,
  -- they must correspond to some power series of order k.
  have: ∀ k : ℕ, ∀ a ∈ S k, ∃ f ∈ I,
    a = coeff R k f ∧ f.order = k  := by
    intro k a ha
    have : a ∈ Ideal.span (S k) := by
      rw [Ideal.mem_span]
      exact fun p a_1 ↦ a_1 ha
    rwa [(hS k).left, mem_coeffOrderGE_iff_exists] at this
    exact (hS k).right a ha
  choose! f hf using this

  -- then we claim f '' union S generate the whole ideal.
  letI := Classical.decEq R⟦X⟧
  let t : Finset R⟦X⟧ := (Finset.biUnion
    (Finset.range (m+1)) (fun i => Finset.image (f i) (S i)))
  use t
  suffices I ≤ Ideal.span t by
    refine le_antisymm ?_ this
    rw [← Ideal.span_eq I]
    apply Ideal.span_mono ?_
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_Iio,
      Finset.coe_image, Set.iUnion_subset_iff, Set.image_subset_iff, t]
    intro i hi
    intro a
    simp only [Finset.mem_coe, Set.mem_preimage, SetLike.mem_coe]
    intro ha
    exact (hf i a ha).left

  -- we need show given any p from I, it's member of span t.
  intro p' p_mem'
  -- split off first m terms, so that remaining part has order > m.
  obtain ⟨pp', pp_mem_ideal', pp_trunc', pp_mem_span'⟩:
    ∃ q ∈ I, p'.trunc (m+1) = q.trunc (m+1) ∧ q ∈ Ideal.span t := by
    dsimp [t]
    refine exists_trunc_eq_mem_span_biUnion_of_forall_coeff_mem_span
      m S f ?_ ?_ p' p_mem'
    · intro p p_mem
      by_cases hp : p = 0
      · simp [hp]
      rw [(hS _).left, mem_coeffOrderGE_iff_exists <| coeff_order <| hp]
      use p
      simp [p_mem, coe_toNat_order hp]
    · intro j a ha
      rcases (hf j a ha) with ⟨h1, h2, h3⟩
      use h3, h2.symm, h1
  suffices ∀ k : ℕ, ∀ p ∈ I, p.order = k + m →
    p ∈ Ideal.span (Finset.image (f m) (S m)) by
    by_cases h : p' - pp' = 0
    · rw [sub_eq_zero] at h
      rwa [h]
    · have h1 : ↑(m + 1 : ℕ) ≤ (p'-pp').order :=
        le_order_of_trunc_eq pp_trunc'
      rw [← coe_toNat_order h, Nat.cast_le] at h1
      specialize this ((p' - pp').order.toNat - m) (p' - pp')
        (I.sub_mem p_mem' pp_mem_ideal')
      rw [← coe_toNat_order h] at this
      change m < (p' - pp').order.toNat at h1
      norm_cast at this
      simp only [ENat.toNat_coe, h1.le, Nat.sub_add_cancel,
        Finset.coe_image, forall_const] at this
      rw [show p' = (p' - pp') + pp' by simp]
      refine Ideal.add_mem _ ?_ pp_mem_span'
      suffices h : (f m '' (S m)) ⊆ t by
        exact (Ideal.span_mono h) this
      dsimp [t]
      rw [← Finset.coe_image]
      exact Finset.subset_biUnion_of_mem
        (fun i => Finset.image (f i) (S i)) (by simp)
  suffices ∀ p ∈ I, p.order ≥ m →
    p ∈ Ideal.span (Finset.image (f m) (S m)) by
    intro k p hp p_order
    exact this p hp (by simp [p_order])
  clear pp_mem_span' pp_trunc' pp_mem_ideal' pp' p_mem' p' t

  -- S m is set of coefficients, denote them a0, a1, ..., a_{n-1}
  have : (S m).toSet.Finite := by simp
  rcases this.fin_embedding with ⟨n, a, ha⟩
  by_cases Snz: (S m) = ∅
  · intro p p_mem p_order
    by_cases hp : p = 0
    · simp [hp]
    have h1 : coeff R p.order.toNat p ∈
      coeffOrderGE I p.order.toNat := by
      rw [mem_coeffOrderGE_iff_exists (coeff_order hp)]
      use p, p_mem
      simp [coe_toNat_order hp]
    specialize hm p.order.toNat
    rw [← (hS m).left] at hm
    simp only [Snz, Finset.coe_empty,
      Ideal.span_empty, le_bot_iff] at hm
    simp only [hm, Ideal.mem_bot] at h1
    absurd h1
    exact coeff_order hp
  have hn : n ≥ 1 := by
    contrapose! Snz
    suffices (S m).toSet = ∅ by simpa only [Finset.coe_eq_empty]
    rw [← ha]
    have : n = 0 := Nat.lt_one_iff.mp Snz
    rw [Set.range_eq_empty_iff, this]
    exact Fin.isEmpty'
  rw [Finset.coe_image, ← ha]

  -- let g0, g1, ..., g_{n-1} be representative power series of a0, a1, ..., a_{n-1}
  set g : Fin n → R⟦X⟧ := fun i => f m (a i) with g_def
  have g_order : ∀ i, (g i).order = m := by
    intro i
    dsimp only [g]
    refine (hf m (a i) ?_).right.right
    suffices a i ∈ (S m).toSet by simpa only [Finset.mem_coe]
    simp [← ha]
  have : f m '' (Set.range a) = Set.range g := by
    ext i
    simp [g_def]
  intro p' p_mem' p_order'
  by_cases pnz' : p' = 0
  · simp [pnz']
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, p'.order = m' := by
    use p'.order.toNat
    exact (coe_toNat_order pnz').symm
  simp only [hm', ge_iff_le, Nat.cast_le] at p_order'
  rw [this, Ideal.mem_span_range_iff_exists_fun]

  -- let c denote the linear combination, such that sum c_i g_i
  -- has the same leading coefficient as we give.
  have : ∀ aa ∈ Ideal.span (S m), ∃ c : Fin n → R,
    (coeff R m (∑ i : Fin n, (C R (c i)) * g i) = aa ∧ (aa = 0 → c = 0)) := by
    intro aa haa
    rw [← ha, Ideal.mem_span_range_iff_exists_fun] at haa
    rcases haa with ⟨c, hc⟩
    by_cases haa : aa = 0
    · use 0
      simp [haa]
    use c
    simp only [map_sum, coeff_C_mul, haa, IsEmpty.forall_iff, and_true, g_def]
    rw [← hc]
    apply Finset.sum_congr rfl ?_
    intro i _
    have : a i ∈ S m := by
      suffices a i ∈ (S m).toSet by simpa only [Finset.mem_coe]
      simp only [← ha, Set.mem_range,
        EmbeddingLike.apply_eq_iff_eq, exists_eq]
    rw [← (hf m (a i) this).right.left]
  choose! c hc c_zero using this
  replace c_zero : c 0 = 0 := by simp [c_zero]
  -- getC picks the leading coefficient of a power series.
  let getC : R⟦X⟧ → R := fun p => coeff R p.order.toNat p
  have getC_def (p : R⟦X⟧) : getC p = coeff R p.order.toNat p := rfl
  have getC_zero : getC 0 = 0 := by simp [getC_def]
  have getC_mem : ∀ p ∈ I, p.order ≥ m → getC p ∈ Ideal.span (S m) := by
    intro p hp1 hp2
    rw [getC_def]
    by_cases hp3 : p = 0
    · simp [hp3]
    · rw [(hS m).left]
      refine (hm p.order.toNat) ?_
      rw [mem_coeffOrderGE_iff_exists (coeff_order hp3)]
      use p, hp1
      simp [coe_toNat_order hp3]
  have c_order : ∀ p ∈ I, p.order ≥ m → p ≠ 0 →
    (∑ i, (C R (c (getC p) i)) * g i).order = m := by
    intro p hp1 hp2 hp3
    refine order_C_mul_finsum ?_ g_order hn
    rw [hc (getC p) (getC_mem p hp1 hp2)]
    exact coeff_order hp3
  -- define q, such that q(p) has same leading coefficient as p and has order m'.
  let q : R⟦X⟧ → R⟦X⟧ := fun p =>
    X ^ (m' - m) * (∑ i : Fin n, (C R (c (getC p) i)) * g i)
  have q_def (p : R⟦X⟧) : q p = X ^ (m' - m) * (∑ i : Fin n, (C R (c (getC p) i)) * g i) := rfl
  have q_mem_ideal : ∀ p ∈ I, q p ∈ I := by
    intro p hp
    rw [q_def p]
    refine I.mul_mem_left (X^(m'-m)) ?_
    have h1 : ∑ i, (C R (c (getC p) i) * g i) ∈ Ideal.span (Set.range g) := by
      rw [Ideal.mem_span_range_iff_exists_fun]
      use fun i => C R (c (getC p) i)
    have h2 : Ideal.span (Set.range g) ≤ I := by
      rw [← Ideal.span_eq I]
      refine Ideal.span_mono ?_
      intro _
      rw [← this]
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and,
        SetLike.mem_coe, forall_exists_index]
      rintro i rfl
      refine (hf m (a i) ?_).left
      suffices a i ∈ (S m).toSet by simpa only [Finset.mem_coe]
      simp [← ha]
    exact h2 h1
  have q_zero : q 0 = 0 := by simp [q, getC_zero, c_zero]
  have q_order : ∀ p ∈ I, p.order ≥ ↑m → p ≠ 0 → (q p).order = m' := by
    intro p hp1 hp2 hp3
    rw [q_def, order_X_pow_mul, c_order p hp1 hp2 hp3]
    norm_cast
    simp [p_order']
  -- q p has same leading coefficient as p.
  have getC_q: ∀ p ∈ I, p.order ≥ m → getC (q p) = getC p := by
    intro p hp1 hp2
    by_cases hp3 : p = 0
    · simp [hp3, q_zero]
    nth_rw 1 [getC_def, q_order p hp1 hp2 hp3]
    simp only [ENat.toNat_coe, q_def]
    have : m' = m + (m' - m) := by simp [p_order']
    nth_rw 1 [this, coeff_X_pow_mul, hc (getC p) (getC_mem p hp1 hp2)]
  have getC_X_pow_mul : ∀ p ∈ I, p.order ≥ m → ∀ j : ℕ,
    getC (X^j * p) = getC p := by
    intro p hp1 hp2 j
    by_cases hp3 : p = 0
    · simp [hp3]
    rw [getC_def, getC_def, order_X_pow_mul, ← coe_toNat_order hp3]
    norm_cast
    simp only [ENat.toNat_coe]
    rw [add_comm j _, coeff_X_pow_mul]
  have q_q : ∀ p ∈ I, p.order ≥ m → q (q p) = q p := by
    intro p hp1 hp2
    nth_rw 1 [q_def]
    nth_rw 2 [q_def]
    simp [getC_q p hp1 hp2]
  have q_X_pow_mul : ∀ p ∈ I, p.order ≥ m → ∀ j : ℕ,
    q (X^j * p) = q p := by
    intro p hp1 hp2 j
    simp [q_def, getC_X_pow_mul p hp1 hp2]
  have hq : ∀ p ∈ I, ∀ k : ℕ, p.order = m' + k →
    trunc (m' + k + 1) (X^k * q p) = trunc (m' + k + 1) p := by
    intro p hp1 k hp2
    have hp3 : p ≠ 0 := by
      contrapose! hp2
      simp only [hp2, order_zero, ne_eq]
      norm_cast
      exact ENat.top_ne_coe (m' + k)
    have h1 : (X^k * q p).order = ↑(m' + k) := by
      rw [order_X_pow_mul, q_order p hp1 ?_ hp3]
      · simp [add_comm]
      · rw [hp2]
        norm_cast
        exact p_order'.trans (by simp)
    norm_cast at hp2
    rw [trunc_order_succ h1, trunc_order_succ hp2]
    congr 1
    simp only [coeff_X_pow_mul, q_def]
    have h2 : m' = m + (m' - m) := by simp [p_order']
    nth_rw 1 [h2, coeff_X_pow_mul]
    rw [hc (getC p) (getC_mem p hp1 ?_)]
    · rw [getC_def]
      congr 2
      rw [hp2]
      norm_cast
    · rw [hp2]
      norm_cast
      exact p_order'.trans (by simp)


  -- q gives a "canonical representation" of p ∈ I.
  -- build a sequence approximate p using q.
  let p_cal_aux : ℕ → (R ⟦X⟧ × R ⟦X⟧) := fun i =>
    Nat.recOn i ⟨(q p'), 0⟩
      (fun i pi => ⟨if (p' - pi.2 - pi.1).order = m'+i+1 then X^(i+1) * q (p' - pi.2 - pi.1) else 0,
        pi.1 + pi.2⟩)
  have p_cal_aux_1_succ (n : ℕ) : (p_cal_aux (n+1)).1 =
    if (p' - (p_cal_aux n).2 - (p_cal_aux n).1).order = m'+n+1
      then X^(n+1) * q (p' - (p_cal_aux n).2 - (p_cal_aux n).1) else 0 := rfl
  have p_cal_aux2_succ (n : ℕ) :
    (p_cal_aux (n+1)).2 = (p_cal_aux n).1 + (p_cal_aux n).2 := rfl
  let p_cal : ℕ → R ⟦X⟧ := fun i => (p_cal_aux i).1
  have p_cal_zero : p_cal 0 = q p' := rfl
  have p_cal_2 (n : ℕ) : (p_cal_aux (n+1)).2 = ∑ i ∈ Finset.range (n+1), p_cal i := by
    induction' n with n ih
    · simp [p_cal_zero, p_cal_aux]
    · rw [p_cal_aux2_succ (n+1), ih]
      simp only [Finset.sum_range_succ _ (n + 1), p_cal]
      rw [add_comm]
  have p_cal_succ (n : ℕ) : p_cal (n+1) =
    if (p' - ∑ i ∈ Finset.range (n+1), p_cal i).order = m' + n + 1 then
    X ^ (n + 1) * q (p' - ∑ i ∈ Finset.range (n+1), p_cal i) else 0 := by
    dsimp only [p_cal]
    rw [← p_cal_2, p_cal_aux_1_succ n, p_cal_aux2_succ n]
    rw [add_comm (p_cal_aux n).1 _, sub_sub]
  have p_cal_mem_ideal : ∀ nn : ℕ,
    ∑ i ∈ Finset.range (nn+1), p_cal i ∈ I := by
    intro nn
    induction' nn with nn ih
    · simp [p_cal_zero, q_mem_ideal p' p_mem']
    · rw [Finset.sum_range_succ]
      refine I.add_mem ih ?_
      rw [p_cal_succ]
      by_cases hh : (p' - ∑ i ∈ Finset.range (nn + 1), p_cal i).order = ↑m' + ↑nn + 1
      · rw [if_pos hh]
        refine I.mul_mem_left (X^(nn+1)) ?_
        refine q_mem_ideal _ ?_
        exact I.sub_mem p_mem' ih
      · simp [hh]
  have p_cal_sum : ∀ nn : ℕ,
    trunc (m' + nn + 1) (∑ i ∈ Finset.range (nn+1), p_cal i) =
    trunc (m' + nn + 1) p' := by
    intro nn
    induction' nn with nn ih
    · simp only [zero_add, Finset.range_one,
        Finset.sum_singleton, add_zero]
      rw [p_cal_zero]
      specialize hq p' p_mem' 0 (by simp [hm'])
      simp only [add_zero, pow_zero, one_mul] at hq
      exact hq
    · simp only [← add_assoc, Finset.sum_range_succ _ (nn+1), p_cal_succ]
      by_cases h : (p' - ∑ i ∈ Finset.range (nn+1), p_cal i).order = m' + nn + 1
      · rw [if_pos h]
        refine trunc_succ_eq_of_trunc_sub_eq ?_
        refine hq _ ?_ _ h
        refine I.sub_mem p_mem' ?_
        exact p_cal_mem_ideal nn
      · rw [if_neg h, add_zero]
        refine trunc_eq_trunc_of_lt_sub_order ?_
        norm_cast at h
        refine lt_of_le_of_ne ?_ ?_
        · apply le_order_of_trunc_eq ih
        · rw [order_sub_comm]
          symm
          exact h
  have q_p_cal {i : ℕ} : X^i * q (p_cal i) = p_cal i := by
    induction' i with i
    · simp only [pow_zero, p_cal_zero, one_mul]
      refine q_q p' p_mem' ?_
      simp [hm', p_order']
    · rw [p_cal_succ]
      by_cases hh : (p' - ∑ j ∈ Finset.range (i + 1), p_cal j).order = m' + i + 1
      · simp only [hh, ↓reduceIte]
        specialize p_cal_mem_ideal i
        have h1 : p' - ∑ j ∈ Finset.range (i + 1), p_cal j ∈ I :=
          I.sub_mem p_mem' p_cal_mem_ideal
        have h2 : p' - ∑ j ∈ Finset.range (i + 1), p_cal j ≠ 0 := by
          contrapose! hh
          rw [hh, order_zero]
          norm_cast
          exact ENat.top_ne_coe (m' + i + 1)
        have h3 : (p' - ∑ j ∈ Finset.range (i + 1), p_cal j).order ≥ m := by
          specialize p_cal_sum i
          have := le_order_of_trunc_eq p_cal_sum
          rw [order_sub_comm]
          refine le_trans ?_ this
          norm_cast
          exact p_order'.trans (by simp [add_assoc])
        specialize q_order _ h1 h3 h2
        have h1' := q_mem_ideal (p' - ∑ j ∈ Finset.range (i+1), p_cal j) h1
        rw [q_X_pow_mul _ h1' (by simp [q_order, p_order']), q_q _ h1 h3]
      · simp [hh, q_zero]

  use fun i' => (X^(m' - m) * mk (fun j => c (getC (p_cal j)) i'))
  rw [eq_iff_forall_trunc]
  intro i
  refine trunc_down m' ?_
  simp only [← add_assoc, ← p_cal_sum i]
  have h1 : ∑ j ∈ Finset.range (i+1), p_cal j =
    ∑ j ∈ Finset.range (i + 1), X^j * q (p_cal j) := by
    refine Finset.sum_congr rfl ?_
    simp [q_p_cal]
  have h2 : ∑ j ∈ Finset.range (i + 1), X^j * q (p_cal j) =
    ∑ i' : Fin n, (∑ j ∈ Finset.range (i + 1),
      X^j * (X ^ (m' - m) * ((C R) (c (getC (p_cal j)) i') * g i')) ):= by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [q_def, Finset.mul_sum]
  rw [h1, h2]
  simp only [trunc_finsum]
  refine Finset.sum_congr rfl ?_
  intro i' _
  have h3 : m' + i + 1 = (m' - m + i + 1) + m := by
    clear * - p_order'
    omega
  set ff : R⟦X⟧ := (X^(m' - m) * mk (fun j => c (getC (p_cal j)) i')) with ff_def
  have h4 : trunc (m' + i + 1) (ff * g i') = trunc (m' + i + 1)
    ( (trunc (m' - m + i + 1) ff) * g i' : R⟦X⟧) := by
    specialize g_order i'
    nth_rw 1 [h3, ← trunc_trunc_mul_of_order_eq g_order, ← h3]
  rw [h4]
  congr 1
  rw [ff_def, add_assoc _ i 1, trunc_X_pow_mul]
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  rw [cast_trunc_mk_eq_finset_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j' _
  simp only [← mul_assoc, ← pow_add, add_comm _ j']



end Ring

end PowerSeries


/- as an immediate corollary, we get Hibert basis theorem for Laurent series.  -/
example {R : Type*} [CommRing R] [inst : IsNoetherianRing R] :
  IsNoetherianRing (LaurentSeries R) := by
  have h1 := @LaurentSeries.of_powerSeries_localization R
  have h2 : IsNoetherianRing (PowerSeries R) := PowerSeries.isNoetherianRing'
  apply IsLocalization.isNoetherianRing (Submonoid.powers PowerSeries.X)
    (LaurentSeries R) h2
