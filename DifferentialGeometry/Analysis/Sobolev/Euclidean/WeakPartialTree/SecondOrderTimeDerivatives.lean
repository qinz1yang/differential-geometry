import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.FiniteSourceTimeDerivatives
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_time_weak_derivative_tree_of_finite_second_order_sum
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hIcc : Icc a b ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m k : ℕ)
    (l : ι → Fin k)
    (A : ι → Fin d → Fin d → ℝ × E → ℝ)
    (B : ι → Fin d → ℝ × E → ℝ) (C : ι → ℝ × E → ℝ)
    (hA : ∀ j i r, ContDiffOn ℝ (⊤ : ℕ∞) (A j i r) (I ×ˢ O))
    (hB : ∀ j i, ContDiffOn ℝ (⊤ : ℕ∞) (B j i) (I ×ˢ O))
    (hC : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (C j) (I ×ˢ O))
    (X : Fin (k + 1) → ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hX : ∀ j n, n < m + 2 → ∀ α i,
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => X j (n + 1) (Fin.cons i α) (t, x)) (fun x => X j n α (t, x)) Ω)
    (htime : ∀ j : Fin k, ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, X j.castSucc 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, X j.succ 0 (fun i => Fin.elim0 i) q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hroot :
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      X (Fin.last k) 0 e =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] fun q =>
        ∑ j, ((∑ i, ∑ r, A j i r q * X (l j).castSucc 2 (Fin.cons r (Fin.cons i e)) q) +
          (∑ i, B j i q * X (l j).castSucc 1 (Fin.cons i e) q) + C j q * X (l j).castSucc 0 e q)) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    let e : Fin 0 → Fin d := fun i => Fin.elim0 i
    ∃ W : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν,
      (W 0 e =ᵐ[ν] fun q => ∑ j,
        ((∑ i, ∑ r, (A j i r q * X (l j).succ 2 (Fin.cons r (Fin.cons i e)) q +
          fderiv ℝ (A j i r) q (1, 0) * X (l j).castSucc 2 (Fin.cons r (Fin.cons i e)) q)) +
        (∑ i, (B j i q * X (l j).succ 1 (Fin.cons i e) q +
          fderiv ℝ (B j i) q (1, 0) * X (l j).castSucc 1 (Fin.cons i e) q)) +
        (C j q * X (l j).succ 0 e q + fderiv ℝ (C j) q (1, 0) * X (l j).castSucc 0 e q))) ∧
      (∀ n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => W (n + 1) (Fin.cons i α) (t, x)) (fun x => W n α (t, x)) Ω) ∧
      ∀ n, n ≤ m → ∀ α (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, X (Fin.last k) n α q * fderiv ℝ φ q (1, 0) ∂ν) =
          -∫ q, W n α q * φ q ∂ν := by
  intro ν e
  classical
  have hXbounded (j : Fin (k + 1)) (n : ℕ) (hn : n < m + 2) :
      ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => X j (n + 1) (Fin.cons i α) (t, x)) (fun x => X j n α (t, x)) Ω :=
    hX j n hn
  have htimeAll (j : Fin k) :=
    integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
      (Z := ℝ) (μ := volume.restrict (Icc a b)) (W := Ioo a b) (m + 2) (1 : ℝ)
      (fun n α q => X j.castSucc n α q) (fun n α q => X j.succ n α q)
      (fun n _ α => (Lp.memLp (X j.castSucc n α)).locallyIntegrable hp)
      (fun n _ α => (Lp.memLp (X j.succ n α)).locallyIntegrable hp)
      (hXbounded j.castSucc) (hXbounded j.succ) (htime j)
  let σ := (Fin d × Fin d) ⊕ (Fin d ⊕ Unit)
  let Y : ι × σ → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν := fun j =>
    Sum.elim (fun ir n α => X (l j.1).castSucc (n + 2) (Fin.snoc (Fin.snoc α ir.2) ir.1))
      (Sum.elim (fun i n α => X (l j.1).castSucc (n + 1) (Fin.snoc α i))
        (fun _ => X (l j.1).castSucc)) j.2
  let Z : ι × σ → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν := fun j =>
    Sum.elim (fun ir n α => X (l j.1).succ (n + 2) (Fin.snoc (Fin.snoc α ir.2) ir.1))
      (Sum.elim (fun i n α => X (l j.1).succ (n + 1) (Fin.snoc α i))
        (fun _ => X (l j.1).succ)) j.2
  let D : ι × σ → ℝ × E → ℝ := fun j =>
    Sum.elim (fun ir => A j.1 ir.1 ir.2) (Sum.elim (B j.1) (fun _ => C j.1)) j.2
  have hD (j : ι × σ) : ContDiffOn ℝ (⊤ : ℕ∞) (D j) (I ×ˢ O) := by
    rcases j with ⟨j, ⟨i, r⟩ | (i | _)⟩
    · exact hA j i r
    · exact hB j i
    · exact hC j
  have hY (j : ι × σ) (n : ℕ) (hn : n < m) (α : Fin n → Fin d) (i : Fin d) :
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x)) (fun x => Y j n α (t, x)) Ω := by
    rcases j with ⟨j, ⟨r, s⟩ | (r | _)⟩
    · simpa only [Y, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hXbounded (l j).castSucc (n + 2) (by omega) (Fin.snoc (Fin.snoc α s) r) i
    · simpa only [Y, Sum.elim_inr, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hXbounded (l j).castSucc (n + 1) (by omega) (Fin.snoc α r) i
    · exact hXbounded (l j).castSucc n (by omega) α i
  have hZ (j : ι × σ) (n : ℕ) (hn : n < m) (α : Fin n → Fin d) (i : Fin d) :
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => Z j (n + 1) (Fin.cons i α) (t, x)) (fun x => Z j n α (t, x)) Ω := by
    rcases j with ⟨j, ⟨r, s⟩ | (r | _)⟩
    · simpa only [Z, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hXbounded (l j).succ (n + 2) (by omega) (Fin.snoc (Fin.snoc α s) r) i
    · simpa only [Z, Sum.elim_inr, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hXbounded (l j).succ (n + 1) (by omega) (Fin.snoc α r) i
    · exact hXbounded (l j).succ n (by omega) α i
  have hYZtime (j : ι × σ) (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
      (∫ q, Y j 0 e q * fderiv ℝ φ q (1, 0) ∂ν) = -∫ q, Z j 0 e q * φ q ∂ν := by
    rcases j with ⟨j, ⟨i, r⟩ | (i | _)⟩
    · exact htimeAll (l j) 2 (by omega) (Fin.snoc (Fin.snoc e r) i) φ hφ hφc hφs
    · exact htimeAll (l j) 1 (by omega) (Fin.snoc e i) φ hφ hφc hφs
    · exact htime (l j) φ hφ hφc hφs
  have hsingle (i : Fin d) : Fin.snoc e i = (Fin.cons i e : Fin 1 → Fin d) := by
    funext j
    refine Fin.cases ?_ (fun r => Fin.elim0 r) j
    rfl
  have hdouble (i r : Fin d) :
      Fin.snoc (Fin.cons r e) i = (Fin.cons r (Fin.cons i e) : Fin 2 → Fin d) := by
    rw [← Fin.cons_snoc_eq_snoc_cons, hsingle]
  have hsum : X (Fin.last k) 0 e =ᵐ[ν] fun q => ∑ j, D j q * Y j 0 e q := by
    filter_upwards [hroot] with q hq
    rw [hq]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    change _ = ∑ s : (Fin d × Fin d) ⊕ (Fin d ⊕ Unit), D (j, s) q * Y (j, s) 0 e q
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [D, Y, Fintype.sum_prod_type, Fintype.sum_unique, Sum.elim_inl,
      Sum.elim_inr, hsingle, hdouble]
    ring
  obtain ⟨W, hW, hWweak, hWtime⟩ := exists_lp_time_weak_derivative_tree_of_smooth_finite_sum
    hp hI hIcc hO hΩ hΩc hΩO m (X (Fin.last k) 0 e) D Y Z hD hY hZ hYZtime hsum
  refine ⟨W, ?_, hWweak, ?_⟩
  · filter_upwards [hW] with q hq
    rw [hq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    change (∑ s : (Fin d × Fin d) ⊕ (Fin d ⊕ Unit),
      (D (j, s) q * Z (j, s) 0 e q + fderiv ℝ (D (j, s)) q (1, 0) * Y (j, s) 0 e q)) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [D, Y, Z, Fintype.sum_prod_type, Fintype.sum_unique, Sum.elim_inl,
      Sum.elim_inr, hsingle, hdouble]
    ring
  · exact integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
      (Z := ℝ) (μ := volume.restrict (Icc a b)) (W := Ioo a b) m (1 : ℝ)
      (fun n α q => X (Fin.last k) n α q) (fun n α q => W n α q)
      (fun n _ α => (Lp.memLp (X (Fin.last k) n α)).locallyIntegrable hp)
      (fun n _ α => (Lp.memLp (W n α)).locallyIntegrable hp)
      (fun n hn => hXbounded (Fin.last k) n (by omega)) hWweak hWtime


private theorem exists_lp_time_weak_derivative_trees_with_source
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hIcc : Icc a b ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m k : ℕ)
    (A : Fin d → Fin d → ℝ × E → ℝ) (B : Fin d → ℝ × E → ℝ) (C : ℝ × E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (I ×ˢ O))
    (hB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (B i) (I ×ˢ O))
    (hC : ContDiffOn ℝ (⊤ : ℕ∞) C (I ×ˢ O))
    (V Z : ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hV : ∀ n, n < m + 2 * (k + 1) → ∀ α i,
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => V (n + 1) (Fin.cons i α) (t, x)) (fun x => V n α (t, x)) Ω)
    (hZ : ∀ n, n < m + 2 * k → ∀ α i,
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => Z (n + 1) (Fin.cons i α) (t, x)) (fun x => Z n α (t, x)) Ω)
    (htime : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, V 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, Z 0 (fun i => Fin.elim0 i) q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hroot :
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      Z 0 e =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] fun q =>
        (∑ i, ∑ j, A i j q * V 2 (Fin.cons j (Fin.cons i e)) q) +
          (∑ i, B i q * V 1 (Fin.cons i e) q) + C q * V 0 e q) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    let e : Fin 0 → Fin d := fun i => Fin.elim0 i
    ∃ X : Fin (k + 2) → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν,
      X 0 = V ∧ X 1 = Z ∧
      (∀ j n, n < m + 2 * (k + 1 - j.val) → ∀ α i,
        ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
          (fun x => X j (n + 1) (Fin.cons i α) (t, x)) (fun x => X j n α (t, x)) Ω) ∧
      (∀ j : Fin (k + 1), ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, X j.castSucc 0 e q * fderiv ℝ φ q (1, 0) ∂ν) =
          -∫ q, X j.succ 0 e q * φ q ∂ν) ∧
      ∃ (ι : Type) (_ : Fintype ι) (l : ι → Fin (k + 1))
        (D : ι → Fin d → Fin d → ℝ × E → ℝ)
        (F : ι → Fin d → ℝ × E → ℝ) (H : ι → ℝ × E → ℝ),
        (∀ j i r, ContDiffOn ℝ (⊤ : ℕ∞) (D j i r) (I ×ˢ O)) ∧
        (∀ j i, ContDiffOn ℝ (⊤ : ℕ∞) (F j i) (I ×ˢ O)) ∧
        (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (H j) (I ×ˢ O)) ∧
        (X (Fin.last (k + 1)) 0 e =ᵐ[ν] fun q => ∑ j,
          ((∑ i, ∑ r, D j i r q * X (l j).castSucc 2 (Fin.cons r (Fin.cons i e)) q) +
          (∑ i, F j i q * X (l j).castSucc 1 (Fin.cons i e) q) +
            H j q * X (l j).castSucc 0 e q)) := by
  induction k generalizing m with
  | zero =>
      intro ν e
      let X : Fin 2 → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν :=
        Fin.cons V (Fin.cons Z (fun i => Fin.elim0 i))
      refine ⟨X, rfl, rfl, ?_, ?_, Unit, inferInstance, (fun _ => 0),
        (fun _ => A), (fun _ => B), (fun _ => C), (fun _ => hA),
        (fun _ => hB), (fun _ => hC), ?_⟩
      · intro j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => Fin.elim0 i) j) j
        · intro n hn
          exact hV n (by simpa using hn)
        · intro n hn
          exact hZ n (by simpa using hn)
      · intro j
        have hj : j = 0 := by apply Fin.ext; have := j.isLt; omega
        subst j
        exact htime
      · have hz : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
        have hl : Fin.last (0 + 1) = (1 : Fin 2) := Fin.ext rfl
        simpa only [Fintype.sum_unique, hz, hl, X, Fin.cons_zero, Fin.cons_one] using hroot
  | succ k ih =>
      intro ν e
      obtain ⟨X, hXzero, hXone, hXweak, hXtime, ι, hι, l, D, F, H, hD, hF, hH, hXsource⟩ :=
        ih (m + 2) (fun n hn => hV n (by omega)) (fun n hn => hZ n (by omega))
      let _ := hι
      have hXbudget (j : Fin (k + 2)) (n : ℕ) (hn : n < m + 2) :=
        hXweak j n (by omega)
      obtain ⟨W, hWsource, hWweak, hWtime⟩ :=
        exists_lp_time_weak_derivative_tree_of_finite_second_order_sum hp hI hIcc
          hO hΩ hΩc hΩO m (k + 1) l D F H hD hF hH X hXbudget hXtime hXsource
      let X' : Fin (k + 3) → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν := Fin.snoc X W
      let l' : ι ⊕ ι → Fin (k + 2) :=
        Sum.elim (fun j => (l j).succ) (fun j => (l j).castSucc)
      let D' : ι ⊕ ι → Fin d → Fin d → ℝ × E → ℝ :=
        Sum.elim D (fun j i r q => fderiv ℝ (D j i r) q (1, 0))
      let F' : ι ⊕ ι → Fin d → ℝ × E → ℝ :=
        Sum.elim F (fun j i q => fderiv ℝ (F j i) q (1, 0))
      let H' : ι ⊕ ι → ℝ × E → ℝ :=
        Sum.elim H (fun j q => fderiv ℝ (H j) q (1, 0))
      have hD' (j : ι ⊕ ι) (i r : Fin d) :
          ContDiffOn ℝ (⊤ : ℕ∞) (D' j i r) (I ×ˢ O) := by
        cases j with
        | inl j => exact hD j i r
        | inr j =>
            exact ((hD j i r).fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply contDiffOn_const
      have hF' (j : ι ⊕ ι) (i : Fin d) :
          ContDiffOn ℝ (⊤ : ℕ∞) (F' j i) (I ×ˢ O) := by
        cases j with
        | inl j => exact hF j i
        | inr j =>
            exact ((hF j i).fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply contDiffOn_const
      have hH' (j : ι ⊕ ι) : ContDiffOn ℝ (⊤ : ℕ∞) (H' j) (I ×ˢ O) := by
        cases j with
        | inl j => exact hH j
        | inr j => exact ((hH j).fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply contDiffOn_const
      refine ⟨X', ?_, ?_, ?_, ?_, ι ⊕ ι, inferInstance, l', D', F', H', hD', hF', hH', ?_⟩
      · have hz : (0 : Fin (k + 3)) = (0 : Fin (k + 2)).castSucc := Fin.ext rfl
        rw [hz]
        exact (Fin.snoc_castSucc ..).trans hXzero
      · have ho : (1 : Fin (k + 3)) = (1 : Fin (k + 2)).castSucc := Fin.ext rfl
        rw [ho]
        exact (Fin.snoc_castSucc ..).trans hXone
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro n hn
          simpa only [X', Fin.snoc_last] using hWweak n (by simpa using hn)
        · intro n hn
          simpa only [X', Fin.snoc_castSucc] using hXweak j n (by
            simp only [Fin.val_castSucc] at hn
            have := j.isLt
            omega)
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · have hs : (Fin.last (k + 1)).succ = Fin.last (k + 2) := Fin.ext rfl
          simpa only [X', hs, Fin.snoc_castSucc, Fin.snoc_last] using hWtime 0 (Nat.zero_le _) e
        · have hs : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
          simpa only [X', hs, Fin.snoc_castSucc] using hXtime j
      · filter_upwards [hWsource] with q hq
        simp only [X', Fin.snoc_last]
        rw [hq, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [l', D', F', H', Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc,
          Finset.sum_add_distrib]
        ring

theorem exists_lp_time_weak_derivative_trees_of_second_order_equation
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hIcc : Icc a b ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m k : ℕ)
    (A : Fin d → Fin d → ℝ × E → ℝ) (B : Fin d → ℝ × E → ℝ) (C : ℝ × E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (I ×ˢ O))
    (hB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (B i) (I ×ˢ O))
    (hC : ContDiffOn ℝ (⊤ : ℕ∞) C (I ×ˢ O))
    (V Z : ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hV : ∀ n, n < m + 2 * (k + 1) → ∀ α i,
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => V (n + 1) (Fin.cons i α) (t, x)) (fun x => V n α (t, x)) Ω)
    (hZ : ∀ n, n < m + 2 * k → ∀ α i,
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => Z (n + 1) (Fin.cons i α) (t, x)) (fun x => Z n α (t, x)) Ω)
    (htime : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, V 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, Z 0 (fun i => Fin.elim0 i) q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hroot :
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      Z 0 e =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] fun q =>
        (∑ i, ∑ j, A i j q * V 2 (Fin.cons j (Fin.cons i e)) q) +
          (∑ i, B i q * V 1 (Fin.cons i e) q) + C q * V 0 e q) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    ∃ X : Fin (k + 2) → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν,
      X 0 = V ∧ X 1 = Z ∧
      (∀ j n, n < m + 2 * (k + 1 - j.val) → ∀ α i,
        ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
          (fun x => X j (n + 1) (Fin.cons i α) (t, x)) (fun x => X j n α (t, x)) Ω) ∧
      ∀ j : Fin (k + 1), ∀ n, n ≤ m + 2 * (k - j.val) →
        ∀ α (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, X j.castSucc n α q * fderiv ℝ φ q (1, 0) ∂ν) =
          -∫ q, X j.succ n α q * φ q ∂ν := by
  intro ν
  obtain ⟨X, hXzero, hXone, hXweak, hXtime, _⟩ :=
    exists_lp_time_weak_derivative_trees_with_source hp hI hIcc hO hΩ hΩc hΩO m k
      A B C hA hB hC V Z hV hZ htime hroot
  refine ⟨X, hXzero, hXone, hXweak, ?_⟩
  intro j
  exact integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
    (Z := ℝ) (μ := volume.restrict (Icc a b)) (W := Ioo a b)
    (m + 2 * (k - j.val)) (1 : ℝ)
    (fun n α q => X j.castSucc n α q) (fun n α q => X j.succ n α q)
    (fun n _ α => (Lp.memLp (X j.castSucc n α)).locallyIntegrable hp)
    (fun n _ α => (Lp.memLp (X j.succ n α)).locallyIntegrable hp)
    (fun n hn => hXweak j.castSucc n (by
      simp only [Fin.val_castSucc]
      have := j.isLt
      omega))
    (fun n hn => hXweak j.succ n (by
      simp only [Fin.val_succ]
      have := j.isLt
      omega)) (hXtime j)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
