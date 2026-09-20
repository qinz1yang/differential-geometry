import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.SmoothFiniteSource
import DifferentialGeometry.Analysis.Sobolev.WeakDerivative.FiniteSource

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_time_weak_derivative_tree_of_smooth_finite_sum
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hIcc : Icc a b ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m : ℕ)
    (f : Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (A : ι → ℝ × E → ℝ)
    (Y Z : ι → ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hA : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (A j) (I ×ˢ O))
    (hY : ∀ j n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Y j (n + 1) (Fin.cons i α) (t, x)) (fun x => Y j n α (t, x)) Ω)
    (hZ : ∀ j n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Z j (n + 1) (Fin.cons i α) (t, x)) (fun x => Z j n α (t, x)) Ω)
    (htime : ∀ j (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, Y j 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, Z j 0 (fun i => Fin.elim0 i) q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hf : f =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] fun q =>
      ∑ j, A j q * Y j 0 (fun i => Fin.elim0 i) q) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    ∃ W : ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν,
      (W 0 (fun i => Fin.elim0 i) =ᵐ[ν] fun q => ∑ j,
        (A j q * Z j 0 (fun i => Fin.elim0 i) q +
          fderiv ℝ (A j) q (1, 0) * Y j 0 (fun i => Fin.elim0 i) q)) ∧
      (∀ n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
        DeGiorgi.HasWeakPartialDeriv i
          (fun x => W (n + 1) (Fin.cons i α) (t, x)) (fun x => W n α (t, x)) Ω) ∧
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, f q * fderiv ℝ φ q (1, 0) ∂ν) =
          -∫ q, W 0 (fun i => Fin.elim0 i) q * φ q ∂ν := by
  intro ν
  classical
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  let DA := fun j (q : ℝ × E) => fderiv ℝ (A j) q (1, 0)
  have hDA (j) : ContDiffOn ℝ (⊤ : ℕ∞) (DA j) (I ×ˢ O) :=
    ((hA j).fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply contDiffOn_const
  have hlift (g : ℝ × E → ℝ) (hg : ContinuousOn g (I ×ˢ O)) : MemLp g ∞ ν := by
    have hm := (hg.mono (prod_mono hIcc hΩO)).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (prod_mono Subset.rfl subset_closure) (μ := (volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict] at hm
    exact hm
  obtain ⟨R, hR, hRtime⟩ := Sobolev.exists_lp_weak_deriv_of_ae_eq_finite_sum
    hp (isOpen_Ioo.prod hΩ) (1, 0) f (fun j => Y j 0 e) (fun j => Z j 0 e) A
    (fun j => hlift _ (hA j).continuousOn) (fun j => hlift _ (hDA j).continuousOn)
    (fun j => (hA j).mono (prod_mono (Ioo_subset_Icc_self.trans hIcc)
      (subset_closure.trans hΩO))) htime hf
  let B : ι ⊕ ι → ℝ × E → ℝ := Sum.elim A DA
  let V : ι ⊕ ι → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν := Sum.elim Z Y
  have hB (j : ι ⊕ ι) : ContDiffOn ℝ (⊤ : ℕ∞) (B j) (I ×ˢ O) := by
    cases j with
    | inl j => exact hA j
    | inr j => exact hDA j
  have hV (j : ι ⊕ ι) (n : ℕ) (hn : n < m) (α : Fin n → Fin d) (i : Fin d) :
      ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => V j (n + 1) (Fin.cons i α) (t, x)) (fun x => V j n α (t, x)) Ω := by
    cases j with
    | inl j => exact hZ j n hn α i
    | inr j => exact hY j n hn α i
  have hRsum : R =ᵐ[ν] fun q => ∑ j, B j q * V j 0 e q := by
    filter_upwards [hR] with q hq
    simpa only [B, V, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_add_distrib] using hq
  obtain ⟨W, hW, hWweak⟩ := exists_lp_weak_partial_tree_of_smooth_finite_sum
    hp hI.uniqueDiffOn isCompact_Icc hIcc hO hΩ hΩc hΩO m R B V hB hV hRsum
  refine ⟨W, ?_, hWweak, ?_⟩
  · simpa only [hW] using hR
  · simpa only [hW] using hRtime

end DifferentialGeometry.Analysis.Sobolev.Euclidean
