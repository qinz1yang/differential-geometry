import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.SecondOrderTimeDerivatives
import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_time_weak_derivative_trees_of_homogeneous_weighted_divergence_equation
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hIcc : Icc a b ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m k : ℕ)
    (ρ : ℝ × E → ℝ) (A : Fin d → Fin d → ℝ × E → ℝ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (I ×ˢ O))
    (hρne : ∀ q ∈ I ×ˢ O, ρ q ≠ 0)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (I ×ˢ O))
    (V Z : ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hV : ∀ n, n < m + 2 * (k + 1) → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => V (n + 1) (Fin.cons i α) (t, x)) (fun x => V n α (t, x)) Ω)
    (hZ : ∀ n, n < m + 2 * k → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => Z (n + 1) (Fin.cons i α) (t, x)) (fun x => Z n α (t, x)) Ω)
    (htime : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, V 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, Z 0 (fun i => Fin.elim0 i) q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω))
    (hroot :
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      Z 0 e =ᵐ[(volume.restrict (Icc a b)).prod (volume.restrict Ω)] fun q => (ρ q)⁻¹ *
        ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
          fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
            V 1 (Fin.cons i e) q)) - fderiv ℝ ρ q (1, 0) * V 0 e q)) :
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
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  let A₀ := fun i j (q : ℝ × E) => (ρ q)⁻¹ * A i j q
  let B₀ := fun i (q : ℝ × E) => ∑ j, (ρ q)⁻¹ *
    fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1)
  let C₀ := fun q : ℝ × E => -((ρ q)⁻¹ * fderiv ℝ ρ q (1, 0))
  classical
  have hρinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => (ρ q)⁻¹) (I ×ˢ O) := hρ.inv hρne
  have hA₀ (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A₀ i j) (I ×ˢ O) := hρinv.mul (hA i j)
  have hB₀ (i) : ContDiffOn ℝ (⊤ : ℕ∞) (B₀ i) (I ×ˢ O) := by
    apply ContDiffOn.sum
    intro j _
    exact hρinv.mul ((DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t x => A i j (t, x)) hI.uniqueDiffOn hO (hA i j)).clm_apply
        contDiffOn_const)
  have hC₀ : ContDiffOn ℝ (⊤ : ℕ∞) C₀ (I ×ˢ O) :=
    (hρinv.mul ((hρ.fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply
      contDiffOn_const)).neg
  have hRcoeff : Z 0 e =ᵐ[ν] fun q =>
      (∑ i, ∑ j, A₀ i j q * V 2 (Fin.cons j (Fin.cons i e)) q) +
        (∑ i, B₀ i q * V 1 (Fin.cons i e) q) + C₀ q * V 0 e q := by
    filter_upwards [hroot] with q hq
    rw [hq]
    simp only [A₀, B₀, C₀, mul_sub, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    ring
  exact exists_lp_time_weak_derivative_trees_of_second_order_equation hp hI hIcc
    hO hΩ hΩc hΩO m k A₀ B₀ C₀ hA₀ hB₀ hC₀ V Z hV hZ htime hRcoeff

end DifferentialGeometry.Analysis.Sobolev.Euclidean
