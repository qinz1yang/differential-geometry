import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.FrozenReplacement

noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff InnerProductSpace

namespace DifferentialGeometry.Analysis

open DeGiorgi Laplacian.MetricExtension Sobolev.NirenbergEuclidean Parabolic.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The frozen harmonic replacement with a prescribed constant coefficient.
The replacement, its trace and its smooth representative are those supplied by
`exists_frozen_harmonic_replacement_with_gradient_comparison`; the comparison
uses the actual lower ellipticity constant of the caller's coefficient `B`. -/
theorem exists_prescribed_frozen_harmonic_replacement_with_gradient_comparison
    (hd : 2 ≤ d) {c : E} {R : ℝ}
    (A B : EllipticCoeff d (Metric.ball c R)) (hAc : (A.a c).PosDef)
    (hB : B.a = (fun _ => A.a c))
    {u : E → ℝ} (hu : IsHomogeneousWeakSolution A u)
    (wu : MemW1pWitness 2 u (Metric.ball c R))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ᵐ x ∂volume.restrict (Metric.ball c R), ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (A.a c) ξ‖ ≤ ε * ‖ξ‖) :
    ∃ (h : E → ℝ) (wh : MemW1pWitness 2 h (Metric.ball c R)) (v : E → ℝ),
      IsHomogeneousWeakSolution B h ∧
      MemW01p 2 (fun x => h x - u x) (Metric.ball c R) ∧
      (∫ x, ‖wh.weakGrad x - wu.weakGrad x‖ ^ (2 : ℝ)
        ∂volume.restrict (Metric.ball c R)) ^ (1 / (2 : ℝ)) ≤
        (ε / B.lam) * (∫ x, ‖wu.weakGrad x‖ ^ (2 : ℝ)
          ∂volume.restrict (Metric.ball c R)) ^ (1 / (2 : ℝ)) ∧
      ContDiffOn ℝ ∞ v (Metric.ball c R) ∧
      h =ᵐ[volume.restrict (Metric.ball c R)] v ∧
      wh.weakGrad =ᵐ[volume.restrict (Metric.ball c R)] smoothGradField v ∧
      HasWeakDiv 0 (fun x => matMulE (A.a c) (smoothGradField v x))
        (Metric.ball c R) ∧
      HarmonicOnNhd (v ∘ spdSqrtEquiv (A.a c) hAc)
        (spdSqrtEquiv (A.a c) hAc ⁻¹' Metric.ball c R) := by
  obtain ⟨B₀, h, wh, v, hB₀, hh₀, htrace, _, hv, hhv, hgrad, hdiv, hharm⟩ :=
    exists_frozen_harmonic_replacement_with_gradient_comparison hd A hAc hu wu hε hosc
  have hcoeff : B.a = B₀.a := hB.trans hB₀.symm
  have hh : IsHomogeneousWeakSolution B h := by
    refine ⟨hh₀.1, ?_⟩
    intro wh' φ hφ wφ
    simpa only [bilinFormOfCoeff, bilinFormIntegrandOfCoeff, hcoeff] using
      hh₀.2 wh' φ hφ wφ
  have hoscB : ∀ᵐ x ∂volume.restrict (Metric.ball c R), ∀ ξ : E,
      ‖matMulE (A.a x) ξ - matMulE (B.a x) ξ‖ ≤ ε * ‖ξ‖ := by
    simpa only [hB] using hosc
  have hcompare := weakGrad_l2_sub_le_of_coefficient_oscillation
    Metric.isOpen_ball A B hu hh htrace wu wh hε hoscB
  exact ⟨h, wh, v, hh, htrace, hcompare, hv, hhv, hgrad, hdiv, hharm⟩

end DifferentialGeometry.Analysis
