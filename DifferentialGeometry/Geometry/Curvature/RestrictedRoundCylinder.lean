import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.RoundCylinderPerturbation
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open Poincare.Geometry.Metric

namespace Poincare.Geometry.Curvature

theorem ricciSharp_restricted_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (x : U) (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    ricciSharp ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) x v =
      ((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ)) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = n + 1 from Fact.out]
    omega)
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ((𝓡 n).prod 𝓘(ℝ)) U.isOpen)
  have h := ricciSharp_restrictOpen (roundCylinderMetric (E := E) (n := n)) U x v
  rw [mfderiv_subtype_val] at h
  exact h.trans (ricciSharp_roundCylinder (E := E) (n := n) (x : Metric.sphere (0 : E) 1 × ℝ) v)

theorem ricciSharp_restricted_roundCylinder_difference_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U)
    (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    let gRef := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
    let d := ricciSharp g x v - ricciSharp gRef x v
    Real.sqrt (gRef.inner x d d) ≤ 1441 * ε * Real.sqrt (gRef.inner x v v) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
    norm_num)
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ((𝓡 2).prod 𝓘(ℝ)) U.isOpen)
  let gC := roundCylinderMetric (E := E) (n := 2)
  let gRef := gC.restrictOpen U
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have href (w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
      ricciSharp gRef x w = ricciSharp gC (x : Metric.sphere (0 : E) 1 × ℝ) w := by
    have hh := ricciSharp_restrictOpen gC U x w
    rw [mfderiv_subtype_val] at hh
    exact hh
  have hnorm : Real.sqrt (gRef.inner x (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
      (1 / 2 : ℝ) * Real.sqrt (gRef.inner x v v) := by
    have h := ricciSharp_roundCylinder_norm_le (E := E) (n := 2)
      (x : Metric.sphere (0 : E) 1 × ℝ) v
    norm_num only [Nat.cast_ofNat, sub_self, sub_zero, sub_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    change Real.sqrt (gC.inner (x : Metric.sphere (0 : E) 1 × ℝ)
      (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
      (1 / 2 : ℝ) * Real.sqrt (gC.inner (x : Metric.sphere (0 : E) 1 × ℝ) v v)
    rw [href]
    convert h using 1
  have h := ricciSharp_difference_bound_of_small_metric_derivatives g gRef x ε hε hsmall v
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  dsimp only at h ⊢
  rw [hdim] at h
  norm_num only [Nat.cast_ofNat] at h
  apply h.trans
  apply (div_le_iff₀ (show 0 < 1 - ε by linarith only [hε])).mpr
  change 720 * ε * Real.sqrt (gRef.inner x v v) +
    ε * Real.sqrt (gRef.inner x (ricciSharp gRef x v) (ricciSharp gRef x v)) ≤
      1441 * ε * Real.sqrt (gRef.inner x v v) * (1 - ε)
  have hb := mul_le_mul_of_nonneg_left hnorm hε0
  have hc := mul_le_mul_of_nonneg_left hε
    (show 0 ≤ 1441 * ε * Real.sqrt (gRef.inner x v v) by positivity)
  nlinarith only [hb, hc]

end Poincare.Geometry.Curvature
