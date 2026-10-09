import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import Mathlib.Analysis.Calculus.Deriv.Basic



noncomputable section

open Set Function Manifold DifferentialGeometry
open scoped Topology ContDiff Manifold ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem exists_compact_source_curve_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {r : V → M} {U S : Set V}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 r U)
    (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ≥0, ∀ (L : ℝ≥0) (v : ℝ → V), ContDiff ℝ 1 v → LipschitzWith L v →
      (∀ t, v t ∈ S) → ∀ x y,
        riemannianEDistOf g (r (v x)) (r (v y)) ≤ ((C * L : ℝ≥0) : ℝ≥0∞) * edist x y := by
  obtain ⟨C, hC⟩ := exists_compact_source_mfderiv_bound g hU hr hS hSU
  refine ⟨C, fun L v hv hLip hvS => ?_⟩
  have hrv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (r ∘ v) := by
    intro t
    exact ((hr _ (hSU (hvS t))).contMDiffAt (hU.mem_nhds (hSU (hvS t)))).comp t
      hv.contMDiff.contMDiffAt
  apply riemannian_curve_edist_le_of_speed_bound g hrv
  intro t
  have hD := mfderiv_comp t
    (((hr _ (hSU (hvS t))).contMDiffAt (hU.mem_nhds (hSU (hvS t)))).mdifferentiableAt one_ne_zero)
    (hv.contMDiff.mdifferentiableAt one_ne_zero)
  have hDv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ) = deriv v t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := v) (x := t)
  rw [hD]
  change Real.sqrt (g.inner (r (v t))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ)))
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ)))) ≤ _
  rw [hDv]
  exact (hC (v t) (hvS t) (deriv v t)).trans
    (mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hLip) C.coe_nonneg)

end DifferentialGeometry.Geometry
