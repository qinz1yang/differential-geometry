import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Mathlib.Analysis.Calculus.Deriv.AffineMap



noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

set_option backward.isDefEq.respectTransparency false in


theorem riemannian_edist_le_on_convex_source
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : V → M} {U S : Set V} {C : ℝ≥0}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U)
    (hSU : S ⊆ U) (hS : Convex ℝ S)
    (hC : ∀ p ∈ S, ∀ v : V,
      Real.sqrt (g.inner (f p) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p v)) ≤ C * ‖v‖)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    riemannianEDistOf g (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 η := η.contDiff.contMDiff
  have hηS : MapsTo η (Icc (0 : ℝ) 1) S := hS.mapsTo_lineMap hx hy
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (f ∘ η) (Icc 0 1) :=
    hf.comp hη.contMDiffOn (fun t ht => hSU (hηS ht))
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      riemannianCurveSpeed g (f ∘ η) t ≤ (C * ‖y - x‖₊ : ℝ≥0) := by
    intro t ht
    have hdf := ((hf _ (hSU (hηS ht))).contMDiffAt
      (hU.mem_nhds (hSU (hηS ht)))).mdifferentiableAt one_ne_zero
    have hder : HasDerivAt η (y - x) t := AffineMap.hasDerivAt_lineMap
    rw [riemannianCurveSpeed_comp g hdf hder.differentiableAt, hder.deriv]
    exact hC _ (hηS ht) _
  have hlen := riemannianCurveELength_le g hspeed
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hd : riemannianEDistOf g (f x) (f y) ≤ riemannianCurveELength g (f ∘ η) 0 1 := by
    rw [riemannianCurveELength_eq_pathELength]
    apply riemannianEDist_le_pathELength hγ _ _ zero_le_one
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero]
    · simp only [Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_one]
  apply hd.trans
  simpa only [sub_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_mul,
    ← edist_nndist, ← nndist_eq_nnnorm_sub, edist_comm] using hlen

end DifferentialGeometry.Geometry
