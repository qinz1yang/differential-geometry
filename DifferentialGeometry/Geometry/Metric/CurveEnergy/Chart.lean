import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import DifferentialGeometry.Geometry.Metric.ChartDistance.InverseMetric
import DifferentialGeometry.Geometry.Metric.LipschitzCurves

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lipschitzOnWith_comp_of_contMDiffOn_of_isCompact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : M → F} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f U)
    {X : Type*} [PseudoMetricSpace X] {γ : X → M} {K : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (K : ℝ≥0∞) * edist s t)
    {S : Set X} (hS : IsCompact S) (hγU : MapsTo γ S U) :
    ∃ L : ℝ≥0, LipschitzOnWith L (f ∘ γ) S := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
    ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
    ⟨(riemannianMetricVectorSpace F).inner,
      (riemannianMetricVectorSpace F).contMDiff.continuous, fun _ _ _ => rfl⟩
  have hγLip : LipschitzWith K γ := hγ
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  intro t ht
  have hft := (hf (γ t) (hγU ht)).contMDiffAt (hU.mem_nhds (hγU ht))
  obtain ⟨C, V, hV, hCV⟩ := hft.exists_lipschitzOnWith
  refine ⟨C * K, γ ⁻¹' V, nhdsWithin_le_nhds (hγLip.continuous.continuousAt hV), ?_⟩
  intro x hx y hy
  exact (hCV hx hy).trans ((mul_le_mul_right (hγLip x y) (C : ℝ≥0∞)).trans_eq (by
    rw [ENNReal.coe_mul, mul_assoc]))

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem mul_norm_deriv_symm_comp_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (ψ : OpenPartialHomeomorph V M)
    (hψ : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 ψ ψ.source)
    (hψsymm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) 1 ψ.symm ψ.target)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t)
    (ht : γ t ∈ ψ.target) {m : ℝ}
    (hbound : ∀ ξ : V, m * ‖ξ‖ ^ 2 ≤
      g.inner (ψ (ψ.symm (γ t)))
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (ψ.symm (γ t)) ξ)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ (ψ.symm (γ t)) ξ)) :
    m * ‖deriv ((ψ.symm : M → V) ∘ γ) t‖ ^ 2 ≤ (riemannianCurveSpeed g γ t) ^ 2 := by
  have hψmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, V) ψ.symm (γ t) :=
    (hψsymm.contMDiffAt (ψ.open_target.mem_nhds ht)).mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, V)) t hψmd hγ (1 : ℝ)
  have hcoordD : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) ((ψ.symm : M → V) ∘ γ) t (1 : ℝ) =
      deriv ((ψ.symm : M → V) ∘ γ) t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := (ψ.symm : M → V) ∘ γ) (x := t)
  have hder := hcoordD.symm.trans hchain
  have hmetric := mul_norm_mfderiv_symm_sq_le g ψ hψ hψsymm (ψ.map_target ht) hbound
  rw [ψ.right_inv ht] at hmetric
  have h := hmetric (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)
  have hspeed : (riemannianCurveSpeed g γ t) ^ 2 =
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) :=
    Real.sq_sqrt (metric_inner_self_nonneg g _ _)
  rw [hspeed]
  rw [hder]
  exact h

variable [FiniteDimensional ℝ E] [T3Space M]

theorem ae_mul_norm_deriv_symm_comp_sq_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (ψ : OpenPartialHomeomorph V M)
    (hψ : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 ψ ψ.source)
    (hψsymm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) 1 ψ.symm ψ.target)
    {S : Set V} (hS : S ⊆ ψ.source) {m : ℝ}
    (hbound : ∀ y ∈ S, ∀ ξ : V, m * ‖ξ‖ ^ 2 ≤
      g.inner (ψ y) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) ψ y ξ))
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {s : Set ℝ} (hs : MeasurableSet s) (himage : MapsTo γ s (ψ '' S)) :
    ∀ᵐ t ∂volume.restrict s,
      m * ‖deriv ((ψ.symm : M → V) ∘ γ) t‖ ^ 2 ≤ (riemannianCurveSpeed g γ t) ^ 2 := by
  filter_upwards [ae_restrict_mem hs,
    ae_restrict_of_ae (s := s) (ae_mdifferentiableAt_riemannian_curve g hγ)] with t ht hdt
  obtain ⟨y, hy, hyt⟩ := himage ht
  have htarget : γ t ∈ ψ.target := hyt ▸ ψ.map_source (hS hy)
  apply mul_norm_deriv_symm_comp_sq_le g ψ hψ hψsymm hdt htarget
  have hcoord : ψ.symm (γ t) = y := by rw [← hyt, ψ.left_inv (hS hy)]
  intro ξ
  convert hbound y hy ξ using 1
  rw [hcoord]

end DifferentialGeometry.Geometry

end

end
