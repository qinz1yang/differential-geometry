import DifferentialGeometry.Geometry.Comparison.Variation.ArcLength
import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Analysis.Integration.Measure.CompactParametricIntegral

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuousOn_arcLength_of_continuous_tangentLift
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {K : Set P} (hK : IsCompact K) {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    (τ : P → ℝ) (hτ : ContinuousOn τ K) (hτJ : Set.MapsTo τ K J)
    (γ : P → ℝ → M)
    (hγ : ContinuousOn (fun p : P × ℝ =>
      (⟨γ p.1 p.2, mfderiv 𝓘(ℝ, ℝ) I (γ p.1) p.2 (1 : ℝ)⟩ : TangentBundle I M))
      (K ×ˢ Icc a b)) :
    ContinuousOn (fun p => arcLength (I := I) (g (τ p)) (γ p) a b) K := by
  apply DifferentialGeometry.Integral.Measure.continuousOn_intervalIntegral_of_continuousOn_compact hK hab
  apply Real.continuous_sqrt.comp_continuousOn
  rw [continuousOn_iff_continuous_domRestrict]
  let Q := ↥(K ×ˢ Icc a b)
  have hparam : Continuous (fun q : Q => q.val.1) := continuous_fst.comp continuous_subtype_val
  have htime : Continuous (fun q : Q => τ q.val.1) :=
    hτ.comp_continuous hparam (fun q => q.property.1)
  have hv : Continuous (fun q : Q =>
      (⟨γ q.val.1 q.val.2, mfderiv 𝓘(ℝ, ℝ) I (γ q.val.1) q.val.2 (1 : ℝ)⟩ : TangentBundle I M)) :=
    hγ.comp_continuous continuous_subtype_val (fun q => q.property)
  have hb : Continuous (fun q : Q => γ q.val.1 q.val.2) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp hv
  have heval := hg.eval_continuous (P := Q) (τ := fun q => τ q.val.1)
    (b := fun q => γ q.val.1 q.val.2) htime (fun q => hτJ q.property.1) hb
    (v := fun _i q => mfderiv 𝓘(ℝ, ℝ) I (γ q.val.1) q.val.2 (1 : ℝ))
    (fun _i => hv)
  exact heval.congr (fun q => by rw [Tensor0SBundle.metricTensorField_apply]; rfl)

end DifferentialGeometry.Geometry.Riemannian.Variation
