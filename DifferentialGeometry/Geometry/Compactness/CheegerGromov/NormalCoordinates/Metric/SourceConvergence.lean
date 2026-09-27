import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChart
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import DifferentialGeometry.Geometry.Metric.Pullback.CoefficientConvergence

section

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : ∀ (x : M) (v : TangentSpace I x),
  ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

theorem IntrinsicBallChart.pullbackMetricCoefficients_eq_intrinsicFrameMetric
    (p : M) {r : ℝ} (c : IntrinsicBallChart (I := I) g hEnorm p r) :
    EqOn (pullbackMetricCoefficients g c.hom) (intrinsicFrameMetric g hEnorm p)
      (Metric.ball (0 : E) r) := by
  intro z hz
  have heq : c.hom =ᶠ[𝓝 z] intrinsicFramedExp g hEnorm p :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz) (fun q hq => c.hom_eq hq)
  have hD := Filter.EventuallyEq.mfderiv_eq
    (I := 𝓘(ℝ, E)) (I' := I) heq
  ext v w
  rw [pullbackMetricCoefficients_apply, intrinsicFrameMetric_apply]
  rw [hD, c.hom_eq hz]

theorem IntrinsicBallChart.pullbackMetricCoefficients_eq_pullbackForm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : M) {r : ℝ} (c : IntrinsicBallChart (I := I) g hEnorm p r)
    {P : V → M} {z : V} (hP : MDifferentiableAt 𝓘(ℝ, V) I P z)
    (hz : P z ∈ c.hom.target) :
    pullbackMetricCoefficients g P z =
      CheegerGromovCompactness.pullbackForm
        (intrinsicFrameMetric g hEnorm p (c.hom.symm (P z)),
          fderiv ℝ (c.hom.symm ∘ P) z) := by
  have hsource : c.hom.symm (P z) ∈ Metric.ball (0 : E) r := by
    rw [← c.source_eq]
    exact c.hom.map_target hz
  rw [← c.pullbackMetricCoefficients_eq_intrinsicFrameMetric g hEnorm p hsource]
  ext v w
  exact (pullbackMetricCoefficients_fderiv_symm g c.hom hP hz v w).symm

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.pullbackMetricCoefficients_convergence_of_chart_convergence
    {U : Set E} (hU : IsOpen U) {ρ : ℝ} (hUρ : U ⊆ Metric.ball (0 : E) ρ)
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p : ∀ k, M k) (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) ρ)
    (P : ∀ k, E → M k) (hP : ∀ k, ContMDiffOn 𝓘(ℝ, E) I ∞ (P k) U)
    (hcapture : ∀ K, IsCompact K → K ⊆ U →
      ∀ᶠ k in atTop, MapsTo (P k) K (c k).hom.target)
    (hcoord : CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => (c k).hom.symm ∘ P k) id)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) ρ)
      (fun k => intrinsicFrameMetric (g k) (hEnorm k) (p k)) B)
    (hBC : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) ρ)) :
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
      (fun k => pullbackMetricCoefficients (g k) (P k)) B := by
  apply Geometry.pullbackMetricCoefficients_convergence_of_chart_convergence
    hU Metric.isOpen_ball hUρ g (fun k => (c k).hom) (fun k => (c k).source_eq)
      P hP hcapture hcoord _ hBC
  exact hB.congr Metric.isOpen_ball
    (fun k => (c k).pullbackMetricCoefficients_eq_intrinsicFrameMetric (g k) (hEnorm k) (p k))
    (fun _ _ => rfl)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, PseudoEMetricSpace (M k)]
  [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

theorem IntrinsicBallChart.pullbackMetricCoefficients_convergence_of_local_inclusion
    (U : TopologicalSpace.Opens E) {ρ : ℝ} (hUρ : (U : Set E) ⊆ Metric.ball (0 : E) ρ)
    (j : U → Q) (hj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ j)
    (jbar : E → Q) (hjbar : ∀ z : U, jbar z = j z)
    (V : TopologicalSpace.Opens Q)
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (gQ : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (p : ∀ k, M k) (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) ρ)
    (F : ∀ k, Q → M k) (hF : ∀ k, ContMDiffOn 𝓘(ℝ, E) I ∞ (F k) V)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) ρ)
      (fun k => intrinsicFrameMetric (g k) (hEnorm k) (p k)) B)
    (hBC : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) ρ))
    (hmetric : ∀ (z : U) (v w : E),
      gQ.inner (j z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) j z v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) j z w) = B z v w)
    (hcapture : ∀ K, IsCompact K → K ⊆ Subtype.val '' (j ⁻¹' (V : Set Q)) →
      ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ K →
        F k (j ⟨z, hz⟩) ∈ (c k).hom.target)
    (hcoord : CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Subtype.val '' (j ⁻¹' (V : Set Q)))
      (fun k z => @dite E (z ∈ U) (Classical.propDecidable _)
        (fun hz => (c k).hom.symm (F k (j ⟨z, hz⟩))) (fun _ => 0)) id) :
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts
      (Subtype.val '' (j ⁻¹' (V : Set Q)))
      (fun k => pullbackMetricCoefficients (g k) (F k ∘ jbar))
      (pullbackMetricCoefficients gQ jbar) := by
  refine Geometry.pullbackMetricCoefficients_convergence_of_local_inclusion
    U Metric.isOpen_ball hUρ j hj jbar hjbar V g gQ (fun k => (c k).hom)
      (fun k => (c k).source_eq) F hF ?_ hBC hmetric ?_ ?_
  · exact hB.congr Metric.isOpen_ball
      (fun k => (c k).pullbackMetricCoefficients_eq_intrinsicFrameMetric (g k) (hEnorm k) (p k))
      (fun _ _ => rfl)
  · intro K hK hKD
    filter_upwards [hcapture K hK hKD] with k hk
    intro z hz
    obtain ⟨x, _, hx⟩ := hKD hz
    rw [← hx] at hz ⊢
    change F k (jbar (x : E)) ∈ (c k).hom.target
    rw [hjbar x]
    exact hk x x.property hz
  · have hD : IsOpen (Subtype.val '' (j ⁻¹' (V : Set Q))) :=
      U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage hj.continuous)
    apply hcoord.congr hD _ (fun _ _ => rfl)
    intro k z hz
    obtain ⟨x, _, rfl⟩ := hz
    simp only [Function.comp_apply, dif_pos x.property, hjbar x]

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
