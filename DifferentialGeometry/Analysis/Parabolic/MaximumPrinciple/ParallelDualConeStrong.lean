import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.DualConeStrong
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ParallelCone

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

universe u uE uH uF

variable {M : Type u}
variable (F : M → Type uF)
  [∀ x, NormedAddCommGroup (F x)]
  [∀ x, InnerProductSpace Real (F x)]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parallelProperCone_mem_dualZeroFace_of_terminal_eq_zero
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (u : Real → ∀ x, F x)
    (phi : StrongDual Real (F x₀))
    (hphi : ProperCone.IsDualElement (C x₀) phi)
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (dualScalarization (transportedSectionFamily F P x₀ u) phi))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C x)
    (hgrad_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) tau))
    (hlaplacian_cont : ∀ rho : M → Real,
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M ↦
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) tau))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₁ : M}
    (hzero : dualScalarization (transportedSectionFamily F P x₀ u) phi tau x₁ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ ProperCone.dualZeroFace (C x)
        (phi.comp
          (P.transport x₀ x).toContinuousLinearEquiv.symm.toContinuousLinearMap) := by
  have hfixed_mem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      transportedSectionFamily F P x₀ u t x ∈ C x₀ := by
    intro t ht x
    exact (hC.transport_mem_iff F x x₀ (u t x)).2 (hmem t ht x)
  have hfixed_face := properCone_mem_dualZeroFace_of_terminal_eq_zero
    (I := I) G hT (C x₀) (transportedSectionFamily F P x₀ u) phi hphi V
      hsol htau hfixed_mem hgrad_cont hlaplacian_cont L hV hzero
  intro t ht x
  have htransported :=
    (hC.transport_mem_dualZeroFace_iff F x₀ x phi
      (transportedSectionFamily F P x₀ u t x)).2 (hfixed_face t ht x)
  simpa using htransported

theorem parallelProperCone_mem_dualZeroFace_of_terminal_eq_zero_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (P : LinearIsometricTransport F)
    (C : ProperConeFamily F)
    (hC : IsParallelProperConeFamily F P C)
    (x₀ : M)
    (u : Real → ∀ x, F x)
    (phi : StrongDual Real (F x₀))
    (hphi : ProperCone.IsDualElement (C x₀) phi)
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (dualScalarization (transportedSectionFamily F P x₀ u) phi))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C x)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₁ : M}
    (hzero : dualScalarization (transportedSectionFamily F P x₀ u) phi tau x₁ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ ProperCone.dualZeroFace (C x)
        (phi.comp
          (P.transport x₀ x).toContinuousLinearEquiv.symm.toContinuousLinearMap) := by
  apply parallelProperCone_mem_dualZeroFace_of_terminal_eq_zero
    (I := I) F G hT P C hC x₀ u phi hphi V hsol htau hmem (L := L) (x₁ := x₁)
  · intro rho hrho
    exact G.gradient_norm_sq_continuousOn hG hslab hrho
  · intro rho hrho
    exact G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc htau.1) hconn hrho
  · exact hV
  · exact hzero

end

end DifferentialGeometry.Analysis.Parabolic
