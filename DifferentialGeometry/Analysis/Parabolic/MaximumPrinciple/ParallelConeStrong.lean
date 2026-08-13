import DifferentialGeometry.Analysis.InnerProductSpace.ProperConeFace
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ParallelCone
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ParallelDualConeStrong

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

universe u uE uH uF

variable {M : Type u}
variable (F : M → Type uF)
  [∀ x, NormedAddCommGroup (F x)]
  [∀ x, InnerProductSpace Real (F x)]
  [∀ x, CompleteSpace (F x)]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parallelProperCone_mem_innerDualZeroFace_of_terminal_eq_zero
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
    (y : F x₀) (hy : y ∈ ProperCone.innerDual (C x₀ : Set (F x₀)))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (innerScalarization (transportedSectionFamily F P x₀ u) y))
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
    (hzero : innerScalarization (transportedSectionFamily F P x₀ u) y tau x₁ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ ProperCone.innerDualZeroFace (C x) (P.transport x₀ x y) := by
  let phi : StrongDual Real (F x₀) := innerSL Real y
  have hphi : ProperCone.IsDualElement (C x₀) phi := by
    intro z hz
    simpa [phi, real_inner_comm] using hy hz
  have hscalar :
      dualScalarization (transportedSectionFamily F P x₀ u) phi =
        innerScalarization (transportedSectionFamily F P x₀ u) y := by
    funext t x
    simp [phi, dualScalarization, innerScalarization, real_inner_comm]
  have hsol' : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (dualScalarization (transportedSectionFamily F P x₀ u) phi) := by
    rw [hscalar]
    exact hsol
  have hzero' :
      dualScalarization (transportedSectionFamily F P x₀ u) phi tau x₁ = 0 := by
    rw [hscalar]
    exact hzero
  have hface := parallelProperCone_mem_dualZeroFace_of_terminal_eq_zero
    (I := I) F G hT P C hC x₀ u phi hphi V hsol' htau hmem
      hgrad_cont hlaplacian_cont L hV hzero'
  intro t ht x
  have hfunctional :
      phi.comp (P.transport x₀ x).toContinuousLinearEquiv.symm.toContinuousLinearMap =
        innerSL Real (P.transport x₀ x y) := by
    ext z
    simpa [phi] using
      ((P.transport x₀ x).inner_map_map y
        ((P.transport x₀ x).symm z)).symm
  change u t x ∈ DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace
    (C x) (innerSL Real (P.transport x₀ x y))
  rw [← hfunctional]
  exact hface t ht x

theorem parallelProperCone_mem_innerDualZeroFace_of_terminal_eq_zero_of_metricFamilySmoothOn
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
    (y : F x₀) (hy : y ∈ ProperCone.innerDual (C x₀ : Set (F x₀)))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V
        (innerScalarization (transportedSectionFamily F P x₀ u) y))
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
    (hzero : innerScalarization (transportedSectionFamily F P x₀ u) y tau x₁ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ ProperCone.innerDualZeroFace (C x) (P.transport x₀ x y) := by
  apply parallelProperCone_mem_innerDualZeroFace_of_terminal_eq_zero
    (I := I) F G hT P C hC x₀ u y hy V hsol htau hmem (L := L) (x₁ := x₁)
  · intro rho hrho
    exact G.gradient_norm_sq_continuousOn hG hslab hrho
  · intro rho hrho
    exact G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc htau.1) hconn hrho
  · exact hV
  · exact hzero

end

end DifferentialGeometry.Analysis.Parabolic
