import DifferentialGeometry.Analysis.InnerProductSpace.ProperConeFace
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.DualConeStrong
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ProperCone

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

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

theorem properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (y : F) (hy : y ∈ ProperCone.innerDual (C : Set F))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (innerScalarization u y))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C)
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
    {x₀ : M} (hzero : innerScalarization u y tau x₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      innerScalarization u y t x = 0 := by
  let phi : StrongDual Real F := innerSL Real y
  have hphi : ProperCone.IsDualElement C phi := by
    intro z hz
    simpa [phi, real_inner_comm] using hy hz
  have hscalar : dualScalarization u phi = innerScalarization u y := by
    funext t x
    simp [phi, dualScalarization, innerScalarization, real_inner_comm]
  have hsol' : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (dualScalarization u phi) := by
    rw [hscalar]
    exact hsol
  have hzero' : dualScalarization u phi tau x₀ = 0 := by
    rw [hscalar]
    exact hzero
  simpa only [hscalar] using
    properCone_dualScalarization_eq_zero_of_terminal_eq_zero
      (I := I) G hT C u phi hphi V hsol' htau hmem hgrad_cont
        hlaplacian_cont L hV hzero'

theorem properCone_mem_innerDualZeroFace_of_terminal_eq_zero
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (y : F) (hy : y ∈ ProperCone.innerDual (C : Set F))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (innerScalarization u y))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C)
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
    {x₀ : M} (hzero : innerScalarization u y tau x₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ ProperCone.innerDualZeroFace C y := by
  have hpairing := properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero
    (I := I) G hT C u y hy V hsol htau hmem hgrad_cont hlaplacian_cont
      L hV hzero
  intro t ht x
  exact ProperCone.mem_innerDualZeroFace.mpr
    ⟨hmem t ht x, by
      simpa [innerScalarization, real_inner_comm] using hpairing t ht x⟩

theorem properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (y : F) (hy : y ∈ ProperCone.innerDual (C : Set F))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (innerScalarization u y))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₀ : M} (hzero : innerScalarization u y tau x₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      innerScalarization u y t x = 0 := by
  apply properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero
    (I := I) G hT C u y hy V hsol htau hmem (L := L) (x₀ := x₀)
  · intro rho hrho
    exact G.gradient_norm_sq_continuousOn hG hslab hrho
  · intro rho hrho
    exact G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc htau.1) hconn hrho
  · exact hV
  · exact hzero

theorem properCone_mem_innerDualZeroFace_of_terminal_eq_zero_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (y : F) (hy : y ∈ ProperCone.innerDual (C : Set F))
    (V : Real → M → Real)
    (hsol : IsHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G V (innerScalarization u y))
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hmem : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, u t x ∈ C)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (L : Real)
    (hV : ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M, L ≤ V t x)
    {x₀ : M} (hzero : innerScalarization u y tau x₀ = 0) :
    ∀ t : Real, t ∈ Set.Icc 0 tau → ∀ x : M,
      u t x ∈ ProperCone.innerDualZeroFace C y := by
  have hpairing :=
    properCone_innerDual_pairing_eq_zero_of_terminal_eq_zero_of_metricFamilySmoothOn
      (I := I) G hT C u y hy V hsol htau hmem hG hslab hconn L hV hzero
  intro t ht x
  exact ProperCone.mem_innerDualZeroFace.mpr
    ⟨hmem t ht x, by
      simpa [innerScalarization, real_inner_comm] using hpairing t ht x⟩

end

end DifferentialGeometry.Analysis.Parabolic
