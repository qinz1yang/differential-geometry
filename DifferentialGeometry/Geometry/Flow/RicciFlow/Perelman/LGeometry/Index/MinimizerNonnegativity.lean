import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Comparison.Variation.FieldRealization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegIndex_nonneg_var
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z)
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b)
    (hmin : IsLocalMin (fun u : Real ↦ lRegAction S T (f u) a b) 0) :
    0 ≤ lRegIndex S T (f 0)
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u s) 0)
      (fun s : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u s) 0) a b := by
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hfirst := lRegAction_deriv (I := I) S hS T f hf a b ht
  have hfirst_zero := hmin.hasDerivAt_eq_zero hfirst
  have hfirst' := hfirst.congr_deriv hfirst_zero
  have hsecond := lRegAction_second (I := I) S hS T f hf a b x Z hgeo hfixa hfixb
  have hnonneg := second_deriv_nonneg_of_isLocalMin hmin hfirst' hsecond
  linarith

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegIndex_nonneg
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M) (a b : Real) (x : M)
    (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T gamma (Set.uIcc a b) x Z)
    (Y : Real → E)
    (hY : ContMDiff 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle I M)))
    (hYa : Y a = 0) (hYb : Y b = 0)
    (hmin : ∀ f : Real → Real → M, IsSmoothVariation (I := I) f →
      (∀ s, f 0 s = gamma s) →
      (∀ u, f u a = gamma a) →
      (∀ u, f u b = gamma b) →
      IsLocalMin (fun u => lRegAction S T (f u) a b) 0) :
    0 ≤ lRegIndex S T gamma Y Y a b := by
  obtain ⟨f, hf, hfzero, hfield, hfixa, hfixb⟩ :=
    exists_var_fix_ends (I := I) (S.base.metric T) gamma Y a b hY hYa hYb
  have hcenter : f 0 = gamma := funext hfzero
  subst gamma
  have hnonneg := lRegIndex_nonneg_var (I := I) S hS T f hf a b x Z hgeo
    hfixa hfixb (hmin f hf (fun _ => rfl) hfixa hfixb)
  have hEq : Set.EqOn
      (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0)
      Y (Set.uIoo a b) := by
    intro s hs
    with_unfolding_all exact hfield s (Set.uIoo_subset_uIcc_self hs)
  rw [lRegIndex_congr (I := I) S T (f 0)
    (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0)
    (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0)
    Y Y a b hEq hEq] at hnonneg
  exact hnonneg

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
