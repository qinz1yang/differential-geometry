import DifferentialGeometry.Analysis.Parabolic.OneFormHeat
import DifferentialGeometry.Geometry.Hodge.OneFormHodgeLaplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

structure IsHodgeHeatOneFormOn
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) : Prop where
  realizes :
    forall t : RealTimeInterval.FlowTime D, forall x : M,
      Nabla2OneFormRealizesAt (I := I) (G.connection (t : Real))
        (h (t : Real)) (nablaH (t : Real)) x (nabla2H (t : Real) x)
  equation :
    forall t : RealTimeInterval.RegularTime D, forall (x : M) (X : TangentSpace I x),
      HasDerivAt (fun s : Real => h s x (fun _ : Fin 1 => X))
        (-(oneFormHodgeLaplacianAt (I := I) (G.metric (t : Real))
            (nablaH (t : Real)) (nabla2H (t : Real)) x (fun _ : Fin 1 => X)))
        (t : Real)
  jointSmooth :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u ->
      forall i : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => h p.1 p.2 (fun _ : Fin 1 => frame i p.2))
          (D.regular ×ˢ u)
  jointSmoothNabla :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u ->
      forall i j : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            nablaH p.1 p.2 (vec2 (frame i p.2) (frame j p.2)))
          (D.regular ×ˢ u)

lemma IsHodgeHeatOneFormOn.toEvolving
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    {h : Real -> OneFormSection (I := I) (M := M)}
    {nablaH : Real -> TwoTensorSection (I := I) (M := M)}
    {nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x}
    (hHodge : IsHodgeHeatOneFormOn (I := I) G h nablaH nabla2H) :
    IsEvolvingOneFormOn (I := I) G h nablaH nabla2H
      (fun t x =>
        -(oneFormHodgeLaplacianAt (I := I) (G.metric t) (nablaH t) (nabla2H t) x)) where
  realizes := hHodge.realizes
  equation := by
    intro t x X
    simpa only [Tensor0SSpace.neg_apply] using hHodge.equation t x X
  jointSmooth := hHodge.jointSmooth
  jointSmoothNabla := hHodge.jointSmoothNabla

end

end DifferentialGeometry.Analysis.Parabolic
