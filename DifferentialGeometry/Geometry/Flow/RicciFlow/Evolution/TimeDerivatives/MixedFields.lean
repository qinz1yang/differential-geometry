import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.TimeJetFields

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance mixedFieldC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance mixedFieldC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem exists_closedWindow_mixed_curvature_fields
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Set.Icc a b) (hregular : Set.Ioo a b ⊆ D.regular) (p : ℕ) :
    ∃ A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) (4 + p),
      ∀ q : ℕ, ∀ t : ℝ, t ∈ Set.Icc c b → ∀ x : M,
        A q t x = mixedCurvatureTensor S p q t x ∧
        HasDerivWithinAt (fun s => A q s x)
          (A (q + 1) t x - covariantEndomorphismAction0S (A q t x)
            (ricciSharp (S.base.metric t) x)) (Set.Icc c b) t := by
  exact exists_mixed_curvature_fields_on_closed_interval S hS hac hcb hcarrier hregular p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
