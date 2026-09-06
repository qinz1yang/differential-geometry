import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.HCGCompactness

open Bundle DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable [T2Space (TangentBundle I M)]

def parabolicPointedFlowSeq
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscale : ∀ i, 0 < scale i)
    (htime : ∀ i, time i ∈ D₀.carrier)
    (hcarrier : ∀ i,
      D.carrier ⊆ (paraInterval D₀ (time i) (scale i) (htime i)).carrier)
    (hregular : ∀ i,
      D.regular ⊆ (paraInterval D₀ (time i) (scale i) (htime i)).regular)
    (basepoint : Nat → M) :
    PointedFlowSeq.{u, uE, uH} (I := I) := by
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  exact {
    D := D
    term := fun i => {
      M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := basepoint i
      S := (paraSolution (I := I) S (time i) (scale i) (hscale i) (htime i)).timeRestrict D
      isSolution := isSoln_timeRestrict (I := I)
        (paraSol (I := I) S hS (time i) (scale i) (hscale i) (htime i))
        (hcarrier i) (hregular i) } }

@[simp]
theorem parabolicPointedFlowSeq_metric
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscale : ∀ i, 0 < scale i)
    (htime : ∀ i, time i ∈ D₀.carrier)
    (hcarrier : ∀ i,
      D.carrier ⊆ (paraInterval D₀ (time i) (scale i) (htime i)).carrier)
    (hregular : ∀ i,
      D.regular ⊆ (paraInterval D₀ (time i) (scale i) (htime i)).regular)
    (basepoint : Nat → M) (i : Nat) (s : Real) :
    let X := parabolicPointedFlowSeq (I := I) S hS time scale hscale htime
      hcarrier hregular basepoint
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (X.term i).S.family.metric s =
      scaleMetric (I := I) (scale i) (hscale i)
        (S.family.metric (paraTime (time i) (scale i) s)) := by
  let X := parabolicPointedFlowSeq (I := I) S hS time scale hscale htime
    hcarrier hregular basepoint
  let : TopologicalSpace (X.term i).M := (X.term i).topology
  let : ChartedSpace H (X.term i).M := (X.term i).charted
  let : IsManifold I ∞ (X.term i).M := (X.term i).smooth
  let : IsManifold I 1 (X.term i).M :=
    IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
    change IsManifold I ∞ (X.term i).M
    infer_instance
  let : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
  let : T2Space (X.term i).M := (X.term i).t2
  rfl

@[simp]
theorem parabolicPointedFlowSeq_scalar
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscale : ∀ i, 0 < scale i)
    (htime : ∀ i, time i ∈ D₀.carrier)
    (hcarrier : ∀ i,
      D.carrier ⊆ (paraInterval D₀ (time i) (scale i) (htime i)).carrier)
    (hregular : ∀ i,
      D.regular ⊆ (paraInterval D₀ (time i) (scale i) (htime i)).regular)
    (basepoint : Nat → M) (i : Nat) (s : Real) (x : M) :
    let X := parabolicPointedFlowSeq (I := I) S hS time scale hscale htime
      hcarrier hregular basepoint
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (X.term i).S.scalar s x =
      (scale i)⁻¹ * S.scalar (paraTime (time i) (scale i) s) x := by
  let X := parabolicPointedFlowSeq (I := I) S hS time scale hscale htime
    hcarrier hregular basepoint
  let : TopologicalSpace (X.term i).M := (X.term i).topology
  let : ChartedSpace H (X.term i).M := (X.term i).charted
  let : IsManifold I ∞ (X.term i).M := (X.term i).smooth
  let : IsManifold I 1 (X.term i).M :=
    IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
    change IsManifold I ∞ (X.term i).M
    infer_instance
  let : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
  let : T2Space (X.term i).M := (X.term i).t2
  exact congrFun (congrFun
    (paraSolution_scalar (I := I) S (time i) (scale i) (hscale i) (htime i)) s) x

end DifferentialGeometry.HCGCompactness
