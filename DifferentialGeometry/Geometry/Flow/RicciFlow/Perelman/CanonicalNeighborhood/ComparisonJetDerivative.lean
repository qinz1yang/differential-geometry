import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
  {F : N → M} {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}

theorem MetricComparisonOn.hasDerivWithinAt_jet
    (c : MetricComparisonOn h g F U times order eps) {b : ℕ} {s : ℝ} {x : N}
    (hs : s ∈ times) (hx : x ∈ U)
    (hdiff : ∀ v : Fin 2 → TangentSpace I x,
      DifferentiableWithinAt ℝ (fun a => c.jet b a x v) times s) :
    HasDerivWithinAt (fun a => c.jet b a x) (c.jet (b + 1) s x) times s := by
  let basis := Module.finBasis ℝ (TangentSpace I x)
  apply tensor0S_hasDerivWithinAt_of_components basis
  intro slots
  change HasDerivWithinAt (fun a => c.jet b a x (fun j => basis (slots j)))
    (c.jet (b + 1) s x (fun j => basis (slots j))) times s
  rw [c.jet_succ b s hs x hx]
  exact (hdiff (fun j => basis (slots j))).hasDerivWithinAt

theorem MetricComparisonOn.jet_succ_eq_derivWithin
    (c : MetricComparisonOn h g F U times order eps) {b : ℕ} {s : ℝ} {x : N}
    (hs : s ∈ times) (hx : x ∈ U) (hunique : UniqueDiffWithinAt ℝ times s)
    (hdiff : ∀ v : Fin 2 → TangentSpace I x,
      DifferentiableWithinAt ℝ (fun a => c.jet b a x v) times s) :
    c.jet (b + 1) s x = derivWithin (fun a => c.jet b a x) times s :=
  ((c.hasDerivWithinAt_jet hs hx hdiff).derivWithin hunique).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
