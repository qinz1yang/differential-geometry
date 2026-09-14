import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerMassClassification

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} (I := I))

local instance massBridgeTopology : TopologicalSpace L.M := L.topology
local instance massBridgeCharted : ChartedSpace H L.M := L.charted
local instance massBridgeSmooth : IsManifold I ∞ L.M := L.smooth
local instance massBridgeT2 : T2Space L.M := L.t2
local instance massBridgeSigma : SigmaCompactSpace L.M := L.sigmaCompact

theorem normalized_nonflat_three_shrinker_round_or_mass_of_classification
    (hdim : Module.finrank ℝ E = 3) (hcomplete : MetricComplete (I := I) L)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f) :
    (CompactSpace L.M ∧ (∀ x : L.M, metricScalarAt L.metric x = (3 : ℝ) / 2) ∧
      ∀ x : L.M, ∀ v : TangentSpace I x,
        ricciTensor L.metric x v v = ((3 / 2 : ℝ) / 3) * L.metric.inner x v v) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (2 * Real.exp (-1)) ∨
    normalizedShrinkerMass L.metric f = ENNReal.ofReal (Real.exp (-1)) :=
  normalized_nonflat_three_shrinker_classification L hdim hcomplete hconnected hnonflat
    hnco f hsoliton hnormal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
