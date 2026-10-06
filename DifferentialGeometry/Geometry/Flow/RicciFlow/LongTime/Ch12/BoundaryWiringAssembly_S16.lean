import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringG2_S16

/-!
# CH12-S16: unconditional `hT2` and the A13 assembly with only `hT3`, `hW1` remaining
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- S5's `hT2` shape, with no G2 parameter. -/
theorem LateCutFamily.hT2_shape_unconditional_S16 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : GC.LongTime.LateCutFamily F K slices) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ c i, L.thin j c i →
      ∀ p : ((L.decomposition j c).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p →
      ∃ p' : (slices j).stage.Carrier,
        (curvatureRadius (L.metric j c i) p ≠ ⊤ →
          ∃ z ∈ connectedComponent p',
            ¬ SectionalBoundedBelowAt (slices j).normalizedMetric z 0) ∧
        ∀ r : ℝ, 0 < r → r ≤ 9 →
          (ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
            ∀ q ∈ riemannianBallOf (slices j).normalizedMetric p' r,
              SectionalBoundedBelowAt (slices j).normalizedMetric q (-(r ^ 2)⁻¹)) ∧
          (∀ w : ℝ, 0 < w →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (slices j).normalizedMetric p' r) ∧
          (∀ k : ℕ, ∀ q ∈ riemannianBallOf (L.metric j c i) p r,
            ∃ q' ∈ riemannianBallOf (slices j).normalizedMetric p' r,
              curvatureDerivativeNorm (L.metric j c i) k q =
                curvatureDerivativeNorm (slices j).normalizedMetric k q') :=
  LateCutFamily.hT2_shape_T2 L (collarNegativePlane_S16 K)

/-- A13 assembly with `hT1` and `hT2` supplied: the remaining inputs are exactly
`hT3` (TCF04) and `hW1` (WBD04 normalized output). -/
theorem late_derivative_tests_of_flow_S16 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : GC.LongTime.LateCutFamily F K slices)
    -- T3 (TCF04)
    (hT3 : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume → ∀ b : ℝ, 0 < b →
      ∃ N : ℕ, ∀ j, N ≤ j → ∀ c i, L.thin j c i →
        ∀ p : ((L.decomposition j c).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p →
          ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r → r < b)
    -- W1 (WBD04 output, normalized form)
    (hW1 : ∃ (b T C : ℝ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧ (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹) :
    L.hasEventualDerivativeBounds :=
  late_derivative_tests_of_flow_assembly_W1 F K hK δ hadm hdec slices htimes hnonempty L
    (LateCutFamily.hT1_of_picked_S16 L) (LateCutFamily.hT2_shape_unconditional_S16 L) hT3 hW1

end GC.LongTime.Ch12

#print axioms GC.LongTime.Ch12.late_derivative_tests_of_flow_S16
#print axioms GC.LongTime.Ch12.collarNegativePlane_S16
#print axioms GC.LongTime.Ch12.LateCutFamily.hT1_of_picked_S16
#print axioms GC.LongTime.Ch12.wbar_S16_collar_ok
