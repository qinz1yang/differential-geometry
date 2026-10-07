import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BoundaryWiringAssembly_S16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerMain_S21

/-!
# CH12-S21: A13 assembly with `hT3` discharged from LTF03

Remaining inputs: `hW1` (WBD04 normalized output), `hLTF03` (LTF03 for the analytic profile) and
the negative-scalar branch `hneg` that LTF03 is stated under.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.LongTime Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem late_derivative_tests_of_flow_S21 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : GC.LongTime.LateCutFamily F K slices)
    -- LTF03 (explicit input; hneg is the branch it is stated under)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ H : AnalyticSurgeryProfile F δ, ∀ (S : LatePointSequence_S13 F) (a v Lr : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 H hdec hneg S a v Lr)
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
    L.hasEventualDerivativeBounds := by
  obtain ⟨H⟩ := hadm
  exact late_derivative_tests_of_flow_S16 F K hK δ ⟨H⟩ hdec slices htimes hnonempty L
    (LateCutFamily.hT3_of_LTF03_S21 F K δ hdec H hneg slices htimes L (hLTF03 H)) hW1

end GC.LongTime.Ch12

#print axioms GC.LongTime.Ch12.LateCutFamily.hT3_of_LTF03_S21
#print axioms GC.LongTime.Ch12.late_derivative_tests_of_flow_S21
#print axioms GC.LongTime.Ch12.seed_scale_down_S21
#print axioms GC.LongTime.Ch12.curvatureRadius_le_five_of_defect_S21
