import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerVolumeZero_R2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LargeTriggerAssembly_S21

set_option autoImplicit false

/-!
# CH12-CX9: A13 for both scalar branches

The external inputs are W1 and LTF03 quantified over profiles and the negative
branch. In the complementary branch, the profile proves vanishing normalized
volume, which supplies T3 directly. S16 and S21 are unchanged.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.LongTime Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem late_derivative_tests_of_flow_allBranches_CX9 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : GC.LongTime.LateCutFamily F K slices)
    (hLTF03 : ∀ H : AnalyticSurgeryProfile F δ, ∀ hn : EventuallyNegativeScalar_S13 F,
      ∀ (S : LatePointSequence_S13 F) (a v Lr : ℝ),
        SeedHyperbolicOnFixedBallsSeq_S13 H hdec hn S a v Lr)
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
  classical
  by_cases hn : EventuallyNegativeScalar_S13 F
  · exact late_derivative_tests_of_flow_S21 F K hK δ hadm hdec slices htimes hnonempty L
      hn (fun H => hLTF03 H hn) hW1
  · obtain ⟨H⟩ := hadm
    have hvol := normalizedVolumeVanishes_of_not_negative_R2 H hn
    exact late_derivative_tests_of_flow_S16 F K hK δ ⟨H⟩ hdec slices htimes hnonempty L
      (LateCutFamily.hT3_of_volumeVanishes_R2 F K slices htimes L hvol) hW1

end GC.LongTime.Ch12
