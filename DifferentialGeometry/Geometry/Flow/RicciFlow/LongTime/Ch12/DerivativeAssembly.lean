import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBoundScaling

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- T4 (TCF05 + Adapter 4) assembly skeleton for A13.  The conclusion is the A13 statement
`GC.LongTime.late_derivative_tests_of_flow` verbatim; T1, T2, T3 and W1 are explicit inputs. -/
theorem late_derivative_tests_of_flow_assembly_W1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : LateCutFamily F K slices)
    -- T1 (TCF03): near-boundary whole-ball bound
    (hT1 : ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ≤
          ENNReal.ofReal 10 →
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j C i) p →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
        curvatureDerivativeNorm (L.metric j C i) k q ≤ A * (r ^ (k + 2))⁻¹)
    -- T2 (TCF02): interior scale / ball / volume agree with the ambient normalized slice
    (hT2 : ∃ N : ℕ, ∀ j, N ≤ j → ∀ c i, L.thin j c i →
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
                curvatureDerivativeNorm (slices j).normalizedMetric k q'))
    -- T3 (TCF04): no large test balls at interior points
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
    L.hasEventualDerivativeBounds := by
  obtain ⟨A₁, hA₁, N₁, h₁⟩ := hT1
  obtain ⟨N₂, h₂⟩ := hT2
  obtain ⟨b, T, C, hb, hC, hW⟩ := hW1
  intro w hw hwv
  obtain ⟨N₃, h₃⟩ := hT3 w hw hwv (min (b w) 1) (lt_min (hb w hw) one_pos)
  refine ⟨max (max N₁ N₂) (max N₃ ⌈T w⌉₊), max A₁ (C w), lt_max_of_lt_left hA₁, ?_⟩
  intro j hj c i hthin p r hr hrad hvol k hk q hq
  have hjN₁ : N₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hjN₂ : N₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hjN₃ : N₃ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
  have hjT : T w ≤ (slices j).time := by
    have h1 : ⌈T w⌉₊ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
    have h2 : T w ≤ (⌈T w⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈T w⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h1
    exact (h2.trans h3).trans (htimes j).le
  have hpos : (0 : ℝ) ≤ (r ^ (k + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hr.le _)
  by_cases hd : distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p ≤
      ENNReal.ofReal 10
  · exact (h₁ j hjN₁ c i hthin p hd r hr hrad k hk q hq).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
  · have hd' := not_le.mp hd
    have hsmall : r < min (b w) 1 := h₃ j hjN₃ c i hthin p hd' r hr hrad hvol
    have hrb : r ≤ b w := (hsmall.trans_le (min_le_left _ _)).le
    have hr9 : r ≤ 9 := by linarith [min_le_right (b w) 1]
    obtain ⟨p', hneg, hr'⟩ := h₂ j hjN₂ c i hthin p hd'
    obtain ⟨hsec, hvolA, hderiv⟩ := hr' r hr hr9
    obtain ⟨q', hq', heq⟩ := hderiv k q hq
    have hneg' := hneg (L.finite_scales j c i hthin p)
    rw [heq]
    exact (hW w hw (slices j) hjT p' r hr hrb hneg' (hsec hrad) (hvolA w hw hvol) k hk q' hq').trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)

end GC.LongTime.Ch12

