import DifferentialGeometry.Geometry.Comparison.HingeModel

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem endpointHingeComparison_of_nonpos {X : Type*} [MetricSpace X]
    (κ : ℝ) (p : X) {r : ℝ} (hr : r ≤ 0) : endpointHingeComparison κ p r := by
  intro x R S γ β hR hS hsum
  exfalso
  linarith

noncomputable def cappedEndpointComparisonRadius {X : Type*} [MetricSpace X]
    (κ : ℝ) (p : X) (M : ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ r ≤ M ∧ endpointHingeComparison κ p r}

theorem le_cappedEndpointComparisonRadius {X : Type*} [MetricSpace X]
    {κ M r : ℝ} {p : X} (hr : 0 ≤ r) (hrM : r ≤ M)
    (hgood : endpointHingeComparison κ p r) : r ≤ cappedEndpointComparisonRadius κ p M :=
  le_csSup ⟨M, fun _ hs => hs.2.1⟩ ⟨hr, hrM, hgood⟩

theorem cappedEndpointComparisonRadius_mem_Icc {X : Type*} [MetricSpace X]
    (κ : ℝ) (p : X) {M : ℝ} (hM : 0 ≤ M) :
    cappedEndpointComparisonRadius κ p M ∈ Icc (0 : ℝ) M := by
  have hzero : (0 : ℝ) ∈ {r : ℝ | 0 ≤ r ∧ r ≤ M ∧ endpointHingeComparison κ p r} :=
    ⟨le_rfl, hM, endpointHingeComparison_of_nonpos κ p le_rfl⟩
  exact ⟨le_cappedEndpointComparisonRadius le_rfl hM hzero.2.2,
    csSup_le ⟨0, hzero⟩ (fun _ hs => hs.2.1)⟩

theorem endpointHingeComparison_of_lt_cappedRadius {X : Type*} [MetricSpace X]
    {κ M r : ℝ} {p : X} (hM : 0 ≤ M) (hr : r < cappedEndpointComparisonRadius κ p M) :
    endpointHingeComparison κ p r := by
  obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup
    (show Set.Nonempty {s : ℝ | 0 ≤ s ∧ s ≤ M ∧ endpointHingeComparison κ p s} from
      ⟨0, le_rfl, hM, endpointHingeComparison_of_nonpos κ p le_rfl⟩) hr
  exact hs.2.2.mono hrs.le

theorem exists_uniform_cappedComparisonRadius_lower_bound
    {X : Type*} [MetricSpace X] {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 < M)
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ q ∈ ball p a,
      c ≤ cappedEndpointComparisonRadius κ q M := by
  obtain ⟨a, ha, hgood⟩ := exists_uniform_endpointHingeComparison hκ hΩ hcomp hp
  refine ⟨a, min a M, ha, lt_min ha hM, ?_⟩
  intro q hq
  exact le_cappedEndpointComparisonRadius (le_min ha.le hM.le) (min_le_right _ _)
    ((hgood q hq).mono (min_le_left _ _))

theorem cappedEndpointComparisonRadius_pos_of_local_fourPointComparison
    {X : Type*} [MetricSpace X] {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 < M)
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) :
    0 < cappedEndpointComparisonRadius κ p M := by
  obtain ⟨a, c, ha, hc, hbound⟩ := exists_uniform_cappedComparisonRadius_lower_bound hκ hM hΩ hcomp hp
  exact hc.trans_le (hbound p (by simpa only [mem_ball, dist_self] using ha))

theorem cappedEndpointComparisonRadius_le_armSum_of_bad_hinge
    {X : Type*} [MetricSpace X] {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    {p q : X} (H : MinimizingHinge p q) (hbad : H.modelSide κ < dist p q) :
    cappedEndpointComparisonRadius κ p M ≤ dist H.center p + dist H.center q := by
  apply csSup_le (show Set.Nonempty {r : ℝ | 0 ≤ r ∧ r ≤ M ∧ endpointHingeComparison κ p r} from
    ⟨0, le_rfl, hM, endpointHingeComparison_of_nonpos κ p le_rfl⟩)
  intro r hr
  by_contra hn
  exact (not_le_of_gt hbad)
    (H.modelSide_ge_dist_of_endpoint_comparison hκ hr.2.2 (lt_of_not_ge hn))

end DifferentialGeometry.Geometry.Comparison.Toponogov
