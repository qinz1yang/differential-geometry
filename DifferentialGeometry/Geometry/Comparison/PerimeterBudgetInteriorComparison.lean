import DifferentialGeometry.Geometry.Comparison.ComparisonRadius
import DifferentialGeometry.Geometry.Comparison.EndpointEnlargementThreeFifths
import DifferentialGeometry.Topology.MetricSpace.BudgetAlmostMinimum
import DifferentialGeometry.Topology.MetricSpace.PerimeterBufferSegment

set_option autoImplicit false


open Set Metric Filter Topology

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

theorem modelSide_ge_dist_of_complete_perimeter_budget_buffer
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {p q : X} {L : ℝ} (hcomplete : IsComplete (closedBall p L))
    (H : MinimizingHinge p q) (hsum : dist H.center p + dist H.center q < 79 * L / 202) :
    dist p q ≤ H.modelSide κ := by
  by_contra hn
  have hbad : H.modelSide κ < dist p q := lt_of_not_ge hn
  let M := dist H.center p + dist H.center q + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  let r : X → ℝ := fun x => cappedEndpointComparisonRadius κ x M
  have hrpos (x : X) : 0 < r x := by
    obtain ⟨Ω, hΩ, hcomp, hx⟩ := hlocal x
    exact cappedEndpointComparisonRadius_pos_of_local_fourPointComparison hκ hM hΩ hcomp hx
  have hr0M : r p < M :=
    (cappedEndpointComparisonRadius_le_armSum_of_bad_hinge hκ hM.le H hbad).trans_lt (by
      dsimp only [M]
      linarith)
  have hr0L : r p < 79 * L / 202 :=
    (cappedEndpointComparisonRadius_le_armSum_of_bad_hinge hκ hM.le H hbad).trans_lt hsum
  have hsmallcomplete : IsComplete (closedBall p (((101 : ℝ) / 100) * r p / (1 - (121 : ℝ) / 200))) := by
    apply Metric.isComplete_closedBall_of_add_dist_le hcomplete
    rw [dist_self]
    norm_num
    nlinarith [hrpos p]
  have hlower : ∀ x ∈ closedBall p (((101 : ℝ) / 100) * r p / (1 - (121 : ℝ) / 200)),
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ y in 𝓝 x, c ≤ r y := by
    intro x hx
    obtain ⟨Ω, hΩ, hcomp, hxΩ⟩ := hlocal x
    obtain ⟨ρ, c, hρ, hc, hbound⟩ :=
      exists_uniform_cappedComparisonRadius_lower_bound hκ hM hΩ hcomp hxΩ
    refine ⟨c, hc, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hρ] with y hy using hbound y hy
  obtain ⟨pstar, hpstar, hle, hminimum⟩ :=
    Metric.exists_relative_almost_minimum_with_budget (r := r) (o := p)
      (a := (101 : ℝ) / 100) (θ := (121 : ℝ) / 200)
      (by norm_num) (by norm_num) (by norm_num) hrpos
      hsmallcomplete hlower
  have hstarM : r pstar < M := hle.trans_lt hr0M
  let ℓ := 201 * r pstar / 200
  have hℓ : 0 < ℓ := by
    have hstarpos := hrpos pstar
    dsimp only [ℓ]
    positivity
  have hbuffer : dist pstar p + ℓ ≤ L := by
    norm_num at hpstar
    dsimp only [ℓ]
    nlinarith [hrpos p, hrpos pstar]
  have hstarcomplete : IsComplete (closedBall pstar ℓ) :=
    Metric.isComplete_closedBall_of_add_dist_le hcomplete hbuffer
  let : LocallyCompactSpace (ball pstar ℓ) := isOpen_ball.locallyCompactSpace
  have hnear (y : X) (hy : y ∈ ball pstar ℓ) : 3 * ℓ / 5 < r y := by
    have hd : dist pstar y ≤ ((101 : ℝ) / 100) * r pstar := by
      have ht : dist y pstar < ℓ := hy
      rw [dist_comm y pstar] at ht
      dsimp only [ℓ] at ht
      nlinarith [hrpos pstar]
    have hm := hminimum y hd
    norm_num at hm
    dsimp only [ℓ]
    nlinarith [hrpos pstar]
  have hshort (y : X) (hy : y ∈ ball pstar ℓ) : endpointHingeComparison κ y (3 * ℓ / 5) :=
    endpointHingeComparison_of_lt_cappedRadius hM.le (hnear y hy)
  have henlarge : endpointHingeComparison κ pstar ℓ := by
    apply endpointHingeComparison_enlarge_three_fifths hκ hℓ
      (hshort pstar (by simpa only [mem_ball, dist_self] using hℓ)) hshort
    · intro y hy z hz
      have hleft : (dist z pstar + dist pstar pstar + dist z pstar) / 2 < ℓ := by
        rw [dist_self]
        linarith [dist_nonneg (x := z) (y := y)]
      have hright : (dist z pstar + dist y pstar + dist z y) / 2 < ℓ := by
        have ht := dist_triangle y z pstar
        rw [dist_comm y z] at ht
        linarith
      obtain ⟨η, hη, hη0, hηp, _⟩ :=
        Metric.exists_isometric_segment_in_closedBall_of_half_perimeter_lt
          hcurves pstar hstarcomplete hleft
      obtain ⟨σ, hσ, hσ0, hσq, _⟩ :=
        Metric.exists_isometric_segment_in_closedBall_of_half_perimeter_lt
          hcurves pstar hstarcomplete hright
      exact ⟨⟨z, η, σ, hη, hσ, hη0, hσ0, hηp, hσq⟩, rfl⟩
    · intro z hz
      exact hlocal z
  have hcap : min ℓ M ≤ r pstar :=
    le_cappedEndpointComparisonRadius (le_min hℓ.le hM.le) (min_le_right _ _)
      (henlarge.mono (min_le_left _ _))
  have hgreater : r pstar < min ℓ M := lt_min (by
    dsimp only [ℓ]
    nlinarith [hrpos pstar]) hstarM
  exact (not_lt_of_ge hcap) hgreater

end Metric.MinimizingHinge

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparisonAngle_le_of_complete_perimeter_budget_buffer
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {p q : X} {L : ℝ} (hcomplete : IsComplete (closedBall p L))
    (H : MinimizingHinge p q) (hsum : dist H.center p + dist H.center q < 79 * L / 202)
    (ha : 0 < dist H.center p) (hb : 0 < dist H.center q) :
    comparisonAngleNegCurvature κ (dist H.center p) (dist H.center q) (dist p q) ≤ H.germAngle κ :=
  (H.comparisonAngle_le_iff_dist_le_modelSide hκ ha hb).mpr
    (modelSide_ge_dist_of_complete_perimeter_budget_buffer hκ hcurves hlocal hcomplete H hsum)

end Metric.MinimizingHinge

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem endpointHingeComparison_of_complete_perimeter_budget_buffer
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    {p : X} {L : ℝ} (hcomplete : IsComplete (closedBall p L)) :
    endpointHingeComparison κ p (79 * L / 202) := by
  intro x R S γ β hR hS hsum hγend hγrad hβrad hγmin hβmin
  have ha : dist x p = R := by simpa only [hγend] using hγrad R ⟨hR, le_rfl⟩
  have hb : dist x (β S) = S := hβrad S ⟨hS, le_rfl⟩
  obtain ⟨H, hcenter, hangle⟩ := MinimizingHinge.exists_hinge_of_germs
    (κ := κ) hR hS hγend rfl hγrad hβrad hγmin hβmin
  have ht := H.comparisonAngle_le_of_complete_perimeter_budget_buffer hκ hcurves hlocal hcomplete
    (by rw [hcenter, ha, hb]; exact hsum)
    (by rw [hcenter, ha]; exact hR) (by rw [hcenter, hb]; exact hS)
  rwa [hcenter, ha, hb, hangle] at ht

end DifferentialGeometry.Geometry.Comparison.Toponogov
