import DifferentialGeometry.Geometry.Comparison.PairedDistanceResidual
import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow

set_option autoImplicit false

open Set Metric Real
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

theorem PairedComparisonPacket.isOpenMap_distanceCoordinates_one
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : ι → X} {a₀ A δ : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω) (hVopen : IsOpen V)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι))
    (hcomplete : ∀ q ∈ V, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall q R))
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A) :
    IsOpenMap (fun z : V => distanceCoordinates 1 a (z : X)) := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro w ⟨q, hqU, rfl⟩
  have hW : IsOpen (((↑) : V → X) '' U) := hVopen.isOpenMap_subtype_val U hU
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW (q : X) ⟨q, hqU, rfl⟩
  obtain ⟨R, hR, hC⟩ := hcomplete q q.property
  let r := min (R / 2) (ε / 4)
  have hr : 0 < r := lt_min (half_pos hR) (by positivity)
  have hrR : r ≤ R := (min_le_left _ _).trans (half_le_self hR.le)
  have hrε : r ≤ ε / 4 := min_le_right _ _
  have hCr : IsComplete (closedBall (q : X) r) :=
    isComplete_closedBall_of_add_dist_le hC (by simpa only [dist_self, zero_add] using hrR)
  have hWsub : ((↑) : V → X) '' U ⊆ V := by
    rintro z ⟨z', _, rfl⟩
    exact z'.property
  have hbuf : ball (q : X) (2 * r) ⊆ V :=
    ((ball_subset_ball (show 2 * r ≤ ε by linarith)).trans hεW).trans hWsub
  have hquant := hpacket.ball_subset_distanceCoordinates_image hcurves hcomp hV hanchors
    ha₀ hδ hδm hr hCr hbuf hbounds
  let μ := 1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ
  let τ := min 1 (min (a₀ / 2) (min (δ ^ 2 / (4 * cosh (A + 1) / sinh a₀)) (μ * r / 2)))
  change 0 < τ ∧ ball (distanceCoordinates 1 a (q : X)) τ ⊆
    distanceCoordinates 1 a '' ball (q : X) r at hquant
  refine ⟨τ, hquant.1, ?_⟩
  intro y hy
  obtain ⟨z, hz, hfz⟩ := hquant.2 hy
  obtain ⟨zV, hzU, rfl⟩ := hεW ((ball_subset_ball (show r ≤ ε by linarith)) hz)
  exact ⟨zV, hzU, hfz⟩

theorem PairedComparisonPacket.isOpenMap_distanceCoordinates
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : ι → X} {a₀ A δ : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω) (hVopen : IsOpen V)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι))
    (hcomplete : ∀ q ∈ V, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall q R))
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    (p : ℝ≥0∞) : IsOpenMap (fun z : V => distanceCoordinates p a (z : X)) := by
  have h := ((PiLp.homeomorph p (fun _ : ι => ℝ)).symm.isOpenMap.comp
    (PiLp.homeomorph 1 (fun _ : ι => ℝ)).isOpenMap).comp
    (hpacket.isOpenMap_distanceCoordinates_one hcurves hcomp hV hVopen hanchors
      ha₀ hδ hδm hcomplete hbounds)
  exact h

end DifferentialGeometry.Geometry.Comparison.Toponogov
