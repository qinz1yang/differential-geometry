import DifferentialGeometry.Geometry.Comparison.RankExclusionLower
import DifferentialGeometry.Geometry.Comparison.PairedDistanceOpenness
import DifferentialGeometry.Topology.MetricSpace.LipschitzHomeomorph

set_option autoImplicit false

open Set Real Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

theorem PairedComparisonPacket.exists_chart_of_rank_exclusion
    {δ β : ℝ} {V Ω : Set X} {a b : ι → X}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω) {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hβ : 0 < β) (hβm : β ≤ 1 / (200 * ((Fintype.card ι : ℝ) + 1)))
    (hδ : 0 < δ) (hδβ : δ ≤ β / 100)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    (hcomplete : ∀ z ∈ V, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    (hno : ∀ z ∈ V, ∀ c d : Option ι → X, range c ∪ range d ⊆ Ω →
      ¬ PairedComparisonPacket β {z} c d)
    {q : X} {r : ℝ} (hr : 0 < r) (hbuf : ball q (3 * r) ⊆ V)
    (hr1 : 2 * r ≤ 1) (hra : 2 * r ≤ a₀ / 2)
    (hrK : 2 * r ≤ (β / (100 * Real.pi)) ^ 2 / (4 * cosh (A + 1) / sinh a₀)) :
    ∃ U : Set (PiLp 2 (fun _ : ι => ℝ)), IsOpen U ∧
      ∃ e : ball q r ≃ₜ U, (∀ z, (e z : PiLp 2 (fun _ : ι => ℝ)) = distanceCoordinates 2 a (z : X)) ∧
        (∀ x y, (β / (100 * Real.pi)) ^ 2 * dist x y ≤ dist (e x) (e y)) ∧
        LipschitzWith (NNReal.sqrt (Fintype.card ι)) e ∧
        LipschitzWith (⟨(β / (100 * Real.pi)) ^ 2, sq_nonneg _⟩ : ℝ≥0)⁻¹ e.symm := by
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hden : 0 < 200 * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hβ1 : β ≤ 1 := hβm.trans ((div_le_one hden).mpr (by nlinarith))
  have hδm : δ ≤ 1 / (100 * Fintype.card ι) :=
    (show δ ≤ β by linarith).trans (hβm.trans
      (one_div_le_one_div_of_le (by positivity) (by nlinarith)))
  have hB : ball q r ⊆ V := (ball_subset_ball (show r ≤ 3 * r by linarith)).trans hbuf
  let F := fun z : ball q r => distanceCoordinates 2 a (z : X)
  have hopen : IsOpenMap F := (hpacket.mono hB).isOpenMap_distanceCoordinates
    hcurves hcomp (hB.trans hV) isOpen_ball hanchors ha₀ hδ hδm
    (fun z hz => hcomplete z (hB hz)) (fun z hz c hc => hbounds z (hB hz) c hc) 2
  have hLip : LipschitzWith (NNReal.sqrt (Fintype.card ι)) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (lipschitzWith_distanceCoordinates_two a).dist_le_mul x y
  let ε : ℝ≥0 := ⟨(β / (100 * Real.pi)) ^ 2, sq_nonneg _⟩
  have hε : 0 < ε := by change 0 < (β / (100 * Real.pi)) ^ 2; positivity
  have hlower (x y : ball q r) : (ε : ℝ) * dist x y ≤ dist (F x) (F y) :=
    hpacket.distanceCoordinates_lower_of_rank_exclusion hcurves hcomp hV hanchors
      ha₀ hβ hβ1 hδ.le hδβ hbounds hno hbuf hr1 hra hrK x.property y.property
  obtain ⟨e, he, heLip, heInv⟩ := exists_homeomorph_range_of_lipschitz_lower_bound hLip hε hlower
  refine ⟨range F, hopen.isOpen_range, e, he, ?_, heLip, heInv⟩
  intro x y
  change (ε : ℝ) * dist x y ≤ dist (e x : PiLp 2 (fun _ : ι => ℝ)) (e y : PiLp 2 (fun _ : ι => ℝ))
  rw [he, he]
  exact hlower x y

end DifferentialGeometry.Geometry.Comparison.Toponogov
