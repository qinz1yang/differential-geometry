import DifferentialGeometry.Geometry.Comparison.PairedCoordinateMove

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

private theorem delta_le_hundredth {δ : ℝ}
    (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι)) : δ ≤ 1 / 100 := by
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm0 : (0 : ℝ) < Fintype.card ι := by linarith
  have h := (le_div_iff₀ (show 0 < 100 * (Fintype.card ι : ℝ) by positivity)).mp hδm
  nlinarith

theorem PairedComparisonPacket.exists_distance_residual_correction
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : ι → X} {x : X} {a₀ A δ T : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι))
    (hT1 : T ≤ 1) (hTa : T ≤ a₀ / 2)
    (hTK : T ≤ δ ^ 2 / (4 * cosh (A + 1) / sinh a₀))
    (hball : closedBall x T ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    {w : PiLp 1 (fun _ : ι => ℝ)} (he : 0 < dist (distanceCoordinates 1 a x) w)
    (hscale : ∀ i, dist (dist x (a i)) (w i) ≤ T) :
    let μ := 1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ
    ∃ y ∈ V, dist (distanceCoordinates 1 a x) w / Fintype.card ι ≤ dist x y ∧
      dist x y ≤ dist (distanceCoordinates 1 a x) w ∧
      dist (distanceCoordinates 1 a y) w ≤ (1 - μ / Fintype.card ι) * dist (distanceCoordinates 1 a x) w ∧
      μ * dist x y ≤ dist (distanceCoordinates 1 a x) w - dist (distanceCoordinates 1 a y) w := by
  have hδ1 := delta_le_hundredth hδ hδm
  have hconstants := paired_correction_constants Fintype.card_pos hδ hδm
  have hμ : 0 ≤ (1 - 3 * δ ^ 2) - (Fintype.card ι - 1 : ℝ) * (6 * δ) := by
    nlinarith [hconstants.1]
  have h := exists_residual_correction_of_coordinate_moves
    (f := distanceCoordinates 1 a) (w := w) (V := V) (t₀ := T)
    (α := 1 - 3 * δ ^ 2) (β := 6 * δ) hμ he hscale
    (fun i t ht htT => by
      obtain ⟨y, hy, hxy, hdir, hrest⟩ := hpacket.exists_distance_coordinate_move
        hcurves hcomp hV hanchors ha₀ hδ hδ1 ht (htT.trans hT1) (htT.trans hTa)
        (htT.trans hTK) ((closedBall_subset_closedBall htT).trans hball) hbounds i (w i)
      exact ⟨y, hy, hxy, hdir, hrest⟩)
  have hμeq : (1 - 3 * δ ^ 2) - (Fintype.card ι - 1 : ℝ) * (6 * δ) =
      1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ := by ring
  simpa only [hμeq] using h

theorem PairedComparisonPacket.exists_preimage_in_complete_buffer
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : ι → X} {q : X} {a₀ A δ r : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι))
    (hr : 0 < r) (hcomplete : IsComplete (closedBall q r)) (hbuffer : ball q (2 * r) ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A)
    {w : PiLp 1 (fun _ : ι => ℝ)}
    (he1 : dist (distanceCoordinates 1 a q) w ≤ 1)
    (hea : dist (distanceCoordinates 1 a q) w ≤ a₀ / 2)
    (heK : dist (distanceCoordinates 1 a q) w ≤ δ ^ 2 / (4 * cosh (A + 1) / sinh a₀))
    (hebuffer : dist (distanceCoordinates 1 a q) w ≤
      (1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ) * r / 2) :
    ∃ z ∈ closedBall q (r / 2), distanceCoordinates 1 a z = w ∧
      dist q z ≤ dist (distanceCoordinates 1 a q) w /
        (1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ) := by
  let μ := 1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ
  have hconstants := paired_correction_constants Fintype.card_pos hδ hδm
  change 9 / 10 ≤ μ ∧ μ < 1 ∧ 0 ≤ 1 - μ / Fintype.card ι ∧ 1 - μ / Fintype.card ι < 1 at hconstants
  have hμ : 0 < μ := by linarith [hconstants.1]
  change dist (distanceCoordinates 1 a q) w ≤ μ * r / 2 at hebuffer
  have her : dist (distanceCoordinates 1 a q) w ≤ r / 2 := by nlinarith [hconstants.2.1]
  obtain ⟨z, _, hfz, hd⟩ := exists_preimage_of_local_residual_correction
    hμ hconstants.2.2.1 hconstants.2.2.2 hcomplete
    (lipschitzWith_distanceCoordinates_one a).continuous.continuousOn
    (show dist (distanceCoordinates 1 a q) w ≤ μ * r by nlinarith)
    (fun x hx he heq => by
      have hballx : closedBall x (dist (distanceCoordinates 1 a q) w) ⊆ V := by
        intro y hy
        apply hbuffer
        rw [mem_ball]
        have hx' := mem_closedBall.mp hx
        have hy' := mem_closedBall.mp hy
        linarith [dist_triangle y x q]
      obtain ⟨y, _, _, _, hy, hb⟩ := hpacket.exists_distance_residual_correction
        hcurves hcomp hV hanchors ha₀ hδ hδm he1 hea heK hballx hbounds he
        (fun i => (PiLp.dist_apply_le (distanceCoordinates 1 a x) w i).trans heq)
      exact ⟨y, hy, hb⟩)
  refine ⟨z, ?_, hfz, hd⟩
  rw [mem_closedBall, dist_comm]
  apply hd.trans
  exact (div_le_iff₀ hμ).mpr (by nlinarith)

theorem PairedComparisonPacket.ball_subset_distanceCoordinates_image
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V : Set X} {a b : ι → X} {q : X} {a₀ A δ r : ℝ}
    (hpacket : PairedComparisonPacket δ V a b)
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : range a ∪ range b ⊆ Ω)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * Fintype.card ι))
    (hr : 0 < r) (hcomplete : IsComplete (closedBall q r)) (hbuffer : ball q (2 * r) ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ range a ∪ range b, dist z c ∈ Icc a₀ A) :
    let μ := 1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ
    let ε := min 1 (min (a₀ / 2) (min (δ ^ 2 / (4 * cosh (A + 1) / sinh a₀)) (μ * r / 2)))
    0 < ε ∧ ball (distanceCoordinates 1 a q) ε ⊆ distanceCoordinates 1 a '' ball q r := by
  let μ := 1 - 3 * δ ^ 2 - 6 * (Fintype.card ι - 1 : ℝ) * δ
  let K := 4 * cosh (A + 1) / sinh a₀
  let ε := min 1 (min (a₀ / 2) (min (δ ^ 2 / K) (μ * r / 2)))
  change 0 < ε ∧ _
  have hconstants := paired_correction_constants Fintype.card_pos hδ hδm
  have hμ : 0 < μ := by dsimp [μ]; linarith [hconstants.1]
  have hK : 0 < K := div_pos (mul_pos (by norm_num) (cosh_pos _)) (sinh_pos_iff.mpr ha₀)
  have hε : 0 < ε := lt_min zero_lt_one
    (lt_min (half_pos ha₀) (lt_min (div_pos (sq_pos_of_pos hδ) hK) (half_pos (mul_pos hμ hr))))
  refine ⟨hε, ?_⟩
  intro w hw
  have he : dist (distanceCoordinates 1 a q) w ≤ ε := by
    simpa only [mem_ball, dist_comm] using hw.le
  have he1 := he.trans (min_le_left _ _)
  have herest := he.trans (min_le_right _ _)
  have hea := herest.trans (min_le_left _ _)
  have heK := herest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hebuf := herest.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z, hz, hfz, _⟩ := hpacket.exists_preimage_in_complete_buffer hcurves hcomp hV hanchors
    ha₀ hδ hδm hr hcomplete hbuffer hbounds he1 hea heK hebuf
  refine ⟨z, ?_, hfz⟩
  exact (closedBall_subset_ball (show r / 2 < r by linarith)) hz

end DifferentialGeometry.Geometry.Comparison.Toponogov
