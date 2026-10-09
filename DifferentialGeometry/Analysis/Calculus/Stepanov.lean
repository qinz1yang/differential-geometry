/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Tactic.Ext

noncomputable section

open Set Filter Metric MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Stepanov

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (μ : Measure E) [IsAddHaarMeasure μ]

theorem ae_relative_dense {s : Set E} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ.restrict s, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 x, ∃ z ∈ s, dist y z ≤ ε * dist y x := by
  have hd (k : ℕ) :=
    IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ s ((k : ℝ) + 1)
  filter_upwards [ae_all_iff.2 hd, ae_restrict_mem hs] with x hx hxs
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hkp : 0 < (k : ℝ) + 1 := by positivity
  have hlim : Tendsto (fun y : E => dist y x / ((k : ℝ) + 1))
      (𝓝[≠] x) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous (fun y : E => dist y x / ((k : ℝ) + 1)) :=
        (continuous_id.dist continuous_const).div_const _
      simpa only [dist_self, zero_div] using (hc.tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact div_pos (dist_pos.mpr hy) hkp
  have hcent : ∀ᶠ y in 𝓝[≠] x,
      x ∈ closedBall y (((k : ℝ) + 1) * (dist y x / ((k : ℝ) + 1))) := by
    filter_upwards with y
    have he : ((k : ℝ) + 1) * (dist y x / ((k : ℝ) + 1)) = dist y x := by
      field_simp
    rw [he]
    simp [dist_comm]
  have ht := hx k (fun y : E => y) (fun y => dist y x / ((k : ℝ) + 1)) hlim hcent
  have hn : ∀ᶠ y in 𝓝[≠] x, ∃ z ∈ s, dist y z ≤ ε * dist y x := by
    filter_upwards [ht.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))]
      with y hy
    have hm : μ (s ∩ closedBall y (dist y x / ((k : ℝ) + 1))) ≠ 0 := by
      intro he
      simp [he] at hy
    obtain ⟨z, hz, hzy⟩ := nonempty_of_measure_ne_zero hm
    refine ⟨z, hz, ?_⟩
    calc
      dist y z ≤ dist y x / ((k : ℝ) + 1) := by
        simpa [dist_comm] using hzy
      _ ≤ ε * dist y x := by
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right (by simpa [one_div] using hk.le) dist_nonneg
  exact eventually_nhdsWithin_iff.1 hn |>.mono fun y hy => by
    by_cases hyx : y = x
    · subst y
      exact ⟨x, hxs, by simp⟩
    · exact hy hyx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] in
theorem hasFDerivAt_of_relative_dense {s : Set E} {f : E → F}
    {x : E} {A : E →L[ℝ] F} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hbound : ∀ z ∈ s, ∀ y, dist y z < r → dist (f y) (f z) ≤ C * dist y z)
    (hdense : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 x, ∃ z ∈ s, dist y z ≤ ε * dist y x)
    (hA : HasFDerivWithinAt f A s x) : HasFDerivAt f A x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let δ := min 1 (ε / (2 * (C + ‖A‖ + 1)))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : (C + ‖A‖) * δ ≤ ε / 2 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 2 * (C + ‖A‖ + 1))).mp
      (min_le_right 1 (ε / (2 * (C + ‖A‖ + 1))))
    change δ * (2 * (C + ‖A‖ + 1)) ≤ ε at hb
    nlinarith [hδ.le]
  obtain ⟨u, hu, hxu, huA⟩ := mem_nhdsWithin.mp (hA.isLittleO.def (by positivity : 0 < ε / 4))
  obtain ⟨a, ha, hau⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds hxu)
  filter_upwards [hdense δ hδ, ball_mem_nhds x (half_pos ha),
      ball_mem_nhds x hr] with y hy hya hyr
  obtain ⟨z, hzs, hyz⟩ := hy
  have hyz' : dist y z ≤ dist y x := by
    exact hyz.trans (mul_le_of_le_one_left dist_nonneg hδ1)
  have hzx : dist z x ≤ 2 * dist y x := by
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ ≤ 2 * dist y x := by rw [dist_comm z y]; linarith
  have hzu : z ∈ u := hau (by
    change dist z x < a
    have : dist y x < a / 2 := hya
    linarith)
  have hrem : ‖f z - f x - A (z - x)‖ ≤ (ε / 4) * dist z x := by
    simpa [dist_eq_norm] using huA ⟨hzu, hzs⟩
  have hb : ‖f y - f z‖ ≤ C * dist y z := by
    simpa [dist_eq_norm] using hbound z hzs y (hyz'.trans_lt hyr)
  have hid : f y - f x - A (y - x) =
      (f y - f z) + (f z - f x - A (z - x)) + A (z - y) := by
    rw [map_sub, map_sub, map_sub]
    abel
  calc
    ‖f y - f x - A (y - x)‖
        ≤ ‖f y - f z‖ + ‖f z - f x - A (z - x)‖ + ‖A (z - y)‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * dist y z + (ε / 4) * dist z x + ‖A‖ * dist y z := by
      apply add_le_add (add_le_add hb hrem)
      simpa [dist_eq_norm, norm_sub_rev] using A.le_opNorm (z - y)
    _ ≤ C * (δ * dist y x) + (ε / 4) * (2 * dist y x) +
        ‖A‖ * (δ * dist y x) := by gcongr
    _ = ((C + ‖A‖) * δ + ε / 2) * dist y x := by ring
    _ ≤ ε * ‖y - x‖ := by
      rw [← dist_eq_norm]
      gcongr
      linarith

def centeredPiece (f : E → F) (N k : ℕ) : Set E :=
  {x | ∀ y, dist y x < ((k : ℝ) + 1)⁻¹ →
    dist (f y) (f x) ≤ (N : ℝ) * dist y x}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem isClosed_centeredPiece {f : E → F} (hf : Continuous f) (N k : ℕ) :
    IsClosed (centeredPiece f N k) := by
  have he : centeredPiece f N k = ⋂ y : E,
      {x | ((k : ℝ) + 1)⁻¹ ≤ dist y x ∨ dist (f y) (f x) ≤ (N : ℝ) * dist y x} := by
    ext x
    simp only [centeredPiece, mem_ofPred_eq, mem_iInter, ← not_lt, ← imp_iff_not_or]
  rw [he]
  apply isClosed_iInter
  intro y
  exact (isClosed_le continuous_const (continuous_const.dist continuous_id)).union
    (isClosed_le (continuous_const.dist hf)
      (continuous_const.mul (continuous_const.dist continuous_id)))

def smallPiece (f : E → F) (N k j : ℕ) : Set E :=
  centeredPiece f N k ∩ ball (denseSeq E j) (((k : ℝ) + 1)⁻¹ / 3)

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem measurableSet_smallPiece {f : E → F} (hf : Continuous f) (N k j : ℕ) :
    MeasurableSet (smallPiece f N k j) :=
  (isClosed_centeredPiece hf N k).measurableSet.inter measurableSet_ball

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem lipschitzOnWith_smallPiece (f : E → F) (N k j : ℕ) :
    LipschitzOnWith (N : ℝ≥0) f (smallPiece f N k j) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  apply hy.1 x
  have hxy := dist_triangle_right x y (denseSeq E j)
  have hk : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  have hxb : dist x (denseSeq E j) < ((k : ℝ) + 1)⁻¹ / 3 := hx.2
  have hyb : dist y (denseSeq E j) < ((k : ℝ) + 1)⁻¹ / 3 := hy.2
  linarith

theorem ae_differentiableAt_smallPiece {f : E → F} (hf : Continuous f) (N k j : ℕ) :
    ∀ᵐ x ∂μ, x ∈ smallPiece f N k j → DifferentiableAt ℝ f x := by
  have hs := measurableSet_smallPiece hf N k j
  have hd : ∀ᵐ x ∂μ, x ∈ smallPiece f N k j →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ y in 𝓝 x, ∃ z ∈ smallPiece f N k j, dist y z ≤ ε * dist y x :=
    (ae_restrict_iff' hs).mp (ae_relative_dense μ hs)
  filter_upwards [hd, (lipschitzOnWith_smallPiece f N k j).ae_differentiableWithinAt_of_mem
      (μ := μ)] with x hx hdx hxs
  obtain ⟨A, hA⟩ := hdx hxs
  exact (hasFDerivAt_of_relative_dense (Nat.cast_nonneg N) (by positivity)
    (fun z hz => hz.1) (hx hxs) hA).differentiableAt

theorem ae_differentiableAt_of_ae_centered_bound {f : E → F} (hf : Continuous f)
    (hbound : ∀ᵐ x ∂μ, ∃ C r : ℝ, 0 < r ∧
      ∀ y, dist y x < r → dist (f y) (f x) ≤ C * dist y x) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  have hd : ∀ᵐ x ∂μ, ∀ N k j : ℕ,
      x ∈ smallPiece f N k j → DifferentiableAt ℝ f x :=
    ae_all_iff.2 fun N => ae_all_iff.2 fun k =>
      ae_all_iff.2 fun j => ae_differentiableAt_smallPiece μ hf N k j
  filter_upwards [hd, hbound] with x hx hxb
  obtain ⟨C, r, hr, hb⟩ := hxb
  obtain ⟨N, hN⟩ := exists_nat_gt C
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
  obtain ⟨j, hj⟩ := (denseRange_denseSeq E).exists_dist_lt x
    (by positivity : 0 < ((k : ℝ) + 1)⁻¹ / 3)
  apply hx N k j
  refine ⟨?_, ?_⟩
  · intro y hy
    exact (hb y (hy.trans (by simpa [one_div] using hk))).trans
      (mul_le_mul_of_nonneg_right hN.le dist_nonneg)
  · simpa [dist_comm] using hj

end DifferentialGeometry.Stepanov
