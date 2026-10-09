import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization
import DifferentialGeometry.Geometry.Comparison.ModelAngleStability

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v w

theorem PairedComparisonPacket.exists_uniform_metric_perturbation
    {X : Type u} [MetricSpace X] {ι : Type w} {q : X} {a b : ι → X}
    {τ δ a₀ A rmax : ℝ} (hpacket : PairedComparisonPacket τ {q} a b)
    (hquality : τ < δ) (ha₀ : 0 < a₀) (hrmax : 0 < rmax)
    (hbounds : ∀ j : ι ⊕ ι, dist q (Sum.elim a b j) ∈ Icc a₀ A) :
    ∃ η r : ℝ, 0 < η ∧ 0 < r ∧ r < rmax ∧
      ∀ (Y : Type v) [MetricSpace Y] (y : Y) (c : ι ⊕ ι → Y),
        (∀ j, |dist y (c j) - dist q (Sum.elim a b j)| < η) →
        (∀ j k, |dist (c j) (c k) - dist (Sum.elim a b j) (Sum.elim a b k)| < η) →
        PairedComparisonPacket δ (ball y (2 * r)) (c ∘ Sum.inl) (c ∘ Sum.inr) ∧
          ∀ z ∈ ball y (2 * r), ∀ j, dist z (c j) ∈ Icc (a₀ / 2) (A + 1) := by
  obtain ⟨ξ, hξ, hangle⟩ := comparisonAngleNegCurvature_uniform_stability_on_side_window
    (κ := 1) (Lmax := A + 1) (by norm_num) (half_pos ha₀) (sub_pos.mpr hquality)
  let η := min (a₀ / 4) (min (1 / 4) (ξ / 4))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hηa : η ≤ a₀ / 4 := min_le_left _ _
  have hη1 : η ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηξ : η ≤ ξ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let r := min (rmax / 2) (η / 4)
  have hr : 0 < r := lt_min (half_pos hrmax) (by positivity)
  have hrmax' : r < rmax := (min_le_left _ _).trans_lt (by linarith)
  have hrη : r ≤ η / 4 := min_le_right _ _
  refine ⟨η, r, hη, hr, hrmax', ?_⟩
  intro Y _ y c hcentral hpair
  have hdiff (z : Y) (hz : z ∈ ball y (2 * r)) (j : ι ⊕ ι) :
      |dist z (c j) - dist q (Sum.elim a b j)| < 2 * η := by
    have hz' := mem_ball.mp hz
    have htri := abs_dist_sub_le z y (c j)
    obtain ⟨hlo, hhi⟩ := abs_lt.mp (hcentral j)
    obtain ⟨htlo, hthi⟩ := abs_le.mp htri
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hwin (z : Y) (hz : z ∈ ball y (2 * r)) (j : ι ⊕ ι) :
      dist z (c j) ∈ Icc (a₀ / 2) (A + 1) := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp (hdiff z hz j)
    obtain ⟨ha, hA⟩ := hbounds j
    constructor <;> linarith
  have hbase (j : ι ⊕ ι) : dist q (Sum.elim a b j) ∈ Icc (a₀ / 2) (A + 1) := by
    obtain ⟨ha, hA⟩ := hbounds j
    constructor <;> linarith
  have hcompare (z : Y) (hz : z ∈ ball y (2 * r)) (j k : ι ⊕ ι) :
      |comparisonAngleNegCurvature 1
          (dist z (c j)) (dist z (c k)) (dist (c j) (c k)) -
        comparisonAngleNegCurvature 1 (dist q (Sum.elim a b j))
          (dist q (Sum.elim a b k)) (dist (Sum.elim a b j) (Sum.elim a b k))| < δ - τ := by
    apply hangle _ _ _ _ _ _ (hwin z hz j) (hwin z hz k) ?_
      (hbase j) (hbase k) ?_ (by linarith [hdiff z hz j])
      (by linarith [hdiff z hz k]) (by linarith [hpair j k])
    · refine ⟨dist_nonneg, ?_⟩
      have ht := dist_triangle (c j) z (c k)
      rw [dist_comm (c j) z] at ht
      linarith [(hwin z hz j).2, (hwin z hz k).2]
    · refine ⟨dist_nonneg, ?_⟩
      have ht := dist_triangle (Sum.elim a b j) q (Sum.elim a b k)
      rw [dist_comm (Sum.elim a b j) q] at ht
      linarith [(hbase j).2, (hbase k).2]
  refine ⟨⟨?_, ?_⟩, hwin⟩
  · intro z hz i
    have hh := (abs_lt.mp (hcompare z hz (Sum.inl i) (Sum.inr i))).1
    have hp := hpacket.opposite q (by simp) i
    simp only [Sum.elim_inl, Sum.elim_inr] at hh
    change Real.pi - δ < comparisonAngleNegCurvature 1 (dist z (c (Sum.inl i)))
      (dist z (c (Sum.inr i))) (dist (c (Sum.inl i)) (c (Sum.inr i)))
    linarith
  · intro z hz i j hij u hu v hv
    rcases (by simpa only [mem_insert_iff, mem_singleton_iff, Function.comp_apply] using hu :
      u = c (Sum.inl i) ∨ u = c (Sum.inr i)) with rfl | rfl <;>
      rcases (by simpa only [mem_insert_iff, mem_singleton_iff, Function.comp_apply] using hv :
        v = c (Sum.inl j) ∨ v = c (Sum.inr j)) with rfl | rfl
    · have hh := (abs_lt.mp (hcompare z hz (Sum.inl i) (Sum.inl j))).1
      have hp := hpacket.cross q (by simp) i j hij (a i) (by simp) (a j) (by simp)
      simp only [Sum.elim_inl] at hh
      linarith
    · have hh := (abs_lt.mp (hcompare z hz (Sum.inl i) (Sum.inr j))).1
      have hp := hpacket.cross q (by simp) i j hij (a i) (by simp) (b j) (by simp)
      simp only [Sum.elim_inl, Sum.elim_inr] at hh
      linarith
    · have hh := (abs_lt.mp (hcompare z hz (Sum.inr i) (Sum.inl j))).1
      have hp := hpacket.cross q (by simp) i j hij (b i) (by simp) (a j) (by simp)
      simp only [Sum.elim_inl, Sum.elim_inr] at hh
      linarith
    · have hh := (abs_lt.mp (hcompare z hz (Sum.inr i) (Sum.inr j))).1
      have hp := hpacket.cross q (by simp) i j hij (b i) (by simp) (b j) (by simp)
      simp only [Sum.elim_inr] at hh
      linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
