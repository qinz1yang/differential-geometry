import DifferentialGeometry.Topology.Planar.SlitSeamCharts
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section
set_option autoImplicit false
open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology.Planar.SlitSeamCharts

private theorem slit_affine_displacement_bounds
    (ell : ℝ) {η : ℝ} (hη : 0 ≤ η) {w : ℂ}
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖Bplus ell η w - (ell / 4 : ℂ)‖ ≤ 4 * η ∧
      ‖Bminus ell η w - (-(ell / 4 : ℂ))‖ ≤ 4 * η ∧
      ‖T ell η w - Complex.I * (ell / 4 : ℂ)‖ ≤ 4 * η := by
  have hn : ‖w‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hre : |η * w.re| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    nlinarith [Complex.abs_re_le_norm w]
  have him : |η * w.im| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    nlinarith [Complex.abs_im_le_norm w]
  have him3 : |(3 * η / 2) * w.im| ≤ 3 * η / 2 := by
    have heq : (3 * η / 2) * w.im = (3 / 2 : ℝ) * (η * w.im) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  have hplus : ‖Bplus ell η w - (ell / 4 : ℂ)‖ ≤ 4 * η := by
    have heq : Bplus ell η w - (ell / 4 : ℂ) =
        Complex.mk (η * w.re + (3 * η / 2) * w.im) (η * w.im) := by
      apply Complex.ext <;> simp [Bplus]
      ring
    rw [heq]
    have hb := Complex.norm_le_abs_re_add_abs_im
      (Complex.mk (η * w.re + (3 * η / 2) * w.im) (η * w.im))
    change ‖Complex.mk (η * w.re + (3 * η / 2) * w.im) (η * w.im)‖ ≤
      |η * w.re + (3 * η / 2) * w.im| + |η * w.im| at hb
    have ha := abs_add_le (η * w.re) ((3 * η / 2) * w.im)
    linarith
  refine ⟨hplus, ?_, ?_⟩
  · have heq : Bminus ell η w - (-(ell / 4 : ℂ)) =
        -star (Bplus ell η w - (ell / 4 : ℂ)) := by
      apply Complex.ext <;> simp [Bminus, Bplus]
      ring
    rw [heq, norm_neg, norm_star]
    exact hplus
  · have heq : T ell η w - Complex.I * (ell / 4 : ℂ) =
        -(Complex.I * (η : ℂ) * w) := by
      simp only [T, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    rw [heq, norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη]
    nlinarith [norm_nonneg w]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

-- Exact private proof reused from PairedReplacementFoldLocalRank, lines 27–56.
private theorem exists_open_original_rank_neighborhood
    {Q : ℂ → M} (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q (Metric.ball 0 1))
    {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1)
    (hrank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q a)) :
    ∃ N : Set ℂ, IsOpen N ∧ a ∈ N ∧ N ⊆ Metric.ball (0 : ℂ) 1 ∧
      ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
  let S : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let F : S → M := fun z => Q z
  let aS : S := ⟨a, ha⟩
  have hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F :=
    hQ.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  have hDF : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F aS) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) aS : ℂ →L[ℝ] E)
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact hrank
  have hImm := DifferentialGeometry.Topology.Manifold.isImmersionAt_of_injective_mfderiv
    (by simp : (∞ : ℕ∞ω) ≠ 0) hF aS hDF
  let T : Set S := {z | IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ F z}
  have hT : IsOpen T := IsOpen.isImmersionAt
  refine ⟨Subtype.val '' T, Metric.isOpen_ball.isOpenMap_subtype_val T hT,
    ⟨aS, hImm, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩
    have hd := hz.mfderiv_injective (by simp : (∞ : ℕ∞ω) ≠ 0)
    change Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : S => Q z) z : ℂ →L[ℝ] E) at hd
    rw [DifferentialGeometry.mfderiv_restrict_open] at hd
    exact hd

/-- One common affine buffer stays in the original regular neighborhoods on
both sheets and in the original interior along the slit. The point-rank inputs
are discharged at the selected actual seam before this theorem is applied. -/
theorem exists_branch_slit_regular_buffer
    {Q : ℂ → M}
    (hQ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Q (Metric.ball 0 1))
    (κ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    {ell : ℝ} (hell : 0 < ell)
    (hp : (ell / 4 : ℂ) ∈ κ.source)
    (hm : (-(ell / 4 : ℂ)) ∈ κ.source)
    (ht : Complex.I * (ell / 4 : ℂ) ∈ κ.source)
    (hκ : Set.MapsTo κ κ.source (Metric.ball (0 : ℂ) 1))
    (hrankp : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (κ (ell / 4 : ℂ))))
    (hrankm : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q (κ (-(ell / 4 : ℂ))))) :
    ∃ Np Nm : Set ℂ, IsOpen Np ∧ IsOpen Nm ∧
      κ (ell / 4 : ℂ) ∈ Np ∧ κ (-(ell / 4 : ℂ)) ∈ Nm ∧
      Np ⊆ Metric.ball (0 : ℂ) 1 ∧ Nm ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∀ z ∈ Np, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) ∧
      (∀ z ∈ Nm, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z)) ∧
      ∃ η : ℝ, 0 < η ∧ η < ell / 16 ∧
        ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
          Bplus ell η w ∈ κ.source ∧ κ (Bplus ell η w) ∈ Np ∧
          Bminus ell η w ∈ κ.source ∧ κ (Bminus ell η w) ∈ Nm ∧
          T ell η w ∈ κ.source ∧ κ (T ell η w) ∈ Metric.ball (0 : ℂ) 1 := by
  obtain ⟨Np, hNp, hpNp, hNpball, hNprank⟩ :=
    exists_open_original_rank_neighborhood hQ (hκ hp) hrankp
  obtain ⟨Nm, hNm, hmNm, hNmball, hNmrank⟩ :=
    exists_open_original_rank_neighborhood hQ (hκ hm) hrankm
  have hcontp : ContinuousAt (κ : ℂ → ℂ) (ell / 4 : ℂ) :=
    κ.contMDiffOn_toFun.continuousOn.continuousAt (κ.open_source.mem_nhds hp)
  have hcontm : ContinuousAt (κ : ℂ → ℂ) (-(ell / 4 : ℂ)) :=
    κ.contMDiffOn_toFun.continuousOn.continuousAt (κ.open_source.mem_nhds hm)
  obtain ⟨rp, hrp, hballp⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (κ.open_source.mem_nhds hp) (hcontp.preimage_mem_nhds (hNp.mem_nhds hpNp)))
  obtain ⟨rm, hrm, hballm⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (κ.open_source.mem_nhds hm) (hcontm.preimage_mem_nhds (hNm.mem_nhds hmNm)))
  obtain ⟨rt, hrt, hballt⟩ := Metric.mem_nhds_iff.mp (κ.open_source.mem_nhds ht)
  let η : ℝ := min (ell / 32) (min rp (min rm rt) / 8)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηell : η < ell / 16 := by
    have hle : η ≤ ell / 32 := min_le_left _ _
    linarith
  have hηr : 8 * η ≤ min rp (min rm rt) := by
    have hle : η ≤ min rp (min rm rt) / 8 := min_le_right _ _
    linarith
  have hηp : 4 * η < rp := by
    have hle := min_le_left rp (min rm rt)
    linarith
  have hηm : 4 * η < rm := by
    have hle : min rp (min rm rt) ≤ rm := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hηt : 4 * η < rt := by
    have hle : min rp (min rm rt) ≤ rt := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨Np, Nm, hNp, hNm, hpNp, hmNm, hNpball, hNmball, hNprank, hNmrank,
    η, hη, hηell, ?_⟩
  intro w hw
  obtain ⟨hdp, hdm, hdt⟩ := slit_affine_displacement_bounds ell hη.le hw
  have hwp := hballp (show Bplus ell η w ∈ Metric.ball (ell / 4 : ℂ) rp by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hdp.trans_lt hηp)
  have hwm := hballm (show Bminus ell η w ∈ Metric.ball (-(ell / 4 : ℂ)) rm by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hdm.trans_lt hηm)
  have hwt := hballt (show T ell η w ∈ Metric.ball (Complex.I * (ell / 4 : ℂ)) rt by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hdt.trans_lt hηt)
  exact ⟨hwp.1, hwp.2, hwm.1, hwm.2, hwt, hκ hwt⟩

end DifferentialGeometry.Geometry
