import DifferentialGeometry.Topology.Morse.ExtremumChart
import DifferentialGeometry.Topology.Morse.RegularLevel.NoCriticalValues
import DifferentialGeometry.Topology.Morse.QuadraticSublevel
import DifferentialGeometry.Topology.Handle.SphereComplement

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem isConnected_superlevel_of_no_critical_values_above_minimum (m : ℕ)
    {f : sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1 → ℝ}
    (hf : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {p : sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1}
    (hnd : IsNondegenerateCriticalPointAt (𝓡 (m + 1)) f p)
    (hmin : ∀ x, x ≠ p → f p < f x) {a : ℝ} (ha : f p < a)
    (hregular : ∀ x, f x ∈ Ioc (f p) a → ¬ IsCriticalPointAt (𝓡 (m + 1)) f x) :
    IsConnected {x | a < f x} := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 := by simp
  have hm : IsMinOn f univ p := by
    intro x _
    by_cases hx : x = p
    · exact le_of_eq (congrArg f hx).symm
    · exact (hmin x hx).le
  have hchart₀ := exists_quadratic_chart_of_isLocalMin hf hnd
    (hm.isLocalMin Filter.univ_mem)
  rw [hdim] at hchart₀
  obtain ⟨R, hR, χ₀, hsource₀, hχ₀0, hnormal₀⟩ := hchart₀
  have hzero₀ : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ χ₀.source := hsource₀ ▸ mem_ball_self hR
  obtain ⟨R₀, hR₀, hsrc₀, hsub₀⟩ :=
    χ₀.toOpenPartialHomeomorph.exists_closedBall_image_sublevel_of_unique_minimum
      hzero₀ hf.continuous (by norm_num : (0 : ℝ) < 1)
      (fun y hy => by
        change f (χ₀ y) = f (χ₀ 0) + 1 / 2 * ‖y‖ ^ 2
        rw [hχ₀0, hnormal₀ y hy]
        ring)
      (by simpa only [show χ₀.toOpenPartialHomeomorph 0 = p from hχ₀0] using hmin)
  simp only [show χ₀.toOpenPartialHomeomorph 0 = p from hχ₀0] at hsub₀
  obtain ⟨r₀, hr₀, hr₀small⟩ := exists_between
    (lt_min hR₀ (Real.sqrt_pos.mpr (sub_pos.mpr ha)))
  have hr₀R : r₀ ≤ R₀ := (hr₀small.trans_le (min_le_left _ _)).le
  have hr₀sq : r₀ ^ 2 < a - f p := by
    have h := sq_lt_sq₀ hr₀.le (Real.sqrt_nonneg (a - f p)) |>.mpr
      (hr₀small.trans_le (min_le_right _ _))
    rwa [Real.sq_sqrt (sub_pos.mpr ha).le] at h
  let b := f p + 1 / 2 * r₀ ^ 2
  have hmb : f p < b := by dsimp [b]; nlinarith [sq_pos_of_pos hr₀]
  have hba : b < a := by dsimp [b]; nlinarith [sq_nonneg r₀]
  have hr₀src : closedBall 0 r₀ ⊆ χ₀.source :=
    (closedBall_subset_closedBall hr₀R).trans hsrc₀
  let u := fun x : ClosedCell (m + 1) => χ₀ (r₀ • x.val)
  have hu : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u :=
    isSmoothEmbedding_scaled_closedCell_sphere_chart m χ₀ hr₀ hr₀src
  have hurange : range u = χ₀ '' closedBall 0 r₀ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨r₀ • z.val, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr₀]
      exact (mul_le_mul_of_nonneg_left z.property hr₀.le).trans_eq (mul_one _)
    · rintro ⟨z, hz, rfl⟩
      have hn : ‖r₀⁻¹ • z‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₀)]
        simpa only [inv_mul_cancel₀ hr₀.ne'] using
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) (inv_nonneg.mpr hr₀.le)
      refine ⟨⟨r₀⁻¹ • z, hn⟩, ?_⟩
      change χ₀ (r₀ • (r₀⁻¹ • z)) = χ₀ z
      rw [smul_smul, mul_inv_cancel₀ hr₀.ne', one_smul]
  have hlow : IsConnected {x | b < f x} := by
    have hc := isConnected_compl_range_closedCell_sphere m hu
    have hlevel : χ₀ '' closedBall 0 r₀ = {x | f x ≤ b} := (hsub₀ r₀ hr₀.le hr₀R).1
    rw [hurange, hlevel] at hc
    convert hc using 1
    ext x
    change b < f x ↔ ¬ f x ≤ b
    exact lt_iff_not_ge
  obtain ⟨D, hD⟩ := no_critical_values f hf hba.le
    (isClosed_Icc.preimage hf.continuous).isCompact (fun x hx => hregular x ⟨hmb.trans_le hx.1, hx.2⟩)
  have hDcompl : D.toEquiv '' {x | b < f x} = {x | a < f x} := by
    have h := D.toEquiv.image_compl (sublevel f b)
    rw [hD] at h
    have hcompl (t : ℝ) : (sublevel f t)ᶜ = {x | t < f x} := by
      ext x
      change ¬ f x ≤ t ↔ t < f x
      exact not_le
    simpa only [hcompl] using h
  rw [← hDcompl]
  exact hlow.image D D.contMDiff.continuous.continuousOn

end DifferentialGeometry.Topology.Morse
