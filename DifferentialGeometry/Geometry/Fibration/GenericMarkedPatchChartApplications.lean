import DifferentialGeometry.Geometry.Fibration.GenericMarkedPatchChart
import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateOrthogonalGraphApplications

/-!
# Consumer of the naive CGP07 chain (G2 of lane C14-BASES-PRE)

Concrete data in `ℂ`: zero set `Z = {Im = 1}`, vector coordinate `u = Re`, marker `v = Im`,
`R = ℓ = 1`; the stage map is the real shift `f z = z + 1/200` of the source map `F' = id`
(cumulative error `c = 1/200`, scale `ρ ≡ 1`), the inner section `s b = b + i` (values `u = b`,
marker `v = 1`), threshold-6 domain `B⁶ = Z`; the local graph at every target is the zero graph
over the real axis based at `i`, on the ball of radius `6`. The Brouwer step is used with a
non-trivial shift. The assembly gives: `Re : V ≅ B(0, 5.5)` as sets, every point of `V` is a
shifted point of `B⁶`, a smooth inverse, compact preimages. `cgp07_one_sheet_horizontalLine_BPRE`
runs the primitive-data form: rough graph `Φ b = b + i` (`Ω = 1`), centers `x_a = a + i`, the
zero graph over the real axis at each center, the trivial (MW) witness `y = w`, (OS) with
`e = ε = 0`, `Σ = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

theorem im_eq_zero_of_mem_realAxis_BPRE {t : ℂ} (ht : t ∈ realAxis_BPRE) : t.im = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ht
  rw [← hc]
  simp

theorem horizontalLine_graph_eq_BPRE :
    {z : ℂ | z.im = 1} ∩ ball Complex.I 6 =
      {z | ∃ t ∈ ball (0 : realAxis_BPRE) 6,
        z = Complex.I + orthogonalCoordinateSum realAxis_BPRE (t, (fun _ => (0 : realAxis_BPREᗮ)) t)} ∩
      ball Complex.I 6 := by
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, and_congr_left_iff]
  intro hz
  constructor
  · intro him
    refine ⟨⟨(z.re : ℂ), ofRealCLM_mem_realAxis_BPRE z.re⟩, ?_, ?_⟩
    · rw [mem_ball_zero_iff, ← Submodule.norm_coe]
      rw [mem_ball, dist_eq_norm] at hz
      have h : z - Complex.I = (z.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      rwa [h] at hz
    · change z = Complex.I + ((z.re : ℂ) + 0)
      apply Complex.ext <;> simp [him]
  · rintro ⟨t, -, rfl⟩
    change (Complex.I + ((t : ℂ) + 0)).im = 1
    simp [im_eq_zero_of_mem_realAxis_BPRE t.property]

/-- **G2 consumer.** The naive CGP07 chain on the horizontal line `Im = 1` of `ℂ` with the shifted
stage map `z ↦ z + 1/200`. -/
theorem cgp07_horizontalLine_chart_BPRE :
    BijOn ((1 : ℝ)⁻¹ • Complex.reCLM)
        (markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1)
        (ball 0 (11 / 2 * 1)) ∧
    (∀ w ∈ markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1,
      ∃ p ∈ {z : ℂ | z.im = 1}, p + (1 / 200 : ℂ) = w) ∧
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ ∞ φ (ball 0 (11 / 2 * 1)) ∧
      InvOn φ ((1 : ℝ)⁻¹ • Complex.reCLM)
        (markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1)
        (ball 0 (11 / 2 * 1)) := by
  have hex := cgp07_existence_all_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.reCLM_norm.le
    Complex.imCLM Complex.imCLM_norm.le (fun z : ℂ => z + (1 / 200 : ℂ)) id
    (fun b : ℝ => (b : ℂ) + Complex.I) (fun _ => (1 : ℝ)) {z : ℂ | z.im = 1}
    (R := 1) (ℓ := 1) (c := 1 / 200) (r₀ := 1 / 100) one_pos (by norm_num) (by norm_num)
    (by norm_num) (fun a _ => by fun_prop)
    (fun a _ b _ => by simp)
    (fun a _ b _ => by
      simp only [id, add_sub_cancel_left, mul_one]
      rw [show (1 / 200 : ℂ) = ((1 / 200 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)])
    (fun a _ b _ => by norm_num)
    (fun a _ b _ => ⟨by simp, by simp⟩)
  have hgraph : ∀ a ∈ ball (0 : ℝ) (11 / 2 * 1), ∃ (x : ℂ) (ρ R₀ m s : ℝ)
      (L : Submodule ℝ ℂ) (g : L → Lᗮ), (∀ v' ∈ L, m * ‖v'‖ ≤ ‖Complex.reCLM v'‖) ∧ s < m ∧
      Module.finrank ℝ L = Module.finrank ℝ ℝ ∧ ContDiffOn ℝ ∞ g (ball 0 R₀) ∧
      (∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ g t‖ ≤ s) ∧
      {z : ℂ | z.im = 1} ∩ ball x ρ =
        {z | ∃ t ∈ ball (0 : L) R₀, z = x + orthogonalCoordinateSum L (t, g t)} ∩ ball x ρ ∧
      ∀ w ∈ markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1,
        ((1 : ℝ)⁻¹ • Complex.reCLM) w = a → w ∈ ball x ρ := by
    intro a _
    refine ⟨Complex.I, 6, 6, 1, 0, realAxis_BPRE, fun _ => 0, fun v' hv' => ?_, one_pos,
      finrank_realAxis_BPRE, contDiffOn_const, fun t _ => by simp, horizontalLine_graph_eq_BPRE,
      fun w hw _ => ?_⟩
    · have h0 := im_eq_zero_of_mem_realAxis_BPRE hv'
      have hv : v' = (v'.re : ℂ) := by apply Complex.ext <;> simp [h0]
      rw [one_mul, hv, Complex.norm_real]
      simp
    · obtain ⟨him, -, hre⟩ := hw
      change w.im = 1 at him
      rw [mem_ball, dist_eq_norm]
      have h : w - Complex.I = (w.re : ℂ) := by apply Complex.ext <;> simp [him]
      rw [h, Complex.norm_real]
      have : ‖w.re‖ ≤ ‖w‖ := by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm w
      change ‖w.re‖ < 6
      have hre' : ‖Complex.reCLM w‖ < 11 / 2 * 1 * 1 := hre
      simp only [Complex.reCLM_apply] at hre'
      linarith
  obtain ⟨hbij, hexh, φ, hφ, hinv, -, -⟩ := cgp07_marked_patch_chart_BPRE {z : ℂ | z.im = 1}
    Complex.reCLM Complex.reCLM_norm.le Complex.imCLM one_pos (fun z : ℂ => z + (1 / 200 : ℂ))
    {z : ℂ | z.im = 1} hgraph hex
  exact ⟨hbij, hexh, φ, hφ, hinv⟩

theorem horizontalLine_graph_eq_at_BPRE (c : ℝ) :
    {z : ℂ | z.im = 1} ∩ ball ((c : ℂ) + Complex.I) 6 =
      {z | ∃ t ∈ ball (0 : realAxis_BPRE) 6, z = ((c : ℂ) + Complex.I) +
        orthogonalCoordinateSum realAxis_BPRE (t, (fun _ => (0 : realAxis_BPREᗮ)) t)} ∩
      ball ((c : ℂ) + Complex.I) 6 := by
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, and_congr_left_iff]
  intro hz
  constructor
  · intro him
    refine ⟨⟨((z.re - c : ℝ) : ℂ), ofRealCLM_mem_realAxis_BPRE (z.re - c)⟩, ?_, ?_⟩
    · rw [mem_ball_zero_iff, ← Submodule.norm_coe]
      rw [mem_ball, dist_eq_norm] at hz
      have h : z - ((c : ℂ) + Complex.I) = ((z.re - c : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      rwa [h] at hz
    · change z = ((c : ℂ) + Complex.I) + (((z.re - c : ℝ) : ℂ) + 0)
      apply Complex.ext <;> simp [him]
  · rintro ⟨t, -, rfl⟩
    change ((c : ℂ) + Complex.I + ((t : ℂ) + 0)).im = 1
    simp [im_eq_zero_of_mem_realAxis_BPRE t.property]

theorem re_lower_bound_realAxis_BPRE : ∀ v' ∈ realAxis_BPRE, 1 * ‖v'‖ ≤ ‖Complex.reCLM v'‖ := by
  intro v' hv'
  have h0 := im_eq_zero_of_mem_realAxis_BPRE hv'
  have hv : v' = (v'.re : ℂ) := by apply Complex.ext <;> simp [h0]
  rw [one_mul, hv, Complex.norm_real]
  simp

/-- **G2 consumer (primitive-data CGP07).** -/
theorem cgp07_one_sheet_horizontalLine_BPRE :
    BijOn ((1 : ℝ)⁻¹ • Complex.reCLM)
        (markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1)
        (ball 0 (11 / 2 * 1)) ∧
    (∀ w ∈ markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1,
      ∃ p ∈ {z : ℂ | z.im = 1}, p + (1 / 200 : ℂ) = w) ∧
    ∀ K ⊆ ball (0 : ℝ) (11 / 2 * 1), IsCompact K →
      IsCompact (markedPatch_BPRE {z : ℂ | z.im = 1} Complex.reCLM Complex.imCLM 1 1 ∩
        ((1 : ℝ)⁻¹ • Complex.reCLM) ⁻¹' K) := by
  have hΦd : ∀ b : ℝ, HasFDerivAt (fun b : ℝ => (b : ℂ) + Complex.I) Complex.ofRealCLM b :=
    fun b => Complex.ofRealCLM.hasFDerivAt.add_const Complex.I
  obtain ⟨h1, h2, -, -, -, -, h7⟩ := cgp07_one_sheet_BPRE {z : ℂ | z.im = 1} Complex.reCLM
    Complex.reCLM_norm.le Complex.imCLM Complex.imCLM_norm.le (R := 1) (ℓ := 1) (Ω := 1) (e := 0)
    (ε := 0) (S := 1) (c := 1 / 200) (r₀ := 1 / 100) one_pos le_rfl one_pos (by norm_num) le_rfl
    (by positivity) (fun b : ℝ => (b : ℂ) + Complex.I) convex_univ
    (fun b _ => (hΦd b).differentiableAt)
    (fun b _ => by rw [(hΦd b).fderiv, Complex.ofRealCLM_norm])
    (fun a : ℝ => (a : ℂ) + Complex.I) (fun _ => 1) (fun _ => 6)
    (fun a _ => ⟨trivial, by simp, by norm_num, by norm_num⟩)
    (fun a _ => ⟨6, 1, 0, realAxis_BPRE, fun _ => 0, re_lower_bound_realAxis_BPRE, one_pos,
      finrank_realAxis_BPRE, contDiffOn_const, fun t _ => by simp,
      horizontalLine_graph_eq_at_BPRE a⟩)
    (fun w hw => ⟨w, w.re, trivial, by
      have him : w.im = 1 := hw.1
      have h0 : (1 : ℝ)⁻¹ • w - ((w.re : ℂ) + Complex.I) = 0 := by
        apply Complex.ext <;> simp [him]
      rw [h0, norm_zero], by simp, by simp⟩)
    (fun z : ℂ => z + (1 / 200 : ℂ)) id (fun b : ℝ => (b : ℂ) + Complex.I) (fun _ => (1 : ℝ))
    {z : ℂ | z.im = 1} (by norm_num) (by norm_num) (by norm_num) (fun a _ => by fun_prop)
    (fun a _ b _ => by simp)
    (fun a _ b _ => by
      simp only [id, add_sub_cancel_left, mul_one]
      rw [show (1 / 200 : ℂ) = ((1 / 200 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)])
    (fun a _ b _ => by norm_num)
    (fun a _ b _ => ⟨by simp, by simp⟩)
  exact ⟨h1, h2, h7⟩

end DifferentialGeometry.Geometry.Collapse
