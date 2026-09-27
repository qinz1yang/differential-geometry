/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SmoothNormalForm
import DifferentialGeometry.Topology.Morse.ConnectingOrbit

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Morse

private theorem norm_le_of_sum_sq_eq {r : ℝ} (hr : 0 ≤ r) {z : MorseModel 2}
    (hz : z 0 ^ 2 + z 1 ^ 2 = r ^ 2) : ‖z‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  fin_cases i
  · change |z 0| ≤ r
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z 1)]
  · change |z 1| ≤ r
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (z 0)]

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H} [IsManifold I ∞ M] [T2Space M]

theorem exists_minimum_section_of_descendingConnection {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    {p q : M} (hq : I.IsInteriorPoint q) (hnd : IsNondegenerateCriticalPointAt I f q)
    (hindex : sigNeg (chartHessianAt (fun y => f ((extChartAt I q).symm y))
      (extChartAt I q q)) = 0) {γ : ℝ → M}
    (hγ : IsDescendingConnection I f v p q γ) (T₀ : ℝ)
    {O : Set M} (hO : IsOpen O) (hqO : q ∈ O) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, MorseModel 2) I (MorseModel 2) M ∞,
      0 ∈ χ.source ∧ χ 0 = q ∧
      (∀ z ∈ χ.source, f (χ z) = f q + (z 0 ^ 2 + z 1 ^ 2) / 2) ∧
      ∃ r T : ℝ, 0 < r ∧ T₀ < T ∧
        f (γ T) = f q + r ^ 2 / 2 ∧ f q + r ^ 2 / 2 ∈ Ioo (f q) (f p) ∧
        (∀ z, ‖z‖ ≤ r → z ∈ χ.source ∧ χ z ∈ O) ∧
        χ '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2} ⊆ O ∧
        Topology.IsClosedEmbedding
          (fun z : {z : MorseModel 2 // z 0 ^ 2 + z 1 ^ 2 = r ^ 2} => χ z) ∧
        χ '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2} =
          χ.target ∩ f ⁻¹' {f q + r ^ 2 / 2} ∧
        γ T ∈ χ '' {z : MorseModel 2 | z 0 ^ 2 + z 1 ^ 2 = r ^ 2} := by
  obtain ⟨χ, hχ0, hχq, hn, _⟩ := exists_interior_morse_normal_form I f hf q
    hq 0 (by decide) hnd hindex
  have hnormal (z : MorseModel 2) (hz : z ∈ χ.source) :
      f (χ z) = f q + (z 0 ^ 2 + z 1 ^ 2) / 2 := by
    rw [hn z hz]
    simp only [morseNormalForm, Fin.sum_univ_zero, Nat.sub_zero, Fin.sum_univ_two, posIdx]
    change f q + 1 / 2 * (0 + (z 0 ^ 2 + z 1 ^ 2)) = _
    ring
  have hnhds : χ.source ∩ χ ⁻¹' O ∈ 𝓝 (0 : MorseModel 2) :=
    inter_mem (χ.open_source.mem_nhds hχ0)
      ((χ.contMDiffOn.continuousOn.continuousAt (χ.open_source.mem_nhds hχ0)).preimage_mem_nhds
        (hO.mem_nhds (hχq.symm ▸ hqO)))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hsmall : Metric.ball (0 : MorseModel 2) (δ / 4) ⊆ χ.source := by
    intro z hz
    exact (hball (Metric.ball_subset_ball (by linarith) hz)).1
  have hopen := χ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hsmall
  have hqimage : q ∈ χ '' Metric.ball (0 : MorseModel 2) (δ / 4) :=
    ⟨0, by simpa only [Metric.mem_ball, dist_self] using (by positivity : 0 < δ / 4), hχq⟩
  obtain ⟨T, hT, z, hz, hzT⟩ :=
    ((eventually_gt_atTop T₀).and (hγ.2.2.1.eventually (hopen.mem_nhds hqimage))).exists
  change χ z = γ T at hzT
  have hzδ : ‖z‖ < δ / 4 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hcoord (i : Fin 2) : |z i| < δ / 4 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm z i).trans_lt hzδ
  let r := Real.sqrt (z 0 ^ 2 + z 1 ^ 2)
  have hrsq : r ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hvalue : f (γ T) = f q + r ^ 2 / 2 := by
    rw [← hzT, hnormal z (hsmall hz), hrsq]
  have hr : 0 < r := by
    apply Real.sqrt_pos.mpr
    have hh := (hγ.value_mem_Ioo hf T).1
    rw [hvalue, hrsq] at hh
    linarith
  have hrδ : r < δ := by
    have h0 := hcoord 0
    have h1 := hcoord 1
    have hz0 : z 0 ^ 2 < (δ / 4) ^ 2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (z 0)) (by positivity)).2 h0
    have hz1 : z 1 ^ 2 < (δ / 4) ^ 2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (z 1)) (by positivity)).2 h1
    nlinarith
  have hcontain (w : MorseModel 2) (hw : ‖w‖ ≤ r) : w ∈ χ.source ∧ χ w ∈ O := by
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right] using hw.trans_lt hrδ
  let C : Set (MorseModel 2) := {w | w 0 ^ 2 + w 1 ^ 2 = r ^ 2}
  have hCs : C ⊆ χ.source := fun w hw => (hcontain w (norm_le_of_sum_sq_eq hr.le hw)).1
  have hCc : IsCompact C := by
    apply (isCompact_closedBall (0 : MorseModel 2) r).of_isClosed_subset
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro w hw
      simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_of_sum_sq_eq hr.le hw
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hemb : Topology.IsClosedEmbedding (fun w : C => χ w) := by
    apply (χ.contMDiffOn.continuousOn.mono hCs).domRestrict.isClosedEmbedding
    intro u w heq
    exact Subtype.ext (χ.injOn (hCs u.2) (hCs w.2) heq)
  have himage : χ '' C = χ.target ∩ f ⁻¹' {f q + r ^ 2 / 2} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨χ.map_source (hCs hw), ?_⟩
      change f (χ w) = f q + r ^ 2 / 2
      rw [hnormal w (hCs hw), hw]
    · rintro ⟨hxt, hfx⟩
      have hinv : χ (χ.symm x) = x := χ.right_inv hxt
      have hh := hnormal (χ.symm x) (χ.map_target hxt)
      rw [hinv] at hh
      refine ⟨χ.symm x, ?_, hinv⟩
      change χ.symm x 0 ^ 2 + χ.symm x 1 ^ 2 = r ^ 2
      change f x = f q + r ^ 2 / 2 at hfx
      linarith
  refine ⟨χ, hχ0, hχq, hnormal, r, T, hr, hT, hvalue,
    hvalue ▸ hγ.value_mem_Ioo hf T, hcontain, ?_, hemb, himage, ⟨z, hrsq.symm, hzT⟩⟩
  rintro x ⟨w, hw, rfl⟩
  exact (hcontain w (norm_le_of_sum_sq_eq hr.le hw)).2

end DifferentialGeometry.Morse
