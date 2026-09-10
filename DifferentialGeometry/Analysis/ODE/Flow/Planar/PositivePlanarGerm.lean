import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactPositiveLinearGerm
import DifferentialGeometry.Analysis.ODE.Flow.Planar.IdentityTangentGerm

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem exists_compact_isotopy_realizing_positive_planar_germ
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h0U : (0 : ℂ) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0)
    (A : ℂ →L[ℝ] ℂ) (hdf0 : HasFDerivAt f A 0) (hA : 0 < A.toLinearMap.det)
    (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] f ∧
      ∀ p z, z ∉ closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  obtain ⟨L, hL, hLi, hL0, hLg, hLfix⟩ :=
    exists_compact_isotopy_realizing_positive_linear_map A.toLinearMap hA r hr
  have hLzero : L 1 0 = 0 := by simpa using hLg.eq_of_nhds
  have hLizero : (L 1).symm 0 = 0 := by
    simpa only [hLzero] using (L 1).symm_apply_apply (0 : ℂ)
  let R : ℂ → ℂ := fun z ↦ f ((L 1).symm z)
  let V : Set ℂ := (L 1).symm ⁻¹' U ∩ ball 0 r
  have hV : IsOpen V := (hU.preimage (L 1).symm.continuous).inter isOpen_ball
  have h0V : (0 : ℂ) ∈ V := ⟨by simpa only [mem_preimage, hLizero] using h0U, mem_ball_self hr⟩
  have hR : ContDiffOn ℝ ∞ R V := hf.comp (L 1).symm.contMDiff.contDiff.contDiffOn
    (fun _ hz ↦ hz.1)
  have hRzero : R 0 = 0 := by simp only [R, hLizero, hf0]
  let B := fderiv ℝ (L 1).symm 0
  have hB : HasFDerivAt (L 1).symm B 0 :=
    ((L 1).symm.contMDiff.contDiff.differentiable (by simp) 0).hasFDerivAt
  have hLA : HasFDerivAt (L 1) A 0 := A.hasFDerivAt.congr_of_eventuallyEq hLg
  have hLA' : HasFDerivAt (L 1) A ((L 1).symm 0) := by simpa only [hLizero] using hLA
  have hAB : A.comp B = ContinuousLinearMap.id ℝ ℂ := by
    have hc := hLA'.comp 0 hB
    have he : (L 1) ∘ (L 1).symm = id := funext (L 1).apply_symm_apply
    rw [he] at hc
    exact hc.unique (hasFDerivAt_id 0)
  have hdR : HasFDerivAt R (ContinuousLinearMap.id ℝ ℂ) 0 := by
    have hdf' : HasFDerivAt f A ((L 1).symm 0) := by simpa only [hLizero] using hdf0
    have hh := hdf'.comp 0 hB
    rw [hAB] at hh
    exact hh
  obtain ⟨C, hC, hCi, hC0, hCg, _, K, _, hKV, hCfix⟩ :=
    exists_compact_isotopy_realizing_identity_tangent_germ hV h0V hR hRzero hdR
  let D (p : ℝ) := (L p).trans (C p)
  have hD : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) :=
    hC.comp (contDiff_fst.prodMk hL)
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) :=
    hLi.comp (contDiff_fst.prodMk hCi)
  have htL : Tendsto (L 1) (𝓝 0) (𝓝 0) := by
    simpa only [hLzero] using (L 1).continuous.tendsto 0
  refine ⟨D, hD, hDi, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro z
    change C 0 (L 0 z) = z
    rw [hC0, hL0]
    rfl
  · filter_upwards [hCg.comp_tendsto htL] with z hz
    change C 1 (L 1 z) = f ((L 1).symm (L 1 z)) at hz
    change C 1 (L 1 z) = f z
    simpa only [(L 1).symm_apply_apply] using hz
  · intro p z hz
    have hzK : z ∉ K := by
      intro hk
      have hzr : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using (hKV hk).2
      exact hz (mem_closedBall_zero_iff.mpr (by linarith))
    constructor
    · change C p (L p z) = z
      rw [(hLfix p z hz).1, (hCfix p z hzK).1]
    · change (L p).symm ((C p).symm z) = z
      rw [(hCfix p z hzK).2, (hLfix p z hz).2]

end Poincare.Analysis
