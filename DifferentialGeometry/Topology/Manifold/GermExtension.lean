/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Analysis.Calculus.Cutoff.SmallGermCutoff
import DifferentialGeometry.Analysis.Calculus.Interpolation.SmallPerturbation
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

open Set Filter Topology
open scoped ContDiff Manifold NNReal

namespace DifferentialGeometry.Topology.Manifold

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_diffeomorph_realizing_germ_with_small_displacement
    (φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞) {x : F} (hx : x ∈ φ.source)
    (c : ℝ≥0) (hc : 0 < c) (hc1 : c < 1) {V : Set ℂ} (hV : IsOpen V) (hVx : φ x ∈ V) :
    ∃ A : F ≃L[ℝ] ℂ, (A : F →L[ℝ] ℂ) = fderiv ℝ φ x ∧
      ∃ J : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
        J (φ x) = φ x ∧
        (∀ᶠ z in 𝓝 x, J (A (z - x) + φ x) = φ z) ∧
        (∀ z, ‖J z - z‖ ≤ (c : ℝ) * ‖z - φ x‖) ∧
        ∃ K : Set ℂ, IsCompact K ∧ K ⊆ V ∧
          ∀ z, z ∉ K → J z = z ∧ J.symm z = z := by
  have hlocal := φ.isLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ∞ hx
  let A : F ≃L[ℝ] ℂ := hlocal.mfderivToContinuousLinearEquiv (by simp)
  have hAe : (A : F →L[ℝ] ℂ) = fderiv ℝ φ x := mfderiv_eq_fderiv
  have hA : HasFDerivAt φ (A : F →L[ℝ] ℂ) x := by
    rw [hAe]
    exact (φ.contMDiffOn.contDiffOn.contDiffAt (φ.open_source.mem_nhds hx)).differentiableAt
      (by simp) |>.hasFDerivAt
  let W := (fun z : ℂ => A.symm z + x) ⁻¹' φ.source ∩
    (fun z => z + φ x) ⁻¹' V
  have hW : IsOpen W :=
    (φ.open_source.preimage (A.symm.continuous.add continuous_const)).inter
      (hV.preimage (continuous_id.add continuous_const))
  have h0W : (0 : ℂ) ∈ W := by simp [W, hx, hVx]
  let h : ℂ → ℂ := fun z => φ (A.symm z + x) - φ x - z
  have hh : ContDiffOn ℝ ∞ h W :=
    ((φ.contMDiffOn.contDiffOn.comp
      (A.symm.contDiff.add contDiff_const).contDiffOn (fun _ hz => hz.1)).sub
        contDiffOn_const).sub contDiffOn_id
  have hh0 : h 0 = 0 := by simp [h]
  have hhd : fderiv ℝ h 0 = 0 := by
    have hdφ : HasFDerivAt φ (A : F →L[ℝ] ℂ) (A.symm 0 + x) := by simpa using hA
    have hd := ((hdφ.comp 0 (A.symm.hasFDerivAt.add_const x)).sub_const (φ x)).sub
      (hasFDerivAt_id 0)
    simpa only [h, Function.comp_def, Pi.sub_def, id_eq,
      ContinuousLinearEquiv.coe_comp_coe_symm, sub_self] using hd.fderiv
  obtain ⟨g, hg, hgc, hgW, hge, hglip⟩ :=
    DifferentialGeometry.Analysis.exists_small_compact_extension_of_zero_derivative
      hW h0W hh hh0 hhd c hc
  have hg0 : g 0 = 0 := hge.eq_of_nhds.trans hh0
  obtain ⟨D, _, _, hD⟩ :=
    DifferentialGeometry.Analysis.exists_diffeomorphs_of_small_lipschitz_displacement
      (hg.comp contDiff_snd : ContDiff ℝ ∞ (fun z : ℝ × ℂ => g z.2))
      (fun _ => ⟨c, hc1, hglip⟩)
  let T := DifferentialGeometry.Topology.translateDiffeomorph (φ x)
  let J := (T.symm.trans (D 0)).trans T
  have hJ (z : ℂ) : J z = z + g (z - φ x) := by
    change D 0 (z + -(φ x)) + φ x = _
    rw [← sub_eq_add_neg, hD]
    abel
  have hfix (z : ℂ) (hz : z ∉ (fun y => y + φ x) '' tsupport g) : J z = z := by
    have hn : z - φ x ∉ tsupport g := fun hy => hz ⟨z - φ x, hy, sub_add_cancel _ _⟩
    rw [hJ, image_eq_zero_of_notMem_tsupport hn, add_zero]
  refine ⟨A, hAe, J, ?_, ?_, ?_, (fun y => y + φ x) '' tsupport g,
    hgc.isCompact.image (continuous_id.add continuous_const), ?_, ?_⟩
  · rw [hJ, sub_self, hg0, add_zero]
  · have ht : Tendsto (fun z => A (z - x)) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self, map_zero] using
        (show Continuous (fun z : F => A (z - x)) from
          A.continuous.comp (continuous_id.sub continuous_const)).tendsto x
    filter_upwards [hge.comp_tendsto ht] with z hz
    change g (A (z - x)) = h (A (z - x)) at hz
    rw [hJ, add_sub_cancel_right, hz]
    simp only [h, A.symm_apply_apply, sub_add_cancel]
    abel
  · intro z
    have hn := hglip.norm_sub_le (z - φ x) 0
    rw [hg0, sub_zero, sub_zero] at hn
    simpa only [hJ, add_sub_cancel_left] using hn
  · rintro z ⟨y, hy, rfl⟩
    exact (hgW hy).2
  · intro z hz
    refine ⟨hfix z hz, ?_⟩
    apply J.injective
    exact (J.apply_symm_apply z).trans (hfix z hz).symm

theorem exists_diffeomorph_realizing_germ_separating_ray
    (φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞) {x : F} (hx : x ∈ φ.source)
    {u : F} (hr : (fderiv ℝ φ x u).im ≠ 0) :
    ∃ E : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞,
      E x = φ x ∧ (E : F → ℂ) =ᶠ[𝓝 x] φ ∧
      ∀ t : ℝ, 0 < t → ((E (x + t • u)).im - (φ x).im) *
        (fderiv ℝ φ x u).im > 0 := by
  let v := fderiv ℝ φ x u
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr fun he => hr (by change v.im = 0; rw [he]; rfl)
  let ε := min (1 / 2 : ℝ) (|v.im| / (2 * ‖v‖))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (abs_pos.mpr hr) (by positivity))
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεbound : ε * ‖v‖ ≤ |v.im| / 2 := by
    calc
      ε * ‖v‖ ≤ (|v.im| / (2 * ‖v‖)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)
      _ = |v.im| / 2 := by field_simp [hv.ne']
  obtain ⟨A, hA, J, hJx, hmatch, hbound, _⟩ :=
    exists_diffeomorph_realizing_germ_with_small_displacement φ hx ⟨ε, hε.le⟩ hε hε1
      isOpen_univ (mem_univ _)
  have hAu : A u = v := congrArg (fun L : F →L[ℝ] ℂ => L u) hA
  let E := (((DifferentialGeometry.Topology.translateDiffeomorph (-x)).trans
    A.toDiffeomorph).trans (DifferentialGeometry.Topology.translateDiffeomorph (φ x))).trans J
  have hE (z : F) : E z = J (A (z - x) + φ x) := by
    change J (A (z + -x) + φ x) = _
    rw [sub_eq_add_neg]
  refine ⟨E, ?_, ?_, ?_⟩
  · rw [hE, sub_self, map_zero, zero_add, hJx]
  · exact hmatch.mono fun z hz => (hE z).trans hz
  · intro t ht
    have hEt : E (x + t • u) = J (t • v + φ x) := by
      rw [hE, add_sub_cancel_left, map_smul, hAu]
    have hb := hbound (t • v + φ x)
    change ‖J (t • v + φ x) - (t • v + φ x)‖ ≤ ε * ‖t • v + φ x - φ x‖ at hb
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hb
    have he : |(E (x + t • u)).im - (t * v.im + (φ x).im)| ≤ t * (|v.im| / 2) := by
      have hi := (Complex.abs_im_le_norm (J (t • v + φ x) - (t • v + φ x))).trans hb
      rw [Complex.sub_im, Complex.add_im, Complex.smul_im, smul_eq_mul, ← hEt] at hi
      exact hi.trans (by nlinarith [mul_le_mul_of_nonneg_left hεbound ht.le])
    rcases lt_or_gt_of_ne hr with hrn | hrp
    · have he' := (abs_le.mp he).2
      rw [abs_of_neg hrn] at he'
      apply mul_pos_of_neg_of_neg _ hrn
      nlinarith [mul_neg_of_pos_of_neg ht hrn]
    · have he' := (abs_le.mp he).1
      rw [abs_of_pos hrp] at he'
      apply mul_pos _ hrp
      nlinarith [mul_pos ht hrp]
end DifferentialGeometry.Topology.Manifold
