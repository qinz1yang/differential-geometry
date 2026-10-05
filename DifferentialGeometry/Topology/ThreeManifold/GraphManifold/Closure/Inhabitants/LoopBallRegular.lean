import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBallOrbit

/-!
Every zero of the genuine global original ball defining function is regular in the native model.
The original radial path projects to the true base and pulls the defining function back to -16r.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopBallDefining_regular (z : loopCircleBase) (hz : loopBallDefining z = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopBallDefining z ≠ 0 := by
  classical
  have ht := (loopBallDefining_zero.mp hz).1
  let x := loopActualBallChart.symm (loopCircleSection z)
  have hxs : x ∈ loopActualBallChart.source := loopActualBallChart.symm.map_source ht
  have hxn : ‖x‖ = 1 := (loopBallDefining_zero.mp hz).2
  have hxv : loopActualBallChart x = loopCircleSection z :=
    loopActualBallChart.right_inv ht
  have hxd : loopActualBallChart x ∈ loopCircleDomain := by
    rw [hxv]
    exact loopCircleSection_domain z
  let f : ℝ → SphereCarrier.{0} := fun r => loopActualBallChart (r • x)
  have hr : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun r : ℝ => r • x) :=
    (contDiff_id.smul contDiff_const).contMDiff
  have hf : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ f 1 := by
    have h1 : (1 : ℝ) • x = x := one_smul ℝ x
    exact (loopActualBallChart.contMDiffOn_toFun.contMDiffAt
      (loopActualBallChart.open_source.mem_nhds (h1.symm ▸ hxs))).comp 1 hr.contMDiffAt
  have hf1 : f 1 = loopCircleSection z := by simp only [f, one_smul, hxv]
  have hd1 : f 1 ∈ loopCircleDomain := by simpa only [f, one_smul] using hxd
  have hn : ∀ᶠ r in 𝓝 (1 : ℝ), f r ∈ loopCircleDomain :=
    hf.continuousAt (loopCircleDomain.isOpen.mem_nhds hd1)
  let safe : ℝ → SphereCarrier.{0} := fun r => if f r ∈ loopCircleDomain then f r
    else loopCircleSection z
  have hs : ∀ r, safe r ∈ loopCircleDomain := by
    intro r
    dsimp only [safe]
    split_ifs with hd
    · exact hd
    · exact loopCircleSection_domain z
  let q : ℝ → loopCircleDomain := fun r => ⟨safe r, hs r⟩
  have hsafe : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ safe 1 := by
    apply hf.congr_of_eventuallyEq
    filter_upwards [hn] with r hd
    exact ite_eq_left hd
  have hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ q 1 :=
    (ContMDiffAt.subtypeVal_comp_iff loopCircleDomain q 1).mp hsafe
  let c : ℝ → loopCircleBase := fun r => loopCircleProjection (q r)
  have hc : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ c 1 :=
    loopCircleProjection_smooth.contMDiffAt.comp 1 hq
  have hq1 : q 1 = ⟨loopCircleSection z, loopCircleSection_domain z⟩ := by
    apply Subtype.ext
    change safe 1 = loopCircleSection z
    rw [show safe 1 = f 1 from ite_eq_left hd1, hf1]
  have hc1 : c 1 = z := by
    change loopCircleProjection (q 1) = z
    rw [hq1, loopCircleSection_projection]
  have he : (fun r => loopBallDefining (c r)) =ᶠ[𝓝 (1 : ℝ)]
      (fun r : ℝ => 16 * (1 - r)) := by
    filter_upwards [hn, Ioo_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 11 / 10)] with r hd hb
    have hp : 0 < r := by linarith [hb.1]
    have hrs : r • x ∈ loopActualBallChart.source := by
      rw [loopActualBallChart_source, mem_ball_zero_iff, norm_smul, hxn, mul_one,
        Real.norm_of_nonneg hp.le]
      linarith [hb.2]
    have hqr : q r = ⟨f r,hd⟩ := by
      apply Subtype.ext
      exact ite_eq_left hd
    have hct : loopCircleSection (c r) ∈ loopActualBallChart.target := by
      change loopCircleSection (loopCircleProjection (q r)) ∈ _
      rw [hqr]
      rw [loopBallRotation_section hrs hd]
      exact loopActualBallChart.map_source (loopBallRotation_source hrs 1)
    rw [loopBallDefining_target hct]
    change loopBallProfile ‖loopActualBallChart.symm
      (loopCircleSection (loopCircleProjection (q r)))‖ = _
    rw [hqr, loopBallRotation_inverse_norm hrs hd, norm_smul, hxn, mul_one,
      Real.norm_of_nonneg hp.le, loopBallProfile_small (by linarith [hb.2])]
  have ha : HasDerivAt (fun r : ℝ => 16 * (1 - r)) (-16) 1 := by
    have hh := ((hasDerivAt_const (1 : ℝ) 1).sub
      (hasDerivAt_id (1 : ℝ))).const_mul 16
    convert hh using 1 <;> norm_num
  have hg := ha.congr_of_eventuallyEq he
  intro hzero
  have hdg := loopBallDefining_smooth.mdifferentiableAt (x := z) (by simp)
  have hdc := hc.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp 1 (hc1.symm ▸ hdg) hdc
  have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r => loopBallDefining (c r)) 1 = 0 := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (loopBallDefining ∘ c) 1 = 0
    rw [hcomp, hc1, hzero]
    apply ContinuousLinearMap.ext
    intro w
    rfl
  have hd0 : fderiv ℝ (fun r => loopBallDefining (c r)) 1 = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    rw [mfderiv_eq_fderiv] at hm
    have hh := DFunLike.congr_fun hm ((NormedSpace.fromTangentSpace (1 : ℝ)).symm w)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] at hh
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (loopBallDefining (c 1))).symm.injective
    simpa only [zero_apply, map_zero] using hh
  have hdv := hg.hasFDerivAt.fderiv
  rw [hd0] at hdv
  have hh := DFunLike.congr_fun hdv (1 : ℝ)
  norm_num at hh

end GC.GraphManifold.Assembly
