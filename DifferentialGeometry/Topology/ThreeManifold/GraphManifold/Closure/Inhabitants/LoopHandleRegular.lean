import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleOrbit

/-!
Every zero of the actual global handle defining function is regular in the native model.
The original radial path has nonzero pullback derivative throughout the true zero set.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopHandleDefining_regular (z : loopCircleBase) (hz : loopHandleDefining z = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopHandleDefining z ≠ 0 := by
  classical
  have ht := (loopHandleDefining_zero.mp hz).1
  let x := loopActualHandleChart.symm (loopCircleSection z)
  have hxs : x ∈ loopActualHandleChart.source := loopActualHandleChart.symm.map_source ht
  have hbounds := loopHandleDefining_zero_bounds hz
  have hxp : 0 < ‖x.1‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hrot : loopHandleRotation x 1 = x := by
      apply Prod.ext
      · simp [loopHandleRotation,he]
      · rfl
    have hf := loopHandleRotation_first hxs 1
    rw [hrot] at hf
    change sphereFirst (loopActualHandleChart x) =
      ((Real.sqrt 2)⁻¹ * zoneRatio (1/16) ‖x.1‖ (zoneHeight ‖x.1‖ x.2) * ‖x.1‖) •
        ((1 : Circle) : ℂ) at hf
    rw [he,norm_zero,mul_zero,zero_smul] at hf
    have hdom : loopActualHandleChart x ∈ loopCircleDomain := by
      have hv : loopActualHandleChart x = loopCircleSection z :=
        loopActualHandleChart.right_inv ht
      rw [hv]
      exact loopCircleSection_domain z
    exact hdom hf
  let T := Real.smoothTransition (16*(x.2+3/16))*Real.smoothTransition (16*(19/16-x.2))
  have hT : 0 < T := by
    have hh := loopHandleProfile_zero_time (loopHandleDefining_zero.mp hz).2
    exact hh
  have hxv : loopActualHandleChart x = loopCircleSection z :=
    loopActualHandleChart.right_inv ht
  have hxd : loopActualHandleChart x ∈ loopCircleDomain := by
    rw [hxv]
    exact loopCircleSection_domain z
  let a : ℝ → ModelSpace := fun r => (r • x.1,x.2)
  let f : ℝ → SphereCarrier.{0} := fun r => loopActualHandleChart (a r)
  have hr : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ModelSpace) ∞ a :=
    ((contDiff_id.smul contDiff_const).prodMk contDiff_const).contMDiff
  have hf : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ f 1 := by
    have h1 : a 1 = x := by simp only [a,one_smul]
    exact (loopActualHandleChart.contMDiffOn_toFun.contMDiffAt
      (loopActualHandleChart.open_source.mem_nhds (h1.symm ▸ hxs))).comp 1 hr.contMDiffAt
  have hf1 : f 1 = loopCircleSection z := by simp only [f, a, one_smul, hxv]
  have hd1 : f 1 ∈ loopCircleDomain := by simpa only [f, a, one_smul] using hxd
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
  have he : (fun r => loopHandleDefining (c r)) =ᶠ[𝓝 (1 : ℝ)]
      (fun r : ℝ => -1 + T*(17-16*r*‖x.1‖)) := by
    filter_upwards [hn,Ioo_mem_nhds (by norm_num : (9/10 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 11/10)] with r hd hb
    have hp : 0 < r := by linarith [hb.1]
    have hnval : ‖(a r).1‖ = r*‖x.1‖ := by
      change ‖r • x.1‖ = _
      rw [norm_smul,Real.norm_of_nonneg hp.le]
    have hsmall : ‖(a r).1‖ ≤ 9/8 := by
      rw [hnval]
      have hh := mul_le_mul_of_nonneg_left hbounds.1 hp.le
      nlinarith [hb.2]
    have hrs : a r ∈ loopActualHandleChart.source := by
      rw [loopActualHandleChart_source]
      have hh : x ∈ zoneDomain := by rwa [loopActualHandleChart_source] at hxs
      exact ⟨by linarith,hh.2⟩
    have hqr : q r = ⟨f r,hd⟩ := by
      apply Subtype.ext
      exact ite_eq_left hd
    have hct : loopCircleSection (c r) ∈ loopActualHandleChart.target := by
      change loopCircleSection (loopCircleProjection (q r)) ∈ _
      rw [hqr,loopHandleRotation_section hrs hd]
      exact loopActualHandleChart.map_source (loopHandleRotation_source hrs 1)
    rw [loopHandleDefining_target hct]
    change loopHandleProfile ‖(loopActualHandleChart.symm
      (loopCircleSection (loopCircleProjection (q r)))).1‖
      (loopActualHandleChart.symm (loopCircleSection (loopCircleProjection (q r)))).2 = _
    rw [hqr,loopHandleRotation_inverse_norm hrs hd,loopHandleRotation_inverse_time hrs hd]
    change -1 + Real.smoothTransition (8*(5/4-‖(a r).1‖)) *
      (Real.smoothTransition (16*((a r).2+3/16))*
        Real.smoothTransition (16*(19/16-(a r).2))) * (17-16*‖(a r).1‖) = _
    rw [Real.smoothTransition.one_of_one_le (by linarith :
      1 ≤ 8*(5/4-‖(a r).1‖)),one_mul,hnval]
    dsimp only [a,T]
    ring
  have ha : HasDerivAt (fun r : ℝ => -1 + T*(17-16*r*‖x.1‖)) (-16*‖x.1‖*T) 1 := by
    have hh := (hasDerivAt_const (1 : ℝ) (-1 : ℝ)).add
      (((hasDerivAt_const (1 : ℝ) (17 : ℝ)).sub
        ((hasDerivAt_id (1 : ℝ)).const_mul (16*‖x.1‖))).const_mul T)
    convert hh using 1
    · funext r
      change -1 + T*(17-16*r*‖x.1‖) = -1 + T*(17-16*‖x.1‖*r)
      ring
    · ring
  have hg := ha.congr_of_eventuallyEq he
  intro hzero
  have hdg := loopHandleDefining_smooth.mdifferentiableAt (x := z) (by simp)
  have hdc := hc.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp 1 (hc1.symm ▸ hdg) hdc
  have hm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r => loopHandleDefining (c r)) 1 = 0 := by
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (loopHandleDefining ∘ c) 1 = 0
    rw [hcomp, hc1, hzero]
    apply ContinuousLinearMap.ext
    intro w
    rfl
  have hd0 : fderiv ℝ (fun r => loopHandleDefining (c r)) 1 = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    rw [mfderiv_eq_fderiv] at hm
    have hh := DFunLike.congr_fun hm ((NormedSpace.fromTangentSpace (1 : ℝ)).symm w)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] at hh
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (loopHandleDefining (c 1))).symm.injective
    simpa only [zero_apply, map_zero] using hh
  have hdv := hg.hasFDerivAt.fderiv
  rw [hd0] at hdv
  have hh := DFunLike.congr_fun hdv (1 : ℝ)
  have hnon : (-16*‖x.1‖*T : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hxp.ne') hT.ne'
  apply hnon
  simpa only [zero_apply,ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using hh.symm

end GC.GraphManifold.Assembly
