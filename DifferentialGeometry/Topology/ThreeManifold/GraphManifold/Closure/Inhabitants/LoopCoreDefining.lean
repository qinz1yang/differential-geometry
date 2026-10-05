import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCoreBase

/-!
The actual core boundary has a globally smooth regular defining function on the true circle base.
Its sign is strictly negative on both entire prescribed corner charts.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private def corePlaneDefining (z : EuclideanSpace ℝ (Fin 2)) : ℝ := 1 / 8 - ‖z‖ ^ 2

private theorem corePlane_regular {z : EuclideanSpace ℝ (Fin 2)}
    (hz : corePlaneDefining z = 0) : fderiv ℝ corePlaneDefining z ≠ 0 := by
  have hn : ‖z‖ ^ 2 = 1 / 8 := by change 1 / 8 - ‖z‖ ^ 2 = 0 at hz; linarith
  change fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) => 1 / 8 - ‖w‖ ^ 2) z ≠ 0
  rw [fderiv_const_sub, fderiv_norm_sq_apply]
  intro he
  have hh := DFunLike.congr_fun he z
  rw [two_smul, neg_apply, add_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, zero_apply] at hh
  linarith

private def coreBaseInclusion : PartialDiffeomorph (𝓡 2) (𝓡 2)
    loopCircleBase (EuclideanSpace ℝ (Fin 2)) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    loopCircleBase loopCircleBase_nonempty

private theorem coreBaseInclusion_source : coreBaseInclusion.source = Set.univ :=
  TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source
    loopCircleBase loopCircleBase_nonempty

def loopCoreDefining (z : loopCircleBase) : ℝ := corePlaneDefining z.val

theorem loopCoreDefining_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ loopCoreDefining :=
  (contDiff_const.sub (contDiff_norm_sq ℝ)).contMDiff.comp contMDiff_subtype_val

theorem loopCoreDefining_regular (z : loopCircleBase) (hz : loopCoreDefining z = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopCoreDefining z ≠ 0 := by
  have hsource : z ∈ coreBaseInclusion.source := by rw [coreBaseInclusion_source]; trivial
  have hv : Surjective (mfderiv (𝓡 2) (𝓡 2)
      (Subtype.val : loopCircleBase → EuclideanSpace ℝ (Fin 2)) z) := by
    have hl := coreBaseInclusion.isLocalDiffeomorphAt _ _ _ hsource
    exact (hl.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hdfSmooth : ContDiff ℝ ∞ corePlaneDefining :=
    contDiff_const.sub (contDiff_norm_sq ℝ)
  have hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) corePlaneDefining z.val :=
    hdfSmooth.contMDiff.mdifferentiableAt (by simp)
  have hvalSmooth : ContMDiff (𝓡 2) (𝓡 2) ∞
      (Subtype.val : loopCircleBase → EuclideanSpace ℝ (Fin 2)) := contMDiff_subtype_val
  have hval := hvalSmooth.mdifferentiableAt (x := z) (by simp)
  have hc := mfderiv_comp z hf hval
  intro hzero
  have hg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) corePlaneDefining z.val = 0 := by
    ext w
    obtain ⟨v, he⟩ := hv w
    rw [← he, ← ContinuousLinearMap.comp_apply, ← hc]
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopCoreDefining z v = 0
    rw [hzero, zero_apply]
  have hdf : fderiv ℝ corePlaneDefining z.val = 0 := by
    ext w
    rw [mfderiv_eq_fderiv] at hg
    have hs := DFunLike.congr_fun hg ((NormedSpace.fromTangentSpace z.val).symm w)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] at hs
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (corePlaneDefining z.val)).symm.injective
    simpa only [zero_apply, map_zero] using hs
  exact corePlane_regular hz hdf

theorem loopCoreDefining_zero {z : loopCircleBase} :
    loopCoreDefining z = 0 ↔ z ∈ Set.range loopCoreBaseCircle := by
  constructor
  · intro hz
    have hn : ‖z.val‖ ^ 2 = 1 / 8 := by
      change 1 / 8 - ‖z.val‖ ^ 2 = 0 at hz
      linarith
    have he : z.val ∈ Subtype.val '' range loopCoreBaseCircle := by
      rw [loopCoreBaseCircle_image]
      exact hn
    obtain ⟨w, hw, he⟩ := he
    exact Subtype.ext he ▸ hw
  · rintro ⟨θ, rfl⟩
    change 1 / 8 - ‖(loopCoreBaseCircle θ).val‖ ^ 2 = 0
    rw [loopCoreBaseCircle_norm]
    ring

theorem loopCoreDefining_loop (θ : Circle) : loopCoreDefining (loopCoreBaseCircle θ) = 0 :=
  (loopCoreDefining_zero (z := _)).mpr (mem_range_self θ)

theorem loopCoreDefining_corner (b : Bool) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    loopCoreDefining (loopBaseCorner b v) < 0 := by
  let p := standardLoopBallHandleCycle.rimChart
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (1, v)
  have hsource : (1, v) ∈ (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).source :=
    (standardLoopBallHandleCycle.rim_source _ b).mpr hv
  have hnc : p ∉ range loopComplementVertex.map := by
    intro hc
    exact Set.disjoint_left.mp (loopRim_core_disjoint b)
      ((standardLoopBallHandleCycle.rimChart
        ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).map_source hsource) hc
  rw [loopComplementVertex_range] at hnc
  have hlt : cliffordHeight p < 3 / 4 := not_le.mp hnc
  have he : (loopBaseCorner b v).val = modelPlaneComplex.symm (sphereSecond p) := by
    rw [← loopRegionRim_projection b 1 v hv, loopCircleProjection_val]
  change 1 / 8 - ‖(loopBaseCorner b v).val‖ ^ 2 < 0
  rw [he, modelPlaneComplex.symm.norm_map, norm_sphereSecond_sq_eq]
  linarith

end GC.GraphManifold.Assembly
