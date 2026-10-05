import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopShellRegular

/-!
The actual full-circle bundle on the first-Clifford free locus has its genuine open unitdisc base.
The same two corner charts land in this base, and each projection fibre is a whole circle orbit.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

def loopCircleBase : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) :=
  ⟨{z | ‖z‖ < 1}, isOpen_lt continuous_norm continuous_const⟩

def loopCircleDomain : TopologicalSpace.Opens SphereCarrier.{0} :=
  ⟨{p | sphereFirst p ≠ 0}, isOpen_ne.preimage contMDiff_sphereFirst.continuous⟩

theorem loopCircleBase_nonempty : Nonempty loopCircleBase :=
  ⟨⟨0, by change ‖(0 : EuclideanSpace ℝ (Fin 2))‖ < 1; norm_num⟩⟩

private def bundleForward (p : loopCircleDomain) : loopCircleBase × Circle :=
  (⟨(loopCircleCoordinates.symm p.val).1, loopCircleCoordinates.symm.map_source p.2⟩,
    (loopCircleCoordinates.symm p.val).2)

private def bundleInverse (p : loopCircleBase × Circle) : loopCircleDomain :=
  ⟨loopCircleCoordinates (p.1.val, p.2), loopCircleCoordinates.map_source p.1.2⟩

private theorem bundleForward_smooth :
    ContMDiff (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ bundleForward := by
  have hh : ContMDiff (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞
      (fun p : loopCircleDomain => loopCircleCoordinates.symm p.val) := by
    intro p
    exact (loopCircleCoordinates.symm.contMDiffOn_toFun.contMDiffAt
      (loopCircleCoordinates.open_target.mem_nhds p.2)).comp p
      contMDiff_subtype_val.contMDiffAt
  have hf : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun p : loopCircleDomain => (bundleForward p).1) :=
    (ContMDiff.subtypeVal_comp_iff loopCircleBase _).mp (contMDiff_fst.comp hh)
  exact hf.prodMk (contMDiff_snd.comp hh)

private theorem bundleInverse_smooth :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ bundleInverse := by
  have hi : ContMDiff ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (fun p : loopCircleBase × Circle => (p.1.val, p.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  have hh : ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞
      (fun p : loopCircleBase × Circle => loopCircleCoordinates (p.1.val, p.2)) := by
    intro p
    have hp : (p.1.val, p.2) ∈ loopCircleCoordinates.source := p.1.2
    have hat : ContMDiffAt ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞
        (fun q : EuclideanSpace ℝ (Fin 2) × Circle => loopCircleCoordinates q)
        (p.1.val, p.2) :=
      loopCircleCoordinates.contMDiffOn_toFun.contMDiffAt
        (loopCircleCoordinates.open_source.mem_nhds hp)
    exact hat.comp p (hi p)
  exact (ContMDiff.subtypeVal_comp_iff loopCircleDomain _).mp hh

def loopCircleBundle : loopCircleDomain
    ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ (loopCircleBase × Circle) where
  toFun := bundleForward
  invFun := bundleInverse
  left_inv := by
    intro p
    apply Subtype.ext
    exact loopCircleCoordinates.right_inv p.2
  right_inv := by
    intro p
    have hp : (p.1.val, p.2) ∈ loopCircleCoordinates.source := p.1.2
    have hh : loopCircleCoordinates.symm (loopCircleCoordinates (p.1.val, p.2)) =
        (p.1.val, p.2) := loopCircleCoordinates.left_inv hp
    apply Prod.ext
    · apply Subtype.ext
      change (loopCircleCoordinates.symm (loopCircleCoordinates (p.1.val, p.2))).1 = p.1.val
      exact congrArg Prod.fst hh
    · change (loopCircleCoordinates.symm (loopCircleCoordinates (p.1.val, p.2))).2 = p.2
      exact congrArg Prod.snd hh
  contMDiff_toFun := bundleForward_smooth
  contMDiff_invFun := bundleInverse_smooth

def loopCircleProjection : C(loopCircleDomain, loopCircleBase) :=
  ⟨fun p => (loopCircleBundle p).1, continuous_fst.comp loopCircleBundle.continuous⟩

theorem loopCircleProjection_smooth : ContMDiff (𝓡 3) (𝓡 2) ∞ loopCircleProjection :=
  contMDiff_fst.comp loopCircleBundle.contMDiff

theorem loopCircleProjection_submersion (p : loopCircleDomain) :
    Surjective (mfderiv (𝓡 3) (𝓡 2) loopCircleProjection p) := by
  obtain ⟨e, he⟩ := loopCircleBundle.isInvertible_mfderiv (x := p) (by simp)
  have hb : Bijective (mfderiv (𝓡 3) ((𝓡 2).prod (𝓡 1)) loopCircleBundle p) := by
    rw [← he, ContinuousLinearEquiv.coe_coe]
    exact e.bijective
  change Surjective (mfderiv (𝓡 3) (𝓡 2) (Prod.fst ∘ loopCircleBundle) p)
  rw [mfderiv_comp p mdifferentiableAt_fst (loopCircleBundle.mdifferentiable (by simp) p),
    mfderiv_fst]
  change Surjective fun w =>
    (mfderiv (𝓡 3) ((𝓡 2).prod (𝓡 1)) loopCircleBundle p w).1
  intro v
  obtain ⟨w, hw⟩ := hb.surjective (v, 0)
  exact ⟨w, congrArg Prod.fst hw⟩

theorem loopCircleProjection_fibre (z : loopCircleBase) :
    Subtype.val '' (loopCircleProjection ⁻¹' {z}) =
      loopCircleCoordinates '' ({z.val} ×ˢ Set.univ) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hz : (loopCircleBundle q).1 = z := hq
    refine ⟨(z.val, (loopCircleBundle q).2), ⟨rfl, trivial⟩, ?_⟩
    have he : loopCircleBundle.symm (z, (loopCircleBundle q).2) = q := by
      rw [← hz]
      exact loopCircleBundle.symm_apply_apply q
    exact congrArg Subtype.val he
  · rintro ⟨⟨w, θ⟩, hw, rfl⟩
    have he : w = z.val := hw.1
    subst w
    refine ⟨loopCircleBundle.symm (z, θ), ?_, rfl⟩
    change (loopCircleBundle (loopCircleBundle.symm (z, θ))).1 = z
    exact congrArg Prod.fst (loopCircleBundle.apply_symm_apply (z, θ))

private def baseInclusion : PartialDiffeomorph (𝓡 2) (𝓡 2)
    loopCircleBase (EuclideanSpace ℝ (Fin 2)) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    loopCircleBase loopCircleBase_nonempty

private theorem baseInclusion_target : baseInclusion.target = loopCircleBase :=
  TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target
    loopCircleBase loopCircleBase_nonempty

def loopBaseCorner (b : Bool) : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2)
    (ℝ × ℝ) loopCircleBase ∞ :=
  (loopCornerChart b).trans baseInclusion.symm

theorem loopBaseCorner_source (b : Bool) : (loopBaseCorner b).source = rimBox 2 := by
  rw [loopBaseCorner, PartialDiffeomorph.trans_source, loopCornerChart_source,
    PartialDiffeomorph.symm_source, baseInclusion_target]
  ext v
  constructor
  · exact fun hv => hv.1
  · intro hv
    exact ⟨hv, loopCornerChart_unitDisc b ((loopCornerChart b).map_source hv)⟩

theorem loopBaseCorner_val (b : Bool) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    (loopBaseCorner b v).val = loopCornerChart b v := by
  rw [loopBaseCorner, PartialDiffeomorph.trans_apply]
  apply baseInclusion.right_inv
  rw [baseInclusion_target]
  exact loopCornerChart_unitDisc b ((loopCornerChart b).map_source hv)

theorem loopBaseCorner_disjoint :
    Disjoint (loopBaseCorner false).target (loopBaseCorner true).target := by
  apply Set.disjoint_left.mpr
  intro z hf ht
  exact Set.disjoint_left.mp loopCornerChart_disjoint hf.2 ht.2


theorem loopCircleProjection_val (p : loopCircleDomain) :
    (loopCircleProjection p).val = modelPlaneComplex.symm (sphereSecond p.val) := by
  change (loopCircleCoordinates.symm p.val).1 = _
  rw [loopCircleCoordinates_inverse]

private theorem baseInclusion_source : baseInclusion.source = Set.univ :=
  TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source
    loopCircleBase loopCircleBase_nonempty

def loopCircleBaseRounding (z : loopCircleBase) : ℝ := loopShellRounding z.val

theorem loopCircleBaseRounding_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ loopCircleBaseRounding := by
  intro z
  have hopen : IsOpen {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} :=
    isOpen_lt continuous_norm continuous_const
  exact (loopShellRounding_smooth.contMDiffOn.contMDiffAt
    (hopen.mem_nhds z.2)).comp z contMDiff_subtype_val.contMDiffAt

theorem loopCircleBaseRounding_regular (z : loopCircleBase)
    (hz : loopCircleBaseRounding z = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopCircleBaseRounding z ≠ 0 := by
  have hsource : z ∈ baseInclusion.source := by rw [baseInclusion_source]; trivial
  have hv : Surjective (mfderiv (𝓡 2) (𝓡 2)
      (Subtype.val : loopCircleBase → EuclideanSpace ℝ (Fin 2)) z) :=
    by
      have hl := baseInclusion.isLocalDiffeomorphAt _ _ _ hsource
      exact (hl.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hopen : IsOpen {w : EuclideanSpace ℝ (Fin 2) | ‖w‖ < 1} :=
    isOpen_lt continuous_norm continuous_const
  have hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) loopShellRounding z.val :=
    (loopShellRounding_smooth.contMDiffOn.contMDiffAt
      (hopen.mem_nhds z.2)).mdifferentiableAt (by simp)
  have hvalSmooth : ContMDiff (𝓡 2) (𝓡 2) ∞
      (Subtype.val : loopCircleBase → EuclideanSpace ℝ (Fin 2)) := contMDiff_subtype_val
  have hval := hvalSmooth.mdifferentiableAt (x := z) (by simp)
  have hc := mfderiv_comp z hf hval
  intro hzero
  have hg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopShellRounding z.val = 0 := by
    ext w
    obtain ⟨v, hval⟩ := hv w
    rw [← hval, ← ContinuousLinearMap.comp_apply, ← hc]
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) loopCircleBaseRounding z v = 0
    rw [hzero, zero_apply]
  have hdf : fderiv ℝ loopShellRounding z.val = 0 := by
    ext w
    rw [mfderiv_eq_fderiv] at hg
    have hs := DFunLike.congr_fun hg ((NormedSpace.fromTangentSpace z.val).symm w)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] at hs
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (loopShellRounding z.val)).symm.injective
    simpa only [zero_apply, map_zero] using hs
  exact loopShellRounding_regular hz hdf

theorem loopCircleBaseRounding_compact :
    IsCompact {z : loopCircleBase | loopCircleBaseRounding z ≤ 0} := by
  apply _root_.Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : Subtype.val '' {z : loopCircleBase | loopCircleBaseRounding z ≤ 0} =
      {z : EuclideanSpace ℝ (Fin 2) | loopShellRounding z ≤ 0} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hz
      exact ⟨⟨z, loopShellRounding_source hz⟩, hz, rfl⟩
  rw [he]
  exact loopShellRounding_compact

theorem loopCircleBaseRounding_corner (b : Bool) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    loopCircleBaseRounding (loopBaseCorner b v) = -standardRimRounding v := by
  rw [loopCircleBaseRounding, loopBaseCorner_val b v hv]
  exact loopShellRounding_corner b v hv

def loopCircleTrivialization :
    (TopologicalSpace.Opens.comap loopCircleProjection
      (⊤ : TopologicalSpace.Opens loopCircleBase))
      ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ ((⊤ : TopologicalSpace.Opens loopCircleBase) × Circle) :=
  (openDiffeomorphOfForall
    (TopologicalSpace.Opens.comap loopCircleProjection
      (⊤ : TopologicalSpace.Opens loopCircleBase))
    (fun p => Set.mem_univ (loopCircleProjection p))).trans
    (loopCircleBundle.trans
      ((openDiffeomorphOfForall (⊤ : TopologicalSpace.Opens loopCircleBase)
        (fun p => Set.mem_univ p)).symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)))

theorem loopCircleTrivialization_proj
    (p : TopologicalSpace.Opens.comap loopCircleProjection
      (⊤ : TopologicalSpace.Opens loopCircleBase)) :
    ((loopCircleTrivialization p).1).val = loopCircleProjection p.val := rfl

end GC.GraphManifold.Assembly
