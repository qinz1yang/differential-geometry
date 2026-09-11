import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreBoundaryAtlas

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev InteriorE2 := EuclideanSpace ℝ (Fin 2)
private abbrev InteriorIR := (𝓡 2).prod (𝓡∂ 1)
private abbrev InteriorIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev InteriorIH := ModelProd InteriorE2 (EuclideanHalfSpace 1)
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (hdim : Module.finrank ℝ E = 3)

def coreInteriorModelDiffeomorph : H ≃ₘ⟮I, InteriorIC⟯ (InteriorE2 × ℝ) where
  toEquiv := (I.toHomeomorph.trans
    ((LinearEquiv.ofFinrankEq (R := ℝ) E (InteriorE2 × ℝ) (by simpa using hdim)).toContinuousLinearEquiv.toHomeomorph)).toEquiv
  contMDiff_toFun := by
    let L := (LinearEquiv.ofFinrankEq (R := ℝ) E (InteriorE2 × ℝ) (by simpa using hdim)).toContinuousLinearEquiv
    have hL : ContDiff ℝ ∞ L := L.contDiff
    exact (hL.fst.contMDiff.comp I.contMDiff).prodMk (hL.snd.contMDiff.comp I.contMDiff)
  contMDiff_invFun := by
    have hs : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
      rw [← contMDiffOn_univ, ← I.range_eq_univ]
      exact I.contMDiffOn_symm
    have hid : ContMDiff InteriorIC 𝓘(ℝ, InteriorE2 × ℝ) ∞ (id : InteriorE2 × ℝ → InteriorE2 × ℝ) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact hs.comp (((LinearEquiv.ofFinrankEq (R := ℝ) E (InteriorE2 × ℝ) (by simpa using hdim)).toContinuousLinearEquiv.symm.contDiff.contMDiff).comp hid)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type*} {precision : ι → ℝ}
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)

theorem cutCoreInteriorHalfChart_apply_original (x p : coreInteriorDomain f) :
    cutCoreInteriorHalfChart I hdim f x (coreInteriorInclusion f p) =
      ((coreInteriorModelDiffeomorph I hdim (chartAt H x p)).1,
        halfSpaceInteriorChart ((coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1)
          (coreInteriorModelDiffeomorph I hdim (chartAt H x p)).2) := by
  let D := coreInteriorModelDiffeomorph I hdim
  let e := ((chartAt H x).transHomeomorph D.toHomeomorph).lift_openEmbedding (isOpenEmbedding_coreInteriorInclusion f)
  change ( (e (coreInteriorInclusion f p)).1,
      halfSpaceInteriorChart ((e (coreInteriorInclusion f x)).2 - 1) (e (coreInteriorInclusion f p)).2) = _
  dsimp only [e]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem cutCoreInteriorHalfChart_symm_original (x : coreInteriorDomain f) (z : InteriorIH) :
    (cutCoreInteriorHalfChart I hdim f x).symm z =
      coreInteriorInclusion f ((chartAt H x).symm
        ((coreInteriorModelDiffeomorph I hdim).symm
          (z.1, z.2.val 0 + ((coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1)))) := by
  let D := coreInteriorModelDiffeomorph I hdim
  let e := ((chartAt H x).transHomeomorph D.toHomeomorph).lift_openEmbedding (isOpenEmbedding_coreInteriorInclusion f)
  change coreInteriorInclusion f ((chartAt H x).symm
    (D.symm (z.1, z.2.val 0 + ((e (coreInteriorInclusion f x)).2 - 1)))) = _
  dsimp only [e]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem cutCoreInteriorHalfChart_source_original (x : coreInteriorDomain f) :
    (cutCoreInteriorHalfChart I hdim f x).source = coreInteriorInclusion f ''
      {p : coreInteriorDomain f | p ∈ (chartAt H x).source ∧
        (coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1 <
          (coreInteriorModelDiffeomorph I hdim (chartAt H x p)).2} := by
  let D := coreInteriorModelDiffeomorph I hdim
  let e := ((chartAt H x).transHomeomorph D.toHomeomorph).lift_openEmbedding (isOpenEmbedding_coreInteriorInclusion f)
  ext z
  change (z ∈ e.source ∧ e z ∈ ((OpenPartialHomeomorph.refl InteriorE2).prod
    (halfSpaceInteriorChart ((e (coreInteriorInclusion f x)).2 - 1))).source) ↔ _
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hh⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    have ht := hh.2
    change (e (coreInteriorInclusion f x)).2 - 1 < (e (coreInteriorInclusion f p)).2 at ht
    dsimp only [e] at ht
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.lift_openEmbedding_apply] at ht
    exact ht
  · rintro ⟨p, ⟨hp, ht⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    change True ∧ (e (coreInteriorInclusion f x)).2 - 1 < (e (coreInteriorInclusion f p)).2
    refine ⟨trivial, ?_⟩
    dsimp only [e]
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact ht

theorem cutCoreInteriorHalfChart_target_original (x : coreInteriorDomain f) :
    (cutCoreInteriorHalfChart I hdim f x).target =
      {z : InteriorIH | 0 < z.2.val 0 ∧
        (coreInteriorModelDiffeomorph I hdim).symm
          (z.1, z.2.val 0 + ((coreInteriorModelDiffeomorph I hdim (chartAt H x x)).2 - 1)) ∈
            (chartAt H x).target} := by
  let D := coreInteriorModelDiffeomorph I hdim
  let e := ((chartAt H x).transHomeomorph D.toHomeomorph).lift_openEmbedding (isOpenEmbedding_coreInteriorInclusion f)
  ext z
  change ((True ∧ 0 < z.2.val 0) ∧
    D.symm (z.1, z.2.val 0 + ((e (coreInteriorInclusion f x)).2 - 1)) ∈ (chartAt H x).target) ↔ _
  dsimp only [e]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  simp only [true_and]
  rfl

variable [IsManifold I ∞ M]

theorem cutCoreInteriorHalfChart_symm_ambient_contMDiffOn (x : coreInteriorDomain f) :
    ContMDiffOn InteriorIR I ∞
      (fun z : InteriorIH => ((cutCoreInteriorHalfChart I hdim f x).symm z).val)
      (cutCoreInteriorHalfChart I hdim f x).target := by
  let D := coreInteriorModelDiffeomorph I hdim
  let a := (D (chartAt H x x)).2 - 1
  let ψ : InteriorIH → H := fun z => D.symm (z.1, z.2.val 0 + a)
  have hf : ContMDiff 𝓘(ℝ, InteriorE2 × EuclideanSpace ℝ (Fin 1)) (𝓡 2) ∞
      (Prod.fst : InteriorE2 × EuclideanSpace ℝ (Fin 1) → InteriorE2) := contDiff_fst.contMDiff
  have ht : ContMDiff 𝓘(ℝ, InteriorE2 × EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ) ∞
      (fun z : InteriorE2 × EuclideanSpace ℝ (Fin 1) => z.2 0) :=
    ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).contDiff.comp contDiff_snd).contMDiff
  have hfst : ContMDiff InteriorIR (𝓡 2) ∞ (fun z : InteriorIH => z.1) := hf.comp InteriorIR.contMDiff
  have hheight : ContMDiff InteriorIR 𝓘(ℝ) ∞ (fun z : InteriorIH => z.2.val 0) := ht.comp InteriorIR.contMDiff
  have hψ : ContMDiff InteriorIR I ∞ ψ :=
    D.symm.contMDiff.comp (hfst.prodMk (hheight.add contMDiff_const))
  have he : (fun z : InteriorIH => ((cutCoreInteriorHalfChart I hdim f x).symm z).val) =
      (fun z => ((chartAt H x).symm (ψ z)).val) := by
    funext z
    rw [cutCoreInteriorHalfChart_symm_original]
    rfl
  rw [he]
  intro z hz
  rw [cutCoreInteriorHalfChart_target_original] at hz
  have ht : ψ z ∈ (chartAt H x).target := hz.2
  have hchart : ContMDiffAt I I ∞ (chartAt H x).symm (ψ z) :=
    (contMDiffOn_chart_symm (I := I) (n := ∞) (x := x)).contMDiffAt
      ((chartAt H x).open_target.mem_nhds ht)
  exact ((contMDiff_subtype_val (I := I) (U := coreInteriorDomain f)).contMDiffAt.comp z
    (hchart.comp z hψ.contMDiffAt)).contMDiffWithinAt

theorem cutCoreInteriorHalfChart_comp_contMDiffAt
    {E' H' P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    [TopologicalSpace P] [ChartedSpace H' P]
    (F : P → cutCore f) (x : coreInteriorDomain f) (p : P)
    (hF : ContMDiffAt J I ∞ (fun y => (F y).val) p)
    (hp : F p ∈ (cutCoreInteriorHalfChart I hdim f x).source) :
    ContMDiffAt J InteriorIR ∞ (fun y => cutCoreInteriorHalfChart I hdim f x (F y)) p := by
  let D := coreInteriorModelDiffeomorph I hdim
  let a := (D (chartAt H x x)).2 - 1
  let G : P → InteriorIH := fun y =>
    ((D (chartAt H x.val (F y).val)).1,
      halfSpaceInteriorChart a (D (chartAt H x.val (F y).val)).2)
  have hpin := hp
  rw [cutCoreInteriorHalfChart_source_original] at hpin
  obtain ⟨q, ⟨hq, hh⟩, he⟩ := hpin
  have hval : q.val = (F p).val := congrArg Subtype.val he
  have hqM : q.val ∈ (chartAt H x.val).source := by
    simpa only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hq
  have hchart : ContMDiffAt I I ∞ (chartAt H x.val) (F p).val :=
    (contMDiffOn_chart (I := I) (n := ∞) (x := x.val)).contMDiffAt
      ((chartAt H x.val).open_source.mem_nhds (hval ▸ hqM))
  have hmod : ContMDiffAt J InteriorIC ∞ (fun y => D (chartAt H x.val (F y).val)) p :=
    D.contMDiff.contMDiffAt.comp p (hchart.comp p hF)
  have hfst : ContMDiffAt J (𝓡 2) ∞ (fun y => (D (chartAt H x.val (F y).val)).1) p :=
    contMDiff_fst.contMDiffAt.comp p hmod
  have hsnd : ContMDiffAt J 𝓘(ℝ) ∞ (fun y => (D (chartAt H x.val (F y).val)).2) p :=
    contMDiff_snd.contMDiffAt.comp p hmod
  have ht : a < (D (chartAt H x.val (F p).val)).2 := by
    rw [← hval]
    exact hh
  have hhalf : ContMDiffAt J (𝓡∂ 1) ∞
      (fun y => halfSpaceInteriorChart a (D (chartAt H x.val (F y).val)).2) p :=
    ((halfSpaceInteriorChart_contMDiffOn a).contMDiffAt (isOpen_Ioi.mem_nhds ht)).comp p hsnd
  have hG : ContMDiffAt J InteriorIR ∞ G p := by
    rw [contMDiffAt_iff_target]
    refine ⟨hfst.continuousAt.prodMk hhalf.continuousAt, ?_⟩
    change ContMDiffAt J 𝓘(ℝ, InteriorE2 × EuclideanSpace ℝ (Fin 1)) ∞
      (fun y => ((D (chartAt H x.val (F y).val)).1,
        (halfSpaceInteriorChart a (D (chartAt H x.val (F y).val)).2).val)) p
    exact hfst.prodMk_space ((𝓡∂ 1).contMDiff.contMDiffAt.comp p hhalf)
  have hFc : ContinuousAt F p :=
    _root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hF.continuousAt
  have heq : (fun y => cutCoreInteriorHalfChart I hdim f x (F y)) =ᶠ[𝓝 p] G := by
    filter_upwards [hFc.preimage_mem_nhds ((cutCoreInteriorHalfChart I hdim f x).open_source.mem_nhds hp)] with y hy
    rw [cutCoreInteriorHalfChart_source_original] at hy
    obtain ⟨qy, _, hqy⟩ := hy
    dsimp only [G]
    rw [← hqy, cutCoreInteriorHalfChart_apply_original]
    rfl
  exact hG.congr_of_eventuallyEq heq

theorem cutCoreInteriorHalfChart_contMDiff_transition (x y : coreInteriorDomain f) :
    ContMDiffOn InteriorIR InteriorIR ∞
      ((cutCoreInteriorHalfChart I hdim f x).symm.trans (cutCoreInteriorHalfChart I hdim f y))
      ((cutCoreInteriorHalfChart I hdim f x).symm.trans (cutCoreInteriorHalfChart I hdim f y)).source := by
  intro z hz
  have hF := (cutCoreInteriorHalfChart_symm_ambient_contMDiffOn I hdim f x).contMDiffAt
    ((cutCoreInteriorHalfChart I hdim f x).open_target.mem_nhds hz.1)
  exact (cutCoreInteriorHalfChart_comp_contMDiffAt I hdim f InteriorIR
    (cutCoreInteriorHalfChart I hdim f x).symm y z hF hz.2).contMDiffWithinAt
end DifferentialGeometry.Topology.ThreeManifold.Surgery
