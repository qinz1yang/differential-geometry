import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointWide

/-!
# FC39 producer, packet P0 (gate 1): the arc layer of the one S³ configuration

The circle-region faces of the two partitioned faces (`r = 1`, face `2`; `r = 4`, face `3`), built
from the residual traces and the end registration (review 49: not by calling FC40):

* the base arc of the label `σ`: `s ↦ (ψ, r) = (1 + 3 s, circEndVal σ)` (`sphereArcBase σ`), a smooth
  embedding of `[0, 1]` into the circle base, on the zero set of the `r`-face function of side `σ`;
* the arc face `sphereArcFace σ` = the saturated tube over the base arc = `R ∩ {q₀ = ±3/5}`
  (`sphereArcFace_eq`), parametrized by the annulus `(z, s) ↦ J(arc(s), z)`;
* every partitioned face is the union of its two handle end disks and its arc face
  (`sphere_face_partition`), the arc face is the face's trace in `R` (`sphere_face_region_inter`);
* the end rim of every handle end is the end disk's trace on its arc (`sphere_endDisk_rim`); the two
  ends of the arc `σ` are the ends `(finTwoEquiv.symm e, e != σ)`, at the corners of the circle region;
* **`sphereArcLayer : ArcLayer sphereW sphereEdgeLayer sphereCircleRegion sphereFaceLayer
  sphereHandleEndLayer sphereRimLayer`** — two arcs, no loops.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc

/-! ## The base arcs -/

/-- The base arc of the label `σ` in `ℝ²`: `s ↦ (ψ, r) = (1 + 3 s, circEndVal σ)`. -/
def sphereArcBaseE (σ : Bool) (s : ℝ) : E2 :=
  sphereCircleEquiv.symm (1, circEndVal σ) + s • sphereCircleEquiv.symm (3, 0)

theorem sphereCircleEquiv_arcBaseE (σ : Bool) (s : ℝ) :
    sphereCircleEquiv (sphereArcBaseE σ s) = (1 + 3 * s, circEndVal σ) := by
  rw [sphereArcBaseE, map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · change 1 + s * 3 = 1 + 3 * s
    ring
  · change circEndVal σ + s * 0 = circEndVal σ
    ring

theorem circEndVal_mem_wide_JOINT2 (σ : Bool) : circEndVal σ ∈ sphereCircleWide := by
  cases σ
  · change (1 : ℝ) / 2 < 1 ∧ (1 : ℝ) < 8
    norm_num
  · change (1 : ℝ) / 2 < 4 ∧ (4 : ℝ) < 8
    norm_num

theorem sphereArcBaseE_mem (σ : Bool) (s : Icc (0 : ℝ) 1) :
    sphereArcBaseE σ s ∈ sphereCircleBaseOpens := by
  change sphereArcBaseE σ s ∈ sphereCircleBaseSet
  rw [mem_sphereCircleBaseSet, sphereCircleEquiv_arcBaseE]
  refine ⟨?_, circEndVal_mem_wide_JOINT2 σ⟩
  change (1 : ℝ) / 2 < 1 + 3 * (s : ℝ) ∧ 1 + 3 * (s : ℝ) < 8
  constructor <;> linarith [s.2.1, s.2.2]

/-- **The base arc of the label `σ`** in the circle base. -/
def sphereArcBase (σ : Bool) (s : Icc (0 : ℝ) 1) : sphereCircleBaseOpens :=
  ⟨sphereArcBaseE σ s, sphereArcBaseE_mem σ s⟩

theorem sphereCircleEquiv_arcBase (σ : Bool) (s : Icc (0 : ℝ) 1) :
    sphereCircleEquiv (sphereArcBase σ s : E2) = (1 + 3 * (s : ℝ), circEndVal σ) :=
  sphereCircleEquiv_arcBaseE σ s

theorem continuous_sphereArcBaseE (σ : Bool) : Continuous (sphereArcBaseE σ) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem sphereArcDirection_ne_zero : sphereCircleEquiv.symm ((3 : ℝ), (0 : ℝ)) ≠ 0 := by
  intro h0
  have h1 := congrArg sphereCircleEquiv h0
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at h1
  have h2 := congrArg Prod.fst h1
  norm_num at h2

theorem hasFDerivAt_sphereArcBaseE (σ : Bool) (s : ℝ) :
    HasFDerivAt (sphereArcBaseE σ)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (sphereCircleEquiv.symm ((3 : ℝ), (0 : ℝ)))) s :=
  ((hasFDerivAt_id s).smul_const (sphereCircleEquiv.symm ((3 : ℝ), (0 : ℝ)))).const_add
    (sphereCircleEquiv.symm (1, circEndVal σ))

theorem isImmersion_sphereArcBaseE (σ : Bool) :
    IsImmersion 𝓘(ℝ, ℝ) (𝓡 2) ∞ (sphereArcBaseE σ) := by
  refine isImmersion_of_injective_mfderiv (by simp)
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff fun s => ?_
  rw [mfderiv_eq_fderiv, (hasFDerivAt_sphereArcBaseE σ s).fderiv]
  intro a a' h
  simpa using h

theorem isSmoothEmbedding_sphereArcBaseE (σ : Bool) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ fun s : Icc (0 : ℝ) 1 => sphereArcBaseE σ s := by
  have himm : IsImmersion (𝓡∂ 1) (𝓡 2) ∞ (sphereArcBaseE σ ∘ fun s : Icc (0 : ℝ) 1 => s.val) :=
    IsImmersion.comp_of_boundarylessManifold_middle
      (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)).isImmersion
      (isImmersion_sphereArcBaseE σ) (by simp)
  refine ⟨himm, (Continuous.isClosedEmbedding himm.contMDiff.continuous ?_).isEmbedding⟩
  intro s s' h
  have h1 := congrArg (fun v => (sphereCircleEquiv v).1) h
  simp only [Function.comp, sphereCircleEquiv_arcBaseE] at h1
  exact Subtype.ext (by linarith)

/-- **The base arcs are smooth embeddings of `[0, 1]` into the circle base.** -/
theorem isSmoothEmbedding_sphereArcBase (σ : Bool) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (sphereArcBase σ) :=
  isSmoothEmbedding_codRestrict_opens (isSmoothEmbedding_sphereArcBaseE σ) sphereCircleBaseOpens
    fun s => sphereArcBaseE_mem σ s

/-- The base arc lies on the zero set of the `r`-face function of side `σ`. -/
theorem sphereArcBase_defining (σ : Bool) (t : Icc (0 : ℝ) 1) :
    circDefining (circFaceEquiv (true, σ)) (sphereArcBase σ t) = 0 := by
  rw [circDefining_face, circFaceFn_eq_zero_iff, circCoordL_true, sphereCircleEquiv_arcBase]

theorem one_add_three_iccEnd (e : Bool) : 1 + 3 * ((iccEnd e : Icc (0 : ℝ) 1) : ℝ) = circEndVal e := by
  cases e
  · change 1 + 3 * (0 : ℝ) = 1
    norm_num
  · change 1 + 3 * (1 : ℝ) = 4
    norm_num

theorem sphereCircleEquiv_arcBase_iccEnd (σ e : Bool) :
    sphereCircleEquiv (sphereArcBase σ (iccEnd e) : E2) = (circEndVal e, circEndVal σ) := by
  rw [sphereCircleEquiv_arcBase, one_add_three_iccEnd]

/-! ## The circle of the annulus -/

/-- `S¹ ⊂ ℝ²` is the unit circle of `ℂ`. -/
def sphereArcCircle : Metric.sphere (0 : E2) 1 ≃ₜ Circle :=
  (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]).symm

/-! ## The arc faces and their annuli -/

/-- **The arc face of the label `σ`**: the saturated tube over the base arc. -/
def sphereArcFace (σ : Bool) : Set sphereW.Carrier :=
  sphereCircleBundle.tube (range (sphereArcBase σ))

/-- The annulus parametrization of the arc face of the label `σ`. -/
def sphereArcAnnulus (σ : Bool) (q : Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    sphereW.Carrier :=
  sphereCircleChart ((sphereArcBase σ q.2 : E2), sphereArcCircle q.1)

theorem sphereArcAnnulus_source (σ : Bool) (q : Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    ((sphereArcBase σ q.2 : E2), sphereArcCircle q.1) ∈ sphereCircleChart.source := by
  rw [sphereCircleChart_source]
  exact ⟨(sphereArcBase σ q.2).2, mem_univ _⟩

theorem continuous_sphereArcAnnulus (σ : Bool) : Continuous (sphereArcAnnulus σ) := by
  have hg : Continuous fun q : Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1 =>
      ((sphereArcBase σ q.2 : E2), sphereArcCircle q.1) :=
    ((continuous_sphereArcBaseE σ).comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (sphereArcCircle.continuous.comp continuous_fst)
  exact sphereCircleChart.contMDiffOn.continuousOn.comp_continuous hg (sphereArcAnnulus_source σ)

theorem sphereArcAnnulus_injective (σ : Bool) : Injective (sphereArcAnnulus σ) := by
  intro q q' h
  have h' := sphereCircleChart.injOn (sphereArcAnnulus_source σ q) (sphereArcAnnulus_source σ q') h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  have h3 := congrArg (fun v => (sphereCircleEquiv v).1) h1
  simp only [sphereCircleEquiv_arcBase] at h3
  exact Prod.ext (sphereArcCircle.injective h2) (Subtype.ext (by linarith))

theorem sphereArcFace_eq_image (σ : Bool) :
    sphereArcFace σ = sphereCircleChart '' ((Subtype.val '' range (sphereArcBase σ)) ×ˢ univ) :=
  sphereCircleBundle_tube _

theorem range_sphereArcAnnulus (σ : Bool) : range (sphereArcAnnulus σ) = sphereArcFace σ := by
  rw [sphereArcFace_eq_image]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨⟨sphereArcBase σ q.2, ⟨q.2, rfl⟩, rfl⟩, mem_univ _⟩, rfl⟩
  · rintro ⟨⟨c, θ⟩, ⟨⟨c', ⟨s, rfl⟩, rfl⟩, -⟩, rfl⟩
    refine ⟨(sphereArcCircle.symm θ, s), ?_⟩
    change sphereCircleChart _ = sphereCircleChart _
    rw [Homeomorph.apply_symm_apply]

theorem sphereArcAnnulus_image_fibre (σ : Bool) (s : Icc (0 : ℝ) 1) :
    sphereArcAnnulus σ '' {q | q.2 = s} = sphereCircleBundle.fibre (sphereArcBase σ s) := by
  rw [sphereCircleBundle_fibre]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨sphereArcCircle q.1, ?_⟩
    change q.2 = s at hq
    change sphereCircleChart _ = sphereCircleChart _
    rw [hq]
  · rintro ⟨θ, rfl⟩
    refine ⟨(sphereArcCircle.symm θ, s), rfl, ?_⟩
    change sphereCircleChart _ = sphereCircleChart _
    rw [Homeomorph.apply_symm_apply]

theorem sphereArcAnnulus_proj (σ : Bool) (q : Metric.sphere (0 : E2) 1 × Icc (0 : ℝ) 1) :
    ∃ hx : sphereArcAnnulus σ q ∈ sphereCircleDomain,
      sphereCircleProj ⟨sphereArcAnnulus σ q, hx⟩ = sphereArcBase σ q.2 :=
  ⟨sphereCircleChart_mem_domain (sphereArcAnnulus_source σ q),
    Subtype.ext (sphereCircleProj_chart (sphereArcAnnulus_source σ q))⟩

/-- **The arc face is the trace of the level sphere `q₀ = ±3/5` in the circle region.** -/
theorem sphereArcFace_eq (σ : Bool) :
    sphereArcFace σ =
      sphereCircleBundle.region ∩ {x | sphereHeight x = sphereResidualHeight σ} := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs⟩, rfl⟩
    have hc : sphereCircleEquiv (sphereCircleProj y : E2) = (1 + 3 * (s : ℝ), circEndVal σ) := by
      have hs' : sphereArcBase σ s = sphereCircleProj y := hs
      rw [← hs', sphereCircleEquiv_arcBase]
    refine ⟨⟨y, ?_, rfl⟩, ?_⟩
    · change sphereCircleEquiv (sphereCircleProj y : E2) ∈ Icc (1 : ℝ) 4 ×ˢ Icc (1 : ℝ) 4
      rw [hc]
      refine ⟨⟨by linarith [s.2.1], by linarith [s.2.2]⟩, ?_⟩
      cases σ
      · exact ⟨le_rfl, by norm_num [circEndVal]⟩
      · exact ⟨by norm_num [circEndVal], le_rfl⟩
    · change sphereHeight y.val = sphereResidualHeight σ
      refine (sphereHeight_circDomain y).trans ?_
      rw [circCoordL_true, hc]
      cases σ
      · change circHeight 1 = -3 / 5
        norm_num [circHeight]
      · change circHeight 4 = 3 / 5
        norm_num [circHeight]
  · rintro ⟨⟨y, hy, rfl⟩, hh⟩
    change sphereCircleEquiv (sphereCircleProj y : E2) ∈ Icc (1 : ℝ) 4 ×ˢ Icc (1 : ℝ) 4 at hy
    change sphereHeight y.val = sphereResidualHeight σ at hh
    have hh' := (sphereHeight_circDomain y).symm.trans hh
    rw [circCoordL_true] at hh'
    have hr := (circHeight_eq_residualHeight_iff (by linarith [hy.2.1])).1 hh'
    have hs : ((sphereCircleEquiv (sphereCircleProj y : E2)).1 - 1) / 3 ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
    refine ⟨y, ⟨⟨_, hs⟩, ?_⟩, rfl⟩
    apply Subtype.ext
    apply sphereCircleEquiv.injective
    change sphereCircleEquiv (sphereArcBaseE σ _) = _
    rw [sphereCircleEquiv_arcBaseE]
    refine Prod.ext ?_ hr.symm
    change 1 + 3 * (((sphereCircleEquiv (sphereCircleProj y : E2)).1 - 1) / 3) =
      (sphereCircleEquiv (sphereCircleProj y : E2)).1
    ring

theorem sphereArcFace_subset_level (σ : Bool) :
    sphereArcFace σ ⊆ {x | sphereHeight x = sphereResidualHeight σ} := by
  rw [sphereArcFace_eq]
  exact inter_subset_right

theorem sphereArcFace_disjoint {σ σ' : Bool} (h : σ ≠ σ') :
    Disjoint (sphereArcFace σ) (sphereArcFace σ') := by
  refine Set.disjoint_left.2 fun x hx hx' => h (sphereResidualHeight_injective ?_)
  exact (sphereArcFace_subset_level σ hx).symm.trans (sphereArcFace_subset_level σ' hx')

/-! ## Faces: end disks and arcs -/

theorem sphere_endDisks_label (σ : Bool) :
    (⋃ (h : Fin 2) (b : Bool) (_ : sphereLabelFace (edgeEndLabel (h, b)) = sphereLabelFace σ),
      (sphereEdgeLayer.handle h).endDisk b) =
      sphereEdgeBundle.edgePiece ∩ {x | sphereHeight x = sphereResidualHeight σ} := by
  rw [← residualSet_sphereResidual, sphere_edge_faces]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨h, b, hl, hx⟩
    refine ⟨sphereEdgeEndEquiv (h, b), ?_, ?_⟩
    · rw [sphereHorizontal_apply, sphereLabelFace_injective hl]
    · rw [← sphereEndDisk_eq]
      exact hx
  · rintro ⟨e, he, hx⟩
    obtain ⟨⟨h, b⟩, rfl⟩ := sphereEdgeEndEquiv.surjective e
    rw [sphereHorizontal_apply] at he
    refine ⟨h, b, by rw [sphereResidual_injective he], ?_⟩
    rw [sphereEndDisk_eq]
    exact hx

theorem sphere_arcUnion (σ : Bool) :
    (⋃ (j : Fin 2) (_ : sphereLabelFace (finTwoEquiv j) = sphereLabelFace σ),
      sphereArcFace (finTwoEquiv j)) = sphereArcFace σ := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    rwa [sphereLabelFace_injective hj] at hx
  · intro hx
    exact ⟨finTwoEquiv.symm σ, by rw [Equiv.apply_symm_apply], by rwa [Equiv.apply_symm_apply]⟩

theorem sphereResidualHeight_band (σ : Bool) :
    -3 / 5 ≤ sphereResidualHeight σ ∧ sphereResidualHeight σ ≤ 3 / 5 := by
  cases σ
  · change -3 / 5 ≤ (-3 / 5 : ℝ) ∧ (-3 / 5 : ℝ) ≤ 3 / 5
    norm_num
  · change -3 / 5 ≤ (3 / 5 : ℝ) ∧ (3 / 5 : ℝ) ≤ 3 / 5
    norm_num

/-- **Every partitioned face is the union of its handle end disks and its arc face.** -/
theorem sphere_face_partition (σ : Bool) :
    (⋃ (h : Fin 2) (b : Bool) (_ : sphereLabelFace (edgeEndLabel (h, b)) = sphereLabelFace σ),
        (sphereEdgeLayer.handle h).endDisk b) ∪
      (⋃ (j : Fin 2) (_ : sphereLabelFace (finTwoEquiv j) = sphereLabelFace σ),
        sphereArcFace (finTwoEquiv j)) = sphereFaceSet (sphereLabelFace σ) := by
  rw [sphere_endDisks_label, sphere_arcUnion, sphereArcFace_eq, sphereFaceSet_labelFace,
    ← union_inter_distrib_right]
  refine inter_eq_right.2 fun x hx => ?_
  have hx' : sphereHeight x = sphereResidualHeight σ := hx
  exact band_subset_edge_union_region (by rw [hx']; exact (sphereResidualHeight_band σ).1)
    (by rw [hx']; exact (sphereResidualHeight_band σ).2)

/-- **The trace of a partitioned face in the circle region is its arc face.** -/
theorem sphere_face_region_inter (σ : Bool) :
    sphereFaceSet (sphereLabelFace σ) ∩ sphereCircleBundle.region =
      ⋃ (j : Fin 2) (_ : sphereLabelFace (finTwoEquiv j) = sphereLabelFace σ),
        sphereArcFace (finTwoEquiv j) := by
  rw [sphere_arcUnion, sphereArcFace_eq, sphereFaceSet_labelFace, inter_comm]

/-! ## Ends of arcs and handle rims -/

/-- The rim base point of the end `(h, b)` is the end `finTwoEquiv h` of the arc of its label. -/
theorem sphere_rimBase_eq_arcBase (h : Fin 2) (b : Bool) :
    sphereRimBase (edgeInterval (finTwoEquiv h) (iccEnd b)) =
      sphereArcBase (edgeEndLabel (h, b)) (iccEnd (finTwoEquiv h)) := by
  have he : sphereCircleEquiv (sphereRimBase (edgeInterval (finTwoEquiv h) (iccEnd b)) : E2) =
      (circEndVal (finTwoEquiv h), circEndVal (finTwoEquiv h != b)) :=
    sphereJunctions_rimBase_end (h, b)
  apply Subtype.ext
  apply sphereCircleEquiv.injective
  rw [he, sphereCircleEquiv_arcBase_iccEnd]
  rfl

/-- **The end rim of `(h, b)` is the whole circle fibre over the end of the arc of its label.** -/
theorem sphere_rim_eq_arcFibre (h : Fin 2) (b : Bool) :
    (fun x : ClosedCell 2 => (sphereEdgeLayer.handle h).map (x, iccEnd b)) '' diskRim =
      sphereCircleBundle.fibre (sphereArcBase (edgeEndLabel (h, b)) (iccEnd (finTwoEquiv h))) := by
  rw [← sphere_rimBase_eq_arcBase]
  exact sphereHandle_rim_eq_fibre (finTwoEquiv h) (iccEnd b)

/-- **The end rim is the trace of the end disk on the arc face of its label.** -/
theorem sphere_endDisk_rim (h : Fin 2) (b : Bool) :
    (fun x : ClosedCell 2 => (sphereEdgeLayer.handle h).map (x, iccEnd b)) '' diskRim =
      (sphereEdgeLayer.handle h).endDisk b ∩ sphereArcFace (edgeEndLabel (h, b)) := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨image_subset_range _ _ hx, ?_⟩
    rw [sphere_rim_eq_arcFibre] at hx
    exact (sphere_fibre_subset_tube_iff (V := range (sphereArcBase (edgeEndLabel (h, b))))).2
      (mem_range_self _) hx
  · rintro x ⟨⟨w, rfl⟩, hx⟩
    refine ⟨w, ?_, rfl⟩
    have hreg := ((sphereArcFace_eq _).subset hx).1
    have hedge := range_sphereHandle_subset_edgePiece h (mem_range_self (w, iccEnd b))
    have hv : (sphereEdgeLayer.handle h).map (w, iccEnd b) ∈ sphereEdgeBundle.vertical := by
      rw [← sphere_edge_region]
      exact ⟨hedge, hreg⟩
    obtain ⟨y, ⟨-, hy⟩, hyx⟩ := hv
    have h1 : edgeHeightR ((cycleS3Handle (finTwoEquiv h)).map (w, iccEnd b)) = 1 := by
      change edgeHeightR ((sphereEdgeLayer.handle h).map (w, iccEnd b)) = 1
      rw [← hyx]
      exact hy
    rw [cycleS3Handle_map, edgeHeightR_chart (handle_box w _)] at h1
    exact diskRim_iff_FC39P0b.2
      ((pow_left_inj₀ (norm_nonneg w.val) zero_le_one two_ne_zero).1 (by rw [h1, one_pow]))

theorem sphere_arcEnd_label (j : Fin 2) (e : Bool) :
    edgeEndLabel (finTwoEquiv.symm e, e != finTwoEquiv j) = finTwoEquiv j := by
  change (finTwoEquiv (finTwoEquiv.symm e) != (e != finTwoEquiv j)) = _
  rw [Equiv.apply_symm_apply, bne_bne_self]

theorem sphere_handleArc_arcEnd (j : Fin 2) (e : Bool) :
    finTwoEquiv.symm (edgeEndLabel (finTwoEquiv.symm e, e != finTwoEquiv j)) = j := by
  rw [sphere_arcEnd_label, Equiv.symm_apply_apply]

theorem sphere_arcEnd_surjective (h : Fin 2) (b : Bool) :
    (finTwoEquiv.symm (finTwoEquiv h),
        (finTwoEquiv h != finTwoEquiv (finTwoEquiv.symm (edgeEndLabel (h, b))))) = (h, b) := by
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  change (h, (finTwoEquiv h != (finTwoEquiv h != b))) = (h, b)
  rw [bne_bne_self]

theorem sphere_handleArc_meets (h : Fin 2) (b : Bool) (j : Fin 2)
    (hne : ((sphereEdgeLayer.handle h).endDisk b ∩ sphereArcFace (finTwoEquiv j)).Nonempty) :
    finTwoEquiv.symm (edgeEndLabel (h, b)) = j := by
  obtain ⟨x, hx1, hx2⟩ := hne
  have h1 : sphereHeight x = sphereResidualHeight (edgeEndLabel (h, b)) :=
    sphereEndDisk_subset_level h b hx1
  have h2 : sphereHeight x = sphereResidualHeight (finTwoEquiv j) := sphereArcFace_subset_level _ hx2
  rw [sphereResidualHeight_injective (h1.symm.trans h2), Equiv.symm_apply_apply]

/-- The two ends of the arc `σ` meet the handle end annuli. -/
theorem sphere_arcAnnulus_end (j : Fin 2) (e : Bool) :
    (sphereEdgeLayer.handle (finTwoEquiv.symm e)).endDisk (e != finTwoEquiv j) ∩
        sphereArcFace (finTwoEquiv j) =
      sphereArcAnnulus (finTwoEquiv j) '' {q | q.2 = iccEnd e} := by
  have h1 := sphere_endDisk_rim (finTwoEquiv.symm e) (e != finTwoEquiv j)
  rw [sphere_arcEnd_label] at h1
  rw [← h1, sphere_rim_eq_arcFibre, sphere_arcEnd_label, Equiv.apply_symm_apply,
    sphereArcAnnulus_image_fibre]

/-- The corner centre of the end `(h, b)` is the end `finTwoEquiv h` of the arc of its label. -/
theorem sphere_corner_eq_arcBase (h : Fin 2) (b : Bool) :
    circCorner (sphereHandleCorner h b) (0, 0) =
      sphereArcBase (edgeEndLabel (h, b)) (iccEnd (finTwoEquiv h)) := by
  rw [sphere_corner_center sphereJunctions, circEndOfCorner_handle]
  exact sphere_rimBase_eq_arcBase h b

theorem sphere_arcBase_end (j : Fin 2) (e : Bool) :
    sphereArcBase (finTwoEquiv j) (iccEnd e) =
      circCorner (sphereHandleCorner (finTwoEquiv.symm e) (e != finTwoEquiv j)) (0, 0) := by
  rw [sphere_corner_eq_arcBase, sphere_arcEnd_label, Equiv.apply_symm_apply]

theorem iUnion_fin_zero_JOINT2 {α : Type*} (P : Fin 0 → Prop) (s : Fin 0 → Set α) :
    (⋃ (j : Fin 0) (_ : P j), s j) = ∅ :=
  iUnion_of_empty _

/-! ## The arc layer -/

/-- **The arc layer of the S³ configuration**: two arcs (one per partitioned face), no loops. -/
def sphereArcLayer :
    ArcLayer sphereW sphereEdgeLayer sphereCircleRegion sphereFaceLayer sphereHandleEndLayer
      sphereRimLayer where
  arcFaceCount := 2
  arcFace j := sphereArcFace (finTwoEquiv j)
  arcOwner j := sphereLabelFace (finTwoEquiv j)
  arcOwner_kind _ := sphereFaceKind_labelFace _
  arcBase j := sphereArcBase (finTwoEquiv j)
  arcBase_embedding _ := isSmoothEmbedding_sphereArcBase _
  arcFace_eq _ := rfl
  arcDefining j := circFaceEquiv (true, finTwoEquiv j)
  arcBase_defining j t := sphereArcBase_defining (finTwoEquiv j) t
  arcAnnulus j := sphereArcAnnulus (finTwoEquiv j)
  arcAnnulus_continuous _ := continuous_sphereArcAnnulus _
  arcAnnulus_injective _ := sphereArcAnnulus_injective _
  arcAnnulus_range _ := range_sphereArcAnnulus _
  arcAnnulus_proj j q := sphereArcAnnulus_proj (finTwoEquiv j) q
  loopFaceCount := 0
  loopFace j := j.elim0
  loopOwner j := j.elim0
  loopOwner_kind j := j.elim0
  loopBase j := j.elim0
  loopBase_embedding j := j.elim0
  loopFace_eq j := j.elim0
  loopDefining j := j.elim0
  loopBase_defining j := j.elim0
  loopFace_closed j := j.elim0
  loopFace_nonempty j := j.elim0
  arcFace_disjoint _ _ hne := sphereArcFace_disjoint fun h => hne (finTwoEquiv.injective h)
  loopFace_disjoint j := j.elim0
  arc_loop_disjoint _ j := j.elim0
  face_partition f hf := by
    obtain ⟨σ, rfl⟩ := exists_labelFace_of_partitioned hf
    rw [iUnion_fin_zero_JOINT2, union_empty]
    exact sphere_face_partition σ
  face_region_inter f hf := by
    obtain ⟨σ, rfl⟩ := exists_labelFace_of_partitioned hf
    rw [iUnion_fin_zero_JOINT2, union_empty]
    exact sphere_face_region_inter σ
  handleArc h b := finTwoEquiv.symm (edgeEndLabel (h, b))
  handleArc_owner _ _ := congrArg sphereLabelFace (Equiv.apply_symm_apply _ _)
  handleArc_meets h b j hne := sphere_handleArc_meets h b j hne
  endDisk_loop_disjoint _ _ j := j.elim0
  endDisk_rim h b := by
    refine (sphere_endDisk_rim h b).trans ?_
    rw [Equiv.apply_symm_apply]
  arcEnd j e := (finTwoEquiv.symm e, e != finTwoEquiv j)
  arcEnd_arc j e := sphere_handleArc_arcEnd j e
  arcEnd_injective _ _ _ h := finTwoEquiv.symm.injective (congrArg Prod.fst h)
  arcEnd_surjective h b := ⟨finTwoEquiv h, sphere_arcEnd_surjective h b⟩
  arcAnnulus_end j e := sphere_arcAnnulus_end j e
  arcBase_end j e := sphere_arcBase_end j e

theorem sphereArcLayer_arcFaceCount : sphereArcLayer.arcFaceCount = 2 :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
