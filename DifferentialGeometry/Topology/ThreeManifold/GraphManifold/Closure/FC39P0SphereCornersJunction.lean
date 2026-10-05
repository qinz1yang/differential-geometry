import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersTube

/-!
# FC39 producer, packet P0 (gate 1): the S³ labelled corner tubes, parametric in the junctions

Part C of the circle kind of the S³ inhabitant. For EVERY joint junction structure
`J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
sphereSlimPieces sphereEdgeBundle sphereCircleBundle` (the concrete one is built by another lane):

* the two junction facts used, DERIVED from the junction fields (no extra hypothesis):
  `rimBase_eq_circCorner` (`J.rim_fibre`: the rim base point of the endpoint `(i, e)` is the centre
  of the adapted corner chart `(finTwoEquiv i, e)`) and `horizontal_eq_sphereHorizontal`
  (`J.horizontal_disk`: the label is the one of `sphereHorizontal`);
* the generic owner lemma `SlimPiecesV2.mem_rowSet_residualOwner_iff` (near a residual face its
  vertex owner is the sublevel of its defining function);
* **`sphereLabelledTubes J : LabelledCornerTubes J`**: base = the corner chart target, chart =
  `c ↦ (ψ-slack, r-slack)` (the inverse corner chart scaled by `1/16`), descended equation = the
  `r`-slack of the handle radius of the edge coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-! ## Generic facts -/

/-- A nonempty circle fibre determines its base point. -/
theorem CircleBundle.eq_of_fibre_eq_CIRCC {W : CompactCarrier.{u}} {R : CircleBundle W}
    {c c' : R.Base} (h : R.fibre c = R.fibre c') (hne : (R.fibre c).Nonempty) : c = c' := by
  obtain ⟨_, y, hy, rfl⟩ := hne
  have hy' : (y : W.Carrier) ∈ R.fibre c' := h ▸ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hy'
  have hzy' : z = y := Subtype.ext hzy
  subst hzy'
  exact (hy : R.proj z = c).symm.trans hz

/-- Membership in the whole inverse image of a base component. -/
theorem EdgeBundle.mem_wholeComponent_iff_CIRCC {W : CompactCarrier.{u}} {P : EdgeBundle W}
    {C : P.EdgeBaseComponent} {x : W.Carrier} (hx : x ∈ P.source) :
    x ∈ P.wholeComponent C ↔ P.proj ⟨x, hx⟩ ∈ C.1 ∧ P.height ⟨x, hx⟩ ≤ P.level := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
    subst hyx'
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- **Near a residual face its vertex owner is the sublevel of its defining function** (from
`ZeroDomains.range_eq`, `CuspCores.near_eq`, `SlimPiecesV2.endFn_eq`). -/
theorem SlimPiecesV2.mem_rowSet_residualOwner_iff {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} {Z : ZeroDomains W} {C : CuspCores W E} {S : SlimPiecesV2 W Z C}
    {F : S.ResidualFace} {x : W.Carrier} (hx : x ∈ S.residualNear F) :
    x ∈ S.rowSet (S.residualOwner F) ↔ S.residualFn F x ≤ 0 := by
  rcases F with ⟨F | F, hF⟩ | e
  · change x ∈ range (Z.piece F.1).map ↔ Z.ratio F.1 x ≤ 0
    rw [Z.range_eq]
    rfl
  · change x ∈ C.near F.1 at hx
    change x ∈ range (C.piece F.1).map ↔ C.cuspFn F.1 x ≤ 0
    have h := C.near_eq F.1
    constructor
    · intro hm
      have hm' : x ∈ range (C.piece F.1).map ∩ C.near F.1 := ⟨hm, hx⟩
      rw [h] at hm'
      exact hm'.2
    · intro hle
      have hm' : x ∈ {x | x ∈ C.near F.1 ∧ C.cuspFn F.1 x ≤ 0} := ⟨hx, hle⟩
      rw [← h] at hm'
      exact hm'.1
  · change x ∈ S.endNear e at hx
    change x ∈ range (S.piece e.1.1.1).map ↔ S.endFn e x ≤ 0
    have h := S.endFn_eq e
    constructor
    · intro hm
      have hm' : x ∈ range (S.piece e.1.1.1).map ∩ S.endNear e := ⟨hm, hx⟩
      rw [h] at hm'
      exact hm'.2
    · intro hle
      have hm' : x ∈ {x | x ∈ S.endNear e ∧ S.endFn e x ≤ 0} := ⟨hx, hle⟩
      rw [← h] at hm'
      exact hm'.1

/-! ## The corner of an edge endpoint -/

/-- The handle side `b` of an edge endpoint. -/
def circEndSide (e : sphereEdgeBundle.EdgeEnd) : Bool :=
  finTwoEquiv (sphereEdgeEndEquiv.symm e).1

/-- The interval end of an edge endpoint. -/
def circEndEnd (e : sphereEdgeBundle.EdgeEnd) : Bool :=
  (sphereEdgeEndEquiv.symm e).2

/-- The `r`-side of the corner of an endpoint (= its horizontal label: `true` = the face of `Z₊`). -/
def circEndLabel (e : sphereEdgeBundle.EdgeEnd) : Bool :=
  circEndSide e ^^ circEndEnd e

theorem circEnd_val (e : sphereEdgeBundle.EdgeEnd) :
    e.1 = edgeInterval (circEndSide e) (iccEnd (circEndEnd e)) := by
  have h := sphereEdgeEndEquiv_apply (sphereEdgeEndEquiv.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem edgeEndLabel_symm (e : sphereEdgeBundle.EdgeEnd) :
    edgeEndLabel (sphereEdgeEndEquiv.symm e) = circEndLabel e := by
  change (circEndSide e != circEndEnd e) = (circEndSide e ^^ circEndEnd e)
  cases circEndSide e <;> cases circEndEnd e <;> rfl

theorem sphereHorizontal_eq_circEndLabel (e : sphereEdgeBundle.EdgeEnd) :
    sphereHorizontal e = sphereResidual (circEndLabel e) := by
  rw [sphereHorizontal, edgeEndLabel_symm]

theorem origin_mem_rimBox_CIRCC : ((0 : ℝ), (0 : ℝ)) ∈ rimBox 2 :=
  ⟨by norm_num, by norm_num⟩

/-! ## (J1) The rim base points are the corner centres -/

/-- The end rim of the handle `b` at the interval end `e` is the circle fibre over the centre of the
corner chart `(b, e)`. -/
theorem sphereEdge_rim_eq (b e : Bool) :
    sphereEdgeBundle.rim (edgeInterval b (iccEnd e)) =
      sphereCircleBundle.fibre (circCornerChart b e (0, 0)) := by
  have h1 := cycleS3Handle_rim b (iccEnd e)
  have h2 := circRim_label b e
  change Subtype.val '' {x : edgeSource | edgeProj x = edgeInterval b (iccEnd e) ∧
    edgeHeight x = 1} = _
  rw [← h1, ← h2, sphereCircleBundle_fibre]
  have hc : ∀ θ : Circle, circRim b e (θ, (0, 0)) =
      sphereCircleChart ((circCornerChart b e (0, 0)).val, θ) := fun θ => by
    rw [circRim_apply, circCornerChart_val b e origin_mem_rimBox_CIRCC]
  ext z
  constructor
  · rintro ⟨⟨θ, v⟩, hv, rfl⟩
    change v = (0, 0) at hv
    subst hv
    exact ⟨θ, (hc θ).symm⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨(θ, (0, 0)), rfl, hc θ⟩

theorem sphereCircleBundle_fibre_nonempty (c : sphereCircleBaseOpens) :
    (sphereCircleBundle.fibre c).Nonempty := by
  rw [sphereCircleBundle_fibre]
  exact range_nonempty _

variable (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
  sphereSlimPieces sphereEdgeBundle sphereCircleBundle)

/-- **(J1) The rim base point of an endpoint is the centre of its adapted corner chart** (derived
from `J.rim_fibre`). -/
theorem rimBase_eq_circCorner (e : sphereEdgeBundle.EdgeEnd) :
    J.rimBase e.1 = circCornerChart (circEndSide e) (circEndEnd e) (0, 0) := by
  have hr := J.rim_fibre e.1 (sphereEdgeBundle.frontier_cbase_subset e.2)
  have hc : sphereEdgeBundle.rim e.1 =
      sphereCircleBundle.fibre (circCornerChart (circEndSide e) (circEndEnd e) (0, 0)) :=
    (congrArg sphereEdgeBundle.rim (circEnd_val e)).trans (sphereEdge_rim_eq _ _)
  rw [hc] at hr
  exact (CircleBundle.eq_of_fibre_eq_CIRCC hr (sphereCircleBundle_fibre_nonempty _)).symm

/-! ## (J2) The horizontal labels -/

theorem sphereResidualHeight_injective : Injective sphereResidualHeight := by
  intro b b' h
  cases b <;> cases b' <;> first | rfl | norm_num [sphereResidualHeight] at h

/-- **(J2) The horizontal label of every endpoint is the S³ label** (derived from
`J.horizontal_disk`: the nonempty end disk lies in both labelled faces). -/
theorem horizontal_eq_sphereHorizontal (e : sphereEdgeBundle.EdgeEnd) :
    J.horizontal e = sphereHorizontal e := by
  obtain ⟨c, hc⟩ := sphereResidual_surjective (J.horizontal e)
  obtain ⟨a, rfl⟩ := sphereEdgeEndEquiv.surjective e
  have hx : (cycleS3Handle (finTwoEquiv a.1)).map (⟨0, by simp⟩, iccEnd a.2) ∈
      sphereEdgeBundle.disk (sphereEdgeEndEquiv a).1 := by
    rw [sphereEdge_disk_eq]
    exact ⟨_, rfl⟩
  have h1 := J.horizontal_disk _ hx
  have h2 := sphere_horizontal_disk _ hx
  rw [← hc, residualSet_sphereResidual] at h1
  rw [sphereHorizontal_apply, residualSet_sphereResidual] at h2
  rw [sphereHorizontal_apply, ← hc, sphereResidualHeight_injective (h1.symm.trans h2)]

theorem horizontal_eq_circEndLabel (e : sphereEdgeBundle.EdgeEnd) :
    J.horizontal e = sphereResidual (circEndLabel e) := by
  rw [horizontal_eq_sphereHorizontal, sphereHorizontal_eq_circEndLabel]

/-! ## The tube chart -/

/-- The scaling `v ↦ v / 16` of `ℝ × ℝ`. -/
def circTubeScale : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun v := (1 / 16 : ℝ) • v
  invFun v := (16 : ℝ) • v
  source := univ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := mem_univ _
  left_inv' v _ := by
    rw [smul_smul]
    norm_num
  right_inv' v _ := by
    rw [smul_smul]
    norm_num
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_const_smul (1 / 16 : ℝ)).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_const_smul (16 : ℝ)).contMDiff.contMDiffOn

/-- **The labelled corner chart of an endpoint**: `c ↦ (ψ-slack, r-slack)`. -/
def circTubeChart (e : sphereEdgeBundle.EdgeEnd) :
    PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) sphereCircleBaseOpens (ℝ × ℝ) ∞ :=
  (circCornerChart (circEndSide e) (circEndEnd e)).symm.trans circTubeScale

theorem circTubeChart_apply (e : sphereEdgeBundle.EdgeEnd) (c : sphereCircleBaseOpens) :
    circTubeChart e c = (circSlack false (circEndSide e) (circCoordL false c.val),
      circSlack true (circEndLabel e) (circCoordL true c.val)) := by
  change (1 / 16 : ℝ) • circPlaneInv (circEndSide e) (circEndLabel e) (sphereCircleEquiv c.val) = _
  rw [circCoordL_false, circCoordL_true]
  simp only [circPlaneInv, Prod.smul_mk, smul_eq_mul]
  ext <;> ring

theorem circTubeChart_source (e : sphereEdgeBundle.EdgeEnd) :
    (circTubeChart e).source = (circCornerChart (circEndSide e) (circEndEnd e)).target := by
  change (circCornerChart (circEndSide e) (circEndEnd e)).target ∩
    (circCornerChart (circEndSide e) (circEndEnd e)).symm ⁻¹' univ = _
  rw [preimage_univ, inter_univ]

/-- The base neighbourhood of an endpoint: the target of its corner chart. -/
def circTubeBase (e : sphereEdgeBundle.EdgeEnd) : TopologicalSpace.Opens sphereCircleBaseOpens :=
  ⟨(circCornerChart (circEndSide e) (circEndEnd e)).target,
    (circCornerChart (circEndSide e) (circEndEnd e)).open_target⟩

theorem mem_circTubeBase {e : sphereEdgeBundle.EdgeEnd} {c : sphereCircleBaseOpens} :
    c ∈ circTubeBase e ↔ sphereCircleEquiv c.val ∈ circPlaneTarget (circEndSide e) (circEndLabel e) :=
  mem_circCornerChart_target

theorem circCornerCenter_mem_circTubeBase (e : sphereEdgeBundle.EdgeEnd) :
    circCornerChart (circEndSide e) (circEndEnd e) (0, 0) ∈ circTubeBase e :=
  (circCornerChart (circEndSide e) (circEndEnd e)).map_source
    (by rw [circCornerChart_source]; exact origin_mem_rimBox_CIRCC)

theorem circTubeChart_center (e : sphereEdgeBundle.EdgeEnd) :
    circTubeChart e (circCornerChart (circEndSide e) (circEndEnd e) (0, 0)) = (0, 0) := by
  have h := (circCornerChart (circEndSide e) (circEndEnd e)).toPartialEquiv.left_inv
    (x := (0, 0)) (by
      rw [circCornerChart_source]
      exact origin_mem_rimBox_CIRCC)
  change (1 / 16 : ℝ) • (circCornerChart (circEndSide e) (circEndEnd e)).toPartialEquiv.symm
    ((circCornerChart (circEndSide e) (circEndEnd e)).toPartialEquiv (0, 0)) = (0, 0)
  rw [h]
  simp

/-! ## Tube points -/

section TubePoint

variable {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}

theorem circTube_target (hx : sphereCircleProj x ∈ circTubeBase e) :
    sphereCircleEquiv (sphereCircleProj x).val ∈
      circPlaneTarget (circEndSide e) (circEndLabel e) :=
  mem_circTubeBase.1 hx

/-- The whole circle domain lies in the face neighbourhoods of both residual faces. -/
theorem circDomain_mem_residualNear (σ : Bool) (x : sphereCircleDomain) :
    x.val ∈ sphereSlimPieces.residualNear (sphereResidual σ) := by
  cases σ
  · rw [residualNear_sphereResidual_false]
    change -15 / 17 < sphereHeight x.val
    rw [sphereHeight_circDomain, circHeight]
    have hr := (circCoordL_mem_wide true (sphereCircleProj x)).1
    have hD : 0 < (circCoordL true (sphereCircleProj x).val) ^ 2 + 4 := by positivity
    rw [lt_div_iff₀ hD]
    nlinarith
  · rw [residualNear_sphereResidual_true]
    exact mem_univ _

/-- The `r`-slack is nonnegative exactly on the handle interval `s ∈ [0, 1]`. -/
theorem circHandleS_mem_Icc_iff {σ' : Bool} {r : ℝ} (hr : 0 < r)
    (h : |16 * circSlack true σ' r| < 2) :
    circHandleS σ' r ∈ Icc (0 : ℝ) 1 ↔ 0 ≤ circSlack true σ' r := by
  obtain ⟨-, -, h1, h2⟩ := circHandleS_mem σ' hr h
  cases σ'
  · rw [circSlack_false_nonneg_iff true hr]
    have h1' := h1 rfl
    simp only [circHandleS, mem_Icc] at h1' ⊢
    constructor
    · intro h
      linarith [h.1]
    · intro h
      exact ⟨by linarith, by linarith⟩
  · rw [circSlack_true_nonneg_iff true hr]
    have h2' := h2 rfl
    simp only [circHandleS, mem_Icc] at h2' ⊢
    have key : 1 ≤ 4 / r ↔ r ≤ 4 := by
      rw [le_div_iff₀ hr, one_mul]
    constructor
    · intro h
      exact key.1 (by linarith [h.2])
    · intro h
      exact ⟨by linarith, by linarith [key.2 h]⟩

theorem handleRadiusParam_mem_Icc_iff_CIRCC (b : Bool) {s : ℝ} :
    handleRadiusParam b s ∈ Icc (0 : ℝ) 1 ↔ s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    have h' := handleRadiusParam_mem_Icc b h
    rwa [handleRadiusParam_involutive_CIRCC] at h'
  · exact handleRadiusParam_mem_Icc b

/-- Near one side of an axis, `[1, 4]` is the nonnegative slack of that side. -/
theorem circSlack_mem_Icc_iff (a σ : Bool) {t : ℝ} (ht : 0 < t) (h : |16 * circSlack a σ t| < 2) :
    t ∈ Icc (1 : ℝ) 4 ↔ 0 ≤ circSlack a σ t := by
  have h' : |circSlack a σ t| < 1 / 8 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
    linarith
  have hother := circSlack_other_gt a σ ht h'
  rw [mem_Icc]
  cases σ
  · rw [circSlack_false_nonneg_iff a ht]
    have h4 := (circSlack_true_nonneg_iff a ht).1 (by simp only [Bool.not_false] at hother; linarith)
    exact ⟨fun h => h.1, fun h => ⟨h, h4⟩⟩
  · rw [circSlack_true_nonneg_iff a ht]
    have h1 := (circSlack_false_nonneg_iff a ht).1 (by simp only [Bool.not_true] at hother; linarith)
    exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩

end TubePoint

/-! ## The descended face function -/

theorem contDiff_handleRadiusParam_CIRCC (b : Bool) : ContDiff ℝ ∞ (handleRadiusParam b) := by
  cases b
  · exact contDiff_id
  · exact contDiff_const.sub contDiff_id

theorem hasDerivAt_handleRadiusParam_CIRCC (b : Bool) (t : ℝ) :
    HasDerivAt (handleRadiusParam b) (bif b then -1 else 1) t := by
  cases b
  · exact hasDerivAt_id t
  · change HasDerivAt (fun t : ℝ => 1 - t) (-1) t
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)

/-- The descended face function of an endpoint, as a function of the real edge coordinate: the
`r`-slack of the handle radius. -/
def circDescendedReal (e : sphereEdgeBundle.EdgeEnd) (t : ℝ) : ℝ :=
  circSlack true (circEndLabel e)
    (cycleHandleRadius (handleRadiusParam (circEndSide e) (t - edgeShift (circEndSide e))))

/-- **The descended face function of an endpoint** on the edge base. -/
def circDescended (e : sphereEdgeBundle.EdgeEnd) (c : edgeBaseOpens) : ℝ :=
  circDescendedReal e (edgeBaseCoord c)

/-- The side interval of the edge base of an endpoint. -/
def circDescendedBase (e : sphereEdgeBundle.EdgeEnd) : TopologicalSpace.Opens edgeBaseOpens :=
  ⟨edgeBaseCoord ⁻¹' Ioo (edgeShift (circEndSide e) - 1 / 2) (edgeShift (circEndSide e) + 3 / 2),
    isOpen_Ioo.preimage continuous_edgeBaseCoord⟩

theorem circDescended_param_mem {e : sphereEdgeBundle.EdgeEnd} {t : ℝ}
    (ht : t ∈ Ioo (edgeShift (circEndSide e) - 1 / 2) (edgeShift (circEndSide e) + 3 / 2)) :
    handleRadiusParam (circEndSide e) (t - edgeShift (circEndSide e)) ∈
      Ioo (-1 / 2 : ℝ) (3 / 2) :=
  handleRadiusParam_mem_Ioo _ ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem hasDerivAt_circDescendedReal {e : sphereEdgeBundle.EdgeEnd} {t : ℝ}
    (ht : t ∈ Ioo (edgeShift (circEndSide e) - 1 / 2) (edgeShift (circEndSide e) + 3 / 2)) :
    ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt (circDescendedReal e) d t := by
  have hs := circDescended_param_mem ht
  set s := handleRadiusParam (circEndSide e) (t - edgeShift (circEndSide e)) with hs_def
  have hs2 : s ∈ Iio (2 : ℝ) := show s < 2 by linarith [hs.2]
  have hR : HasDerivAt cycleHandleRadius (deriv cycleHandleRadius s) s :=
    ((cycleHandleRadius_smooth.contDiffAt (Iio_mem_nhds hs2)).differentiableAt
      (by simp)).hasDerivAt
  have hpos := cycleHandleRadius_pos_FC39P0 hs
  have hin : HasDerivAt (fun t => handleRadiusParam (circEndSide e) (t - edgeShift (circEndSide e)))
      ((bif circEndSide e then -1 else 1) * 1) t :=
    (hasDerivAt_handleRadiusParam_CIRCC _ _).comp t ((hasDerivAt_id t).sub_const _)
  have hfull := (hasDerivAt_circSlack true (circEndLabel e) hpos).comp t (hR.comp t hin)
  refine ⟨_, ?_, hfull⟩
  refine mul_ne_zero (circSlackDeriv_ne_zero true _ hpos) (mul_ne_zero
    (cycleHandleRadius_deriv_pos (show s < 2 from hs2)).ne' (mul_ne_zero ?_ one_ne_zero))
  cases circEndSide e <;> norm_num

theorem contDiffAt_circDescendedReal {e : sphereEdgeBundle.EdgeEnd} {t : ℝ}
    (ht : t ∈ Ioo (edgeShift (circEndSide e) - 1 / 2) (edgeShift (circEndSide e) + 3 / 2)) :
    ContDiffAt ℝ ∞ (circDescendedReal e) t := by
  have hs := circDescended_param_mem ht
  have hs2 : handleRadiusParam (circEndSide e) (t - edgeShift (circEndSide e)) < 2 := by
    linarith [hs.2]
  have hin : ContDiffAt ℝ ∞
      (fun t => handleRadiusParam (circEndSide e) (t - edgeShift (circEndSide e))) t :=
    (contDiff_handleRadiusParam_CIRCC _).contDiffAt.comp t
      (contDiffAt_id.sub contDiffAt_const)
  have hR := (cycleHandleRadius_smooth.contDiffAt (Iio_mem_nhds hs2)).comp t hin
  exact (contDiffAt_circSlack true _ (cycleHandleRadius_pos_FC39P0 hs)).comp t hR

theorem mem_circDescendedBase (e : sphereEdgeBundle.EdgeEnd) : e.1 ∈ circDescendedBase e := by
  change edgeBaseCoord e.1 ∈ Ioo _ _
  rw [circEnd_val e, edgeBaseCoord_interval]
  have h := (iccEnd (circEndEnd e)).2
  constructor <;> linarith [h.1, h.2]

theorem circDescended_smooth (e : sphereEdgeBundle.EdgeEnd) :
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (circDescended e) (circDescendedBase e) := by
  intro c hc
  have hF : ContDiffAt ℝ ∞ (fun s : E1 => circDescendedReal e (edgeLineEquiv.symm s)) c.val :=
    (contDiffAt_circDescendedReal hc).comp c.val edgeLineEquiv.symm.contDiff.contDiffAt
  exact ((contMDiffAt_iff_contDiffAt.2 hF).comp c
    contMDiff_subtype_val.contMDiffAt).contMDiffWithinAt

theorem mfderiv_circDescended_ne_zero {e : sphereEdgeBundle.EdgeEnd} {c : edgeBaseOpens}
    (hc : c ∈ circDescendedBase e) : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (circDescended e) c ≠ 0 := by
  obtain ⟨d, hd, hD⟩ := hasDerivAt_circDescendedReal hc
  let G : E1 → ℝ := fun s => circDescendedReal e (edgeLineEquiv.symm s)
  change mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun c : edgeBaseOpens => G (c : E1)) c ≠ 0
  rw [DifferentialGeometry.mfderiv_restrict_open G edgeBaseOpens c]
  have hG : HasFDerivAt G (d • (edgeLineEquiv.symm : E1 →L[ℝ] ℝ)) (c : E1) := by
    have h := hD.hasFDerivAt.comp (c : E1) (edgeLineEquiv.symm.hasFDerivAt (x := (c : E1)))
    refine h.congr_fderiv ?_
    ext v
    simp [smul_eq_mul, mul_comm]
  rw [hG.hasMFDerivAt.mfderiv]
  intro h
  apply hd
  have h1 := congrArg (fun L : E1 →L[ℝ] ℝ => L (edgeLineEquiv 1)) h
  have h2 : (d • (edgeLineEquiv.symm : E1 →L[ℝ] ℝ)) (edgeLineEquiv 1) = d := by simp
  exact h2.symm.trans h1

theorem circDescended_regular (e : sphereEdgeBundle.EdgeEnd) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (circDescended e) e.1 ≠ 0 :=
  mfderiv_circDescended_ne_zero (mem_circDescendedBase e)

/-- On a corner tube the residual function descends: it is the descended function of the edge
coordinate. -/
theorem circTube_descended {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}
    (hx : sphereCircleProj x ∈ circTubeBase e) :
    circSlack true (circEndLabel e) (circCoordL true (sphereCircleProj x).val) =
      circDescended e (edgeProj ⟨x.val, circTube_mem_edgeSource (circTube_target hx)⟩) := by
  have hx' := circTube_target hx
  have hr := (circHandleS_mem (r := circCoordL true (sphereCircleProj x).val) (circEndLabel e)
    (circCoordL_pos true _) hx'.2.2.2).2.1
  change _ = circDescendedReal e (edgeLineEquiv.symm (edgeProjE x.val))
  rw [circTube_projE hx', ContinuousLinearEquiv.symm_apply_apply, circDescendedReal,
    add_sub_cancel_right, handleRadiusParam_involutive_CIRCC, hr]

/-! ## The three side equalities -/

/-- On a corner tube the second chart coordinate is the residual function of the label. -/
theorem circTube_face {e : sphereEdgeBundle.EdgeEnd} (x : sphereCircleDomain) :
    (circTubeChart e (sphereCircleProj x)).2 =
      sphereSlimPieces.residualFn (J.horizontal e) x.val := by
  rw [horizontal_eq_circEndLabel J e, circTubeChart_apply, residualFn_circDomain]

/-- **Vertex side**: the vertex owner of the label is `Y ≤ 0` on the tube. -/
theorem circTube_vertex_side {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain} :
    x.val ∈ sphereSlimPieces.rowSet (sphereSlimPieces.residualOwner (J.horizontal e)) ↔
      (circTubeChart e (sphereCircleProj x)).2 ≤ 0 := by
  have hnear : x.val ∈ sphereSlimPieces.residualNear (J.horizontal e) := by
    rw [horizontal_eq_circEndLabel J e]
    exact circDomain_mem_residualNear _ x
  rw [circTube_face J x]
  exact SlimPiecesV2.mem_rowSet_residualOwner_iff hnear

/-- **Edge side**: the whole component of the endpoint is `Y ≥ 0, X ≤ 0` on the tube. -/
theorem circTube_edge_side {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}
    (hx : sphereCircleProj x ∈ circTubeBase e) :
    x.val ∈ sphereEdgeBundle.wholeComponent e.component ↔
      0 ≤ (circTubeChart e (sphereCircleProj x)).2 ∧
        (circTubeChart e (sphereCircleProj x)).1 ≤ 0 := by
  have hx' := circTube_target hx
  have hcomp : e.component.1 = range (edgeInterval (circEndSide e)) :=
    connectedComponentIn_edgeCbase ⟨iccEnd (circEndEnd e), (circEnd_val e).symm⟩
  rw [EdgeBundle.mem_wholeComponent_iff_CIRCC (circTube_mem_edgeSource hx'), hcomp,
    circTubeChart_apply]
  apply and_congr
  · change edgeProj ⟨x.val, circTube_mem_edgeSource hx'⟩ ∈ range (edgeInterval (circEndSide e)) ↔ _
    rw [range_edgeInterval, mem_preimage]
    change edgeLineEquiv.symm (edgeProjE x.val) ∈ _ ↔ _
    rw [circTube_projE hx', ContinuousLinearEquiv.symm_apply_apply,
      ← circHandleS_mem_Icc_iff (r := circCoordL true (sphereCircleProj x).val)
        (circCoordL_pos true _) hx'.2.2.2,
      ← handleRadiusParam_mem_Icc_iff_CIRCC (circEndSide e)]
    simp only [mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · change edgeHeightR x.val ≤ 1 ↔ _
    rw [circTube_height hx']
    constructor <;> intro h <;> linarith

/-- **Region side**: the circle region is `X ≥ 0, Y ≥ 0` on the tube. -/
theorem circTube_region_side {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}
    (hx : sphereCircleProj x ∈ circTubeBase e) :
    x.val ∈ sphereCircleBundle.region ↔
      0 ≤ (circTubeChart e (sphereCircleProj x)).1 ∧
        0 ≤ (circTubeChart e (sphereCircleProj x)).2 := by
  have hx' := circTube_target hx
  have hmem : x.val ∈ sphereCircleBundle.region ↔ sphereCircleProj x ∈ sphereCircleCbase :=
    Subtype.val_injective.mem_set_image
  rw [hmem, circTubeChart_apply]
  change (sphereCircleEquiv (sphereCircleProj x).val).1 ∈ Icc (1 : ℝ) 4 ∧
    (sphereCircleEquiv (sphereCircleProj x).val).2 ∈ Icc (1 : ℝ) 4 ↔ _
  exact and_congr (circSlack_mem_Icc_iff false _ (circCoordL_pos false (sphereCircleProj x)) hx'.2.2.1)
    (circSlack_mem_Icc_iff true _ (circCoordL_pos true (sphereCircleProj x)) hx'.2.2.2)

/-- **The descended equation** on a corner tube. -/
theorem circTube_residual_descended {e : sphereEdgeBundle.EdgeEnd} {x : sphereCircleDomain}
    (hx : sphereCircleProj x ∈ circTubeBase e) :
    sphereSlimPieces.residualFn (J.horizontal e) x.val =
      circDescended e (edgeProj ⟨x.val, circTube_mem_edgeSource (circTube_target hx)⟩) := by
  rw [horizontal_eq_circEndLabel J e, residualFn_circDomain]
  exact circTube_descended hx

/-! ## The labelled corner tubes -/

/-- **The S³ labelled corner tubes** for every joint junction structure `J`. -/
def sphereLabelledTubes : LabelledCornerTubes J where
  base := circTubeBase
  rimBase_mem e := by
    rw [rimBase_eq_circCorner J e]
    exact circCornerCenter_mem_circTubeBase e
  chart := circTubeChart
  chart_source := circTubeChart_source
  chart_center e := by
    rw [rimBase_eq_circCorner J e]
    exact circTubeChart_center e
  tube_source e := by
    rintro _ ⟨x, hx, rfl⟩
    exact circTube_mem_edgeSource (circTube_target (x := x) hx)
  tube_near e := by
    rintro _ ⟨x, -, rfl⟩
    rw [horizontal_eq_circEndLabel J e]
    exact circDomain_mem_residualNear _ x
  height_eq e x hx := by
    refine ⟨circTube_mem_edgeSource (circTube_target (x := x) hx), ?_⟩
    change (circTubeChart e (sphereCircleProj x)).1 = edgeHeightR x.val - 1
    rw [circTubeChart_apply, circTube_height (circTube_target (x := x) hx)]
    ring
  face_eq e x _ := circTube_face J x
  descended := circDescended
  descended_smooth e := ⟨circDescendedBase e, mem_circDescendedBase e, circDescended_smooth e⟩
  descended_regular := circDescended_regular
  descended_eq e x hx := ⟨_, circTube_residual_descended J (x := x) hx⟩
  vertex_side {_} {x} _ := circTube_vertex_side J (x := x)
  edge_side {_} {_} hx := circTube_edge_side hx
  region_side {_} {_} hx := circTube_region_side hx

theorem sphereLabelledTubes_base (e : sphereEdgeBundle.EdgeEnd) :
    (sphereLabelledTubes J).base e = circTubeBase e :=
  rfl

theorem sphereLabelledTubes_chart (e : sphereEdgeBundle.EdgeEnd) :
    (sphereLabelledTubes J).chart e = circTubeChart e :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
