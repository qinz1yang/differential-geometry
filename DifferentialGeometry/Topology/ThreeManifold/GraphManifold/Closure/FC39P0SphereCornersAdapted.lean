import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersWide
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersLabelled
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlimSeam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Adapted
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointJunctions

/-!
# FC39 producer, packet P0 (gate 1): the S³ adapted edge–rim data, parametric in the junctions

Part C of the circle kind of the S³ inhabitant. For EVERY joint junction structure `J`:

* the WIDE rows `sphereRowsW J` (labelled tubes `sphereLabelledTubesW J`), their global face
  functions `sphereGlobalFacesW J`, `spherePreparedW J` and the labelled corner compatibility
  `sphereLabelledCompatibilityW J` (the G3 proofs; only the raw tube is wider);
* the safe neighbourhoods `sphereSafe J : ProducerSafeNeighbourhoods (sphereRowsW J)`: the shared
  face neighbourhood `sphereSharedSafeFamily` (`q₀ < −4/5`), the safe corner bases = the wide corner
  chart images of the box `|x|, |y| < 9/4`; their closures lie in the compact images of the closed
  boxes (`q₀ ≥ −3/5 − 9/64`), pairwise disjoint;
* **`sphereAdaptedEdgeRimData J : AdaptedEdgeRimData (spherePreparedW J) (sphereSafe J)`**: edge layer
  `sphereEdgeLayer`, circle region `sphereCircleRegion`, rim layer `sphereRimLayer`, rim product
  `sphereRimLayer_rimProduct`; the closure of every rim target (`|x|, |y| < 2`) lies in the closed box
  `|x|, |y| ≤ 2`, inside the safe tube; the rounding differs from `C₁` only on the unit boxes.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## Generic: tubes over disjoint base sets -/

theorem CircleBundle.tube_disjoint_CIRCC {W : CompactCarrier.{u}} {R : CircleBundle W}
    {V V' : Set R.Base} (h : Disjoint V V') : Disjoint (R.tube V) (R.tube V') := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxy : y = x := Subtype.ext hyx
  subst hxy
  exact Set.disjoint_left.1 h hx hy

theorem CircleBundle.tube_mono_CIRCC {W : CompactCarrier.{u}} {R : CircleBundle W}
    {V V' : Set R.Base} (h : V ⊆ V') : R.tube V ⊆ R.tube V' :=
  image_mono (preimage_mono h)

/-! ## Wide targets of distinct corners are disjoint -/

theorem circPlaneTargetW_disjoint {σ₁ σ₁' σ₂ σ₂' : Bool} (h : (σ₁, σ₁') ≠ (σ₂, σ₂')) :
    Disjoint (circPlaneTargetW σ₁ σ₁') (circPlaneTargetW σ₂ σ₂') := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  have key : ∀ (a σ τ : Bool) (t : ℝ), 0 < t → |16 * circSlack a σ t| < 5 / 2 →
      |16 * circSlack a τ t| < 5 / 2 → σ = τ := by
    intro a σ τ t ht h1 h2
    by_contra hne
    have hτ : τ = !σ := by cases σ <;> cases τ <;> simp_all
    have h1' : |circSlack a σ t| < 5 / 32 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h1
      linarith
    have hgt := circSlack_other_gtW a σ ht h1'
    rw [← hτ] at hgt
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h2
    linarith [le_abs_self (circSlack a τ t)]
  exact h (Prod.ext (key false σ₁ σ₂ u.1 hu.1 hu.2.2.1 hu'.2.2.1)
    (key true σ₁' σ₂' u.2 hu.2.1 hu.2.2.2 hu'.2.2.2))

theorem circEnd_injective {e e' : sphereEdgeBundle.EdgeEnd}
    (h : (circEndSide e, circEndLabel e) = (circEndSide e', circEndLabel e')) : e = e' := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have h3 : circEndEnd e = circEndEnd e' := by
    have aux : ∀ c f f' : Bool, (c ^^ f) = (c ^^ f') → f = f' := by decide
    exact aux _ _ _ (show (circEndSide e ^^ circEndEnd e) = (circEndSide e ^^ circEndEnd e') from
      h2.trans (by rw [circEndLabel, h1]))
  apply sphereEdgeEndEquiv.symm.injective
  exact Prod.ext (finTwoEquiv.injective h1) h3

theorem circTubeBaseW_disjoint {e e' : sphereEdgeBundle.EdgeEnd} (h : e ≠ e') :
    Disjoint (circTubeBaseW e : Set sphereCircleBaseOpens) (circTubeBaseW e') := by
  refine Set.disjoint_left.2 fun c hc hc' => ?_
  exact Set.disjoint_left.1 (circPlaneTargetW_disjoint fun h' => h (circEnd_injective h'))
    (mem_circTubeBaseW.1 hc) (mem_circTubeBaseW.1 hc')

/-! ## The wide corner map and compact boxes -/

/-- The wide corner map `(θ, v) ↦ J(k_{b,e}(v), θ)`. -/
def circWideMap (b e : Bool) (p : Circle × (ℝ × ℝ)) : sphereW.Carrier :=
  sphereCircleChart (sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) p.2), p.1)

/-- The closed square `[−ρ, ρ]²`. -/
def circClosedSquare (ρ : ℝ) : Set (ℝ × ℝ) :=
  Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ

theorem circClosedSquare_subset {ρ ρ' : ℝ} (h : ρ < ρ') : circClosedSquare ρ ⊆ rimBox ρ' :=
  fun v hv => ⟨abs_lt.2 ⟨by linarith [hv.1.1], by linarith [hv.1.2]⟩,
    abs_lt.2 ⟨by linarith [hv.2.1], by linarith [hv.2.2]⟩⟩

theorem rimBox_subset_closedSquare (ρ : ℝ) : rimBox ρ ⊆ circClosedSquare ρ :=
  fun v hv => ⟨⟨by linarith [(abs_lt.1 hv.1).1], by linarith [(abs_lt.1 hv.1).2]⟩,
    ⟨by linarith [(abs_lt.1 hv.2).1], by linarith [(abs_lt.1 hv.2).2]⟩⟩

theorem rimBox_mono_CIRCC {ρ ρ' : ℝ} (h : ρ ≤ ρ') : rimBox ρ ⊆ rimBox ρ' :=
  fun _ hv => ⟨lt_of_lt_of_le hv.1 h, lt_of_lt_of_le hv.2 h⟩

theorem continuousOn_circWideMap (b e : Bool) :
    ContinuousOn (circWideMap b e) (univ ×ˢ rimBox (5 / 2)) := by
  have h1 : ContinuousOn (fun p : Circle × (ℝ × ℝ) =>
      (sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) p.2), p.1)) (univ ×ˢ rimBox (5 / 2)) :=
    ((sphereCircleEquiv.symm.continuous.comp_continuousOn
      ((contDiffOn_circPlaneMapW b (b ^^ e)).continuousOn.comp continuous_snd.continuousOn
        fun p hp => hp.2)).prodMk continuous_fst.continuousOn)
  refine sphereCircleChart.contMDiffOn.continuousOn.comp h1 fun p hp => ?_
  rw [sphereCircleChart_source]
  exact ⟨circPlaneMap_mem_baseW hp.2, mem_univ _⟩

theorem isCompact_circWideMap_square (b e : Bool) {ρ : ℝ} (hρ : ρ < 5 / 2) :
    IsCompact (circWideMap b e '' (univ ×ˢ circClosedSquare ρ)) :=
  (isCompact_univ.prod (isCompact_Icc.prod isCompact_Icc)).image_of_continuousOn
    ((continuousOn_circWideMap b e).mono (prod_mono subset_rfl (circClosedSquare_subset hρ)))

/-- The saturated tube over a wide corner image is the image of the wide corner map. -/
theorem tube_circCornerChartW_image (b e : Bool) {S : Set (ℝ × ℝ)} (hS : S ⊆ rimBox (5 / 2)) :
    sphereCircleBundle.tube (circCornerChartW b e '' S) = circWideMap b e '' (univ ×ˢ S) := by
  refine (sphereCircleBundle_tube _).trans ?_
  ext x
  constructor
  · rintro ⟨⟨c, θ⟩, ⟨⟨c', ⟨v, hv, rfl⟩, rfl⟩, -⟩, rfl⟩
    refine ⟨(θ, v), ⟨mem_univ _, hv⟩, ?_⟩
    change sphereCircleChart _ = sphereCircleChart ((circCornerChartW b e v).val, θ)
    rw [circCornerChartW_val b e (hS hv)]
  · rintro ⟨⟨θ, v⟩, ⟨-, hv⟩, rfl⟩
    refine ⟨((circCornerChartW b e v).val, θ), ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, mem_univ _⟩, ?_⟩
    change sphereCircleChart ((circCornerChartW b e v).val, θ) = sphereCircleChart _
    rw [circCornerChartW_val b e (hS hv)]

/-- The stereographic height on the image of the closed square `[−9/4, 9/4]²` is `> −4/5`. -/
theorem sphereHeight_circWideMap (b e : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p.2 ∈ circClosedSquare (9 / 4)) : -4 / 5 < sphereHeight (circWideMap b e p) := by
  have hv : p.2 ∈ rimBox (5 / 2) := circClosedSquare_subset (by norm_num) hp
  have hbase := circPlaneMap_mem_baseW (σ := b) (σ' := b ^^ e) hv
  have h := sphereHeight_chart_base ⟨_, hbase⟩ p.1
  change sphereHeight (circWideMap b e p) = _ at h
  rw [h]
  change -4 / 5 < circHeight (circCoordL true (sphereCircleEquiv.symm (circPlaneMap b (b ^^ e) p.2)))
  rw [circCoordL_symm]
  change -4 / 5 < circHeight (circCornerInv true (b ^^ e) p.2.2)
  have hs := circSlack_circCornerInvW true (b ^^ e) hv.2
  have h1 := hp.2.1
  have h2 := hp.2.2
  generalize (b ^^ e) = σ at hs ⊢
  cases σ
  · change circHeight _ + 3 / 5 = _ at hs
    linarith
  · change 3 / 5 - circHeight _ = _ at hs
    linarith

/-! ## The wide rows, global faces and labelled compatibility -/

variable (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
  sphereSlimPieces sphereEdgeBundle sphereCircleBundle)

/-- **The S³ rows with the WIDE labelled tubes.** -/
def sphereRowsW : FC39RowsV2 sphereW (BoundaryTori.empty sphereW) where
  zero := sphereZeroDomains
  cusp := sphereCuspCores
  slim := sphereSlimPieces
  edge := sphereEdgeBundle
  edgeModels := sphereEdgeModels
  circle := sphereCircleBundle
  junctions := J
  labelledTubes := sphereLabelledTubesW J

theorem circDefining_canonicalW (e : sphereEdgeBundle.EdgeEnd) (c : sphereCircleBaseOpens) :
    circDefining (circActualFace.symm (.vertical e.component)) c = -(circTubeChartW e c).1 ∧
      circDefining (circActualFace.symm (.horizontal (J.horizontal e))) c =
        -(circTubeChartW e c).2 := by
  rw [circTubeChartW_eq]
  exact circDefining_canonical J e c

/-- **The global face functions of the wide S³ rows.** -/
def sphereGlobalFacesW : GlobalFaceFunctions (sphereRowsW J) where
  base := ⊤
  cbase_subset _ _ := trivial
  Face := Fin 4
  finite := inferInstance
  actualFace := circActualFace
  fn := circDefining
  smooth f := (circDefining_smooth f).contMDiffOn
  zero_regular f c _ _ := circDefining_regular f c
  base_eq := by
    change sphereCircleCbase =
      {c | c ∈ (⊤ : TopologicalSpace.Opens sphereCircleBaseOpens) ∧ ∀ l, circDefining l c ≤ 0}
    rw [sphereCircleCbase_eq]
    ext c
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  face_eq := circDefining_face_eq
  depth_le_two c _ := circDefining_ncard_le c
  double_independent c _ f f' hne h h' := circDefining_independent c f f' hne h h'
  double_registered c _ f f' hne h h' := circDefining_double_registered J c f f' hne h h'
  canonical_near_corner e c _ := circDefining_canonicalW J e c

/-- **The wide S³ prepared rows.** -/
def spherePreparedW : FC39Prepared sphereW (BoundaryTori.empty sphereW) where
  rows := sphereRowsW J
  globalFaces := sphereGlobalFacesW J

/-- The global face link for the wide rows (`faceIndex = id`). -/
def sphereGlobalFaceLinkW :
    GlobalFaceLink (sphereGlobalFacesW J) sphereCircleRegion sphereCircleRestriction where
  range_subset _ _ := trivial
  faceIndex := Equiv.refl (Fin 4)
  defining_eq _ _ := rfl

theorem sphereRim_target_in_tubeW (h : Fin 2) (b : Bool) :
    (circRim (finTwoEquiv h) b).target ⊆
      Subtype.val '' (sphereCircleProj ⁻¹' circTubeBaseW (sphereEdgeEndEquiv (h, b))) :=
  (sphereRim_target_in_tube h b).trans (image_mono (preimage_mono (circTubeBase_subset_W _)))

/-- **The S³ labelled corner compatibility for the wide rows.** -/
def sphereLabelledCompatibilityW :
    LabelledCornerCompatibility (spherePreparedW J) sphereEdgeLayer sphereCircleRegion
      sphereRimLayer where
  edgeLink := sphereEdgeLink
  circleLink := sphereCircleRestriction
  globalFaces := sphereGlobalFaceLinkW J
  endOfCorner := circEndOfCorner
  corner_center k := sphere_corner_center J k
  endpoint_label h b := (circEndOfCorner_handle h b).symm
  first_label h b := circActualFace_first h b
  second_label h b := circActualFace_second J h b
  height_eq h b _ hp := circRim_height (finTwoEquiv h) b ((mem_circRim_source _ _).1 hp)
  horizontal_eq h b _ hp := circRim_horizontal J h b ((mem_circRim_source _ _).1 hp)
  target_full h b := sphereRim_target_full h b
  target_in_raw_tube h b := sphereRim_target_in_tubeW h b

/-! ## The safe neighbourhoods -/

/-- The safe corner base of an endpoint: the wide corner image of the box `|x|, |y| < 9/4`. -/
def circSafeBase (e : sphereEdgeBundle.EdgeEnd) : TopologicalSpace.Opens sphereCircleBaseOpens :=
  ⟨circCornerChartW (circEndSide e) (circEndEnd e) '' rimBox (9 / 4),
    (circCornerChartW (circEndSide e) (circEndEnd e)).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_rimBox_CIRCB _)
      (by rw [show (circCornerChartW (circEndSide e) (circEndEnd e)).toOpenPartialHomeomorph.source
            = (circCornerChartW (circEndSide e) (circEndEnd e)).source from rfl,
          circCornerChartW_source]
          exact rimBox_mono_CIRCC (by norm_num))⟩

theorem circSafeBase_subset (e : sphereEdgeBundle.EdgeEnd) :
    (circSafeBase e : Set sphereCircleBaseOpens) ⊆ circTubeBaseW e := by
  rintro _ ⟨v, hv, rfl⟩
  exact (circCornerChartW (circEndSide e) (circEndEnd e)).map_source
    (by rw [circCornerChartW_source]; exact rimBox_mono_CIRCC (by norm_num) hv)

theorem rimBase_mem_circSafeBase (e : sphereEdgeBundle.EdgeEnd) : J.rimBase e.1 ∈ circSafeBase e := by
  rw [rimBase_eq_circCorner J e]
  exact ⟨(0, 0), ⟨by norm_num, by norm_num⟩, rfl⟩

/-- **The closure of a safe tube** lies in the compact image of the closed square `[−9/4, 9/4]²`. -/
theorem closure_tube_circSafeBase (e : sphereEdgeBundle.EdgeEnd) :
    closure (sphereCircleBundle.tube (circSafeBase e : Set sphereCircleBaseOpens)) ⊆
      circWideMap (circEndSide e) (circEndEnd e) '' (univ ×ˢ circClosedSquare (9 / 4)) := by
  refine closure_minimal ?_ (isCompact_circWideMap_square _ _ (by norm_num)).isClosed
  change sphereCircleBundle.tube (circCornerChartW (circEndSide e) (circEndEnd e) '' rimBox (9 / 4))
    ⊆ _
  rw [tube_circCornerChartW_image _ _ (rimBox_mono_CIRCC (by norm_num))]
  exact image_mono (prod_mono subset_rfl (rimBox_subset_closedSquare _))

theorem circWideMap_square_subset_tubeW (e : sphereEdgeBundle.EdgeEnd) :
    circWideMap (circEndSide e) (circEndEnd e) '' (univ ×ˢ circClosedSquare (9 / 4)) ⊆
      sphereCircleBundle.tube (circTubeBaseW e : Set sphereCircleBaseOpens) := by
  have h := tube_circCornerChartW_image (circEndSide e) (circEndEnd e)
    (circClosedSquare_subset (show (9 / 4 : ℝ) < 5 / 2 by norm_num))
  rw [← h]
  refine CircleBundle.tube_mono_CIRCC ?_
  rintro _ ⟨v, hv, rfl⟩
  exact (circCornerChartW (circEndSide e) (circEndEnd e)).map_source
    (by rw [circCornerChartW_source]; exact circClosedSquare_subset (by norm_num) hv)

theorem circSafe_closure_disjoint : Pairwise fun e e' : sphereEdgeBundle.EdgeEnd =>
    Disjoint (closure (sphereCircleBundle.tube (circSafeBase e : Set sphereCircleBaseOpens)))
      (closure (sphereCircleBundle.tube (circSafeBase e' : Set sphereCircleBaseOpens))) := by
  intro e e' hne
  exact ((CircleBundle.tube_disjoint_CIRCC (circTubeBaseW_disjoint hne)).mono
    ((closure_tube_circSafeBase e).trans (circWideMap_square_subset_tubeW e))
    ((closure_tube_circSafeBase e').trans (circWideMap_square_subset_tubeW e')))

theorem circSafe_off_shared (e : sphereEdgeBundle.EdgeEnd) :
    Disjoint (closure (sphereCircleBundle.tube (circSafeBase e : Set sphereCircleBaseOpens)))
      (closure (sphereSharedNear : Set sphereW.Carrier)) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨p, ⟨-, hp⟩, rfl⟩ := closure_tube_circSafeBase e hx
  have h1 := sphereHeight_circWideMap (circEndSide e) (circEndEnd e) hp
  have h2 : sphereHeight (circWideMap (circEndSide e) (circEndEnd e) p) ≤ -4 / 5 :=
    closure_sphereSharedNear hx'
  linarith

/-- **The S³ shared safe neighbourhoods** (`SharedSafe` for the wide rows). -/
theorem sphereSharedSafe : SharedSafe (sphereRowsW J) sphereSharedSafeFamily where
  face_subset σ := sphereSharedSafe_face_subset σ
  closure_disjoint := sphereSharedSafe_closure_disjoint
  off_edge σ := sphereSharedSafe_off_edge σ
  off_region σ := sphereSharedSafe_off_region σ
  off_external _ i := i.elim0

/-- **The S³ producer safe neighbourhoods** for the wide rows. -/
def sphereSafe : ProducerSafeNeighbourhoods (sphereRowsW J) where
  shared := sphereSharedSafeFamily
  shared_safe := sphereSharedSafe J
  cornerBase := circSafeBase
  cornerBase_sub := circSafeBase_subset
  rimBase_mem e := rimBase_mem_circSafeBase J e
  corner_closure_disjoint := circSafe_closure_disjoint
  corner_off_external _ i := i.elim0
  corner_off_shared e _ := circSafe_off_shared e

/-! ## The adapted edge–rim data -/

/-- **The closure of a rim target lies in its safe tube.** -/
theorem closure_circRim_target_subset (h : Fin 2) (b : Bool) :
    closure (circRim (finTwoEquiv h) b).target ⊆
      sphereCircleBundle.tube (circSafeBase (sphereEdgeEndEquiv (h, b)) : Set sphereCircleBaseOpens) := by
  have hs : circEndSide (sphereEdgeEndEquiv (h, b)) = finTwoEquiv h := circEndSide_apply h b
  have he : circEndEnd (sphereEdgeEndEquiv (h, b)) = b := circEndEnd_apply h b
  have hT : (circRim (finTwoEquiv h) b).target =
      circWideMap (finTwoEquiv h) b '' (univ ×ˢ rimBox 2) := by
    rw [circRim_target_eq, ← tube_circCornerChartW_image _ _ (rimBox_mono_CIRCC (by norm_num)),
      ← (circCornerChart (finTwoEquiv h) b).image_source_eq_target, circCornerChart_source]
    rfl
  have hsafe : sphereCircleBundle.tube (circSafeBase (sphereEdgeEndEquiv (h, b)) : Set sphereCircleBaseOpens) =
      circWideMap (finTwoEquiv h) b '' (univ ×ˢ rimBox (9 / 4)) := by
    change sphereCircleBundle.tube (circCornerChartW (circEndSide (sphereEdgeEndEquiv (h, b)))
      (circEndEnd (sphereEdgeEndEquiv (h, b))) '' rimBox (9 / 4)) = _
    rw [hs, he, tube_circCornerChartW_image _ _ (rimBox_mono_CIRCC (by norm_num))]
  rw [hT, hsafe]
  refine closure_minimal (image_mono (prod_mono subset_rfl (rimBox_subset_closedSquare 2)))
    (isCompact_circWideMap_square _ _ (by norm_num)).isClosed |>.trans ?_
  exact image_mono (prod_mono subset_rfl (circClosedSquare_subset (by norm_num)))

/-- **The rounding differs from `C₁` only inside the safe tubes.** -/
theorem sphere_rounding_in_safe :
    Subtype.val '' (sphereCircleProj ⁻¹'
        symmDiff {c | circRounding c ≤ 0} sphereCircleCbase) ⊆
      ⋃ e, sphereCircleBundle.tube (circSafeBase e : Set sphereCircleBaseOpens) := by
  have hsd : symmDiff {c | circRounding c ≤ 0} sphereCircleCbase ⊆
      ⋃ k, circCorner k '' rimBox 1 := by
    intro c hc
    by_contra hU
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : c ∈ {c | circRounding c ≤ 0} \ ⋃ k, circCorner k '' rimBox 1 := ⟨h1, hU⟩
      rw [circRounding_agree] at this
      exact h2 this.1
    · have : c ∈ sphereCircleCbase \ ⋃ k, circCorner k '' rimBox 1 := ⟨h1, hU⟩
      rw [← circRounding_agree] at this
      exact h2 this.1
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, v, hv, hvk⟩ := mem_iUnion.1 (hsd hx)
  refine mem_iUnion.2 ⟨circEndOfCorner k, x, ?_, rfl⟩
  change sphereCircleProj x ∈ circCornerChartW (circEndSide (circEndOfCorner k))
    (circEndEnd (circEndOfCorner k)) '' rimBox (9 / 4)
  rw [circEndOfCorner_apply, circEndSide_apply, circEndEnd_apply, Equiv.apply_symm_apply, ← hvk]
  exact ⟨v, rimBox_mono_CIRCC (by norm_num) hv, rfl⟩

/-- **The S³ adapted edge–rim data** for every joint junction structure `J`. -/
def sphereAdaptedEdgeRimData : AdaptedEdgeRimData (spherePreparedW J) (sphereSafe J) where
  edges := sphereEdgeLayer
  circ := sphereCircleRegion
  components := sphereEdgeLink
  circle := sphereCircleRestriction
  rims := sphereRimLayer
  labelled := sphereLabelledCompatibilityW J
  components_eq := rfl
  circle_eq := rfl
  product := sphereRimLayer_rimProduct
  rim_closure_in_safe h b := closure_circRim_target_subset h b
  rounding_in_safe := sphere_rounding_in_safe

/-- **Regression test C on the wide S³ rows** (the rows of the certificate). -/
theorem sphereRegressionCW (h : Fin 2) (b : Bool) :
    DryCircleLink sphereEdgeBundle sphereCircleBundle sphereCircleRegion ∧
      DryCircleLink sphereEdgeBundle sphereCircleBundle (swapAxesRegion sphereCircleRegion) ∧
      Nonempty (RimChartLayer sphereW sphereEdgeLayer (swapAxesRegion sphereCircleRegion)) ∧
      (¬ ∀ {p}, p ∈ (sphereRimLayer.swap.rimChart h b).source →
        (sphereRimLayer.swap.rimChart h b p ∈
            sphereSlimPieces.rowSet ((sphereLabelledCompatibilityW J).handleEndOwner h b) ↔
          p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibility (spherePreparedW J) sphereEdgeLayer
        (swapAxesRegion sphereCircleRegion) sphereRimLayer.swap) :=
  regressionC_projected sphereRimLayer (sphereLabelledCompatibilityW J) h b _ 1
    (circRim_vertex_side J h b)

/-! ## At the actual S³ junctions `sphereJunctions` (FC39-JOINT) -/

/-- **The S³ adapted edge–rim data at the actual junctions.** -/
def sphereJointAdaptedEdgeRimData :
    AdaptedEdgeRimData (spherePreparedW sphereJunctions) (sphereSafe sphereJunctions) :=
  sphereAdaptedEdgeRimData sphereJunctions

/-- **The S³ labelled corner compatibility at the actual junctions.** -/
def sphereJointLabelledCompatibility :
    LabelledCornerCompatibility (spherePreparedW sphereJunctions) sphereEdgeLayer
      sphereCircleRegion sphereRimLayer :=
  sphereLabelledCompatibilityW sphereJunctions

/-- **Regression test C at the actual junctions** (south handle, both ends). -/
theorem sphereJointRegressionC (b : Bool) :
    DryCircleLink sphereEdgeBundle sphereCircleBundle (swapAxesRegion sphereCircleRegion) ∧
      IsEmpty (LabelledCornerCompatibility (spherePreparedW sphereJunctions) sphereEdgeLayer
        (swapAxesRegion sphereCircleRegion) sphereRimLayer.swap) :=
  ⟨(sphereRegressionCW sphereJunctions 0 b).2.1, (sphereRegressionCW sphereJunctions 0 b).2.2.2.2⟩

end GC.GraphManifold.Assembly.FC39P0
