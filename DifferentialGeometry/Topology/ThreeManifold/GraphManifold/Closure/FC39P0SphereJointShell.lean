import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlimRegions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCircleFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersBase

/-!
# FC39 producer, packet P0 (gate 1): the joint S³ configuration, the shell `1 ≤ r ≤ 4`

The joint structures of the ONE S³ configuration (review 49, T49-1: two zero pieces, one slim
piece, two handles, one sphere seam) need the shell `M₂ = {1 ≤ r ≤ 4} = {−3/5 ≤ q₀ ≤ 3/5}` cut
into the edge piece (the two polar disk handles, `ψ ≤ 1` and `ψ ≥ 4`) and the circle region
(`1 ≤ ψ ≤ 4`). In the stereographic chart `x = ambient(r • θ)` (`θ ∈ S²`, `ψ = ‖stereo_N θ‖`):

* `sphereCircleEquiv_proj_of_eq`: the base point `(ψ, r)` of a shell point of the circle domain;
* `band_subset_edge_union_region`: every point of the band lies on a handle or in the region;
* `edge_mem_domain_psi_le`, `edge_mem_domain_vertical`: a handle point of the circle domain has
  `ψ ≤ 1` or `ψ ≥ 4`, and `ψ ∈ [1, 4]` only on the vertical face;
* `sphere_edge_region` (`edge_region` of `JunctionsV2`): `P ∩ M₃ = V`;
* `sphereCircleRegion_subset_band`, `isClosed_sphereCircleRegion`;
* `vertical_mem_closure_JOINT`: a vertical point is a limit of non-edge points of the same height
  (moving `ψ` into `(1, 4)` in the circle chart).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance diskChartsShell_JOINT : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## Inverses of the charts -/

theorem ambient_symm_ambient_JOINT (y : E3) :
    (cycleBallAmbient false).symm (cycleBallAmbient false y) = y :=
  (cycleBallAmbient false).left_inv (by rw [cycleBallAmbient_source]; exact mem_univ _)

theorem ambient_injective_JOINT : Injective (cycleBallAmbient false) := fun y y' h => by
  rw [← ambient_symm_ambient_JOINT y, h, ambient_symm_ambient_JOINT]

theorem stereo_stereo_symm_JOINT (w : E2) :
    Handle.stereoChart northPole ((Handle.stereoChart northPole).symm w) = w :=
  (Handle.stereoChart northPole).right_inv (by rw [Handle.stereoChart_target]; exact mem_univ _)

theorem stereo_symm_stereo_JOINT {θ : sphere (0 : E3) 1} (hθ : θ ≠ northPole) :
    (Handle.stereoChart northPole).symm (Handle.stereoChart northPole θ) = θ :=
  (Handle.stereoChart northPole).left_inv (by rw [Handle.stereoChart_source]; exact hθ)

theorem stereo_symm_ne_JOINT (w : E2) : (Handle.stereoChart northPole).symm w ≠ northPole := by
  have h := (Handle.stereoChart northPole).map_target
    (show w ∈ (Handle.stereoChart northPole).target by
      rw [Handle.stereoChart_target]; exact mem_univ _)
  rw [Handle.stereoChart_source] at h
  simpa using h

/-- The inverse stereographic image of `0` is the south pole `−N`. -/
theorem stereo_symm_zero_JOINT :
    ((Handle.stereoChart northPole).symm 0 : E3) = -(northPole : E3) := by
  have hi0 := Handle.inner_stereoChart_symm northPole 0
  rw [norm_zero] at hi0
  norm_num at hi0
  have hi : ⟪((Handle.stereoChart northPole).symm 0 : E3), (northPole : E3)⟫_ℝ = -1 := hi0
  have hu : ‖((Handle.stereoChart northPole).symm 0 : E3)‖ = 1 := norm_eq_of_mem_sphere _
  have hN : ‖(northPole : E3)‖ = 1 := norm_eq_of_mem_sphere _
  have h : ‖((Handle.stereoChart northPole).symm 0 : E3) + (northPole : E3)‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hu, hN, hi]
    norm_num
  have h0 := (pow_eq_zero_iff two_ne_zero).1 h
  rw [norm_eq_zero] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- The antipodal stereographic coordinate `w ↦ −(4/‖w‖²) w` has norm `4/‖w‖`. -/
theorem norm_antipodeW_JOINT {w : E2} (hw : w ≠ 0) : ‖-(4 / ‖w‖ ^ 2) • w‖ = 4 / ‖w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
  field_simp

theorem antipodeW_ne_zero_JOINT {w : E2} (hw : w ≠ 0) : -(4 / ‖w‖ ^ 2) • w ≠ 0 := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  refine smul_ne_zero (neg_ne_zero.2 (by positivity)) hw

theorem antipodeW_antipodeW_JOINT {w : E2} (hw : w ≠ 0) :
    -(4 / ‖-(4 / ‖w‖ ^ 2) • w‖ ^ 2) • (-(4 / ‖w‖ ^ 2) • w) = w := by
  rw [norm_antipodeW_JOINT hw, smul_smul]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  convert one_smul ℝ w using 2
  field_simp

/-! ## The handle charts in shell form -/

theorem cycleHandleChart_false_shell (w : E2) (t : ℝ) :
    cycleHandleChart false (w, t) =
      cycleBallAmbient false (cycleHandleRadius t • ((Handle.stereoChart northPole).symm w : E3)) := by
  rw [cycleHandleChart_eq_FC39P0]
  rfl

theorem cycleHandleChart_true_shell (w : E2) (t : ℝ) :
    cycleHandleChart true (w, t) = cycleBallAmbient false
      (cycleHandleRadius (1 - t) • -((Handle.stereoChart northPole).symm w : E3)) := by
  rw [cycleHandleChart_eq_FC39P0]
  rfl

/-! ## The base point of a shell point -/

/-- **The base point of a shell point** `x = ambient(r • θ)` of the circle domain is
`(ψ, r) = (‖stereo_N θ‖, r)`. -/
theorem sphereCircleEquiv_proj_of_eq {x : sphereCircleDomain} {r : ℝ} (hr : 0 < r)
    {θ : sphere (0 : E3) 1} (hx : x.val = cycleBallAmbient false (r • (θ : E3))) :
    sphereCircleEquiv (sphereCircleProj x : E2) = (‖Handle.stereoChart northPole θ‖, r) := by
  rw [sphereCircleEquiv_proj, hx, ambient_symm_ambient_JOINT, sphereDirection_pos_smul _ θ hr,
    norm_smul, Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere θ, mul_one]

/-- The ray of the north pole misses the circle domain. -/
theorem ambient_north_not_mem_domain_JOINT {r : ℝ} (hr : 0 < r) :
    cycleBallAmbient false (r • (northPole : E3)) ∉ sphereCircleDomain := by
  intro hx
  obtain ⟨p, hp, hpx⟩ :=
    (show _ ∈ sphereCircleChart '' sphereCircleChart.source from hx)
  rw [sphereCircleChart_apply] at hpx
  have h := ambient_injective_JOINT hpx
  rw [sphereCircleChart_source] at hp
  have hr' : 0 < (sphereCircleEquiv p.1).2 := sphereCircleWide_pos hp.1.2
  set θ := (Handle.stereoChart northPole).symm ((sphereCircleEquiv p.1).1 • planeOfCircle p.2)
  have hn := congrArg norm h
  rw [norm_smul, norm_smul, norm_eq_of_mem_sphere θ, norm_eq_of_mem_sphere northPole,
    Real.norm_of_nonneg hr'.le, Real.norm_of_nonneg hr.le, mul_one, mul_one] at hn
  rw [hn] at h
  have hθ : (θ : E3) = (northPole : E3) := smul_right_injective E3 hr.ne' h
  exact stereo_symm_ne_JOINT _ (Subtype.ext hθ)

/-- A shell point off the north ray is a point of the circle chart. -/
theorem ambient_eq_sphereCircleChart_JOINT (r : ℝ) {θ : sphere (0 : E3) 1} (hθ : θ ≠ northPole) :
    cycleBallAmbient false (r • (θ : E3)) = sphereCircleChart
      (sphereCircleEquiv.symm (‖Handle.stereoChart northPole θ‖, r),
        unitOf (Complex.orthonormalBasisOneI.repr.symm (Handle.stereoChart northPole θ))) := by
  rw [sphereCircleChart_equiv_symm, planeOfCircle_unitOf_CIRCA, stereo_symm_stereo_JOINT hθ]

/-! ## Heights in the circle chart -/

theorem sphereHeight_sphereCircleChart (p : E2 × Circle) :
    sphereHeight (sphereCircleChart p) = circHeight (sphereCircleEquiv p.1).2 := by
  rw [sphereCircleChart_apply, sphereHeight_ambient_false, norm_smul, norm_eq_of_mem_sphere,
    mul_one, Real.norm_eq_abs, sq_abs]
  rfl

theorem circHeight_mem_band {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 4) :
    -3 / 5 ≤ circHeight r ∧ circHeight r ≤ 3 / 5 := by
  have h0 : 0 < r := by linarith [hr.1]
  have h1 : 0 ≤ circSlack true false r := (circSlack_false_nonneg_iff true h0).2 hr.1
  have h2 : 0 ≤ circSlack true true r := (circSlack_true_nonneg_iff true h0).2 hr.2
  change 0 ≤ circHeight r + 3 / 5 at h1
  change 0 ≤ 3 / 5 - circHeight r at h2
  constructor <;> linarith

/-- **The circle region lies in the band `−3/5 ≤ q₀ ≤ 3/5`** (`M₃ ⊆ M₂`). -/
theorem sphereCircleRegion_subset_band :
    sphereCircleBundle.region ⊆ {x | -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5} := by
  rw [sphereCircleBundle_region]
  rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
  change -3 / 5 ≤ sphereHeight (sphereCircleChart p) ∧ sphereHeight (sphereCircleChart p) ≤ 3 / 5
  rw [sphereHeight_sphereCircleChart]
  exact circHeight_mem_band hp.2

theorem isCompact_sphereCircleRegion : IsCompact sphereCircleBundle.region := by
  rw [sphereCircleBundle_region]
  have hK : IsCompact (sphereCircleCbaseSet ×ˢ (univ : Set Circle)) :=
    (sphereCircleEquiv.toHomeomorph.isCompact_preimage.2
      (isCompact_Icc.prod isCompact_Icc)).prod isCompact_univ
  refine hK.image_of_continuousOn
    (sphereCircleChart.contMDiffOn_toFun.continuousOn.mono ?_)
  rw [sphereCircleChart_source]
  exact prod_mono sphereCircleCbaseSet_subset subset_rfl

theorem isClosed_sphereCircleRegion : IsClosed sphereCircleBundle.region :=
  isCompact_sphereCircleRegion.isClosed

/-! ## The band is the union of the handles and the region -/

theorem norm_mem_Icc_of_band {y : E3} (h1 : -3 / 5 ≤ (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4))
    (h2 : (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) ≤ 3 / 5) : ‖y‖ ∈ Icc (1 : ℝ) 4 := by
  rw [le_stereoHeight_iff (sq_nonneg _) (by norm_num)] at h1
  rw [stereoHeight_le_iff (sq_nonneg _) (by norm_num)] at h2
  norm_num at h1 h2
  constructor <;> nlinarith [norm_nonneg y]

/-- **The band `−3/5 ≤ q₀ ≤ 3/5` is covered by the two handles and the circle region.** -/
theorem band_subset_edge_union_region {x : sphereW.Carrier} (h1 : -3 / 5 ≤ sphereHeight x)
    (h2 : sphereHeight x ≤ 3 / 5) :
    x ∈ sphereEdgeBundle.edgePiece ∪ sphereCircleBundle.region := by
  obtain ⟨y, rfl, hy⟩ := exists_ambient_of_height_lt (by linarith : sphereHeight x < 1)
  rw [hy] at h1 h2
  have hr := norm_mem_Icc_of_band h1 h2
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr
    norm_num at hr
  obtain ⟨⟨t, ht⟩, htr, -⟩ := cycleHandleRadius_inverse hr
  set θ := sphereDirection southPole y with hθdef
  have hyθ : cycleBallAmbient false y =
      cycleBallAmbient false (cycleHandleRadius t • (θ : E3)) := by
    rw [htr, hθdef, norm_smul_sphereDirection southPole hy0]
  rw [hyθ, sphere_edgePiece_eq]
  have ht1 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  by_cases hN : θ = northPole
  · left
    refine mem_iUnion.2 ⟨true, ⟨(⟨0, by simp⟩, ⟨1 - t, ht1⟩), ?_⟩⟩
    rw [cycleS3Handle_map]
    dsimp only
    rw [cycleHandleChart_true_shell, stereo_symm_zero_JOINT, neg_neg, hN, sub_sub_cancel]
  · set w := Handle.stereoChart northPole θ with hwdef
    have hθw : ((Handle.stereoChart northPole).symm w : E3) = (θ : E3) := by
      rw [hwdef, stereo_symm_stereo_JOINT hN]
    rcases le_or_gt ‖w‖ 1 with hw1 | hw1
    · left
      refine mem_iUnion.2 ⟨false, ⟨(⟨w, hw1⟩, ⟨t, ht⟩), ?_⟩⟩
      rw [cycleS3Handle_map]
      dsimp only
      rw [cycleHandleChart_false_shell, hθw]
    rcases le_or_gt 4 ‖w‖ with hw4 | hw4
    · left
      have hw0 : w ≠ 0 := by
        intro h
        rw [h, norm_zero] at hw4
        norm_num at hw4
      have hn' : ‖-(4 / ‖w‖ ^ 2) • w‖ ≤ 1 := by
        rw [norm_antipodeW_JOINT hw0, div_le_one (by positivity)]
        exact hw4
      refine mem_iUnion.2 ⟨true, ⟨(⟨_, hn'⟩, ⟨1 - t, ht1⟩), ?_⟩⟩
      rw [cycleS3Handle_map]
      dsimp only
      rw [cycleHandleChart_true_shell, stereoChart_symm_neg_CIRCA northPole
        (antipodeW_ne_zero_JOINT hw0), antipodeW_antipodeW_JOINT hw0, hθw, sub_sub_cancel]
    · right
      rw [sphereCircleBundle_region]
      refine ⟨(sphereCircleEquiv.symm (‖w‖, cycleHandleRadius t),
        unitOf (Complex.orthonormalBasisOneI.repr.symm w)), ⟨?_, mem_univ _⟩, ?_⟩
      · change sphereCircleEquiv (sphereCircleEquiv.symm (‖w‖, cycleHandleRadius t)) ∈
          Icc (1 : ℝ) 4 ×ˢ Icc (1 : ℝ) 4
        rw [ContinuousLinearEquiv.apply_symm_apply, htr]
        exact ⟨⟨hw1.le, hw4.le⟩, hr⟩
      · rw [sphereCircleChart_equiv_symm, planeOfCircle_unitOf_CIRCA, hθw]

/-! ## Handle points in the circle domain -/

/-- A handle point of the circle domain: its base coordinate `ψ` is `‖w‖` (south handle) or
`4 / ‖w‖` with `w ≠ 0` (north handle). -/
theorem edge_mem_domain_psi {x : sphereCircleDomain} (hx : x.val ∈ sphereEdgeBundle.edgePiece) :
    ∃ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      (x.val = (cycleS3Handle false).map (w, t) ∧
        (sphereCircleEquiv (sphereCircleProj x : E2)).1 = ‖w.val‖) ∨
      (x.val = (cycleS3Handle true).map (w, t) ∧ w.val ≠ 0 ∧
        (sphereCircleEquiv (sphereCircleProj x : E2)).1 = 4 / ‖w.val‖) := by
  rw [sphere_edgePiece_eq] at hx
  obtain ⟨b, ⟨w, t⟩, hwt⟩ := mem_iUnion.1 hx
  refine ⟨w, t, ?_⟩
  have ht := mem_Ioo_of_Icc_FC39P0b t
  cases b
  · left
    have hpos := cycleHandleRadius_pos_FC39P0 ht
    have h := sphereCircleEquiv_proj_of_eq hpos (x := x)
      (θ := (Handle.stereoChart northPole).symm w.val)
      (by rw [← hwt, cycleS3Handle_map, cycleHandleChart_false_shell])
    rw [h, stereo_stereo_symm_JOINT]
    exact ⟨hwt.symm, rfl⟩
  · right
    have hpos := cycleHandleRadius_pos_FC39P0 (t := 1 - t.val)
      ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    by_cases hw : w.val = 0
    · exfalso
      have hxv : x.val =
          cycleBallAmbient false (cycleHandleRadius (1 - t.val) • (northPole : E3)) := by
        rw [← hwt, cycleS3Handle_map, cycleHandleChart_true_shell, hw, stereo_symm_zero_JOINT,
          neg_neg]
      have hx2 := x.2
      rw [hxv] at hx2
      exact ambient_north_not_mem_domain_JOINT hpos hx2
    · have h := sphereCircleEquiv_proj_of_eq hpos (x := x)
        (θ := (Handle.stereoChart northPole).symm (-(4 / ‖w.val‖ ^ 2) • w.val))
        (by rw [← hwt, cycleS3Handle_map, cycleHandleChart_true_shell,
          stereoChart_symm_neg_CIRCA northPole hw])
      rw [h, stereo_stereo_symm_JOINT, norm_antipodeW_JOINT hw]
      exact ⟨hwt.symm, hw, rfl⟩

/-- **A handle point of the circle domain has `ψ ≤ 1` or `ψ ≥ 4`.** -/
theorem edge_mem_domain_psi_le {x : sphereCircleDomain}
    (hx : x.val ∈ sphereEdgeBundle.edgePiece) :
    (sphereCircleEquiv (sphereCircleProj x : E2)).1 ≤ 1 ∨
      4 ≤ (sphereCircleEquiv (sphereCircleProj x : E2)).1 := by
  obtain ⟨w, t, ⟨-, h⟩ | ⟨-, hw, h⟩⟩ := edge_mem_domain_psi hx
  · left
    rw [h]
    exact w.2
  · right
    rw [h, le_div_iff₀ (norm_pos_iff.2 hw)]
    nlinarith [w.2]

/-- A handle point with `‖w‖ = 1` lies on the vertical face. -/
theorem handle_mem_vertical_JOINT (b : Bool) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1)
    (hw : ‖w.val‖ = 1) : (cycleS3Handle b).map (w, t) ∈ sphereEdgeBundle.vertical := by
  obtain ⟨hs, hp⟩ := cycleS3Handle_proj b w t
  refine ⟨⟨_, hs⟩, ⟨?_, ?_⟩, rfl⟩
  · change edgeProj ⟨_, hs⟩ ∈ edgeCbase
    rw [hp]
    exact range_edgeInterval_subset b ⟨t, rfl⟩
  · change edgeHeightR ((cycleS3Handle b).map (w, t)) = 1
    rw [cycleS3Handle_map, edgeHeightR_chart (handle_box w t), hw, one_pow]

/-- **A handle point of the circle domain with `ψ ∈ [1, 4]` lies on the vertical face.** -/
theorem edge_mem_domain_vertical {x : sphereCircleDomain}
    (hx : x.val ∈ sphereEdgeBundle.edgePiece)
    (hψ : (sphereCircleEquiv (sphereCircleProj x : E2)).1 ∈ Icc (1 : ℝ) 4) :
    x.val ∈ sphereEdgeBundle.vertical := by
  obtain ⟨w, t, ⟨hxw, h⟩ | ⟨hxw, hw, h⟩⟩ := edge_mem_domain_psi hx
  · rw [h] at hψ
    rw [hxw]
    exact handle_mem_vertical_JOINT false w t (le_antisymm w.2 hψ.1)
  · rw [h] at hψ
    rw [hxw]
    have hn := norm_pos_iff.2 hw
    have h4 := hψ.2
    rw [div_le_iff₀ hn] at h4
    exact handle_mem_vertical_JOINT true w t (le_antisymm w.2 (by linarith))

/-- **`edge_region` for the S³ data**: `P ∩ M₃ = V` (the edge piece meets the circle region
exactly in the vertical face). -/
theorem sphere_edge_region :
    sphereEdgeBundle.edgePiece ∩ sphereCircleBundle.region = sphereEdgeBundle.vertical := by
  apply Subset.antisymm
  · rintro x ⟨hxe, ⟨y, hy, rfl⟩⟩
    have hy' : sphereCircleEquiv (sphereCircleProj y : E2) ∈ Icc (1 : ℝ) 4 ×ˢ Icc (1 : ℝ) 4 :=
      hy
    exact edge_mem_domain_vertical hxe hy'.1
  · intro x hx
    refine ⟨?_, sphereEdgeBundle_vertical_subset_region hx⟩
    obtain ⟨y, ⟨h1, h2⟩, rfl⟩ := hx
    exact ⟨y, ⟨h1, h2.le⟩, rfl⟩

/-! ## Vertical points are limits of non-edge points -/

/-- **A vertical point is a limit of points of the same height off the edge piece** (move `ψ`
from `1` or `4` into `(1, 4)` in the circle chart). -/
theorem vertical_mem_closure_JOINT {x : sphereW.Carrier} (hx : x ∈ sphereEdgeBundle.vertical) :
    x ∈ closure {z | sphereHeight z = sphereHeight x ∧ z ∉ sphereEdgeBundle.edgePiece} := by
  rw [sphereEdgeBundle_vertical_eq] at hx
  obtain ⟨⟨c, s⟩, ⟨hc, -⟩, rfl⟩ := hx
  have hc1 : (sphereCircleEquiv c).1 ∈ ({1, 4} : Set ℝ) := hc.1
  have hc2 : (sphereCircleEquiv c).2 ∈ Icc (1 : ℝ) 4 := hc.2
  set ψ₀ := (sphereCircleEquiv c).1 with hψ₀def
  set r := (sphereCircleEquiv c).2 with hrdef
  have hcψ : c = sphereCircleEquiv.symm (ψ₀, r) := (sphereCircleEquiv.symm_apply_apply c).symm
  have hψ₀ : ψ₀ ∈ Icc (1 : ℝ) 4 := by
    rcases hc1 with h | h <;> rw [h] <;> norm_num
  have hr : r ∈ sphereCircleWide := ⟨by linarith [hc2.1], by linarith [hc2.2]⟩
  have hwide : ∀ ψ ∈ Icc (1 : ℝ) 4, ψ ∈ sphereCircleWide := fun ψ hψ =>
    ⟨by linarith [hψ.1], by linarith [hψ.2]⟩
  have hsrc : ∀ ψ ∈ Icc (1 : ℝ) 4,
      (sphereCircleEquiv.symm (ψ, r), s) ∈ sphereCircleChart.source := by
    intro ψ hψ
    rw [sphereCircleChart_source]
    exact ⟨sphereCircleEquiv_symm_mem (hwide ψ hψ) hr, mem_univ _⟩
  let f : ℝ → sphereW.Carrier := fun ψ => sphereCircleChart (sphereCircleEquiv.symm (ψ, r), s)
  have hfc : ContinuousAt f ψ₀ := by
    have hJ : ContinuousAt sphereCircleChart (sphereCircleEquiv.symm (ψ₀, r), s) :=
      sphereCircleChart.contMDiffOn_toFun.continuousOn.continuousAt
        (sphereCircleChart.open_source.mem_nhds (hsrc ψ₀ hψ₀))
    have hg : Continuous fun ψ : ℝ => (sphereCircleEquiv.symm (ψ, r), s) :=
      (sphereCircleEquiv.symm.continuous.comp (continuous_id.prodMk continuous_const)).prodMk
        continuous_const
    exact ContinuousAt.comp (f := fun ψ : ℝ => (sphereCircleEquiv.symm (ψ, r), s)) (x := ψ₀) hJ
      hg.continuousAt
  have hf₀ : f ψ₀ = sphereCircleChart (c, s) := by
    change sphereCircleChart (sphereCircleEquiv.symm (ψ₀, r), s) = _
    rw [← hcψ]
  rw [← hf₀]
  have hne : (𝓝[Ioo (1 : ℝ) 4] ψ₀).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num)]
    exact hψ₀
  refine mem_closure_of_tendsto (f := f) (b := 𝓝[Ioo (1 : ℝ) 4] ψ₀)
    (hfc.tendsto.mono_left nhdsWithin_le_nhds) ?_
  refine eventually_nhdsWithin_of_forall fun ψ hψ => ⟨?_, ?_⟩
  · change sphereHeight (sphereCircleChart (sphereCircleEquiv.symm (ψ, r), s)) =
      sphereHeight (sphereCircleChart (sphereCircleEquiv.symm (ψ₀, r), s))
    rw [sphereHeight_sphereCircleChart, sphereHeight_sphereCircleChart,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  · intro he
    have hψI : ψ ∈ Icc (1 : ℝ) 4 := Ioo_subset_Icc_self hψ
    have hdom : f ψ ∈ sphereCircleDomain := sphereCircleChart_mem_domain (hsrc ψ hψI)
    have h := edge_mem_domain_psi_le (x := ⟨f ψ, hdom⟩) he
    rw [sphereCircleEquiv_proj_chart (hwide ψ hψI) hr s hdom] at h
    rcases h with h | h
    · exact absurd h (not_le.2 hψ.1)
    · exact absurd h (not_le.2 hψ.2)

end GC.GraphManifold.Assembly.FC39P0
