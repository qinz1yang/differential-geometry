import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapPatches
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapTransitions
import DifferentialGeometry.Topology.Manifold.OpenTarget

/-!
Actual smooth compatibility of core, tagged-ball and signed-sphere attachment patches.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance sphereCapCompatibilityBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance sphereCapCompatibilityBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

local instance sphereCapCompatibilityLiftedBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} sphereCapBallOpen) :=
  uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

private theorem sphereCapCore_ne_ball_of_open (x : B.sphereCapCoreOpen)
    (i : Fin B.sphereCount) (y : ClosedCell 3) : B.sphereCapCore x.val ≠ B.sphereCapBall i y := by
  intro he
  rcases (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact he) with
    h | ⟨j, z, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · cases h
  · apply x.property
    exact mem_iUnion.mpr ⟨j, z, (Sum.inl_injective hx).symm⟩
  · dsimp [sphereCapRight] at hx
    cases hx

private theorem sphereCapCore_ne_ballInterior (x : C.Carrier)
    (i : Fin B.sphereCount) (y : sphereCapBallOpen) :
    B.sphereCapCore x ≠ B.sphereCapBall i y.val := by
  intro he
  rcases (B.sphereCapGluing_rel_iff _ _).mp (Quotient.exact he) with
    h | ⟨j, z, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
  · cases h
  · have hz : y.val = closureSphereToBall z := congrArg Prod.snd (Sum.inr_injective hy)
    have hn : ‖y.val.val‖ = 1 := by
      rw [hz]
      exact norm_eq_of_mem_sphere z.down
    exact (ne_of_lt y.property) hn
  · dsimp [sphereCapRight] at hx
    cases hx

theorem sphereCapSignedSeam_coreOpen_positive (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ} (hp : p ∈ sphereSignedCollarSource)
    (x : B.sphereCapCoreOpen) (he : B.sphereCapSignedSeam i p = B.sphereCapCore x.val) :
    0 < p.2 := by
  by_cases hs : 0 ≤ p.2
  · have hf := B.sphereCapSignedSeam_positive i p.1 p.2 hs hp.2.2
    have hx := B.sphereCapCore_injective (hf.symm.trans he)
    by_contra hn
    have hz : p.2 = 0 := le_antisymm (le_of_not_gt hn) hs
    apply x.property
    refine mem_iUnion.mpr ⟨i, p.1, ?_⟩
    have hpz : p = (p.1, 0) := Prod.ext rfl hz
    rw [hpz, B.sphereCapSignedSeam_zero] at he
    exact B.sphereCapCore_injective he
  · have hf := B.sphereCapSignedSeam_negative i p.1 p.2 (le_of_not_ge hs) hp.2.1
    exact (B.sphereCapCore_ne_ball_of_open x i _ (he.symm.trans hf)).elim

theorem sphereCapSignedSeam_ballOpen_negative (i j : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ} (hp : p ∈ sphereSignedCollarSource)
    (x : sphereCapBallOpen) (he : B.sphereCapSignedSeam i p = B.sphereCapBall j x.val) :
    p.2 < 0 ∧ i = j := by
  by_cases hs : 0 ≤ p.2
  · have hf := B.sphereCapSignedSeam_positive i p.1 p.2 hs hp.2.2
    exact (B.sphereCapCore_ne_ballInterior _ j x (hf.symm.trans he)).elim
  · refine ⟨lt_of_not_ge hs, ?_⟩
    by_contra hij
    have hf := B.sphereCapSignedSeam_negative i p.1 p.2 (le_of_not_ge hs) hp.2.1
    exact (B.sphereCapBall_disjoint hij).le_bot
      ⟨⟨_, hf.symm.trans he⟩, ⟨x.val, rfl⟩⟩

theorem sphereCapSignedSeam_symm_core (i : Fin B.sphereCount) {x : C.Carrier}
    (hx : x ∈ (B.sphere i).target) :
    (B.sphereCapSignedSeam i).symm (B.sphereCapCore x) =
      (((B.sphere i).symm x).1, ((B.sphere i).symm x).2.val 0) := by
  have hU : Sum.inl x ∈ B.sphereCapSeamUnion i := by
    simp only [sphereCapSeamUnion, mem_union, mem_image, Sum.inl.injEq,
      exists_eq_right, Sum.inr_ne_inl, and_false, exists_false, or_false]
    exact hx
  have hs := B.sphereCapSeamCoordinates_mem i hU
  have hf := (B.sphereCapSignedSeam_apply i _ hs).trans
    (B.sphereCapSeamCoordinates_fold i hU)
  change B.sphereCapSignedSeam i (B.sphereCapSeamCoordinates i (Sum.inl x)) =
    B.sphereCapCore x at hf
  rw [← hf]
  exact (B.sphereCapSignedSeam i).left_inv ((B.sphereCapSignedSeam_source i).symm ▸ hs)

theorem sphereCapSignedSeam_symm_ball (i : Fin B.sphereCount) {x : ClosedCell 3}
    (hx : x ∈ sphereCapBallCollar.{u}.target) :
    (B.sphereCapSignedSeam i).symm (B.sphereCapBall i x) =
      ((sphereCapBallCollar.{u}.symm x).1, -(sphereCapBallCollar.{u}.symm x).2.val 0) := by
  have hU : Sum.inr (i, x) ∈ B.sphereCapSeamUnion i := by
    simp [sphereCapSeamUnion, hx]
  have hs := B.sphereCapSeamCoordinates_mem i hU
  have hf := (B.sphereCapSignedSeam_apply i _ hs).trans
    (B.sphereCapSeamCoordinates_fold i hU)
  change B.sphereCapSignedSeam i (B.sphereCapSeamCoordinates i (Sum.inr (i, x))) =
    B.sphereCapBall i x at hf
  rw [← hf]
  exact (B.sphereCapSignedSeam i).left_inv ((B.sphereCapSignedSeam_source i).symm ▸ hs)

theorem sphereCapSignedCoreTransition_mem (x : B.sphereCapCoreOpen) (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm).source) :
    p ∈ (B.sphereCapCoreTransition i).source := by
  have hps := (B.sphereCapSignedSeam_source i).subset hp.1
  let y := (B.sphereCapPatch (.inl x)).symm (B.sphereCapSignedSeam i p)
  have he : B.sphereCapCore y.val = B.sphereCapSignedSeam i p :=
    (B.sphereCapPatch (.inl x)).right_inv hp.2
  have hs := B.sphereCapSignedSeam_coreOpen_positive i hps y he.symm
  rw [B.sphereCapCoreTransition_source]
  exact ⟨trivial, hs, hps.2.2⟩

theorem sphereCapSignedCoreTransition_apply (x : B.sphereCapCoreOpen) (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm).source) :
    (((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm) p).val =
      B.sphereCapCoreTransition i p := by
  have hpd := B.sphereCapSignedCoreTransition_mem x i hp
  rw [B.sphereCapCoreTransition_source] at hpd
  have hf := B.sphereCapSignedSeam_positive i p.1 p.2 hpd.2.1.le hpd.2.2
  change ((B.sphereCapPatch (.inl x)).symm (B.sphereCapSignedSeam i p)).val = _
  apply B.sphereCapCore_injective
  have he := (B.sphereCapPatch (.inl x)).right_inv hp.2
  change B.sphereCapCore ((B.sphereCapPatch (.inl x)).symm
    (B.sphereCapSignedSeam i p)).val = B.sphereCapSignedSeam i p at he
  rw [he, hf]
  congr 1
  change B.sphere i (p.1, halfPoint p.2 hpd.2.1.le) =
    B.sphere i (sphereCapPositiveHalf p)
  rw [sphereCapPositiveHalf_apply p.1 p.2 hpd.2.1]

theorem sphereCapSignedBallTransition_index (i j : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ ((B.sphereCapSignedSeam i).trans
      (B.sphereCapPatch (.inr (.inl j))).symm).source) : i = j := by
  have hps := (B.sphereCapSignedSeam_source i).subset hp.1
  let y := (B.sphereCapPatch (.inr (.inl j))).symm (B.sphereCapSignedSeam i p)
  have he : B.sphereCapBall j y.down.val = B.sphereCapSignedSeam i p :=
    (B.sphereCapPatch (.inr (.inl j))).right_inv hp.2
  exact (B.sphereCapSignedSeam_ballOpen_negative i j hps y.down he.symm).2

theorem sphereCapSignedBallTransition_mem (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ ((B.sphereCapSignedSeam i).trans
      (B.sphereCapPatch (.inr (.inl i))).symm).source) :
    p ∈ sphereCapBallTransition.{u}.source := by
  have hps := (B.sphereCapSignedSeam_source i).subset hp.1
  let y := (B.sphereCapPatch (.inr (.inl i))).symm (B.sphereCapSignedSeam i p)
  have he : B.sphereCapBall i y.down.val = B.sphereCapSignedSeam i p :=
    (B.sphereCapPatch (.inr (.inl i))).right_inv hp.2
  have hs := (B.sphereCapSignedSeam_ballOpen_negative i i hps y.down he.symm).1
  rw [sphereCapBallTransition_source]
  exact ⟨trivial, hps.2.1, hs⟩

theorem sphereCapSignedBallTransition_apply (i : Fin B.sphereCount)
    {p : ClosureSphere.{u} × ℝ}
    (hp : p ∈ ((B.sphereCapSignedSeam i).trans
      (B.sphereCapPatch (.inr (.inl i))).symm).source) :
    ((B.sphereCapPatch (.inr (.inl i))).symm (B.sphereCapSignedSeam i p)).down.val =
      sphereCapBallTransition.{u} p := by
  have hpd := B.sphereCapSignedBallTransition_mem i hp
  rw [sphereCapBallTransition_source] at hpd
  have hf := B.sphereCapSignedSeam_negative i p.1 p.2 hpd.2.2.le hpd.2.1
  change ((B.sphereCapPatch (.inr (.inl i))).symm (B.sphereCapSignedSeam i p)).down.val = _
  apply B.sphereCapBall_injective i
  have he := (B.sphereCapPatch (.inr (.inl i))).right_inv hp.2
  change B.sphereCapBall i ((B.sphereCapPatch (.inr (.inl i))).symm
    (B.sphereCapSignedSeam i p)).down.val = B.sphereCapSignedSeam i p at he
  rw [he, hf]
  congr 1
  change sphereCapBallCollar (p.1, halfPoint (-p.2) (neg_nonneg.mpr hpd.2.2.le)) =
    sphereCapBallCollar (sphereCapNegativeHalf p)
  rw [sphereCapNegativeHalf_apply p.1 p.2 hpd.2.2]

theorem sphereCapCoreSignedTransition_mem (x : B.sphereCapCoreOpen) (i : Fin B.sphereCount)
    {y : B.sphereCapCoreOpen}
    (hy : y ∈ ((B.sphereCapPatch (.inl x)).trans (B.sphereCapSignedSeam i).symm).source) :
    y.val ∈ (B.sphereCapCoreTransition i).target := by
  let p := (B.sphereCapSignedSeam i).symm (B.sphereCapPatch (.inl x) y)
  have hp : p ∈ ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm).source := by
    refine ⟨(B.sphereCapSignedSeam i).map_target hy.2, ?_⟩
    change B.sphereCapSignedSeam i p ∈ (B.sphereCapPatch (.inl x)).target
    dsimp only [p]
    rw [(B.sphereCapSignedSeam i).right_inv (x := B.sphereCapPatch (.inl x) y) hy.2]
    exact (B.sphereCapPatch (.inl x)).map_source hy.1
  have hm := B.sphereCapSignedCoreTransition_mem x i hp
  have he := B.sphereCapSignedCoreTransition_apply x i hp
  change ((B.sphereCapPatch (.inl x)).symm (B.sphereCapSignedSeam i p)).val = _ at he
  dsimp only [p] at he
  rw [(B.sphereCapSignedSeam i).right_inv (x := B.sphereCapPatch (.inl x) y) hy.2,
    (B.sphereCapPatch (.inl x)).left_inv hy.1] at he
  exact he.symm ▸ (B.sphereCapCoreTransition i).map_source hm

theorem sphereCapCoreSignedTransition_apply (x : B.sphereCapCoreOpen) (i : Fin B.sphereCount)
    {y : B.sphereCapCoreOpen}
    (hy : y ∈ ((B.sphereCapPatch (.inl x)).trans (B.sphereCapSignedSeam i).symm).source) :
    ((B.sphereCapPatch (.inl x)).trans (B.sphereCapSignedSeam i).symm) y =
      (B.sphereCapCoreTransition i).symm y.val := by
  let p := (B.sphereCapSignedSeam i).symm (B.sphereCapPatch (.inl x) y)
  have hp : p ∈ ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm).source := by
    refine ⟨(B.sphereCapSignedSeam i).map_target hy.2, ?_⟩
    change B.sphereCapSignedSeam i p ∈ (B.sphereCapPatch (.inl x)).target
    dsimp only [p]
    rw [(B.sphereCapSignedSeam i).right_inv (x := B.sphereCapPatch (.inl x) y) hy.2]
    exact (B.sphereCapPatch (.inl x)).map_source hy.1
  have hm := B.sphereCapSignedCoreTransition_mem x i hp
  have he := B.sphereCapSignedCoreTransition_apply x i hp
  change ((B.sphereCapPatch (.inl x)).symm (B.sphereCapSignedSeam i p)).val = _ at he
  dsimp only [p] at he
  rw [(B.sphereCapSignedSeam i).right_inv (x := B.sphereCapPatch (.inl x) y) hy.2,
    (B.sphereCapPatch (.inl x)).left_inv hy.1] at he
  change p = (B.sphereCapCoreTransition i).symm y.val
  rw [he]
  exact ((B.sphereCapCoreTransition i).left_inv hm).symm

theorem sphereCapBallSignedTransition_index (i j : Fin B.sphereCount)
    {y : ULift.{u} sphereCapBallOpen}
    (hy : y ∈ ((B.sphereCapPatch (.inr (.inl i))).trans
      (B.sphereCapSignedSeam j).symm).source) : i = j := by
  let p := (B.sphereCapSignedSeam j).symm (B.sphereCapPatch (.inr (.inl i)) y)
  have hp : p ∈ ((B.sphereCapSignedSeam j).trans
      (B.sphereCapPatch (.inr (.inl i))).symm).source := by
    refine ⟨(B.sphereCapSignedSeam j).map_target hy.2, ?_⟩
    change B.sphereCapSignedSeam j p ∈ (B.sphereCapPatch (.inr (.inl i))).target
    dsimp only [p]
    rw [(B.sphereCapSignedSeam j).right_inv
      (x := B.sphereCapPatch (.inr (.inl i)) y) hy.2]
    exact (B.sphereCapPatch (.inr (.inl i))).map_source hy.1
  exact (B.sphereCapSignedBallTransition_index j i hp).symm

theorem sphereCapBallSignedTransition_mem (i : Fin B.sphereCount)
    {y : ULift.{u} sphereCapBallOpen}
    (hy : y ∈ ((B.sphereCapPatch (.inr (.inl i))).trans
      (B.sphereCapSignedSeam i).symm).source) :
    y.down.val ∈ sphereCapBallTransition.{u}.target := by
  let p := (B.sphereCapSignedSeam i).symm (B.sphereCapPatch (.inr (.inl i)) y)
  have hp : p ∈ ((B.sphereCapSignedSeam i).trans
      (B.sphereCapPatch (.inr (.inl i))).symm).source := by
    refine ⟨(B.sphereCapSignedSeam i).map_target hy.2, ?_⟩
    change B.sphereCapSignedSeam i p ∈ (B.sphereCapPatch (.inr (.inl i))).target
    dsimp only [p]
    rw [(B.sphereCapSignedSeam i).right_inv
      (x := B.sphereCapPatch (.inr (.inl i)) y) hy.2]
    exact (B.sphereCapPatch (.inr (.inl i))).map_source hy.1
  have hm := B.sphereCapSignedBallTransition_mem i hp
  have he := B.sphereCapSignedBallTransition_apply i hp
  dsimp only [p] at he
  rw [(B.sphereCapSignedSeam i).right_inv
      (x := B.sphereCapPatch (.inr (.inl i)) y) hy.2,
    (B.sphereCapPatch (.inr (.inl i))).left_inv hy.1] at he
  exact he.symm ▸ sphereCapBallTransition.map_source hm

theorem sphereCapBallSignedTransition_apply (i : Fin B.sphereCount)
    {y : ULift.{u} sphereCapBallOpen}
    (hy : y ∈ ((B.sphereCapPatch (.inr (.inl i))).trans
      (B.sphereCapSignedSeam i).symm).source) :
    ((B.sphereCapPatch (.inr (.inl i))).trans (B.sphereCapSignedSeam i).symm) y =
      sphereCapBallTransition.{u}.symm y.down.val := by
  let p := (B.sphereCapSignedSeam i).symm (B.sphereCapPatch (.inr (.inl i)) y)
  have hp : p ∈ ((B.sphereCapSignedSeam i).trans
      (B.sphereCapPatch (.inr (.inl i))).symm).source := by
    refine ⟨(B.sphereCapSignedSeam i).map_target hy.2, ?_⟩
    change B.sphereCapSignedSeam i p ∈ (B.sphereCapPatch (.inr (.inl i))).target
    dsimp only [p]
    rw [(B.sphereCapSignedSeam i).right_inv
      (x := B.sphereCapPatch (.inr (.inl i)) y) hy.2]
    exact (B.sphereCapPatch (.inr (.inl i))).map_source hy.1
  have hm := B.sphereCapSignedBallTransition_mem i hp
  have he := B.sphereCapSignedBallTransition_apply i hp
  dsimp only [p] at he
  rw [(B.sphereCapSignedSeam i).right_inv
      (x := B.sphereCapPatch (.inr (.inl i)) y) hy.2,
    (B.sphereCapPatch (.inr (.inl i))).left_inv hy.1] at he
  change p = sphereCapBallTransition.{u}.symm y.down.val
  rw [he]
  exact (sphereCapBallTransition.left_inv hm).symm

private theorem sphereCapCoreSignedTransition_smooth (x : B.sphereCapCoreOpen)
    (i : Fin B.sphereCount) : ContMDiffOn C.model sphereSignedCollarModel ∞
      ((B.sphereCapPatch (.inl x)).trans (B.sphereCapSignedSeam i).symm)
      ((B.sphereCapPatch (.inl x)).trans (B.sphereCapSignedSeam i).symm).source := by
  have h := (B.sphereCapCoreTransition i).contMDiffOn_invFun.comp
    contMDiff_subtype_val.contMDiffOn (fun y hy => B.sphereCapCoreSignedTransition_mem x i hy)
  exact h.congr (fun y hy => B.sphereCapCoreSignedTransition_apply x i hy)

private theorem sphereCapBallSignedTransition_smooth (i : Fin B.sphereCount) :
    ContMDiffOn (𝓡∂ 3) sphereSignedCollarModel ∞
      ((B.sphereCapPatch (.inr (.inl i))).trans (B.sphereCapSignedSeam i).symm)
      ((B.sphereCapPatch (.inr (.inl i))).trans (B.sphereCapSignedSeam i).symm).source := by
  have hd : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (fun y : ULift.{u} sphereCapBallOpen => y.down.val) :=
    contMDiff_subtype_val.comp (uliftDiffeomorph (𝓡∂ 3) sphereCapBallOpen).symm.contMDiff
  have h := sphereCapBallTransition.{u}.contMDiffOn_invFun.comp hd.contMDiffOn
    (fun y hy => B.sphereCapBallSignedTransition_mem i hy)
  exact h.congr (fun y hy => B.sphereCapBallSignedTransition_apply i hy)

private theorem sphereCapSignedCoreTransition_smooth (x : B.sphereCapCoreOpen)
    (i : Fin B.sphereCount) : ContMDiffOn sphereSignedCollarModel C.model ∞
      ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm)
      ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inl x)).symm).source := by
  intro p hp
  apply (contMDiffWithinAt_subtypeVal_comp_iff B.sphereCapCoreOpen _ _ _).mp
  have h := ((B.sphereCapCoreTransition i).contMDiffOn.mono
    (fun y hy => B.sphereCapSignedCoreTransition_mem x i hy)).congr
      (fun y hy => B.sphereCapSignedCoreTransition_apply x i hy)
  exact h p hp

private theorem sphereCapSignedBallTransition_smooth (i : Fin B.sphereCount) :
    ContMDiffOn sphereSignedCollarModel (𝓡∂ 3) ∞
      ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inr (.inl i))).symm)
      ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inr (.inl i))).symm).source := by
  intro p hp
  let f := (B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inr (.inl i))).symm
  have h := (sphereCapBallTransition.{u}.contMDiffOn.mono
    (fun y hy => B.sphereCapSignedBallTransition_mem i hy)).congr
      (fun y hy => B.sphereCapSignedBallTransition_apply i hy)
  have hd : ContMDiffWithinAt sphereSignedCollarModel (𝓡∂ 3) ∞
      (fun y => (f y).down) f.source p :=
    (contMDiffWithinAt_subtypeVal_comp_iff sphereCapBallOpen _ _ _).mp (h p hp)
  have hu := (uliftDiffeomorph (𝓡∂ 3) sphereCapBallOpen).contMDiff.contMDiffAt
    (x := (f p).down) |>.comp_contMDiffWithinAt p hd
  simpa only [Function.comp_def, uliftDiffeomorph_apply, ULift.up_down] using hu

theorem sphereCapCoreCoreTransition_apply (x y p : B.sphereCapCoreOpen)
    (hp : p ∈ ((B.sphereCapPatch (.inl x)).trans (B.sphereCapPatch (.inl y)).symm).source) :
    ((B.sphereCapPatch (.inl x)).trans (B.sphereCapPatch (.inl y)).symm) p = p := by
  apply Subtype.ext
  apply B.sphereCapCore_injective
  exact (B.sphereCapPatch (.inl y)).right_inv (x := B.sphereCapPatch (.inl x) p) hp.2

theorem sphereCapCoreBallTransition_empty (x : B.sphereCapCoreOpen)
    (i : Fin B.sphereCount) :
    ((B.sphereCapPatch (.inl x)).trans (B.sphereCapPatch (.inr (.inl i))).symm).source = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  let y := (B.sphereCapPatch (.inr (.inl i))).symm (B.sphereCapPatch (.inl x) p)
  have he : B.sphereCapBall i y.down.val = B.sphereCapCore p.val :=
    (B.sphereCapPatch (.inr (.inl i))).right_inv (x := B.sphereCapPatch (.inl x) p) hp.2
  exact B.sphereCapCore_ne_ball_of_open p i y.down.val he.symm

theorem sphereCapBallCoreTransition_empty (i : Fin B.sphereCount)
    (x : B.sphereCapCoreOpen) :
    ((B.sphereCapPatch (.inr (.inl i))).trans (B.sphereCapPatch (.inl x)).symm).source = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  let y := (B.sphereCapPatch (.inl x)).symm (B.sphereCapPatch (.inr (.inl i)) p)
  have he : B.sphereCapCore y.val = B.sphereCapBall i p.down.val :=
    (B.sphereCapPatch (.inl x)).right_inv (x := B.sphereCapPatch (.inr (.inl i)) p) hp.2
  exact B.sphereCapCore_ne_ball_of_open y i p.down.val he

theorem sphereCapBallBallTransition_empty (i j : Fin B.sphereCount) (hij : i ≠ j) :
    ((B.sphereCapPatch (.inr (.inl i))).trans
      (B.sphereCapPatch (.inr (.inl j))).symm).source = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  let y := (B.sphereCapPatch (.inr (.inl j))).symm (B.sphereCapPatch (.inr (.inl i)) p)
  have he : B.sphereCapBall j y.down.val = B.sphereCapBall i p.down.val :=
    (B.sphereCapPatch (.inr (.inl j))).right_inv
      (x := B.sphereCapPatch (.inr (.inl i)) p) hp.2
  exact (B.sphereCapBall_disjoint hij).le_bot ⟨⟨p.down.val, rfl⟩, ⟨y.down.val, he⟩⟩

theorem sphereCapSignedSignedTransition_empty (i j : Fin B.sphereCount) (hij : i ≠ j) :
    ((B.sphereCapSignedSeam i).trans (B.sphereCapSignedSeam j).symm).source = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (B.sphereCapSignedSeam_disjoint hij).le_bot
    ⟨(B.sphereCapSignedSeam i).map_source hp.1, hp.2⟩

theorem sphereCapPatch_compatible (a b : B.SphereCapPatchIndex) :
    ContMDiffOn (B.sphereCapPatchModel a) (B.sphereCapPatchModel b) ∞
      ((B.sphereCapPatch a).trans (B.sphereCapPatch b).symm)
      ((B.sphereCapPatch a).trans (B.sphereCapPatch b).symm).source := by
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      exact contMDiffOn_id.congr (fun p hp => B.sphereCapCoreCoreTransition_apply x y p hp)
    | inr b =>
      cases b with
      | inl j =>
        rw [B.sphereCapCoreBallTransition_empty x j]
        exact contMDiffOn_empty
      | inr j => exact B.sphereCapCoreSignedTransition_smooth x j
  | inr a =>
    cases a with
    | inl i =>
      cases b with
      | inl y =>
        rw [B.sphereCapBallCoreTransition_empty i y]
        exact contMDiffOn_empty
      | inr b =>
        cases b with
        | inl j =>
          by_cases hij : i = j
          · subst j
            exact contMDiffOn_id.congr (fun p hp =>
              (B.sphereCapPatch (.inr (.inl i))).left_inv hp.1)
          · rw [B.sphereCapBallBallTransition_empty i j hij]
            exact contMDiffOn_empty
        | inr j =>
          change ContMDiffOn (𝓡∂ 3) sphereSignedCollarModel ∞
            ((B.sphereCapPatch (.inr (.inl i))).trans (B.sphereCapSignedSeam j).symm)
            ((B.sphereCapPatch (.inr (.inl i))).trans (B.sphereCapSignedSeam j).symm).source
          by_cases hij : i = j
          · subst j
            exact B.sphereCapBallSignedTransition_smooth i
          · have he : ((B.sphereCapPatch (.inr (.inl i))).trans
                (B.sphereCapSignedSeam j).symm).source = ∅ :=
              eq_empty_iff_forall_notMem.mpr (fun p hp =>
                hij (B.sphereCapBallSignedTransition_index i j hp))
            rw [he]
            exact contMDiffOn_empty
    | inr i =>
      cases b with
      | inl y => exact B.sphereCapSignedCoreTransition_smooth y i
      | inr b =>
        cases b with
        | inl j =>
          change ContMDiffOn sphereSignedCollarModel (𝓡∂ 3) ∞
            ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inr (.inl j))).symm)
            ((B.sphereCapSignedSeam i).trans (B.sphereCapPatch (.inr (.inl j))).symm).source
          by_cases hij : i = j
          · subst j
            exact B.sphereCapSignedBallTransition_smooth i
          · have he : ((B.sphereCapSignedSeam i).trans
                (B.sphereCapPatch (.inr (.inl j))).symm).source = ∅ :=
              eq_empty_iff_forall_notMem.mpr (fun p hp =>
                hij (B.sphereCapSignedBallTransition_index i j hp))
            rw [he]
            exact contMDiffOn_empty
        | inr j =>
          change ContMDiffOn sphereSignedCollarModel sphereSignedCollarModel ∞
            ((B.sphereCapSignedSeam i).trans (B.sphereCapSignedSeam j).symm)
            ((B.sphereCapSignedSeam i).trans (B.sphereCapSignedSeam j).symm).source
          by_cases hij : i = j
          · subst j
            exact contMDiffOn_id.congr (fun p hp => (B.sphereCapSignedSeam i).left_inv hp.1)
          · rw [B.sphereCapSignedSignedTransition_empty i j hij]
            exact contMDiffOn_empty

end GC.GraphManifold.MixedBoundaryCertificate
