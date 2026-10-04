import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideBall
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
Actual positive Euclidean ball charts for the same reparameterized bounded spherical caps.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric TopologicalSpace GC.GraphManifold.MixedBoundaryCertificate
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff Topology

universe u

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

def capBallAmbientNegation :
    EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearEquiv.neg ℝ).toDiffeomorph

private theorem exists_capBallAmbientExtension (i : Fin B.sphereCount) :
    ∃ R : EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3),
      (R = Diffeomorph.refl (𝓡 3) (EuclideanSpace ℝ (Fin 3)) ∞ ∨
        R = capBallAmbientNegation) ∧
      (∀ x : ClosedCell 3, R x.val = (B.sphereCapOrientationData.reparameterization i x).val) ∧
      ∀ x, ‖R x‖ = ‖x‖ := by
  rcases B.sphereCapOrientationData.choices i with h | h
  · refine ⟨Diffeomorph.refl (𝓡 3) (EuclideanSpace ℝ (Fin 3)) ∞, Or.inl rfl, ?_, ?_⟩
    · intro x
      rw [h.1]
      rfl
    · intro x
      rfl
  · refine ⟨capBallAmbientNegation, Or.inr rfl, ?_, ?_⟩
    · intro x
      rw [h.1, sphereCapBallReflection_apply]
      rfl
    · intro x
      exact norm_neg x

def capBallAmbientExtension (i : Fin B.sphereCount) :
    EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) :=
  (exists_capBallAmbientExtension B i).choose

theorem capBallAmbientExtension_choices (i : Fin B.sphereCount) :
    B.capBallAmbientExtension i = Diffeomorph.refl (𝓡 3) (EuclideanSpace ℝ (Fin 3)) ∞ ∨
      B.capBallAmbientExtension i = capBallAmbientNegation :=
  (exists_capBallAmbientExtension B i).choose_spec.1

theorem capBallAmbientExtension_cell (i : Fin B.sphereCount) (x : ClosedCell 3) :
    B.capBallAmbientExtension i x.val =
      (B.sphereCapOrientationData.reparameterization i x).val :=
  (exists_capBallAmbientExtension B i).choose_spec.2.1 x

theorem capBallAmbientExtension_norm (i : Fin B.sphereCount)
    (x : EuclideanSpace ℝ (Fin 3)) : ‖B.capBallAmbientExtension i x‖ = ‖x‖ :=
  (exists_capBallAmbientExtension B i).choose_spec.2.2 x

theorem capBallAmbientExtension_zero (i : Fin B.sphereCount) :
    B.capBallAmbientExtension i 0 = 0 := by
  apply norm_eq_zero.mp
  rw [B.capBallAmbientExtension_norm, norm_zero]

end GC.GraphManifold.MixedBoundaryCertificate

namespace GC.GraphManifold

variable {W : CompactCarrier.{u}}
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior) {n : ℕ} (A : BoundaryTori W n)
  (hA : W.model.boundary W.Carrier = A.image)
  (hav : ∀ i, Disjoint (A.collar i).target d.target)
  (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count} {b : Bool}
  (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))

private abbrev capBallB := boundedPlugCutBoundary d hs hI A hA hav

local instance capBallTargetCharts {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C) :
    ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient :=
  B.sphereCapQuotientChartedSpace

local instance capBallCarrierCharts :
    ChartedSpace (EuclideanHalfSpace 3) (capBallB d hs hI A hA hav).sphereCapCarrier.Carrier :=
  (capBallB d hs hI A hA hav).sphereCapQuotientChartedSpace

set_option backward.isDefEq.respectTransparency false in
def boundedPlugCapBallMap (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3)) :
    (capBallB d hs hI A hA hav).sphereCapCarrier.Carrier :=
  boundedPlugSideBallMap d hs hI A hA hav E h hlin i
    ((capBallB d hs hI A hA hav).capBallAmbientExtension i x)

include heq in
set_option backward.isDefEq.respectTransparency false in
private theorem boundedPlugCapBallMap_local (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ < 5 / 2) :
    IsLocalDiffeomorphAt (𝓡 3) (capBallB d hs hI A hA hav).sphereCapCarrier.model ∞
      (boundedPlugCapBallMap d hs hI A hA hav E h hlin i) x := by
  let B := capBallB d hs hI A hA hav
  have hr := (B.capBallAmbientExtension i).isLocalDiffeomorph x
  have hp := boundedPlugSideBallMap_local d hs hI A hA hav E h hlin heq i
    (B.capBallAmbientExtension i x) ((B.capBallAmbientExtension_norm i x).symm ▸ hx)
  exact hr.comp B.sphereCapCarrier.model B.sphereCapCarrier.Carrier hp

include heq in
set_option backward.isDefEq.respectTransparency false in
private theorem boundedPlugCapBallMap_injOn (i : Fin 2) :
    InjOn (boundedPlugCapBallMap d hs hI A hA hav E h hlin i)
      (Metric.ball 0 (5 / 2)) := by
  intro x hx y hy he
  let B := capBallB d hs hI A hA hav
  apply (B.capBallAmbientExtension i).injective
  apply boundedPlugSideBallMap_injOn d hs hI A hA hav E h hlin heq i
  · apply mem_ball_zero_iff.mpr
    exact (B.capBallAmbientExtension_norm i x).trans_lt (mem_ball_zero_iff.mp hx)
  · apply mem_ball_zero_iff.mpr
    exact (B.capBallAmbientExtension_norm i y).trans_lt (mem_ball_zero_iff.mp hy)
  · exact he

include heq in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_boundedPlugCapBallChart (i : Fin 2) :
    ∃ P : PartialDiffeomorph (𝓡 3) (capBallB d hs hI A hA hav).sphereCapCarrier.model
      (EuclideanSpace ℝ (Fin 3)) (capBallB d hs hI A hA hav).sphereCapCarrier.Carrier ∞,
      P.source = Metric.ball 0 (5 / 2) ∧
      P.target = boundedPlugCapBallMap d hs hI A hA hav E h hlin i ''
        Metric.ball 0 (5 / 2) ∧
      P.toFun = boundedPlugCapBallMap d hs hI A hA hav E h hlin i := by
  apply DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
  · intro x
    exact boundedPlugCapBallMap_local d hs hI A hA hav E h hlin heq i x.val
      (mem_ball_zero_iff.mp x.property)
  · exact isOpen_ball
  · exact ⟨0, by simp⟩
  · exact boundedPlugCapBallMap_injOn d hs hI A hA hav E h hlin heq i

set_option backward.isDefEq.respectTransparency false in
def boundedPlugCapBallChart (i : Fin 2) :
    PartialDiffeomorph (𝓡 3) (capBallB d hs hI A hA hav).sphereCapCarrier.model
      (EuclideanSpace ℝ (Fin 3)) (capBallB d hs hI A hA hav).sphereCapCarrier.Carrier ∞ :=
  (exists_boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).choose

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_source (i : Fin 2) :
    (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).source =
      Metric.ball 0 (5 / 2) :=
  (exists_boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).choose_spec.1

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_apply (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3)) :
    boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i x =
      boundedPlugCapBallMap d hs hI A hA hav E h hlin i x :=
  congrFun (exists_boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).choose_spec.2.2 x

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_closedTwo (i : Fin 2) :
    Metric.closedBall 0 2 ⊆ (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).source := by
  rw [boundedPlugCapBallChart_source]
  intro x hx
  rw [mem_ball_zero_iff]
  have hx' := mem_closedBall_zero_iff.mp hx
  linarith


set_option backward.isDefEq.respectTransparency false in
private def boundedPlugCapCellCorrection (i : Fin 2) :
    ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  let B := capBallB d hs hI A hA hav
  let D := B.sphereCapOrientationData.reparameterization i
  (D.trans boundedPlugCapBallDiffeomorph).trans D.symm

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallMap_cell (i : Fin 2) (x : ClosedCell 3) :
    boundedPlugCapBallMap d hs hI A hA hav E h hlin i x.val =
      (capBallB d hs hI A hA hav).sphereCapReparameterizedCap i
        (boundedPlugCapCellCorrection d hs hI A hA hav i x) := by
  let B := capBallB d hs hI A hA hav
  rw [boundedPlugCapBallMap, B.capBallAmbientExtension_cell,
    boundedPlugSideBallMap_cap _ _ _ _ _ _ _ _ _ _ _
      (B.sphereCapOrientationData.reparameterization i x).property]
  rw [B.boundedPlugWholeCap_eq]
  change B.sphereCapBall i _ = B.sphereCapBall i
    (B.sphereCapOrientationData.reparameterization i
      ((B.sphereCapOrientationData.reparameterization i).symm _))
  rw [Diffeomorph.apply_symm_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem boundedPlugCapCellCorrection_interior (i : Fin 2) (x : ClosedCell 3) :
    ‖(boundedPlugCapCellCorrection d hs hI A hA hav i x).val‖ < 1 ↔ ‖x.val‖ < 1 := by
  have hlocal := (boundedPlugCapCellCorrection d hs hI A hA hav i).isLocalDiffeomorph x
  have ht := hlocal.isInteriorPoint_iff (by simp)
  change x ∈ (𝓡∂ 3).interior (ClosedCell 3) ↔
    (boundedPlugCapCellCorrection d hs hI A hA hav i x) ∈
      (𝓡∂ 3).interior (ClosedCell 3) at ht
  rw [closedCell_interior_eq_ball] at ht
  exact ht.symm

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_closedUnit_image (i : Fin 2) :
    boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i '' Metric.closedBall 0 1 =
      range ((capBallB d hs hI A hA hav).sphereCapReparameterizedCap i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [boundedPlugCapBallChart_apply]
    exact ⟨boundedPlugCapCellCorrection d hs hI A hA hav i
      ⟨x, mem_closedBall_zero_iff.mp hx⟩,
      (boundedPlugCapBallMap_cell d hs hI A hA hav E h hlin i _).symm⟩
  · rintro ⟨x, rfl⟩
    let Q := boundedPlugCapCellCorrection d hs hI A hA hav i
    refine ⟨(Q.symm x).val, mem_closedBall_zero_iff.mpr (Q.symm x).property, ?_⟩
    rw [boundedPlugCapBallChart_apply, boundedPlugCapBallMap_cell]
    exact congrArg _ (Q.apply_symm_apply x)

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_openUnit_image (i : Fin 2) :
    boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i '' Metric.ball 0 1 =
      (capBallB d hs hI A hA hav).sphereCapReparameterizedCap i ''
        {x : ClosedCell 3 | ‖x.val‖ < 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let x' : ClosedCell 3 := ⟨x, (mem_ball_zero_iff.mp hx).le⟩
    refine ⟨boundedPlugCapCellCorrection d hs hI A hA hav i x', ?_, ?_⟩
    · exact (boundedPlugCapCellCorrection_interior d hs hI A hA hav i x').mpr
        (mem_ball_zero_iff.mp hx)
    · rw [boundedPlugCapBallChart_apply]
      exact (boundedPlugCapBallMap_cell d hs hI A hA hav E h hlin i x').symm
  · rintro ⟨x, hx, rfl⟩
    let Q := boundedPlugCapCellCorrection d hs hI A hA hav i
    refine ⟨(Q.symm x).val, ?_, ?_⟩
    · apply mem_ball_zero_iff.mpr
      apply (boundedPlugCapCellCorrection_interior d hs hI A hA hav i (Q.symm x)).mp
      change ‖(Q (Q.symm x)).val‖ < 1
      rw [Q.apply_symm_apply]
      exact hx
    · rw [boundedPlugCapBallChart_apply, boundedPlugCapBallMap_cell]
      exact congrArg _ (Q.apply_symm_apply x)

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_boundary (i : Fin 2) (z : ClosureSphere.{u}) :
    boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i z.down.val =
      (capBallB d hs hI A hA hav).sphereCapCore
        ((capBallB d hs hI A hA hav).sphereMap i
          ((capBallB d hs hI A hA hav).sphereCapOrientationData.attaching i z)) := by
  let B := capBallB d hs hI A hA hav
  rw [boundedPlugCapBallChart_apply, boundedPlugCapBallMap]
  have hv := B.capBallAmbientExtension_cell i (closureSphereToBall z)
  rw [B.sphereCapOrientationData.boundary] at hv
  change B.capBallAmbientExtension i z.down.val = _ at hv
  rw [hv, boundedPlugSideBallMap_cap _ _ _ _ _ _ _ _ _ _ _ (by
    exact (closureSphereToBall _).property), B.boundedPlugWholeCap_boundary]
  rfl


set_option backward.isDefEq.respectTransparency false in
private theorem boundedPlugCapBallMap_center (i : Fin 2) :
    (fun x : ClosedCell 3 => boundedPlugCapBallMap d hs hI A hA hav E h hlin i x.val) =ᶠ[
      𝓝 (⟨0, by simp⟩ : ClosedCell 3)]
        (capBallB d hs hI A hA hav).sphereCapReparameterizedCap i := by
  let B := capBallB d hs hI A hA hav
  let D := B.sphereCapOrientationData.reparameterization i
  have hD0 : (D (⟨0, by simp⟩ : ClosedCell 3)).val = 0 := by
    rw [← B.capBallAmbientExtension_cell, B.capBallAmbientExtension_zero]
  have ht : Tendsto (fun x : ClosedCell 3 => (D x).val)
      (𝓝 (⟨0, by simp⟩ : ClosedCell 3)) (𝓝 0) := by
    have hc : Continuous (fun x : ClosedCell 3 => (D x).val) :=
      continuous_subtype_val.comp D.continuous
    have ht := hc.tendsto (⟨0, by simp⟩ : ClosedCell 3)
    rw [hD0] at ht
    exact ht
  filter_upwards [boundedPlugCapRadialDiffeomorph_center.comp_tendsto ht] with x hx
  rw [boundedPlugCapBallMap, B.capBallAmbientExtension_cell,
    boundedPlugSideBallMap_cap _ _ _ _ _ _ _ _ _ _ _ (D x).property,
    B.boundedPlugWholeCap_eq]
  change B.sphereCapBall i (boundedPlugCapBallDiffeomorph (D x)) = B.sphereCapBall i (D x)
  apply congrArg (B.sphereCapBall i)
  apply Subtype.ext
  rw [boundedPlugCapBallDiffeomorph_apply]
  exact hx

include heq in
set_option backward.isDefEq.respectTransparency false in
private theorem boundedPlugCapBallChart_positive_zero (i : Fin 2) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv
        (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i)
        (show (0 : EuclideanSpace ℝ (Fin 3)) ∈
          (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).source by
            rw [boundedPlugCapBallChart_source]; simp)) sphereCapEuclideanOrientation =
      (capBallB d hs hI A hA hav).sphereCapCarrier.orientation.orientation
        (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i 0) := by
  let B := capBallB d hs hI A hA hav
  let P := boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i
  let x : ClosedCell 3 := ⟨0, by simp⟩
  have hx : (𝓡∂ 3).IsInteriorPoint x := by
    change x ∈ (𝓡∂ 3).interior (ClosedCell 3)
    rw [closedCell_interior_eq_ball]
    simp [x]
  obtain ⟨hi, hj, hp⟩ := B.sphereCapReparameterizedCap_positive i x hx
  have hzero : P 0 = B.sphereCapReparameterizedCap i x := by
    rw [boundedPlugCapBallChart_apply]
    exact (boundedPlugCapBallMap_center d hs hI A hA hav E h hlin i).eq_of_nhds
  have hcomp : mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x =
      (mfderiv (𝓡 3) B.sphereCapCarrier.model P 0).comp
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x) := by
    have he := (boundedPlugCapBallMap_center d hs hI A hA hav E h hlin i).mfderiv_eq
      (I := 𝓡∂ 3) (I' := 𝓡∂ 3)
    have hfun : (fun y : ClosedCell 3 => boundedPlugCapBallMap d hs hI A hA hav E h hlin i
        y.val) = P ∘ Subtype.val := by
      funext y
      exact (boundedPlugCapBallChart_apply d hs hI A hA hav E h hlin heq i y.val).symm
    rw [hfun] at he
    change mfderiv (𝓡∂ 3) (𝓡∂ 3) (P ∘ Subtype.val) x =
      mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x at he
    rw [← he]
    have hm : (0 : EuclideanSpace ℝ (Fin 3)) ∈ P.source := by
      rw [boundedPlugCapBallChart_source]
      simp
    have hP : MDifferentiableAt (𝓡 3) B.sphereCapCarrier.model P 0 :=
      (P.contMDiffOn.contMDiffAt (P.open_source.mem_nhds hm)).mdifferentiableAt (by simp)
    exact mfderiv_comp x hP
      ((isSmoothEmbedding_closedCell_inclusion 2).contMDiff.contMDiffAt.mdifferentiableAt
        (by simp))
  have hlin :
      (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
        (LinearEquiv.ofBijective
          (mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x).toLinearMap hj) =
      carrierSurgeryPatchTangentEquiv P
        (show (0 : EuclideanSpace ℝ (Fin 3)) ∈ P.source by
          rw [boundedPlugCapBallChart_source]; simp) := by
    ext v
    change mfderiv (𝓡∂ 3) (𝓡∂ 3) (B.sphereCapReparameterizedCap i) x
      ((LinearEquiv.ofBijective _ hi).symm v) = _
    rw [hcomp]
    change mfderiv (𝓡 3) B.sphereCapCarrier.model P 0
      ((LinearEquiv.ofBijective _ hi) ((LinearEquiv.ofBijective _ hi).symm v)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [hlin] at hp
  rw [hzero]
  exact hp

include heq in
set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_positive (i : Fin 2)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).source) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv
        (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i) hx)
      sphereCapEuclideanOrientation =
        (capBallB d hs hI A hA hav).sphereCapCarrier.orientation.orientation
          (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i x) := by
  let B := capBallB d hs hI A hA hav
  let P := boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i
  let U : Opens (EuclideanSpace ℝ (Fin 3)) := ⟨P.source, P.open_source⟩
  let f : U → B.sphereCapCarrier.Carrier := fun y => P y.val
  have hf : IsLocalDiffeomorph (𝓡 3) B.sphereCapCarrier.model ∞ f := by
    intro y
    exact ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) U
      ⟨y⟩).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (mem_univ y)).comp
        B.sphereCapCarrier.model B.sphereCapCarrier.Carrier
        (P.isLocalDiffeomorphAt (𝓡 3) B.sphereCapCarrier.model ∞ y.property)
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_compatibleOrientation (𝓡 3)
    (by simp) (fun y : EuclideanSpace ℝ (Fin 3) => sphereCapEuclideanOrientation)
    (DifferentialGeometry.Manifold.Orientation.isCompatibleOrientation_model
      sphereCapEuclideanOrientation)
  let OU := O.restrictOpen U
  have hconst := hf.orientation_agreement_isLocallyConstant OU B.sphereCapCarrier.orientation
  have hconnected : IsConnected (U : Set (EuclideanSpace ℝ (Fin 3))) := by
    change IsConnected P.source
    rw [boundedPlugCapBallChart_source]
    exact (convex_ball 0 (5 / 2)).isConnected ⟨0, by simp⟩
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnected
  let z : U := ⟨0, by change 0 ∈ P.source; rw [boundedPlugCapBallChart_source]; simp⟩
  have he (y : U) : ((hf y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv =
      carrierSurgeryPatchTangentEquiv P y.property := by
    ext v
    change mfderiv (𝓡 3) B.sphereCapCarrier.model f y v =
      mfderiv (𝓡 3) B.sphereCapCarrier.model P y.val v
    rw [DifferentialGeometry.mfderiv_restrict_open P U y]
    rfl
  have hz : Orientation.map (Fin 3)
      ((hf z).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv (OU.orientation z) =
        B.sphereCapCarrier.orientation.orientation (f z) := by
    rw [he, ManifoldOrientation.restrictOpen_orientation, hO]
    exact boundedPlugCapBallChart_positive_zero d hs hI A hA hav E h hlin heq i
  have hp := (hconst.apply_eq_of_preconnectedSpace ⟨x, hx⟩ z).mpr hz
  rw [he, ManifoldOrientation.restrictOpen_orientation, hO] at hp
  exact hp


set_option backward.isDefEq.respectTransparency false in
def boundedPlugCapBallChartData (i : Fin 2) :
    BallChart 3 (capBallB d hs hI A hA hav).sphereCapCarrier.model
      (capBallB d hs hI A hA hav).sphereCapCarrier.Carrier where
  chart := boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i
  closedBall_subset_source := boundedPlugCapBallChart_closedTwo d hs hI A hA hav E h hlin heq i

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugCapBallChart_target_interior (i : Fin 2) :
    (boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i).target ⊆
      (capBallB d hs hI A hA hav).sphereCapCarrier.interior := by
  let P := boundedPlugCapBallChart d hs hI A hA hav E h hlin heq i
  intro y hy
  have hl := P.isLocalDiffeomorphAt (𝓡 3)
    (capBallB d hs hI A hA hav).sphereCapCarrier.model ∞ (P.map_target hy)
  have hi := hl.isInteriorPoint_iff (by simp)
  have hx : (𝓡 3).IsInteriorPoint (P.symm y) := BoundarylessManifold.isInteriorPoint
  have ht := hi.mp hx
  rw [P.right_inv hy] at ht
  exact ht

end GC.GraphManifold
