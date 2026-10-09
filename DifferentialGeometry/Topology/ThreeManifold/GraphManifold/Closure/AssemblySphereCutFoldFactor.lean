import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutFoldMap
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSum

/-!
# Chapter-14 assembly, L2 COMPARE A6-c, part 3: the fold factor maps of the connected sum

Lane ASM-L2d. For a ball chart `β` of the closed model of the component of the cut sphere `j` whose
values on the closed ball of radius `2` are those of the shell chart precomposed with a linear
isometry `A`, `foldFactor β a` is the fold on the punctured model `β.Punctured`, with values in the
closed model `targetModel` of `W`:

* `foldFactor_injective`, `isLocalDiffeomorph_foldFactor` (on the interior of `β`),
  `foldFactor_radialMap` (the collar near the unit sphere: the seam collar at height `± a s`),
  `exists_foldFactor_orientation` (positivity at a point, closed-model orientations);
* `foldFactor_cross`, `foldFactor_cover`: for the left chart (`j = 0`, `A = id`) and the right chart
  (`j = 1`, `A = -id`), the two factor maps meet exactly along the antipodally attached boundary
  spheres and cover `W`;
* `foldCollarChart`: the seam collar at heights `(a/2) u`, the collar chart of the regularity lemma.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier] {S : SphereSeam W}
  {E : BoundaryTori W 0} (X : SphereCutCapped W S E)

/-- The closed oriented model (B0) of `W`. -/
abbrev targetModel : ConnectedClosedOrientedManifold.{u} 3 :=
  boundaryEmptyClosedModel W X.boundary_eq_empty

variable (DQ : X.Q.Components)
  (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
    (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅)

/-- **The fold factor map** on the punctured closed model of the component of the cut sphere `j`. -/
def foldFactor {j : Fin 2}
    (β : BallChart 3 (𝓡 3)
      (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier) (a : ℝ) :
    β.Punctured → X.targetModel.Carrier :=
  fun x => X.foldMap j a (Subtype.val x.val)

theorem foldFactor_apply {j : Fin 2}
    (β : BallChart 3 (𝓡 3)
      (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier) (a : ℝ)
    (x : β.Punctured) : X.foldFactor DQ hQ β a x = X.foldMap j a (Subtype.val x.val) := rfl

section Side

variable {DQ hQ} (h2 : DQ.count = 2) {j : Fin 2} {a : ℝ} (ha : 0 < a) (haμ : a ≤ X.shellSlope j)
  {β : BallChart 3 (𝓡 3)
    (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier}
  {A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)}
  (hβ : ∀ x ∈ Metric.closedBall 0 2,
    (Subtype.val (β.chart x) : X.Q.Carrier) = X.shellChart j (A x))

omit [ConnectedSpace W.Carrier] in
include hβ in
theorem val_notMem_ball (x : β.Punctured) :
    (Subtype.val x.val : X.Q.Carrier) ∉ X.shellChart j '' Metric.ball 0 1 := fun h =>
  x.property ((mem_chart_image_ball_iff_of_isometry hβ (by norm_num)).mpr h)

omit [ConnectedSpace W.Carrier] in
include hβ in
theorem val_notMem_closedBall (x : β.interior) :
    (Subtype.val x.val : X.Q.Carrier) ∉ X.shellChart j '' Metric.closedBall 0 1 := fun h =>
  x.property ((mem_chart_image_closedBall_iff_of_isometry hβ (by norm_num)).mpr h)

include h2 ha haμ hβ in
theorem foldFactor_injective : Injective (X.foldFactor DQ hQ β a) := by
  intro x x' he
  have h := X.foldMap_injOn j ha haμ DQ h2 ⟨(x.val).property, X.val_notMem_ball hβ x⟩
    ⟨(x'.val).property, X.val_notMem_ball hβ x'⟩ he
  exact Subtype.ext (Subtype.ext h)

include h2 ha haμ hβ in
/-- The fold factor map is a local diffeomorphism on the interior of `β`. -/
theorem isLocalDiffeomorph_foldFactor :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (X.foldFactor DQ hQ β a ∘ β.interiorToPunctured) := by
  intro x
  let p := X.spherePiece DQ (Fin.cast X.h2.symm j)
  let Qp := GC.Topology.componentCarrier X.Q DQ p
  let _ := boundaryEmptyChartedSpace Qp (hQ p)
  have _ := boundaryEmptyIsManifold Qp (hQ p)
  let bQ : (componentModel X.Q DQ hQ p).Carrier ≃ₘ⟮𝓡 3, X.Q.model⟯ DQ.piece p :=
    (boundaryEmptyDiffeomorph Qp (hQ p)).symm
  let bW := boundaryEmptyClosedDiffeomorph W X.boundary_eq_empty
  have h1 := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := 𝓡 3) β.interior x
  have h2' := bQ.isLocalDiffeomorph x.val
  have h3 := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := X.Q.model) (DQ.piece p)
    (bQ x.val)
  have h4 := X.isLocalDiffeomorphAt_foldMap j ha haμ DQ h2 (bQ x.val).property
    (X.val_notMem_closedBall hβ x)
  have h5 := bW.isLocalDiffeomorph (X.foldMap j a (Subtype.val (bQ x.val)))
  have hc := (((h1.comp _ _ h2').comp _ _ h3).comp _ _ h4).comp _ _ h5
  exact hc

include ha haμ hβ in
/-- Near the unit sphere of `β`, the fold factor map is the seam collar at the signed height
`± a s`. -/
theorem foldFactor_radialMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {s : ℝ}
    (hs : 0 ≤ s) (hlt : s < 1 / 4) (hr : 1 + s ∈ Icc (1 : ℝ) 2) :
    X.foldFactor DQ hQ β a (β.radialMap z (1 + s) hr) =
      S.collar (ULift.up ⟨A z, by simp⟩, sideSign j * (a * s)) := by
  rw [foldFactor_apply, radialMap_val_of_isometry hβ z (1 + s) hr]
  have h := X.foldMap_smul j ha haμ ⟨A z, by simp⟩ (r := 1 + s) (by linarith) (by linarith)
  rw [show 1 + s - 1 = s by ring, foldStretch_of_le a _ _ (by linarith)] at h
  exact h

include ha haμ hβ in
/-- On the boundary sphere of `β`, the fold factor map is the seam. -/
theorem foldFactor_boundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    X.foldFactor DQ hQ β a (β.boundaryMap z) = S.collar (ULift.up ⟨A z, by simp⟩, 0) := by
  rw [foldFactor_apply, boundaryMap_val_of_isometry hβ z]
  exact X.foldMap_unit j ha haμ ⟨A z, by simp⟩

include hβ in
/-- **Positivity of the fold factor map** at a point of the interior of `β` (closed-model
orientations). -/
theorem exists_foldFactor_orientation :
    ∃ x : β.interior, ∀ hs : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (X.foldFactor DQ hQ β a ∘ β.interiorToPunctured) x,
      Orientation.map (Fin 3) (hs.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        ((componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).orientation.orientation
          x.val) =
        X.targetModel.orientation.orientation
          (X.foldFactor DQ hQ β a (β.interiorToPunctured x)) := by
  obtain ⟨q, hq, hq32, hqy⟩ := X.exists_coreFold_point j DQ
  let x₀ : (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm j))).Carrier := ⟨q, hq⟩
  have hx₀ : x₀ ∈ β.interior := by
    intro h
    exact hq32 (image_mono (Metric.closedBall_subset_closedBall (by norm_num))
      ((mem_chart_image_closedBall_iff_of_isometry hβ (by norm_num)).mp h))
  refine ⟨⟨x₀, hx₀⟩, fun hs => ?_⟩
  have hcpt : IsCompact (X.shellChart j '' Metric.closedBall 0 (3 / 2)) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 / 2)).image_of_continuousOn
      ((X.shellChart j).contMDiffOn.continuousOn.mono
        ((Metric.closedBall_subset_closedBall (by norm_num)).trans
          (X.closedBall_subset_shellChart_source j)))
  have hcont : Continuous fun x' : β.interior => (Subtype.val x'.val : X.Q.Carrier) :=
    continuous_subtype_val.comp continuous_subtype_val
  have heq : (X.foldFactor DQ hQ β a ∘ β.interiorToPunctured) =ᶠ[𝓝 ⟨x₀, hx₀⟩]
      fun x' => X.coreFold (Subtype.val x'.val) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds
      (hcpt.isClosed.isOpen_compl.mem_nhds hq32)] with x' hx'
    exact X.foldMap_eq_coreFold j hx'
  exact X.orientation_map_of_eventuallyEq_coreFold X.boundary_eq_empty DQ hQ β _ _ hs heq hqy

end Side

section TwoSides

variable {DQ hQ} (h2 : DQ.count = 2) {a : ℝ} (ha : 0 < a) (ha0 : a ≤ X.shellSlope 0)
  (ha1 : a ≤ X.shellSlope 1)
  {βL : BallChart 3 (𝓡 3)
    (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 0))).Carrier}
  {βR : BallChart 3 (𝓡 3)
    (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 1))).Carrier}
  (hβL : ∀ x ∈ Metric.closedBall 0 2, (Subtype.val (βL.chart x) : X.Q.Carrier) =
    X.shellChart 0 (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)) x))
  (hβR : ∀ x ∈ Metric.closedBall 0 2, (Subtype.val (βR.chart x) : X.Q.Carrier) =
    X.shellChart 1 (LinearIsometryEquiv.neg ℝ x))

include h2 ha ha0 ha1 hβL hβR in
variable {X} in
/-- **The fold factor maps meet exactly along the antipodally attached boundary spheres.** -/
theorem foldFactor_cross {x : βL.Punctured} {y : βR.Punctured} :
    X.foldFactor DQ hQ βL a x = X.foldFactor DQ hQ βR a y ↔
      ∃ z, βL.boundaryMap z = x ∧ βR.boundaryMap (boundaryAttachment.1 z) = y := by
  refine (foldMap_cross (X := X) DQ h2 ha ha0 ha1 x.val.property
    (X.val_notMem_ball hβL x) y.val.property (X.val_notMem_ball hβR y)).trans ?_
  have hR : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (Subtype.val (βR.boundaryMap (boundaryAttachment.1 z)).val : X.Q.Carrier) =
        X.shellChart 1 (z : EuclideanSpace ℝ (Fin 3)) := by
    intro z
    rw [boundaryMap_val_of_isometry hβR]
    congr 1
    change -(-(z : EuclideanSpace ℝ (Fin 3))) = z
    rw [neg_neg]
  constructor
  · rintro ⟨z, hx, hy⟩
    refine ⟨z, Subtype.ext (Subtype.ext ?_), Subtype.ext (Subtype.ext ?_)⟩
    · rw [boundaryMap_val_of_isometry hβL z]
      exact hx.symm
    · rw [hR z]
      exact hy.symm
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z, boundaryMap_val_of_isometry hβL z, hR z⟩

include ha ha0 ha1 hβL hβR in
/-- **The fold factor maps cover `W`.** -/
theorem foldFactor_cover : ∀ w : X.targetModel.Carrier,
    (∃ x, X.foldFactor DQ hQ βL a x = w) ∨ ∃ x, X.foldFactor DQ hQ βR a x = w := by
  intro w
  rcases X.foldMap_cover DQ ha ha0 ha1 w with ⟨x, ⟨hx, hxb⟩, he⟩ | ⟨x, ⟨hx, hxb⟩, he⟩
  · exact Or.inl ⟨⟨⟨x, hx⟩, fun h =>
      hxb ((mem_chart_image_ball_iff_of_isometry hβL (by norm_num)).mp h)⟩, he⟩
  · exact Or.inr ⟨⟨⟨x, hx⟩, fun h =>
      hxb ((mem_chart_image_ball_iff_of_isometry hβR (by norm_num)).mp h)⟩, he⟩

end TwoSides

/-- The seam collar at heights `(a/2) u`, as a chart of the closed model of `W`: the collar chart of
the regularity lemma `connectedSumFoldCollar_isLocalDiffeomorph`. -/
def foldCollarChart (a : ℝ) (ha : 0 < a) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) X.targetModel.Carrier ∞ :=
  (((uliftDiffeomorph (I := 𝓡 2) (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      _ ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u}).prodCongr
    (shellAffine (a / 2) (a / 2) (by linarith))).toPartialDiffeomorph).trans
    (S.collar.trans (boundaryEmptyClosedDiffeomorph W X.boundary_eq_empty).toPartialDiffeomorph)

theorem foldCollarChart_apply {a : ℝ} (ha : 0 < a)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (u : ℝ) :
    X.foldCollarChart a ha (z, u) = S.collar (ULift.up z, a / 2 * u) := by
  change S.collar (ULift.up z, a / 2 + a / 2 * (u - 1)) = _
  congr 2
  ring

theorem mem_foldCollarChart_source {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {u : ℝ} (hu : |u| < 1 / 2) :
    (z, u) ∈ (X.foldCollarChart a ha).source := by
  refine ⟨mem_univ _, ?_, mem_univ _⟩
  change (ULift.up z, a / 2 + a / 2 * (u - 1)) ∈ S.collar.source
  rw [S.source_eq]
  refine ⟨mem_univ _, ?_⟩
  have h1 := abs_lt.mp hu
  constructor <;> nlinarith

section Collars

variable {DQ hQ} {a : ℝ} (ha : 0 < a) (ha0 : a ≤ X.shellSlope 0) (ha1 : a ≤ X.shellSlope 1)
  {βL : BallChart 3 (𝓡 3)
    (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 0))).Carrier}
  {βR : BallChart 3 (𝓡 3)
    (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 1))).Carrier}

include ha0 in
/-- The left collar formula of the regularity lemma, with the collar chart `foldCollarChart`. -/
theorem foldFactor_left_collar
    (hβL : ∀ x ∈ Metric.closedBall 0 2, (Subtype.val (βL.chart x) : X.Q.Carrier) =
      X.shellChart 0 (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)) x))
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (hs : 0 ≤ s) (hlt : s < 1 / 4) :
    X.foldFactor DQ hQ βL a (βL.radialMap z (1 + s) ⟨by linarith, by linarith⟩) =
      X.foldCollarChart a ha (Diffeomorph.refl (𝓡 2)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ z, 2 * s) := by
  refine (X.foldFactor_radialMap ha ha0 hβL z hs hlt _).trans
    (Eq.trans ?_ (X.foldCollarChart_apply ha _ _).symm)
  change S.collar (ULift.up z, sideSign 0 * (a * s)) = S.collar (ULift.up z, a / 2 * (2 * s))
  congr 2
  simp only [sideSign, Fin.val_zero, ite_true]
  ring

include ha1 in
/-- The right collar formula of the regularity lemma (antipodal angle). -/
theorem foldFactor_right_collar
    (hβR : ∀ x ∈ Metric.closedBall 0 2, (Subtype.val (βR.chart x) : X.Q.Carrier) =
      X.shellChart 1 (LinearIsometryEquiv.neg ℝ x))
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ) (hs : 0 ≤ s) (hlt : s < 1 / 4) :
    X.foldFactor DQ hQ βR a (βR.radialMap z (1 + s) ⟨by linarith, by linarith⟩) =
      X.foldCollarChart a ha (boundaryAttachment.1 z, -(2 * s)) := by
  refine (X.foldFactor_radialMap ha ha1 hβR z hs hlt _).trans
    (Eq.trans ?_ (X.foldCollarChart_apply ha _ _).symm)
  change S.collar (ULift.up ⟨-(z : EuclideanSpace ℝ (Fin 3)), _⟩, sideSign 1 * (a * s)) =
    S.collar (ULift.up (boundaryAttachment.1 z), a / 2 * -(2 * s))
  congr 2
  simp only [sideSign, Fin.val_one, one_ne_zero, ite_false]
  ring

end Collars

end SphereCutCapped

end GC.GraphManifold.Assembly
