import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutFoldFactor
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumSphereCollarRegularity
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumFixedFold
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Commutative

/-!
# Chapter-14 assembly, L2 COMPARE A6-c, part 4: the closed separating comparison

Lane ASM-L2d. **A6** (`compare_closedSeparating`, the frozen FC42 stub
`dry_L2_compare_closedSeparating`): for the cut of a connected carrier `W` without boundary tori along
a separating sphere seam whose two capped components are closed, the fixed connected sum of the
closed models (B0) of the two components is diffeomorphic to `W`.

Route (no Smale isotopy, no Thurston recognition, the fixed antipodal attachment):
* the left chart is the shell chart of the cut sphere `0`, the right chart the reflected shell chart
  of the cut sphere `1` (`exists_orientedComponentBallChart`); each is an oriented ball chart of its
  closed model or of the opposite model;
* the fold factor maps (`foldFactor`) satisfy the seven hypotheses of `connectedSumFoldDiffeomorph`
  (`foldFactor_cross`, `foldFactor_injective`, `foldFactor_cover`, `isLocalDiffeomorph_foldFactor`,
  and the collar `connectedSumFoldCollar_isLocalDiffeomorph` with `foldCollarChart`);
* signs `(+,+)`: `connectedSumFixedFoldDiffeomorph`; `(−,−)`: the fold diffeomorphism of the opposite
  models, the chart change `nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts` and the
  reflection `nonempty_diffeomorph_reflect`; mixed signs contradict the positivity of the factor
  maps (`false_of_connectedSumFold_mixed`);
* the order of the components: `connectedSumCommDiffeomorph`; the target: B0 of `W`.
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
  {E : BoundaryTori W 0} (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h2 : DQ.count = 2)
  (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
    (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅)

include h2 in
/-- **The closed comparison, components in the order of the cut spheres.** -/
theorem nonempty_diffeomorph_connectedSum_spherePieces :
    Nonempty ((connectedSum (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 0)))
        (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 1)))).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      X.targetModel.Carrier) := by
  let a := min (X.shellSlope 0) (X.shellSlope 1)
  have ha : 0 < a := lt_min (X.shellSlope_pos 0) (X.shellSlope_pos 1)
  have ha0 : a ≤ X.shellSlope 0 := min_le_left _ _
  have ha1 : a ≤ X.shellSlope 1 := min_le_right _ _
  have hal : a < 1 := lt_of_le_of_lt ha0
    (by linarith [X.shellBase_add_slope_lt_one 0, X.shellBase_pos 0])
  have hq : ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (s : ℝ), |s| < 2 * (1 / 4) →
      (z, s) ∈ (X.foldCollarChart a ha).source := fun z s hs =>
    X.mem_foldCollarChart_source ha hal z (by linarith)
  have hangle : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      boundaryAttachment.1 (boundaryAttachment.1 z) =
        Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ z :=
    fun z => boundaryAttachment_involutive z
  rcases X.exists_orientedComponentBallChart DQ hQ 0 (LinearIsometryEquiv.refl ℝ _) (Or.inl rfl)
    with ⟨cL, hcL⟩ | ⟨cL, hcL⟩ <;>
  rcases X.exists_orientedComponentBallChart DQ hQ 1 (LinearIsometryEquiv.neg ℝ) (Or.inr rfl)
    with ⟨cR, hcR⟩ | ⟨cR, hcR⟩
  · -- signs (+, +)
    have hsL := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha0 hcL
    have hsR := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha1 hcR
    have hsC := connectedSumFoldCollar_isLocalDiffeomorph _ _ X.targetModel cL cR boundaryAttachment
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (X.foldCollarChart a ha) _ _ hangle (1 / 4) (by norm_num) (by norm_num) hq
      (X.foldFactor_left_collar (hQ := hQ) ha ha0 hcL) (X.foldFactor_right_collar (hQ := hQ) ha ha1 hcR) hsL hsR
    exact ⟨(connectedSumFixedFoldDiffeomorph _ _ X.targetModel cL cR
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (fun _ _ => foldFactor_cross (X := X) (hQ := hQ) h2 ha ha0 ha1 hcL hcR) (X.foldFactor_injective (hQ := hQ) h2 ha ha0 hcL)
      (X.foldFactor_injective (hQ := hQ) h2 ha ha1 hcR) (X.foldFactor_cover (hQ := hQ) ha ha0 ha1 hcL hcR)
      hsL hsR hsC).symm⟩
  · -- signs (+, −): impossible
    exfalso
    have hsL := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha0 hcL
    have hsR := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha1 hcR
    have hsC := connectedSumFoldCollar_isLocalDiffeomorph _ _ X.targetModel cL cR boundaryAttachment
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (X.foldCollarChart a ha) _ _ hangle (1 / 4) (by norm_num) (by norm_num) hq
      (X.foldFactor_left_collar (hQ := hQ) ha ha0 hcL) (X.foldFactor_right_collar (hQ := hQ) ha ha1 hcR) hsL hsR
    obtain ⟨x, hx⟩ := X.exists_foldFactor_orientation (hQ := hQ) hcL
    obtain ⟨y, hy⟩ := X.exists_foldFactor_orientation (hQ := hQ) hcR
    exact false_of_connectedSumFold_mixed _ _ X.targetModel cL cR
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (fun _ _ => foldFactor_cross (X := X) (hQ := hQ) h2 ha ha0 ha1 hcL hcR) (X.foldFactor_injective (hQ := hQ) h2 ha ha0 hcL)
      (X.foldFactor_injective (hQ := hQ) h2 ha ha1 hcR) (X.foldFactor_cover (hQ := hQ) ha ha0 ha1 hcL hcR)
      hsL hsR hsC x (hx (hsL x)) y
      ((Orientation.map_neg (ι := Fin 3)
        ((hsR y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        ((componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 1))).orientation.orientation
          y.val)).trans (congrArg Neg.neg (hy (hsR y))))
  · -- signs (−, +): impossible
    exfalso
    have hsL := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha0 hcL
    have hsR := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha1 hcR
    have hsC := connectedSumFoldCollar_isLocalDiffeomorph _ _ X.targetModel.opposite cL cR
      boundaryAttachment
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (X.foldCollarChart a ha) _ _ hangle (1 / 4) (by norm_num) (by norm_num) hq
      (X.foldFactor_left_collar (hQ := hQ) ha ha0 hcL) (X.foldFactor_right_collar (hQ := hQ) ha ha1 hcR) hsL hsR
    obtain ⟨x, hx⟩ := X.exists_foldFactor_orientation (hQ := hQ) hcL
    obtain ⟨y, hy⟩ := X.exists_foldFactor_orientation (hQ := hQ) hcR
    exact false_of_connectedSumFold_mixed _ _ X.targetModel.opposite cL cR
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (fun _ _ => foldFactor_cross (X := X) (hQ := hQ) h2 ha ha0 ha1 hcL hcR) (X.foldFactor_injective (hQ := hQ) h2 ha ha0 hcL)
      (X.foldFactor_injective (hQ := hQ) h2 ha ha1 hcR) (X.foldFactor_cover (hQ := hQ) ha ha0 ha1 hcL hcR)
      hsL hsR hsC x
      ((Orientation.map_neg (ι := Fin 3)
        ((hsL x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        ((componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 0))).orientation.orientation
          x.val)).trans (congrArg Neg.neg (hx (hsL x)))) y
      ((hy (hsR y)).trans (neg_neg (X.targetModel.orientation.orientation
        (X.foldFactor DQ hQ cR.toBallChart a (cR.toBallChart.interiorToPunctured y)))).symm)
  · -- signs (−, −): the opposite models, a chart change and the reflection
    have hsL := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha0 hcL
    have hsR := X.isLocalDiffeomorph_foldFactor (hQ := hQ) h2 ha ha1 hcR
    have hsC := connectedSumFoldCollar_isLocalDiffeomorph _ _ X.targetModel cL cR boundaryAttachment
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (X.foldCollarChart a ha) _ _ hangle (1 / 4) (by norm_num) (by norm_num) hq
      (X.foldFactor_left_collar (hQ := hQ) ha ha0 hcL) (X.foldFactor_right_collar (hQ := hQ) ha ha1 hcR) hsL hsR
    let F := connectedSumFoldDiffeomorph _ _ X.targetModel cL cR boundaryAttachment
      (X.foldFactor DQ hQ cL.toBallChart a) (X.foldFactor DQ hQ cR.toBallChart a)
      (fun _ _ => foldFactor_cross (X := X) (hQ := hQ) h2 ha ha0 ha1 hcL hcR) (X.foldFactor_injective (hQ := hQ) h2 ha ha0 hcL)
      (X.foldFactor_injective (hQ := hQ) h2 ha ha1 hcR) (X.foldFactor_cover (hQ := hQ) ha ha0 ha1 hcL hcR)
      hsL hsR hsC
    obtain ⟨e₁⟩ := nonempty_diffeomorph_reflect
      (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 0)))
      (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 1)))
    obtain ⟨e₂⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
      (M := (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 0))).opposite)
      (N := (componentModel X.Q DQ hQ (X.spherePiece DQ (Fin.cast X.h2.symm 1))).opposite)
      (orientedBallChart (componentModel X.Q DQ hQ
        (X.spherePiece DQ (Fin.cast X.h2.symm 0)))).reflect cL
      (orientedBallChart (componentModel X.Q DQ hQ
        (X.spherePiece DQ (Fin.cast X.h2.symm 1)))).reflect cR boundaryAttachment
    exact ⟨(e₁.trans e₂.1).trans F⟩

omit [ConnectedSpace W.Carrier] in
theorem fin_cases_of_count_two {k : Fin DQ.count} :
    k = Fin.cast h2.symm 0 ∨ k = Fin.cast h2.symm 1 := by
  have := k.isLt
  rcases (by omega : k.val = 0 ∨ k.val = 1) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

end SphereCutCapped

/-- **A6 (closed half of COMPARE; FC42 dry stub `dry_L2_compare_closedSeparating`, verbatim).**
For a connected carrier `W` without boundary tori cut along a separating sphere seam whose two
capped components are closed, the fixed connected sum of the closed models (B0) of the two
components is diffeomorphic to `W`. -/
theorem compare_closedSeparating (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {E : BoundaryTori W 0}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h2 : DQ.count = 2)
    (hQ : ∀ i, (GC.Topology.componentCarrier X.Q DQ i).model.boundary
      (GC.Topology.componentCarrier X.Q DQ i).Carrier = ∅) :
    Nonempty ((connectedSum
        (@boundaryEmptyClosedModel (GC.Topology.componentCarrier X.Q DQ (Fin.cast h2.symm 0))
          (hQ _) (DQ.connected _))
        (@boundaryEmptyClosedModel (GC.Topology.componentCarrier X.Q DQ (Fin.cast h2.symm 1))
          (hQ _) (DQ.connected _))).Carrier ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) := by
  have key : ∀ p q : Fin DQ.count, X.spherePiece DQ (Fin.cast X.h2.symm 0) = p →
      X.spherePiece DQ (Fin.cast X.h2.symm 1) = q →
      Nonempty ((connectedSum (componentModel X.Q DQ hQ p) (componentModel X.Q DQ hQ q)).Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.targetModel.Carrier) := by
    rintro p q rfl rfl
    exact X.nonempty_diffeomorph_connectedSum_spherePieces DQ h2 hQ
  let bW := (boundaryEmptyClosedDiffeomorph W X.boundary_eq_empty).symm
  have hne := X.spherePiece_ne DQ h2
  rcases X.fin_cases_of_count_two DQ h2 (k := X.spherePiece DQ (Fin.cast X.h2.symm 0)) with h0 | h0
  · have h1 : X.spherePiece DQ (Fin.cast X.h2.symm 1) = Fin.cast h2.symm 1 := by
      rcases X.fin_cases_of_count_two DQ h2 (k := X.spherePiece DQ (Fin.cast X.h2.symm 1))
        with h1 | h1
      · exact (hne (h0.trans h1.symm)).elim
      · exact h1
    obtain ⟨F⟩ := key _ _ h0 h1
    exact ⟨F.trans bW⟩
  · have h1 : X.spherePiece DQ (Fin.cast X.h2.symm 1) = Fin.cast h2.symm 0 := by
      rcases X.fin_cases_of_count_two DQ h2 (k := X.spherePiece DQ (Fin.cast X.h2.symm 1))
        with h1 | h1
      · exact h1
      · exact (hne (h0.trans h1.symm)).elim
    obtain ⟨F⟩ := key _ _ h0 h1
    exact ⟨((connectedSumCommDiffeomorph _ _).trans F).trans bW⟩

end GC.GraphManifold.Assembly
