/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.TwoSheetSection
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LiftedImage

open Set unitInterval

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.complexity_lt_of_isPreconnected
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (hconn : IsPreconnected T.ambientComplex.space) : T.complexity < S.complexity := by
  apply lt_of_le_of_ne R.complexity_le
  intro heq
  obtain ⟨s, hs, hsection, -⟩ := R.exists_isPLHomeomorphOn_image_of_complexity_eq heq
  let _ : PreconnectedSpace T.ambientComplex.space := isPreconnected_iff_preconnectedSpace.mp hconn
  have hnonempty : S.manifoldComplex.space.Nonempty :=
    S.source_isPLBall.nonempty.image S.singularMap |>.mono
      S.singularMap_mapsTo_manifoldComplex.image_subset
  let _ : Nonempty S.manifoldComplex.space := hnonempty.to_subtype
  let p := R.projection_mapsTo.restrict R.projection T.ambientComplex.space S.manifoldComplex.space
  let e : S.manifoldComplex.space ≃ₜ derivedNeighborhoodSpace S.ambientComplex S.imageComplex :=
    Homeomorph.setCongr S.manifold_space
  let r := S.imageStrongDeformationRetract
  let j : C(S.manifoldComplex.space, S.imageComplex.space) :=
    ⟨fun x => ⟨((r.retraction (e x) :
      derivedNeighborhoodSpace S.ambientComplex S.imageComplex) : E),
      (r.retraction (e x)).2⟩,
      (((continuous_subtype_val.comp continuous_subtype_val).comp r.retraction.continuous).comp
        e.continuous).subtype_mk _⟩
  have hsmap : MapsTo s S.imageComplex.space T.ambientComplex.space :=
    fun x hx => space_mono_of_faces_subset T.image_faces_subset_ambient (hs.bijOn.mapsTo hx)
  let sj : C(S.imageComplex.space, T.ambientComplex.space) :=
    ⟨hsmap.restrict s S.imageComplex.space T.ambientComplex.space,
      hs.isPiecewiseAffineOn.continuousOn.mapsToRestrict hsmap⟩
  let s₀ := sj.comp j
  let H := (ContinuousMap.Homotopy.refl (⟨e.symm, e.symm.continuous⟩ : C(_, _))).comp
    (r.homotopy.toHomotopy.symm.compContinuousMap (⟨e, e.continuous⟩ : C(_, _)))
  have hend : (⟨e.symm, e.symm.continuous⟩ : C(_, _)).comp
      ((ContinuousMap.id _).comp (⟨e, e.continuous⟩ : C(_, _))) =
      ContinuousMap.id S.manifoldComplex.space := by
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  have hs₀ : ∀ x, p (s₀ x) =
      ((⟨e.symm, e.symm.continuous⟩ : C(_, _)).comp
        ((((ContinuousMap.id _).restrict _).comp r.retraction).comp
          (⟨e, e.continuous⟩ : C(_, _)))) x := by
    intro x
    apply Subtype.ext
    exact hsection (j x) (j x).2
  obtain ⟨u, hu⟩ := Covering.exists_continuous_section_of_homotopic_lift R.isCoveringMap
    (H.cast rfl hend) s₀ hs₀
  exact Covering.not_exists_continuous_section_of_fiber_card_two
    R.isCoveringMap R.fiber_card ⟨u, hu⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
