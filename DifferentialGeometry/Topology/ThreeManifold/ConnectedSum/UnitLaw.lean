import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set Function

namespace DifferentialGeometry.Topology

universe u

abbrev csE3 : Type := EuclideanSpace ℝ (Fin 3)

abbrev csS2 : Type := Metric.sphere (0 : csE3) 1

theorem finiteConnectedSum_singleton_unit (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum [M]).toClosedOrientedManifold M.toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl M.toClosedOrientedManifold⟩

theorem finiteConnectedSum_nil_unit :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3))).toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl standardThreeSphereLift.{u}.toClosedOrientedManifold⟩

theorem finiteConnectedSum_append_nil
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSum (L ++ []) = finiteConnectedSum L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L M _ => rw [List.append_assoc, List.append_nil]

namespace ConnectedSumUnit

variable {M : ConnectedClosedOrientedManifold.{u} 3}

abbrev BallImage (c : OrientedBallChart M.toClosedOrientedManifold) : Set M.Carrier :=
  c.toBallChart.chart '' Metric.closedBall (0 : csE3) 1

structure UnitFilling (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (a : BoundaryAttachment) where
  fill : d.toBallChart.Punctured ≃ₜ {x : M.Carrier // x ∈ BallImage c}
  map_boundary : ∀ z : csS2,
    fill (d.toBallChart.boundaryMap (a.1 z)) =
      ⟨c.toBallChart.chart z, ⟨z, Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]
        exact le_of_eq (by simpa only [Metric.mem_sphere, dist_zero_right] using z.2)),
        rfl⟩⟩

variable {c : OrientedBallChart M.toClosedOrientedManifold}
  {d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold}
  {a : BoundaryAttachment}

def quotientMap (F : UnitFilling c d a) :
    ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph → M.Carrier :=
  Quot.lift (Sum.elim (fun p : c.toBallChart.Punctured => (p : M.Carrier))
      (fun q : d.toBallChart.Punctured => (F.fill q : M.Carrier)))
    (by
      rintro u v ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (congrArg Subtype.val (F.map_boundary z)).symm
      · exact congrArg Subtype.val (F.map_boundary z))

theorem continuous_quotientMap (F : UnitFilling c d a) : Continuous (quotientMap F) :=
  continuous_adjunction_lift c.toBallChart.boundaryMap
    (d.toBallChart.boundaryMap ∘ a.1.toHomeomorph)
    (by
      rintro u v ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (congrArg Subtype.val (F.map_boundary z)).symm
      · exact congrArg Subtype.val (F.map_boundary z))
    (Continuous.sumElim continuous_subtype_val (continuous_subtype_val.comp F.fill.continuous))

theorem quotientMap_injective (F : UnitFilling c d a) : Function.Injective (quotientMap F) := by
  intro x y hxy
  rcases ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph x with
    ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rcases ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph y with
      ⟨p', rfl⟩ | ⟨q', rfl⟩
    · exact congrArg (ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph)
        (Subtype.ext hxy)
    · have hval : (p : M.Carrier) = (F.fill q' : M.Carrier) := hxy
      have hmem : (p : M.Carrier) ∈ BallImage c := by
        rw [hval]
        exact (F.fill q').2
      rw [BallImage] at hmem
      obtain ⟨w, hw, hwval⟩ := hmem
      have hpnot : (p : M.Carrier) ∉ c.toBallChart.chart '' Metric.ball (0 : csE3) 1 := p.2
      have hnorm : ‖w‖ = 1 := by
        have hle : dist w (0 : csE3) ≤ 1 := Metric.mem_closedBall.mp hw
        have hnle : ¬ dist w (0 : csE3) < 1 := by
          intro hlt
          exact hpnot ⟨w, hlt, hwval⟩
        rw [dist_zero_right] at hle hnle
        exact le_antisymm hle (le_of_not_gt hnle)
      have hdist : dist w (0 : csE3) = 1 := by
        rw [dist_zero_right]; exact hnorm
      have hz : (p : M.Carrier) = c.toBallChart.boundaryMap ⟨w, hdist⟩ := by
        rw [← hwval]
        rfl
      have hFq : F.fill q' = ⟨c.toBallChart.boundaryMap ⟨w, hdist⟩,
          ⟨w, Metric.mem_closedBall.mpr (le_of_eq hdist), rfl⟩⟩ := by
        refine Subtype.ext ?_
        rw [← hval, hz]
      have hq' : q' = d.toBallChart.boundaryMap (a.1 ⟨w, hdist⟩) := by
        refine F.fill.injective ?_
        exact hFq.trans (F.map_boundary ⟨w, hdist⟩).symm
      have hp : p = c.toBallChart.boundaryMap ⟨w, hdist⟩ := Subtype.ext hz
      rw [hq', hp]
      exact ConnectedSumQuotient.boundary_eq c.toBallChart d.toBallChart a.1.toHomeomorph
        ⟨w, hdist⟩
  · rcases ConnectedSumQuotient.jointly_surjective c.toBallChart d.toBallChart a.1.toHomeomorph y with
      ⟨p', rfl⟩ | ⟨q', rfl⟩
    · have hval : (F.fill q : M.Carrier) = (p' : M.Carrier) := hxy
      have hmem : (p' : M.Carrier) ∈ BallImage c := by
        rw [← hval]
        exact (F.fill q).2
      rw [BallImage] at hmem
      obtain ⟨w, hw, hwval⟩ := hmem
      have hpnot : (p' : M.Carrier) ∉ c.toBallChart.chart '' Metric.ball (0 : csE3) 1 := p'.2
      have hnorm : ‖w‖ = 1 := by
        have hle : dist w (0 : csE3) ≤ 1 := Metric.mem_closedBall.mp hw
        have hnle : ¬ dist w (0 : csE3) < 1 := by
          intro hlt
          exact hpnot ⟨w, hlt, hwval⟩
        rw [dist_zero_right] at hle hnle
        exact le_antisymm hle (le_of_not_gt hnle)
      have hdist : dist w (0 : csE3) = 1 := by
        rw [dist_zero_right]; exact hnorm
      have hz : (p' : M.Carrier) = c.toBallChart.boundaryMap ⟨w, hdist⟩ := by
        rw [← hwval]
        rfl
      have hFq : F.fill q = ⟨c.toBallChart.boundaryMap ⟨w, hdist⟩,
          ⟨w, Metric.mem_closedBall.mpr (le_of_eq hdist), rfl⟩⟩ := by
        refine Subtype.ext ?_
        rw [hval, hz]
      have hq : q = d.toBallChart.boundaryMap (a.1 ⟨w, hdist⟩) := by
        refine F.fill.injective ?_
        exact hFq.trans (F.map_boundary ⟨w, hdist⟩).symm
      have hp : p' = c.toBallChart.boundaryMap ⟨w, hdist⟩ := Subtype.ext hz
      rw [hq, hp]
      exact (ConnectedSumQuotient.boundary_eq c.toBallChart d.toBallChart a.1.toHomeomorph
        ⟨w, hdist⟩).symm
    · exact congrArg (ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph)
        (F.fill.injective (Subtype.ext hxy))

theorem quotientMap_surjective (F : UnitFilling c d a) : Function.Surjective (quotientMap F) := by
  intro y
  by_cases hy : y ∈ c.toBallChart.chart '' Metric.ball (0 : csE3) 1
  · obtain ⟨w, hw, hwval⟩ := hy
    have hmem : y ∈ BallImage c := ⟨w, Metric.ball_subset_closedBall hw, hwval⟩
    refine ⟨ConnectedSumQuotient.inr c.toBallChart d.toBallChart a.1.toHomeomorph
      (F.fill.symm ⟨y, hmem⟩), ?_⟩
    change (F.fill (F.fill.symm ⟨y, hmem⟩) : M.Carrier) = y
    rw [F.fill.apply_symm_apply]
  · refine ⟨ConnectedSumQuotient.inl c.toBallChart d.toBallChart a.1.toHomeomorph
      ⟨y, hy⟩, rfl⟩

theorem quotientMap_bijective (F : UnitFilling c d a) : Function.Bijective (quotientMap F) :=
  ⟨quotientMap_injective F, quotientMap_surjective F⟩

def quotientEquiv (F : UnitFilling c d a) :
    ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ M.Carrier :=
  Equiv.ofBijective (quotientMap F) (quotientMap_bijective F)

theorem homeomorph_of_unitFilling (F : UnitFilling c d a) :
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₜ M.Carrier) :=
  ⟨Continuous.homeoOfEquivCompactToT2 (f := quotientEquiv F) (continuous_quotientMap F)⟩

def BallComplementCollar (F : UnitFilling c d a) : Prop :=
  ∀ (z : csS2) (p : ConnectedSumQuotient.K), (p.2 : ℝ) < 0 →
    (F.fill (ConnectedSumQuotient.radialRightClamp d.toBallChart z p) : M.Carrier) =
      c.toBallChart.chart ((1 + (p.2 : ℝ)) • p.1)

theorem quotientMap_collarMap (F : UnitFilling c d a) (hcollar : BallComplementCollar F)
    (p : ConnectedSumQuotient.K) :
    quotientMap F (ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 p) =
      c.toBallChart.chart (ConnectedSumQuotient.rad p) := by
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [ConnectedSumQuotient.collarMap_of_nonneg c.toBallChart d.toBallChart a.1 p ht]
    rfl
  · rw [ConnectedSumQuotient.collarMap_eq_if]
    simp only [if_neg (not_le.mpr (lt_of_not_ge ht)), ConnectedSumQuotient.collarRight]
    exact hcollar (a.1 p.1) p (lt_of_not_ge ht)

def BallComplementSmooth (F : UnitFilling c d a) : Prop :=
  IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (fun x : d.toBallChart.interior => (F.fill (d.toBallChart.interiorToPunctured x) : M.Carrier))

def BallComplementOrientation (F : UnitFilling c d a) (h : BallComplementSmooth F) : Prop :=
  ∀ x : d.toBallChart.interior,
    Orientation.map (Fin 3)
      ((h x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (standardThreeSphereLift.{u}.orientation.orientation x.1) =
    M.orientation.orientation (F.fill (d.toBallChart.interiorToPunctured x))

end ConnectedSumUnit

end DifferentialGeometry.Topology
