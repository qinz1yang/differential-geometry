import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def isSphereTwoTimesCircleFactor (F : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ f : F.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle,
    f.preservesOrientation F.orientation sphereTwoTimesCircleOrientation

theorem isStandardFactor_of_isSphereTwoTimesCircleFactor
    {F : ConnectedClosedOrientedManifold.{u} 3} (h : isSphereTwoTimesCircleFactor F) :
    isStandardFactor F :=
  Or.inr h

theorem isSphereTwoTimesCircleFactor_of_orientedDiffeomorph
    {F F' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F'.toClosedOrientedManifold F.toClosedOrientedManifold))
    (hF : isSphereTwoTimesCircleFactor F) : isSphereTwoTimesCircleFactor F' := by
  obtain ⟨g⟩ := h
  obtain ⟨f, hf⟩ := hF
  exact ⟨g.1.trans f, Diffeomorph.preservesOrientation_trans g.2 hf⟩

theorem isSphereTwoTimesCircleFactor_iff_of_orientedDiffeomorph
    {F F' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F'.toClosedOrientedManifold F.toClosedOrientedManifold)) :
    isSphereTwoTimesCircleFactor F ↔ isSphereTwoTimesCircleFactor F' :=
  ⟨isSphereTwoTimesCircleFactor_of_orientedDiffeomorph h,
    isSphereTwoTimesCircleFactor_of_orientedDiffeomorph
      (h.map ClosedOrientedManifold.OrientedDiffeomorph.symm)⟩

namespace ClosedOrientedManifold

variable (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]

theorem isStandardConnectedSum_of_component (C : ConnectedComponents M.Carrier)
    (h : isStandardConnectedSum (M.component C).Carrier) : isStandardConnectedSum M.Carrier :=
  isStandardConnectedSum_of_diffeomorph (componentDiffeomorph M C) h

end ClosedOrientedManifold

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutIndices (C : ConnectedComponents M.Carrier) : Finset E.tubes.Index := by
  classical
  exact Finset.univ.filter fun a =>
    ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
      (E.tubes.tube a) z ∈ ClosedOrientedManifold.componentSet M C

local instance instLocallyConnectedQ : LocallyConnectedSpace Q.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

local instance instLocallyConnectedDiscarded : LocallyConnectedSpace E.discarded.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

local instance instLocallyConnectedCapped : LocallyConnectedSpace E.capped.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

def outgoingFactor : (Q.Carrier ⊕ E.discarded.Carrier) →
    ConnectedClosedOrientedManifold.{u} 3
  | Sum.inl q => Q.component (ConnectedComponents.mk q)
  | Sum.inr d => E.discarded.component (ConnectedComponents.mk d)

def associatedFactor (x : E.tubes.core) : ConnectedClosedOrientedManifold.{u} 3 :=
  E.outgoingFactor (E.presentation (E.capping.coreInclusion x))

theorem associatedFactor_eq_of_presentation_eq_inl (x : E.tubes.core) (q : Q.Carrier)
    (h : E.presentation (E.capping.coreInclusion x) = Sum.inl q) :
    E.associatedFactor x = Q.component (ConnectedComponents.mk q) := by
  rw [associatedFactor, h]
  rfl

theorem associatedFactor_eq_of_presentation_eq_inr (x : E.tubes.core) (d : E.discarded.Carrier)
    (h : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    E.associatedFactor x = E.discarded.component (ConnectedComponents.mk d) := by
  rw [associatedFactor, h]
  rfl

theorem associatedFactor_eq_of_mk_coreInclusion_eq (x x' : E.tubes.core)
    (h : ConnectedComponents.mk (E.capping.coreInclusion x) =
      ConnectedComponents.mk (E.capping.coreInclusion x')) :
    E.associatedFactor x = E.associatedFactor x' := by
  have hpres : ConnectedComponents.mk (E.presentation (E.capping.coreInclusion x)) =
      ConnectedComponents.mk (E.presentation (E.capping.coreInclusion x')) := by
    simpa only [Continuous.connectedComponentsMap_mk] using
      congrArg E.presentation.continuous.connectedComponentsMap h
  rcases hx : E.presentation (E.capping.coreInclusion x) with q | d
  · rcases hx' : E.presentation (E.capping.coreInclusion x') with q' | d'
    · rw [E.associatedFactor_eq_of_presentation_eq_inl x q hx,
        E.associatedFactor_eq_of_presentation_eq_inl x' q' hx']
      refine congrArg Q.component ?_
      have hsum : ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inl q') := by rw [← hx, ← hx']; exact hpres
      let retr : Q.Carrier ⊕ E.discarded.Carrier → Q.Carrier := Sum.elim id fun _ => q
      have hcont : Continuous retr := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
      simpa [retr] using congrArg hcont.connectedComponentsMap hsum
    · exfalso
      have hsum : ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inr d') := by rw [← hx, ← hx']; exact hpres
      have hmem : (Sum.inr d' : Q.Carrier ⊕ E.discarded.Carrier) ∈
          connectedComponent (Sum.inl q) := ConnectedComponents.coe_eq_coe'.mp hsum.symm
      have hsub := isPreconnected_connectedComponent.subset_isClopen
        (isClopen_range_inl (X := Q.Carrier) (Y := E.discarded.Carrier))
        ⟨Sum.inl q, mem_connectedComponent, ⟨q, rfl⟩⟩
      obtain ⟨y, hy⟩ := hsub hmem
      exact Sum.inl_ne_inr hy
  · rcases hx' : E.presentation (E.capping.coreInclusion x') with q' | d'
    · exfalso
      have hsum : ConnectedComponents.mk (Sum.inr d : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inl q') := by rw [← hx, ← hx']; exact hpres
      have hmem : (Sum.inl q' : Q.Carrier ⊕ E.discarded.Carrier) ∈
          connectedComponent (Sum.inr d) := ConnectedComponents.coe_eq_coe'.mp hsum.symm
      have hsub := isPreconnected_connectedComponent.subset_isClopen
        (isClopen_range_inr (X := Q.Carrier) (Y := E.discarded.Carrier))
        ⟨Sum.inr d, mem_connectedComponent, ⟨d, rfl⟩⟩
      obtain ⟨y, hy⟩ := hsub hmem
      exact Sum.inr_ne_inl hy
    · rw [E.associatedFactor_eq_of_presentation_eq_inr x d hx,
        E.associatedFactor_eq_of_presentation_eq_inr x' d' hx']
      refine congrArg E.discarded.component ?_
      have hsum : ConnectedComponents.mk (Sum.inr d : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inr d') := by rw [← hx, ← hx']; exact hpres
      let retr : Q.Carrier ⊕ E.discarded.Carrier → E.discarded.Carrier :=
        Sum.elim (fun _ => d) id
      have hcont : Continuous retr := continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩
      simpa [retr] using congrArg hcont.connectedComponentsMap hsum

def associatedFactors (C : ConnectedComponents M.Carrier) :
    Set (ConnectedClosedOrientedManifold.{u} 3) :=
  {N | ∃ x : E.tubes.core, ConnectedComponents.mk x.1 = C ∧ E.associatedFactor x = N}

def cappedCutComponents (C : ConnectedComponents M.Carrier) :
    Set (ConnectedComponents E.capped.Carrier) :=
  {D | ∃ x : E.tubes.core, ConnectedComponents.mk x.1 = C ∧
    ConnectedComponents.mk (E.capping.coreInclusion x) = D}

noncomputable def cappedFactor (C : ConnectedComponents M.Carrier)
    (D : E.cappedCutComponents C) : ConnectedClosedOrientedManifold.{u} 3 :=
  E.associatedFactor (Classical.choose D.2)

theorem cappedFactor_eq_of_mem (C : ConnectedComponents M.Carrier)
    (D : E.cappedCutComponents C) (x : E.tubes.core)
    (h : ConnectedComponents.mk (E.capping.coreInclusion x) = D.1) :
    E.cappedFactor C D = E.associatedFactor x :=
  E.associatedFactor_eq_of_mk_coreInclusion_eq (Classical.choose D.2) x
    ((Classical.choose_spec D.2).2.trans h.symm)

theorem associatedFactors_eq_range_cappedFactor (C : ConnectedComponents M.Carrier) :
    E.associatedFactors C = Set.range (E.cappedFactor C) := by
  ext N
  constructor
  · rintro ⟨x, hxC, rfl⟩
    exact ⟨⟨ConnectedComponents.mk (E.capping.coreInclusion x), x, hxC, rfl⟩,
      (E.cappedFactor_eq_of_mem C _ x rfl).trans rfl⟩
  · rintro ⟨D, rfl⟩
    exact ⟨Classical.choose D.2, (Classical.choose_spec D.2).1, rfl⟩

def CompleteEnumeration (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  L.Nodup ∧ (∀ F ∈ L, F ∈ E.associatedFactors C) ∧
    (∀ F ∈ E.associatedFactors C, F ∈ L)

def localReconstruction : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
      ∃ (b : ℕ) (K : List (ConnectedClosedOrientedManifold.{u} 3)),
        K.length = b ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        b + L.length = (E.cutIndices C).card + 1 ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

theorem associatedFactors_finite (C : ConnectedComponents M.Carrier) :
    (E.associatedFactors C).Finite := by
  classical
  refine (Set.finite_range fun s : ConnectedComponents Q.Carrier ⊕
      ConnectedComponents E.discarded.Carrier =>
      match s with
      | Sum.inl c => Q.component c
      | Sum.inr c => E.discarded.component c).subset ?_
  rintro N ⟨x, -, rfl⟩
  cases h : E.presentation (E.capping.coreInclusion x) with
  | inl q => exact ⟨Sum.inl (ConnectedComponents.mk q), by
      rw [associatedFactor, h]; rfl⟩
  | inr d => exact ⟨Sum.inr (ConnectedComponents.mk d), by
      rw [associatedFactor, h]; rfl⟩

theorem exists_completeEnumeration (C : ConnectedComponents M.Carrier) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), E.CompleteEnumeration C L := by
  classical
  obtain ⟨s, hs⟩ := (E.associatedFactors_finite C).exists_finset
  exact ⟨s.toList, s.nodup_toList, fun F hF => (hs F).mp (Finset.mem_toList.mp hF),
    fun F hF => Finset.mem_toList.mpr ((hs F).mpr hF)⟩


end SphericalCutCapTransition


end DifferentialGeometry.Topology
