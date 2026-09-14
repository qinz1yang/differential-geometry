import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentGluingReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapCutSphericalGraphSumRealization

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace ClosedOrientedManifold

def componentSeparated (X : ClosedOrientedManifold.{u} 3) : Prop :=
  Function.Injective X.component

theorem componentSeparated_of_preconnected (X : ClosedOrientedManifold.{u} 3)
    [PreconnectedSpace X.Carrier] : componentSeparated X :=
  fun _ _ _ => Subsingleton.elim _ _

theorem componentSeparated_of_subtype_cast_val_eq (X : ClosedOrientedManifold.{u} 3)
    (h : ∀ (s t : Set X.Carrier) (H : (↥s : Type u) = ↥t) (x : ↥s),
      ((cast H x : ↥t) : X.Carrier) = x) :
    componentSeparated X := by
  intro c c' hcc
  have hC : (↥(componentSet X c) : Type u) = ↥(componentSet X c') :=
    congrArg (fun Y : ConnectedClosedOrientedManifold.{u} 3 => Y.Carrier) hcc
  have hset : componentSet X c = componentSet X c' := by
    refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hmem : ((cast hC ⟨x, hx⟩ : ↥(componentSet X c')) : X.Carrier) ∈
          componentSet X c' := (cast hC ⟨x, hx⟩).2
      rwa [h _ _ hC ⟨x, hx⟩] at hmem
    · have hmem : ((cast hC.symm ⟨x, hx⟩ : ↥(componentSet X c)) : X.Carrier) ∈
          componentSet X c := (cast hC.symm ⟨x, hx⟩).2
      rwa [h _ _ hC.symm ⟨x, hx⟩] at hmem
  obtain ⟨x, hx⟩ := componentSet_nonempty X c
  have hx' : x ∈ componentSet X c' := hset ▸ hx
  exact ((mem_componentSet X c x).mp hx).symm.trans ((mem_componentSet X c' x).mp hx')

end ClosedOrientedManifold

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

noncomputable def cappedCutPieceSummands (C : ConnectedComponents M.Carrier) :
    List (ConnectedClosedOrientedManifold.{u} 3) :=
  (E.cappedCutPieceEnumeration C).map fun D => E.capped.component D.1

theorem mem_cappedCutPieceSummands_iff (C : ConnectedComponents M.Carrier)
    (N : ConnectedClosedOrientedManifold.{u} 3) :
    N ∈ E.cappedCutPieceSummands C ↔
      ∃ D : E.cappedCutComponents C, E.capped.component D.1 = N := by
  rw [cappedCutPieceSummands, List.mem_map]
  exact ⟨fun ⟨D, _, hD⟩ => ⟨D, hD⟩,
    fun ⟨D, hD⟩ => ⟨D, E.mem_cappedCutPieceEnumeration C D, hD⟩⟩

theorem exists_orientedDiffeomorph_cappedCutPiece_cappedFactor
    (C : ConnectedComponents M.Carrier) (D : E.cappedCutComponents C) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (E.capped.component D.1).toClosedOrientedManifold
      (E.cappedFactor C D).toClosedOrientedManifold) := by
  have hD := (Classical.choose_spec D.2).2
  have h := E.cappedPresentationRealization (Classical.choose D.2)
  rwa [hD] at h

theorem exists_orientedDiffeomorph_cappedCutPiece_of_presentation_eq_inl
    (C : ConnectedComponents M.Carrier) (D : E.cappedCutComponents C) (x : E.tubes.core)
    (hxD : ConnectedComponents.mk (E.capping.coreInclusion x) = D.1) (q : Q.Carrier)
    (hq : E.presentation (E.capping.coreInclusion x) = Sum.inl q) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (E.capped.component D.1).toClosedOrientedManifold
      (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold) := by
  obtain ⟨ρ⟩ := E.cappedRetainedPresentationRealization x q hq
  rw [hxD] at ρ
  exact ⟨ρ⟩

theorem exists_orientedDiffeomorph_cappedCutPiece_of_presentation_eq_inr
    (C : ConnectedComponents M.Carrier) (D : E.cappedCutComponents C) (x : E.tubes.core)
    (hxD : ConnectedComponents.mk (E.capping.coreInclusion x) = D.1) (d : E.discarded.Carrier)
    (hd : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (E.capped.component D.1).toClosedOrientedManifold
      (E.discarded.component (ConnectedComponents.mk d)).toClosedOrientedManifold) := by
  obtain ⟨ρ⟩ := E.cappedDiscardedPresentationRealization x d hd
  rw [hxD] at ρ
  exact ⟨ρ⟩

private theorem forall₂_map_map_of {α β : Type*} (R : β → β → Prop) (f g : α → β) :
    ∀ l : List α, (∀ a, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | a :: l, h => List.Forall₂.cons (h a) (forall₂_map_map_of R f g l h)

private theorem forall₂_append {β : Type*} {R : β → β → Prop} :
    ∀ {l₁ l₂ l₃ l₄ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | _, _, _, _, List.Forall₂.nil, h₂ => h₂
  | _, _, _, _, List.Forall₂.cons ha ht, h₂ => List.Forall₂.cons ha (forall₂_append ht h₂)

private theorem forall₂_self {β : Type*} {R : β → β → Prop} (h : ∀ a, R a a) :
    ∀ l : List β, List.Forall₂ R l l
  | [] => List.Forall₂.nil
  | a :: l => List.Forall₂.cons (h a) (forall₂_self h l)

theorem forall₂_cappedCutPieceSummands_cappedCutPieceFactors
    (C : ConnectedComponents M.Carrier) :
    List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        A.toClosedOrientedManifold B.toClosedOrientedManifold))
      (E.cappedCutPieceSummands C) (E.cappedCutPieceFactors C) :=
  forall₂_map_map_of _ _ _
    (E.cappedCutPieceEnumeration C) fun D =>
      E.exists_orientedDiffeomorph_cappedCutPiece_cappedFactor C D

theorem exists_orientedDiffeomorph_finiteConnectedSum_cappedCutPieceSummands
    (C : ConnectedComponents M.Carrier) (K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.cappedCutPieceSummands C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.cappedCutPieceFactors C ++ K)).toClosedOrientedManifold) :=
  finiteConnectedSum_congr
    (forall₂_append (E.forall₂_cappedCutPieceSummands_cappedCutPieceFactors C)
      (forall₂_self (fun A =>
        ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl A.toClosedOrientedManifold⟩) K))

def cutComponentPieceAssembly (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ → ∃ b : ℕ,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.cappedCutPieceSummands C ++
        List.replicate b S)).toClosedOrientedManifold)

theorem cutComponentPieceAssembly_of_cutComponentPieceGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.cutComponentPieceGluing S) :
    E.cutComponentPieceAssembly S := by
  intro C hC
  obtain ⟨b, ⟨ρ⟩⟩ := h C hC
  obtain ⟨σ⟩ := E.exists_orientedDiffeomorph_finiteConnectedSum_cappedCutPieceSummands C
    (List.replicate b S)
  exact ⟨b, ⟨ρ.trans σ.symm⟩⟩

theorem cutComponentPieceGluing_of_cutComponentPieceAssembly
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.cutComponentPieceAssembly S) :
    E.cutComponentPieceGluing S := by
  intro C hC
  obtain ⟨b, ⟨ρ⟩⟩ := h C hC
  obtain ⟨σ⟩ := E.exists_orientedDiffeomorph_finiteConnectedSum_cappedCutPieceSummands C
    (List.replicate b S)
  exact ⟨b, ⟨ρ.trans σ⟩⟩

theorem cutComponentPieceAssembly_iff_cutComponentPieceGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.cutComponentPieceAssembly S ↔ E.cutComponentPieceGluing S :=
  ⟨E.cutComponentPieceGluing_of_cutComponentPieceAssembly S,
    E.cutComponentPieceAssembly_of_cutComponentPieceGluing S⟩

theorem sphericalSummandCompletion_of_cutComponentPieceAssembly
    (S : ConnectedClosedOrientedManifold.{u} 3) (C : ConnectedComponents M.Carrier)
    (hinj : Function.Injective (E.cappedFactor C)) (hC : E.cutIndices C ≠ ∅)
    (h : E.cutComponentPieceAssembly S) : ∃ b : ℕ,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++
          List.replicate b S)).toClosedOrientedManifold) :=
  E.sphericalSummandCompletion_of_cutComponentPieceGluing S C hinj hC
    ((E.cutComponentPieceAssembly_iff_cutComponentPieceGluing S).mp h)

theorem cutComponentPieceAssembly_iff_sphericalSummandCompletion
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C)) :
    E.cutComponentPieceAssembly S ↔ E.sphericalSummandCompletion S :=
  (E.cutComponentPieceAssembly_iff_cutComponentPieceGluing S).trans
    (E.sphericalSummandCompletion_iff_cutComponentPieceGluing S hinj).symm

theorem cutComponentPieceAssembly_of_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (h : E.cutSphericalGraphSumRealization S) : E.cutComponentPieceAssembly S :=
  (E.cutComponentPieceAssembly_iff_cutComponentPieceGluing S).mpr
    (E.cutComponentPieceGluing_of_cutSphericalGraphSumRealization S hinj h)

theorem cutSphericalGraphSumRealization_of_cutComponentPieceAssembly_of_exponentDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (h : E.cutComponentPieceAssembly S) (hdet : E.sphericalSummandExponentDetermined S) :
    E.cutSphericalGraphSumRealization S :=
  E.cutSphericalGraphSumRealization_of_cutComponentPieceGluing_of_exponentDetermined S hinj
    ((E.cutComponentPieceAssembly_iff_cutComponentPieceGluing S).mp h) hdet

theorem cutComponentPieceAssembly_of_forall_cutIndices_eq_empty
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutComponentPieceAssembly S :=
  fun C hC => absurd (h C) hC

theorem cutComponentPieceAssembly_of_isEmpty_index [IsEmpty E.tubes.Index]
    (S : ConnectedClosedOrientedManifold.{u} 3) : E.cutComponentPieceAssembly S :=
  E.cutComponentPieceAssembly_of_forall_cutIndices_eq_empty S
    fun C => E.cutIndices_eq_empty_of_isEmpty_index C

theorem cutComponentPieceAssembly_iff_of_orientedDiffeomorph
    {S S' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      S.toClosedOrientedManifold S'.toClosedOrientedManifold)) :
    E.cutComponentPieceAssembly S ↔ E.cutComponentPieceAssembly S' :=
  (E.cutComponentPieceAssembly_iff_cutComponentPieceGluing S).trans
    ((E.cutComponentPieceGluing_iff_of_orientedDiffeomorph h).trans
      (E.cutComponentPieceAssembly_iff_cutComponentPieceGluing S').symm)

theorem subsingleton_cappedCutComponents_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    Subsingleton (E.cappedCutComponents C) := by
  refine ⟨fun D D' => ?_⟩
  have hspec : ConnectedComponents.mk ((Classical.choose D.2 : E.tubes.core) : M.Carrier) = C ∧
      ConnectedComponents.mk (E.capping.coreInclusion (Classical.choose D.2)) = D.1 :=
    Classical.choose_spec D.2
  have hspec' : ConnectedComponents.mk ((Classical.choose D'.2 : E.tubes.core) : M.Carrier) = C ∧
      ConnectedComponents.mk (E.capping.coreInclusion (Classical.choose D'.2)) = D'.1 :=
    Classical.choose_spec D'.2
  refine Subtype.ext ?_
  rw [← hspec.2, ← hspec'.2]
  have himg := E.image_coreComponentSet_eq_componentSet C hC
    (x := Classical.choose D.2) hspec.1
  have hmem : E.capping.coreInclusion (Classical.choose D'.2) ∈
      E.capping.coreInclusion '' E.coreComponentSet C :=
    ⟨Classical.choose D'.2, hspec'.1, rfl⟩
  rw [himg, ClosedOrientedManifold.mem_componentSet] at hmem
  exact hmem.symm

theorem injective_cappedFactor_of_subsingleton
    (C : ConnectedComponents M.Carrier) [Subsingleton (E.cappedCutComponents C)] :
    Function.Injective (E.cappedFactor C) := by
  intro A B _
  exact Subsingleton.elim A B

theorem injective_cappedFactor_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    Function.Injective (E.cappedFactor C) :=
  fun A B _ => (E.subsingleton_cappedCutComponents_of_cutIndices_eq_empty C hC).elim A B

def summandSidesSeparated : Prop :=
  ∀ (c : ConnectedComponents Q.Carrier) (c' : ConnectedComponents E.discarded.Carrier),
    Q.component c ≠ E.discarded.component c'

theorem injective_cappedFactor_of_componentSeparated_of_sidesSeparated
    (hQ : ClosedOrientedManifold.componentSeparated Q)
    (hD : ClosedOrientedManifold.componentSeparated E.discarded)
    (hside : E.summandSidesSeparated) (C : ConnectedComponents M.Carrier) :
    Function.Injective (E.cappedFactor C) := by
  have key : ∀ (p p' : E.tubes.core),
      E.outgoingFactor (E.presentation (E.capping.coreInclusion p)) =
        E.outgoingFactor (E.presentation (E.capping.coreInclusion p')) →
      ConnectedComponents.mk (E.presentation (E.capping.coreInclusion p)) =
        ConnectedComponents.mk (E.presentation (E.capping.coreInclusion p')) := by
    intro p p' hfac
    rcases hp : E.presentation (E.capping.coreInclusion p) with q | d
    · rcases hp' : E.presentation (E.capping.coreInclusion p') with q' | d'
      · have hq : ConnectedComponents.mk q = ConnectedComponents.mk q' := by
          rw [hp, hp'] at hfac
          exact hQ hfac
        exact congrArg (Continuous.connectedComponentsMap continuous_inl) hq
      · rw [hp, hp'] at hfac
        exact absurd hfac (hside _ _)
    · rcases hp' : E.presentation (E.capping.coreInclusion p') with q' | d'
      · rw [hp, hp'] at hfac
        exact absurd hfac.symm (hside _ _)
      · have hq : ConnectedComponents.mk d = ConnectedComponents.mk d' := by
          rw [hp, hp'] at hfac
          exact hD hfac
        exact congrArg (Continuous.connectedComponentsMap continuous_inr) hq
  intro D D' hfac
  have hx := (Classical.choose_spec D.2).2
  have hx' := (Classical.choose_spec D'.2).2
  refine E.cappedCutOutputComponent_injective C ?_
  change E.presentation.continuous.connectedComponentsMap D.1 =
    E.presentation.continuous.connectedComponentsMap D'.1
  rw [← hx, ← hx', Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk]
  exact key _ _ hfac

noncomputable def cappedCutPieceFactorSet (C : ConnectedComponents M.Carrier) :
    Finset (ConnectedClosedOrientedManifold.{u} 3) := by
  classical
  exact (E.cappedCutPieceFactors C).toFinset

theorem mem_cappedCutPieceFactorSet_iff (C : ConnectedComponents M.Carrier)
    (F : ConnectedClosedOrientedManifold.{u} 3) :
    F ∈ E.cappedCutPieceFactorSet C ↔ F ∈ E.associatedFactors C := by
  classical
  have h : E.cappedCutPieceFactorSet C = (E.cappedCutPieceFactors C).toFinset := rfl
  rw [h, List.mem_toFinset, E.mem_cappedCutPieceFactors_iff]

theorem card_cappedCutPieceFactorSet (C : ConnectedComponents M.Carrier) :
    (E.cappedCutPieceFactorSet C).card = (E.associatedFactors C).ncard := by
  classical
  have h : E.cappedCutPieceFactorSet C = (E.associatedFactors_finite C).toFinset := by
    ext F
    rw [E.mem_cappedCutPieceFactorSet_iff, Set.Finite.mem_toFinset]
  rw [h, Set.ncard_eq_toFinset_card _ (E.associatedFactors_finite C)]

theorem incidenceCycleRank_add_card_cappedCutPieceFactorSet
    (C : ConnectedComponents M.Carrier) :
    E.incidenceCycleRank C + (E.cappedCutPieceFactorSet C).card = (E.cutIndices C).card + 1 := by
  rw [E.card_cappedCutPieceFactorSet C, E.incidenceCycleRank_add_ncard_associatedFactors C]

noncomputable def cappedCutPieceFactorList (C : ConnectedComponents M.Carrier) :
    List (ConnectedClosedOrientedManifold.{u} 3) := by
  classical
  exact (E.cappedCutPieceFactorSet C).toList

theorem nodup_cappedCutPieceFactorList (C : ConnectedComponents M.Carrier) :
    (E.cappedCutPieceFactorList C).Nodup := by
  classical
  rw [cappedCutPieceFactorList]
  exact (E.cappedCutPieceFactorSet C).nodup_toList

theorem mem_cappedCutPieceFactorList_iff (C : ConnectedComponents M.Carrier)
    (F : ConnectedClosedOrientedManifold.{u} 3) :
    F ∈ E.cappedCutPieceFactorList C ↔ F ∈ E.associatedFactors C := by
  classical
  rw [cappedCutPieceFactorList, Finset.mem_toList, E.mem_cappedCutPieceFactorSet_iff]

theorem cappedCutPieceFactorList_perm_canonicalEnumeration
    (C : ConnectedComponents M.Carrier) :
    (E.cappedCutPieceFactorList C).Perm (E.canonicalEnumeration C) := by
  classical
  refine List.perm_of_nodup_nodup_toFinset_eq (E.nodup_cappedCutPieceFactorList C)
    (E.completeEnumeration_canonicalEnumeration C).1 ?_
  ext F
  simp only [List.mem_toFinset]
  exact ⟨fun h => (E.completeEnumeration_canonicalEnumeration C).2.2 F
      ((E.mem_cappedCutPieceFactorList_iff C F).mp h),
    fun h => (E.mem_cappedCutPieceFactorList_iff C F).mpr
      ((E.completeEnumeration_canonicalEnumeration C).2.1 F h)⟩

def cutComponentPieceDistinctGluing (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ → ∃ b : ℕ,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.cappedCutPieceFactorList C ++
        List.replicate b S)).toClosedOrientedManifold)

theorem cutComponentPieceDistinctGluing_iff_sphericalSummandCompletion
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.cutComponentPieceDistinctGluing S ↔ E.sphericalSummandCompletion S := by
  constructor
  · intro h C hC
    obtain ⟨b, ⟨ρ⟩⟩ := h C hC
    obtain ⟨σ⟩ := finiteConnectedSum_perm
      ((E.cappedCutPieceFactorList_perm_canonicalEnumeration C).append_right
        (List.replicate b S))
    exact ⟨b, ⟨ρ.trans σ⟩⟩
  · intro h C hC
    obtain ⟨b, ⟨ρ⟩⟩ := h C hC
    obtain ⟨σ⟩ := finiteConnectedSum_perm
      ((E.cappedCutPieceFactorList_perm_canonicalEnumeration C).append_right
        (List.replicate b S))
    exact ⟨b, ⟨ρ.trans σ.symm⟩⟩

theorem cutComponentPieceGluing_iff_cutComponentPieceDistinctGluing
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C)) :
    E.cutComponentPieceGluing S ↔ E.cutComponentPieceDistinctGluing S :=
  (E.sphericalSummandCompletion_iff_cutComponentPieceGluing S hinj).symm.trans
    (E.cutComponentPieceDistinctGluing_iff_sphericalSummandCompletion S).symm

theorem cutCoreComponent_ne_of_cutEndFactor_ne
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (z z' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (h : E.cutEndFactor C a false z ≠ E.cutEndFactor C a true z') :
    E.cutCoreComponent C a false z ≠ E.cutCoreComponent C a true z' :=
  fun hcomp => h (Subtype.ext (congrArg (E.cappedFactor C) hcomp))

theorem cutEndFactor_mem_cappedCutPieceFactors
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C) (side : Bool)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (E.cutEndFactor C a side z : ConnectedClosedOrientedManifold.{u} 3) ∈
      E.cappedCutPieceFactors C := by
  rw [E.mem_cappedCutPieceFactors_iff]
  exact (E.cutEndFactor C a side z).2

theorem eq_cutEndFactor_false_or_eq_true_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (hcard : (E.cutIndices C).card = 1) (A : ↥(E.associatedFactors C)) :
    A = E.cutEndFactor C a false sphereBasePoint ∨
      A = E.cutEndFactor C a true sphereBasePoint := by
  classical
  rcases E.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one C hcard with h1 | h2
  · have hsub : ∀ a ∈ E.associatedFactors C, ∀ b ∈ E.associatedFactors C, a = b :=
      (Set.ncard_le_one (E.associatedFactors_finite C)).mp (by omega)
    exact Or.inl (Subtype.ext (hsub A A.2 (E.cutEndFactor C a false sphereBasePoint)
      (E.cutEndFactor C a false sphereBasePoint).2))
  · have hne := E.cutEndFactor_ne_of_ncard_associatedFactors_eq_two_of_card_cutIndices_eq_one
      C a hcard h2
    have huniv : ({E.cutEndFactor C a false sphereBasePoint,
        E.cutEndFactor C a true sphereBasePoint} : Set ↥(E.associatedFactors C)) = Set.univ := by
      have hcardV : Nat.card ↥(E.associatedFactors C) ≤ 2 := by
        have hle := (E.cutIncidenceGraph_connected C).card_vert_le_card_edgeSet_add_one
        have hedge : Nat.card ↥((E.cutIncidenceGraph C).edgeSet) ≤ 1 := by
          have h := E.ncard_edgeSet_le_card_cutIndices C
          rw [hcard] at h
          simpa only [Nat.card_coe_set_eq] using h
        omega
      have hpair : ({E.cutEndFactor C a false sphereBasePoint,
          E.cutEndFactor C a true sphereBasePoint} : Set ↥(E.associatedFactors C)).ncard = 2 :=
        Set.ncard_pair hne
      let _ : Fintype ↥(E.associatedFactors C) := (E.associatedFactors_finite C).fintype
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [hpair, Set.ncard_univ]
      exact hcardV
    have hmem : A ∈ ({E.cutEndFactor C a false sphereBasePoint,
        E.cutEndFactor C a true sphereBasePoint} : Set ↥(E.associatedFactors C)) :=
      huniv ▸ Set.mem_univ A
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem

theorem cutComponentPieceAssembly_of_singleTube_dichotomy
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hcard : ∀ C : ConnectedComponents M.Carrier,
      E.cutIndices C ≠ ∅ → (E.cutIndices C).card = 1)
    (hsphere : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ →
      E.incidenceCycleRank C = 1 →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.cappedCutPieceSummands C ++
            [S])).toClosedOrientedManifold))
    (hsplit : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ →
      E.incidenceCycleRank C = 0 →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.cappedCutPieceSummands C)).toClosedOrientedManifold)) :
    E.cutComponentPieceAssembly S := by
  intro C hC
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hC
  have h1 := hcard C hC
  by_cases h : E.cutEndFactor C ⟨a, ha⟩ false sphereBasePoint =
      E.cutEndFactor C ⟨a, ha⟩ true sphereBasePoint
  · have hcyc := (E.incidenceCycleRank_eq_one_iff_cutEndFactor_eq_of_card_cutIndices_eq_one
      C ⟨a, ha⟩ h1).mpr h
    exact ⟨1, by simpa using hsphere C hC hcyc⟩
  · have hcyc := (E.incidenceCycleRank_eq_zero_iff_cutEndFactor_ne_of_card_cutIndices_eq_one
      C ⟨a, ha⟩ h1).mpr h
    exact ⟨0, by simpa using hsplit C hC hcyc⟩

end SphericalCutCapTransition

end DifferentialGeometry.Topology
