import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalSummandCompletionReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private theorem connectedComponentsMap_injective_of_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {g : Y → X}
    (hf : Continuous f) (hg : Continuous g) (hgf : Function.LeftInverse g f) :
    Function.Injective hf.connectedComponentsMap := by
  intro c c' h
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨x', rfl⟩ := ConnectedComponents.surjective_coe c'
  rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk] at h
  have h2 := congrArg hg.connectedComponentsMap h
  simpa only [Continuous.connectedComponentsMap_mk, hgf x, hgf x'] using h2

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private theorem cappedCutComponents_finite' (C : ConnectedComponents M.Carrier) :
    (E.cappedCutComponents C).Finite := by
  let _ : Finite (ConnectedComponents E.capped.Carrier) :=
    ClosedOrientedManifold.finite_components E.capped
  exact Set.toFinite _

noncomputable def cappedCutOutputComponent (C : ConnectedComponents M.Carrier)
    (D : E.cappedCutComponents C) :
    ConnectedComponents (Q.Carrier ⊕ E.discarded.Carrier) :=
  E.presentation.continuous.connectedComponentsMap D.1

theorem cappedCutOutputComponent_injective (C : ConnectedComponents M.Carrier) :
    Function.Injective (E.cappedCutOutputComponent C) := by
  intro D D' h
  have h' : E.presentation.continuous.connectedComponentsMap D.1 =
      E.presentation.continuous.connectedComponentsMap D'.1 := h
  exact Subtype.ext (connectedComponentsMap_injective_of_leftInverse E.presentation.continuous
    E.presentation.symm.continuous E.presentation.symm_apply_apply h')

def cappedCutOutputComponents (C : ConnectedComponents M.Carrier) :
    Set (ConnectedComponents (Q.Carrier ⊕ E.discarded.Carrier)) :=
  range (E.cappedCutOutputComponent C)

theorem ncard_cappedCutOutputComponents (C : ConnectedComponents M.Carrier) :
    (E.cappedCutOutputComponents C).ncard = Nat.card (E.cappedCutComponents C) := by
  rw [cappedCutOutputComponents, ← image_univ]
  have h := Set.InjOn.ncard_image (f := E.cappedCutOutputComponent C) (s := univ)
    fun a _ b _ hab => E.cappedCutOutputComponent_injective C hab
  simpa [Set.ncard_univ] using h

theorem exists_cappedCutPieceEnumeration (C : ConnectedComponents M.Carrier) :
    ∃ L : List (E.cappedCutComponents C), (∀ D, D ∈ L) ∧ L.Nodup := by
  classical
  let _ : Fintype (E.cappedCutComponents C) := (E.cappedCutComponents_finite' C).fintype
  exact ⟨(Finset.univ : Finset (E.cappedCutComponents C)).toList,
    fun D => Finset.mem_toList.mpr (Finset.mem_univ D), Finset.nodup_toList _⟩

noncomputable def cappedCutPieceEnumeration (C : ConnectedComponents M.Carrier) :
    List (E.cappedCutComponents C) :=
  Classical.choose (E.exists_cappedCutPieceEnumeration C)

theorem mem_cappedCutPieceEnumeration (C : ConnectedComponents M.Carrier)
    (D : E.cappedCutComponents C) : D ∈ E.cappedCutPieceEnumeration C :=
  (Classical.choose_spec (E.exists_cappedCutPieceEnumeration C)).1 D

theorem nodup_cappedCutPieceEnumeration (C : ConnectedComponents M.Carrier) :
    (E.cappedCutPieceEnumeration C).Nodup :=
  (Classical.choose_spec (E.exists_cappedCutPieceEnumeration C)).2

theorem cappedCutPieceEnumeration_perm {C : ConnectedComponents M.Carrier}
    {L : List (E.cappedCutComponents C)} (h : (∀ D, D ∈ L) ∧ L.Nodup) :
    (E.cappedCutPieceEnumeration C).Perm L := by
  classical
  refine List.perm_of_nodup_nodup_toFinset_eq (E.nodup_cappedCutPieceEnumeration C) h.2 ?_
  ext D
  simp only [List.mem_toFinset]
  exact ⟨fun _ => h.1 D, fun _ => E.mem_cappedCutPieceEnumeration C D⟩

noncomputable def cappedCutPieceFactors (C : ConnectedComponents M.Carrier) :
    List (ConnectedClosedOrientedManifold.{u} 3) :=
  (E.cappedCutPieceEnumeration C).map (E.cappedFactor C)

theorem mem_cappedCutPieceFactors_iff (C : ConnectedComponents M.Carrier)
    (F : ConnectedClosedOrientedManifold.{u} 3) :
    F ∈ E.cappedCutPieceFactors C ↔ F ∈ E.associatedFactors C := by
  rw [cappedCutPieceFactors, List.mem_map]
  constructor
  · rintro ⟨D, -, rfl⟩
    exact ⟨Classical.choose D.2, (Classical.choose_spec D.2).1, rfl⟩
  · intro hF
    obtain ⟨x, hxC, rfl⟩ := hF
    refine ⟨⟨ConnectedComponents.mk (E.capping.coreInclusion x), x, hxC, rfl⟩, ?_, ?_⟩
    · exact E.mem_cappedCutPieceEnumeration C _
    · rw [E.cappedFactor_eq_of_mem C _ x rfl]

theorem cappedCutPieceFactors_ne_nil (C : ConnectedComponents M.Carrier) :
    E.cappedCutPieceFactors C ≠ [] := by
  obtain ⟨x, hx⟩ := E.exists_core_mem_componentSet C
  refine List.ne_nil_of_mem (a := E.associatedFactor x) ?_
  rw [E.mem_cappedCutPieceFactors_iff]
  exact ⟨x, hx, rfl⟩

theorem nodup_cappedCutPieceFactors (C : ConnectedComponents M.Carrier)
    (hinj : Function.Injective (E.cappedFactor C)) :
    (E.cappedCutPieceFactors C).Nodup :=
  (E.nodup_cappedCutPieceEnumeration C).map hinj

theorem cappedCutPieceFactors_perm_canonicalEnumeration (C : ConnectedComponents M.Carrier)
    (hinj : Function.Injective (E.cappedFactor C)) :
    (E.cappedCutPieceFactors C).Perm (E.canonicalEnumeration C) := by
  classical
  refine List.perm_of_nodup_nodup_toFinset_eq (E.nodup_cappedCutPieceFactors C hinj)
    (E.completeEnumeration_canonicalEnumeration C).1 ?_
  ext F
  simp only [List.mem_toFinset]
  exact ⟨fun h => (E.completeEnumeration_canonicalEnumeration C).2.2 F
      ((E.mem_cappedCutPieceFactors_iff C F).mp h),
    fun h => (E.mem_cappedCutPieceFactors_iff C F).mpr
      ((E.completeEnumeration_canonicalEnumeration C).2.1 F h)⟩

theorem length_cappedCutPieceFactors (C : ConnectedComponents M.Carrier)
    (hinj : Function.Injective (E.cappedFactor C)) :
    (E.cappedCutPieceFactors C).length = (E.associatedFactors C).ncard := by
  rw [(E.cappedCutPieceFactors_perm_canonicalEnumeration C hinj).length_eq,
    E.length_canonicalEnumeration C]

theorem incidenceCycleRank_add_length_cappedCutPieceFactors
    (C : ConnectedComponents M.Carrier) (hinj : Function.Injective (E.cappedFactor C)) :
    E.incidenceCycleRank C + (E.cappedCutPieceFactors C).length = (E.cutIndices C).card + 1 := by
  rw [E.length_cappedCutPieceFactors C hinj, E.incidenceCycleRank_add_ncard_associatedFactors C]

theorem exists_orientedDiffeomorph_finiteConnectedSum_cappedCutPieceFactors
    (C : ConnectedComponents M.Carrier) (hinj : Function.Injective (E.cappedFactor C))
    (K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.cappedCutPieceFactors C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) :=
  finiteConnectedSum_perm
    ((E.cappedCutPieceFactors_perm_canonicalEnumeration C hinj).append_right K)

def cutComponentPieceGluing (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ → ∃ b : ℕ,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.cappedCutPieceFactors C ++
        List.replicate b S)).toClosedOrientedManifold)

theorem sphericalSummandCompletion_of_cutComponentPieceGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) (C : ConnectedComponents M.Carrier)
    (hinj : Function.Injective (E.cappedFactor C)) (hC : E.cutIndices C ≠ ∅)
    (h : E.cutComponentPieceGluing S) : ∃ b : ℕ,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++
          List.replicate b S)).toClosedOrientedManifold) := by
  obtain ⟨b, ⟨ρ⟩⟩ := h C hC
  obtain ⟨σ⟩ := E.exists_orientedDiffeomorph_finiteConnectedSum_cappedCutPieceFactors C hinj
    (List.replicate b S)
  exact ⟨b, ⟨ρ.trans σ⟩⟩

theorem cutComponentPieceGluing_of_sphericalSummandCompletion
    (S : ConnectedClosedOrientedManifold.{u} 3) (C : ConnectedComponents M.Carrier)
    (hinj : Function.Injective (E.cappedFactor C)) (hC : E.cutIndices C ≠ ∅)
    (h : E.sphericalSummandCompletion S) : ∃ b : ℕ,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.cappedCutPieceFactors C ++
          List.replicate b S)).toClosedOrientedManifold) := by
  obtain ⟨b, ⟨ρ⟩⟩ := h C hC
  obtain ⟨σ⟩ := E.exists_orientedDiffeomorph_finiteConnectedSum_cappedCutPieceFactors C hinj
    (List.replicate b S)
  exact ⟨b, ⟨ρ.trans σ.symm⟩⟩

theorem sphericalSummandCompletion_iff_cutComponentPieceGluing
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C)) :
    E.sphericalSummandCompletion S ↔ E.cutComponentPieceGluing S :=
  ⟨fun h C hC => E.cutComponentPieceGluing_of_sphericalSummandCompletion S C (hinj C) hC h,
    fun h C hC => E.sphericalSummandCompletion_of_cutComponentPieceGluing S C (hinj C) hC h⟩

theorem cutComponentPieceGluing_of_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (h : E.cutSphericalGraphSumRealization S) : E.cutComponentPieceGluing S :=
  E.sphericalSummandCompletion_iff_cutComponentPieceGluing S hinj |>.mp
    (E.sphericalSummandCompletion_of_cutSphericalGraphSumRealization S h)

theorem cutSphericalGraphSumRealization_of_cutComponentPieceGluing_of_exponentDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (h : E.cutComponentPieceGluing S) (hdet : E.sphericalSummandExponentDetermined S) :
    E.cutSphericalGraphSumRealization S :=
  ((E.cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined
      S).mp
    ⟨(E.sphericalSummandCompletion_iff_cutComponentPieceGluing S hinj).mpr h, hdet⟩).1

private theorem forall₂_replicate_orientedDiffeomorph
    {S S' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      S.toClosedOrientedManifold S'.toClosedOrientedManifold)) :
    ∀ b : ℕ, List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        A.toClosedOrientedManifold B.toClosedOrientedManifold))
      (List.replicate b S) (List.replicate b S')
  | 0 => by simp
  | b + 1 => by
    simp only [List.replicate_succ]
    exact List.Forall₂.cons h (forall₂_replicate_orientedDiffeomorph h b)

theorem cutComponentPieceGluing_iff_of_orientedDiffeomorph
    {S S' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      S.toClosedOrientedManifold S'.toClosedOrientedManifold)) :
    E.cutComponentPieceGluing S ↔ E.cutComponentPieceGluing S' := by
  have key : ∀ {X Y : ConnectedClosedOrientedManifold.{u} 3}, Nonempty
      (ClosedOrientedManifold.OrientedDiffeomorph X.toClosedOrientedManifold
        Y.toClosedOrientedManifold) →
      E.cutComponentPieceGluing X → E.cutComponentPieceGluing Y := by
    intro X Y hXY hf C hC
    obtain ⟨b, ⟨ρ⟩⟩ := hf C hC
    obtain ⟨σ⟩ := finiteConnectedSum_congr
      (List.rel_append (List.forall₂_same.mpr fun A _ =>
        ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩)
        (forall₂_replicate_orientedDiffeomorph hXY b))
    exact ⟨b, ⟨ρ.trans σ⟩⟩
  exact ⟨key h, key (h.map ClosedOrientedManifold.OrientedDiffeomorph.symm)⟩

theorem cutComponentPieceGluing_of_cutComponentCanonicalGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (h : E.cutComponentCanonicalGluing) : E.cutComponentPieceGluing S :=
  (E.sphericalSummandCompletion_iff_cutComponentPieceGluing S hinj).mp
    ((E.cutComponentCanonicalGluing_iff_sphericalSummandCompletion S hS).mp h)

theorem cutSphericalGraphSumRealization_iff_pieceGluing_of_exponentDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (hinj : ∀ C : ConnectedComponents M.Carrier, Function.Injective (E.cappedFactor C))
    (hdet : E.sphericalSummandExponentDetermined S) :
    E.cutSphericalGraphSumRealization S ↔ E.cutComponentPieceGluing S :=
  ⟨E.cutComponentPieceGluing_of_cutSphericalGraphSumRealization S hinj,
    fun h => E.cutSphericalGraphSumRealization_of_cutComponentPieceGluing_of_exponentDetermined
      S hinj h hdet⟩

theorem cutComponentPieceGluing_of_forall_cutIndices_eq_empty
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutComponentPieceGluing S :=
  fun C hC => absurd (h C) hC

theorem cutComponentPieceGluing_of_isEmpty_index [IsEmpty E.tubes.Index]
    (S : ConnectedClosedOrientedManifold.{u} 3) : E.cutComponentPieceGluing S :=
  E.cutComponentPieceGluing_of_forall_cutIndices_eq_empty S
    fun C => E.cutIndices_eq_empty_of_isEmpty_index C

theorem cutSphericalGraphSumRealization_iff_forall_completeEnumeration
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.cutSphericalGraphSumRealization S ↔
      ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
        ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold
            (finiteConnectedSum (L ++
              List.replicate (E.incidenceCycleRank C) S)).toClosedOrientedManifold) := by
  constructor
  · intro h C hC L hL
    obtain ⟨σ⟩ := finiteConnectedSum_perm
      ((E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).append_right
        (List.replicate (E.incidenceCycleRank C) S))
    exact (h C hC).map fun ρ => ρ.trans σ.symm
  · intro h C hC
    exact h C hC (E.canonicalEnumeration C) (E.completeEnumeration_canonicalEnumeration C)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
