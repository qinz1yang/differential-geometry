import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountInvariance
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

noncomputable section

open Bundle Manifold Set Topology TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

variable {n : ℕ}
variable {M M' : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [TopologicalSpace M']
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M']

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M'] in
private theorem extend_sumInl_aux (p x : M) :
    ((chartAt (EuclideanSpace ℝ (Fin n)) (Sum.inl p : M ⊕ M')).extend
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∘
        ((chartAt (EuclideanSpace ℝ (Fin n)) (Sum.inl x : M ⊕ M')).extend
          𝓘(ℝ, EuclideanSpace ℝ (Fin n))).symm =
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).extend 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∘
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).extend
          𝓘(ℝ, EuclideanSpace ℝ (Fin n))).symm := by
  funext u
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M'] in
private theorem extend_sumInr_aux (p x : M') :
    ((chartAt (EuclideanSpace ℝ (Fin n)) (Sum.inr p : M ⊕ M')).extend
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∘
        ((chartAt (EuclideanSpace ℝ (Fin n)) (Sum.inr x : M ⊕ M')).extend
          𝓘(ℝ, EuclideanSpace ℝ (Fin n))).symm =
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).extend 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∘
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).extend
          𝓘(ℝ, EuclideanSpace ℝ (Fin n))).symm := by
  funext u
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_apply]

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M'] in
private theorem extend_sumInl_aux_apply (x : M) :
    ((chartAt (EuclideanSpace ℝ (Fin n)) (Sum.inl x : M ⊕ M')).extend
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inl x) =
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).extend
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x := by
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    ChartedSpace.sum_chartAt_inl, OpenPartialHomeomorph.lift_openEmbedding_apply]

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M'] in
private theorem extend_sumInr_aux_apply (x : M') :
    ((chartAt (EuclideanSpace ℝ (Fin n)) (Sum.inr x : M ⊕ M')).extend
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inr x) =
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).extend
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x := by
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
    ChartedSpace.sum_chartAt_inr, OpenPartialHomeomorph.lift_openEmbedding_apply]

private theorem tangentChartEquiv_sumInl_apply_aux (p x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet)
    (hx' : (Sum.inl x : M ⊕ M') ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inl p)).baseSet)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M ⊕ M') (Sum.inl p) (Sum.inl x) hx'
        (show TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Sum.inl x) from v) =
      tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M p x hx v := by
  rw [tangentChartEquiv, tangentChartEquiv, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_apply, TangentBundle.trivializationAt_apply,
    TangentBundle.trivializationAt_apply, extend_sumInl_aux, extend_sumInl_aux_apply]

private theorem tangentChartEquiv_sumInr_apply_aux (p x : M')
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet)
    (hx' : (Sum.inr x : M ⊕ M') ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inr p)).baseSet)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M ⊕ M') (Sum.inr p) (Sum.inr x) hx'
        (show TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Sum.inr x) from v) =
      tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M' p x hx v := by
  rw [tangentChartEquiv, tangentChartEquiv, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_apply, TangentBundle.trivializationAt_apply,
    TangentBundle.trivializationAt_apply, extend_sumInr_aux, extend_sumInr_aux_apply]

private theorem tangentChartEquiv_sumInl_aux (p x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet)
    (hx' : (Sum.inl x : M ⊕ M') ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inl p)).baseSet) :
    tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M ⊕ M') (Sum.inl p) (Sum.inl x) hx' =
      tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M p x hx := by
  apply LinearEquiv.ext
  intro v
  exact tangentChartEquiv_sumInl_apply_aux p x hx hx' v

private theorem tangentChartEquiv_sumInr_aux (p x : M')
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet)
    (hx' : (Sum.inr x : M ⊕ M') ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inr p)).baseSet) :
    tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M ⊕ M') (Sum.inr p) (Sum.inr x) hx' =
      tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M' p x hx := by
  apply LinearEquiv.ext
  intro v
  exact tangentChartEquiv_sumInr_apply_aux p x hx hx' v

private theorem mem_trivializationAt_sumInl_aux (p y : M) :
    (Sum.inl y : M ⊕ M') ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inl p)).baseSet ↔
      y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_source, TangentBundle.trivializationAt_baseSet]
  exact ⟨fun ⟨z, hz, hzy⟩ => by rw [Sum.inl_injective hzy] at hz; exact hz,
    fun hy => ⟨y, hy, rfl⟩⟩

private theorem mem_trivializationAt_sumInr_aux (p y : M') :
    (Sum.inr y : M ⊕ M') ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inr p)).baseSet ↔
      y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_source, TangentBundle.trivializationAt_baseSet]
  exact ⟨fun ⟨z, hz, hzy⟩ => by rw [Sum.inr_injective hzy] at hz; exact hz,
    fun hy => ⟨y, hy, rfl⟩⟩

private theorem not_mem_trivializationAt_sumInl_inr_aux (p : M) (y : M') :
    (Sum.inr y : M ⊕ M') ∉ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inl p)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  rintro ⟨z, -, hz⟩
  exact Sum.inl_ne_inr hz

private theorem not_mem_trivializationAt_sumInr_inl_aux (p : M') (y : M) :
    (Sum.inl y : M ⊕ M') ∉ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Sum.inr p)).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_source]
  rintro ⟨z, -, hz⟩
  exact Sum.inr_ne_inl hz

def manifoldOrientationSum (o : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M n)
    (o' : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M' n) :
    ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M ⊕ M') n where
  dimension_eq := o.dimension_eq
  orientation x := match x with
    | Sum.inl q => o.orientation q
    | Sum.inr d => o'.orientation d
  locally_constant := by
    intro p x hx
    rcases p with p | p
    · rcases x with x | x
      · obtain ⟨U, hUopen, hxU, hUsub, hUc⟩ :=
          o.locally_constant p x ((mem_trivializationAt_sumInl_aux p x).mp hx)
        have hU' : Sum.inl '' U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            (Sum.inl p : M ⊕ M')).baseSet := by
          rintro _ ⟨y, hy, rfl⟩
          exact (mem_trivializationAt_sumInl_aux p y).mpr (hUsub hy)
        refine ⟨Sum.inl '' U, isOpenMap_inl U hUopen, ⟨x, hxU, rfl⟩, hU', ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        rw [tangentChartEquiv_sumInl_aux (M' := M') p y (hUsub hy) (hU' ⟨y, hy, rfl⟩),
          tangentChartEquiv_sumInl_aux (M' := M') p x
            ((mem_trivializationAt_sumInl_aux p x).mp hx) hx]
        exact hUc y hy
      · exact absurd hx (not_mem_trivializationAt_sumInl_inr_aux p x)
    · rcases x with x | x
      · exact absurd hx (not_mem_trivializationAt_sumInr_inl_aux p x)
      · obtain ⟨U, hUopen, hxU, hUsub, hUc⟩ :=
          o'.locally_constant p x ((mem_trivializationAt_sumInr_aux p x).mp hx)
        have hU' : Sum.inr '' U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n))
            (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            (Sum.inr p : M ⊕ M')).baseSet := by
          rintro _ ⟨y, hy, rfl⟩
          exact (mem_trivializationAt_sumInr_aux p y).mpr (hUsub hy)
        refine ⟨Sum.inr '' U, isOpenMap_inr U hUopen, ⟨x, hxU, rfl⟩, hU', ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        rw [tangentChartEquiv_sumInr_aux (M := M) p y (hUsub hy) (hU' ⟨y, hy, rfl⟩),
          tangentChartEquiv_sumInr_aux (M := M) p x
            ((mem_trivializationAt_sumInr_aux p x).mp hx) hx]
        exact hUc y hy

@[simp]
theorem manifoldOrientationSum_orientation_inl
    (o : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M n)
    (o' : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M' n) (q : M) :
    (manifoldOrientationSum o o').orientation (Sum.inl q) = o.orientation q := rfl

@[simp]
theorem manifoldOrientationSum_orientation_inr
    (o : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M n)
    (o' : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M' n) (d : M') :
    (manifoldOrientationSum o o').orientation (Sum.inr d) = o'.orientation d := rfl

abbrev closedOrientedSum (M : ClosedOrientedManifold.{u} n) (N : ClosedOrientedManifold.{u} n) :
    ClosedOrientedManifold.{u} n where
  Carrier := M.Carrier ⊕ N.Carrier
  orientation := manifoldOrientationSum M.orientation N.orientation

@[simp]
theorem closedOrientedSum_carrier (M N : ClosedOrientedManifold.{u} n) :
    (closedOrientedSum M N).Carrier = (M.Carrier ⊕ N.Carrier) := rfl

@[simp]
theorem closedOrientedSum_orientation_inl (M N : ClosedOrientedManifold.{u} n) (q : M.Carrier) :
    (closedOrientedSum M N).orientation.orientation (Sum.inl q) = M.orientation.orientation q :=
  rfl

@[simp]
theorem closedOrientedSum_orientation_inr (M N : ClosedOrientedManifold.{u} n) (d : N.Carrier) :
    (closedOrientedSum M N).orientation.orientation (Sum.inr d) = N.orientation.orientation d :=
  rfl

theorem closedOrientedSum_orientation_apply (M N : ClosedOrientedManifold.{u} n)
    (x : M.Carrier ⊕ N.Carrier) :
    (closedOrientedSum M N).orientation.orientation x =
      match x with
      | Sum.inl q => M.orientation.orientation q
      | Sum.inr d => N.orientation.orientation d := by
  cases x <;> rfl

theorem componentSet_closedOrientedSum_inl (M N : ClosedOrientedManifold.{u} n) (q : M.Carrier) :
    ClosedOrientedManifold.componentSet (closedOrientedSum M N)
        (ConnectedComponents.mk (Sum.inl q)) =
      Sum.inl '' ClosedOrientedManifold.componentSet M (ConnectedComponents.mk q) := by
  rw [ClosedOrientedManifold.componentSet_mk]
  have hclop : IsClopen (Sum.inl ''
      ClosedOrientedManifold.componentSet M (ConnectedComponents.mk q)) :=
    ⟨Topology.IsClosedEmbedding.inl (X := M.Carrier) (Y := N.Carrier) |>.isClosedMap
        (ClosedOrientedManifold.componentSet M (ConnectedComponents.mk q))
        (ClosedOrientedManifold.isClosed_componentSet M (ConnectedComponents.mk q)),
      isOpenMap_inl (X := M.Carrier) (Y := N.Carrier)
        (ClosedOrientedManifold.componentSet M (ConnectedComponents.mk q))
        (ClosedOrientedManifold.isOpen_componentSet M (ConnectedComponents.mk q))⟩
  refine Set.Subset.antisymm
    (isPreconnected_connectedComponent.subset_isClopen hclop
      ⟨Sum.inl q, mem_connectedComponent, ⟨q, rfl, rfl⟩⟩) ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ((ClosedOrientedManifold.isConnected_componentSet M
    (ConnectedComponents.mk q)).isPreconnected.image
      (Sum.inl : M.Carrier → M.Carrier ⊕ N.Carrier)
    (continuous_inl (X := M.Carrier) (Y := N.Carrier)).continuousOn).subset_connectedComponent
      ⟨q, rfl, rfl⟩ ⟨y, hy, rfl⟩

theorem isLocalDiffeomorph_sumInl (M N : ClosedOrientedManifold.{u} n) :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Sum.inl : M.Carrier → M.Carrier ⊕ N.Carrier) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    (Sum.inl : M.Carrier → M.Carrier ⊕ N.Carrier)
    (ContMDiff.inl (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (M := M.Carrier) (M' := N.Carrier))
    (fun x => by
      have h : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (Sum.inl : M.Carrier → M.Carrier ⊕ N.Carrier) x =
          ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
        mfderiv_sumInl (p := Sum.inl x)
      rw [h]
      exact fun a b hab => hab)
    (by simp)

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def presentationOrientedDiffeomorph :
    ClosedOrientedManifold.OrientedDiffeomorph E.capped (closedOrientedSum Q E.discarded) := by
  refine ⟨E.presentation, fun x => ?_⟩
  cases hx : E.presentation x with
  | inl q =>
    have h := E.presentation_positive x
    rw [hx] at h
    simpa using h
  | inr d =>
    have h := E.presentation_positive x
    rw [hx] at h
    simpa using h

def cutCapSummandCountDeterminedOnCut : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.cutIndices C ≠ ∅ → E.CompleteEnumeration C L →
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) →
      K.length = (E.cutIndices C).card + 1 - L.length

def cutCapSummandCountDeterminedOnUncut : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.cutIndices C = ∅ → E.CompleteEnumeration C L →
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) →
      K.length = (E.cutIndices C).card + 1 - L.length

theorem cutCapSummandCountDetermined_iff_onCut_and_onUncut :
    E.cutCapSummandCountDetermined ↔
      E.cutCapSummandCountDeterminedOnCut ∧ E.cutCapSummandCountDeterminedOnUncut := by
  constructor
  · intro h
    exact ⟨fun C L K _ => h C L K, fun C L K _ => h C L K⟩
  · rintro ⟨h1, h2⟩ C L K
    by_cases hC : E.cutIndices C = ∅
    · exact h2 C L K hC
    · exact h1 C L K hC

theorem cutComponentRealization_of_cutComponentGluing_of_onCut
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDeterminedOnCut) :
    E.cutComponentRealization := by
  intro C hC L hL
  obtain ⟨K, hKfac, hdiff⟩ := hglue C hC L hL
  exact ⟨K, hcount C L K hC hL hKfac hdiff, hKfac, hdiff⟩

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_onCut
    (hr : E.NoTubeRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDeterminedOnCut) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨hr, E.cutComponentRealization_of_cutComponentGluing_of_onCut hglue hcount⟩

theorem cutCapSummandCountDeterminedOnUncut_of_summandCountUnique
    (huncut : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅ →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold))
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L) :
    E.cutCapSummandCountDeterminedOnUncut := by
  intro C L K hC hL hKfac hdiff
  have hperm : (E.canonicalEnumeration C).Perm L :=
    (E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).symm
  obtain ⟨σ⟩ := finiteConnectedSum_perm (hperm.append_right K)
  have h1 : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) :=
    hdiff.map fun ρ => ρ.trans σ.symm
  obtain ⟨ρ₁⟩ := h1
  obtain ⟨ρ₂⟩ := huncut C hC
  have h2 : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        ([] : List (ConnectedClosedOrientedManifold.{u} 3)))).toClosedOrientedManifold) := by
    simpa using (show Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)
        from ⟨ρ₁.symm.trans ρ₂⟩)
  have hlen := huniq (E.canonicalEnumeration C) K [] hKfac (by simp) h2
  rw [List.length_nil] at hlen
  obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  rw [hlen, hC, hN]
  simp

theorem cutCapSummandCountDeterminedOnUncut_iff_cancellation :
    E.cutCapSummandCountDeterminedOnUncut ↔
      (∀ (C : ConnectedComponents M.Carrier) (K : List (ConnectedClosedOrientedManifold.{u} 3)),
        E.cutIndices C = ∅ → (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) →
        K = []) := by
  constructor
  · intro h C K hC hKfac hdiff
    have hlen := h C (E.canonicalEnumeration C) K hC
      (E.completeEnumeration_canonicalEnumeration C) hKfac hdiff
    obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    rw [hC, hN] at hlen
    simp only [Finset.card_empty, List.length_singleton, Nat.zero_add] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  · intro h C L K hC hL hKfac hdiff
    have hperm : (E.canonicalEnumeration C).Perm L :=
      (E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).symm
    obtain ⟨σ⟩ := finiteConnectedSum_perm (hperm.append_right K)
    have hdiff' : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) :=
      hdiff.map fun ρ => ρ.trans σ.symm
    have hK : K = [] := h C K hC hKfac hdiff'
    obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
    rw [hK, hN, hC]
    simp

theorem exists_cutCapSummandCountDeterminedOnUncut_hypotheses
    (huncut : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅ →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold))
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    ∃ (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
      E.CompleteEnumeration C L ∧ (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) ∧
        K.length = (E.cutIndices C).card + 1 - L.length := by
  refine ⟨E.canonicalEnumeration C, [], E.completeEnumeration_canonicalEnumeration C,
    by simp, ?_, ?_⟩
  · simpa using huncut C hC
  · rw [hC]
    obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    rw [hN]
    simp

theorem cutComponentGluing_statement_iff_of_perm
    {C : ConnectedComponents M.Carrier} {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hL : E.CompleteEnumeration C L) (hL' : E.CompleteEnumeration C L') :
    (∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold
            (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) ↔
      (∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold
            (finiteConnectedSum (L' ++ K)).toClosedOrientedManifold)) := by
  constructor
  · rintro ⟨K, hKfac, hdiff⟩
    obtain ⟨σ⟩ := finiteConnectedSum_perm ((E.completeEnumeration_perm hL hL').append_right K)
    exact ⟨K, hKfac, hdiff.map fun ρ => ρ.trans σ⟩
  · rintro ⟨K, hKfac, hdiff⟩
    obtain ⟨σ⟩ := finiteConnectedSum_perm ((E.completeEnumeration_perm hL' hL).append_right K)
    exact ⟨K, hKfac, hdiff.map fun ρ => ρ.trans σ⟩

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_onCut
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDeterminedOnCut) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition := by
  intro i
  let E := T.transition i
  exact E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_onCut
    (hr i) (hglue i) (hcount i)

end FiniteCutCapTrace

end DifferentialGeometry.Topology
