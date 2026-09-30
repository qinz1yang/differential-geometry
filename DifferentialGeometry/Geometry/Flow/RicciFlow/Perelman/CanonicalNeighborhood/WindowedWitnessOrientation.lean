import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessStrictRestriction

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry.CheegerGromovCompactness (PointedFlowData)
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

section Orientation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]

private def negOrientation (o : TangentOrientationSection M) : TangentOrientationSection M where
  orientation x := -o.orientation x
  locally_constant p x hx := by
    obtain ⟨U, hU, hxU, hsub, h⟩ := o.locally_constant p x hx
    exact ⟨U, hU, hxU, hsub, fun y hy => by simp only [Orientation.map_neg, h y hy]⟩

private theorem isOpen_setOf_orientation_eq (o₁ o₂ : TangentOrientationSection M) :
    IsOpen {x | o₁.orientation x = o₂.orientation x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hb : x ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) x
  obtain ⟨U₁, hU₁, hx₁, hs₁, h₁⟩ := o₁.locally_constant x x hb
  obtain ⟨U₂, hU₂, hx₂, hs₂, h₂⟩ := o₂.locally_constant x x hb
  refine ⟨U₁ ∩ U₂, fun y hy => ?_, hU₁.inter hU₂, hx₁, hx₂⟩
  apply (Orientation.map (Fin 3) (Surgery.Topology.tangentChartEquiv M x y (hs₁ hy.1))).injective
  have hx' : o₁.orientation x = o₂.orientation x := hx
  rw [h₁ y hy.1, hx']
  exact (h₂ y hy.2).symm

private theorem orientation_eq_or_eq_neg [PreconnectedSpace M]
    (o₁ o₂ : TangentOrientationSection M) :
    (∀ x, o₁.orientation x = o₂.orientation x) ∨
      ∀ x, o₁.orientation x = -o₂.orientation x := by
  have hA := isOpen_setOf_orientation_eq o₁ o₂
  have hB := isOpen_setOf_orientation_eq o₁ (negOrientation o₂)
  have hcompl : {x | o₁.orientation x = o₂.orientation x}ᶜ =
      {x | o₁.orientation x = (negOrientation o₂).orientation x} := by
    ext x
    rw [mem_compl_iff]
    change ¬ o₁.orientation x = o₂.orientation x ↔ o₁.orientation x = -o₂.orientation x
    constructor
    · intro hne
      exact (Orientation.eq_or_eq_neg (o₁.orientation x) (o₂.orientation x)
        (by rw [Fintype.card_fin]; exact finrank_euclideanSpace_fin.symm)).resolve_left hne
    · intro hneg heq
      exact Module.Ray.ne_neg_self (o₂.orientation x) (heq.symm.trans hneg)
  have hclopen : IsClopen {x | o₁.orientation x = o₂.orientation x} :=
    ⟨by rw [← isOpen_compl_iff, hcompl]; exact hB, hA⟩
  rcases isClopen_iff.mp hclopen with h | h
  · right
    intro x
    have hx : x ∈ {x | o₁.orientation x = o₂.orientation x}ᶜ := by rw [h]; exact notMem_empty x
    rw [hcompl] at hx
    exact hx
  · left
    intro x
    have hx : x ∈ {x | o₁.orientation x = o₂.orientation x} := by rw [h]; exact mem_univ x
    exact hx

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]

private theorem exists_preserves_of_preconnected [PreconnectedSpace M]
    (o₀ o : TangentOrientationSection M) (oN : TangentOrientationSection N) (f : N → M)
    (s : Set N) (h : ∀ y ∈ s, ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f y),
      PreservesTangentOrientationAt oN o₀ f y hf) :
    ∃ oN' : TangentOrientationSection N, ∀ y ∈ s,
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel f y),
        PreservesTangentOrientationAt oN' o f y hf := by
  rcases orientation_eq_or_eq_neg o o₀ with ho | ho
  · refine ⟨oN, fun y hy => ?_⟩
    obtain ⟨hf, hp⟩ := h y hy
    refine ⟨hf, ?_⟩
    unfold PreservesTangentOrientationAt at hp ⊢
    rw [ho]
    exact hp
  · refine ⟨negOrientation oN, fun y hy => ?_⟩
    obtain ⟨hf, hp⟩ := h y hy
    refine ⟨hf, ?_⟩
    unfold PreservesTangentOrientationAt at hp ⊢
    change Orientation.map (Fin 3) _ (-oN.orientation y) = o.orientation (f y)
    rw [ho, Orientation.map_neg, hp]

end Orientation

section WitnessGeometry

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.exists_toRestrictOpen_orientation
    {U : TopologicalSpace.Opens M} [SigmaCompactSpace U] [PreconnectedSpace U]
    {x : U} {eps kappa t : ℝ} (W : WindowedModelWitness eps kappa S x.val t)
    (hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps + 1) ⊆ (U : Set M))
    (o : TangentOrientationSection M) (oN : TangentOrientationSection W.model.M)
    (hO : ∀ y ∈ W.embedding.source, ∃ hf : Function.Bijective (mfderiv I3 I3 W.embedding y),
      PreservesTangentOrientationAt oN o W.embedding y hf)
    (oU : TangentOrientationSection U) :
    ∃ oN' : TangentOrientationSection W.model.M,
      ∀ y ∈ (W.toRestrictOpen hU).embedding.source,
        ∃ hf : Function.Bijective (mfderiv I3 I3 (W.toRestrictOpen hU).embedding y),
          PreservesTangentOrientationAt oN' oU (W.toRestrictOpen hU).embedding y hf :=
  exists_preserves_of_preconnected (o.restrictOpen U) oU oN _ _
    (W.toRestrictOpen_preservesTangentOrientationAt hU o oN hO)

end WitnessGeometry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
