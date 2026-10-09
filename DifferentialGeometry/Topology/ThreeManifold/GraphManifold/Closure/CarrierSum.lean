import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma

/-!
Actual oriented bounded carrier sums, their full summand charts and finite component ledger.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.Endpoint.CompactCarrier

private abbrev sumHalfCharts (C : CompactCarrier.{u}) (hC : C.kind = .withBoundary) :
    ChartedSpace (EuclideanHalfSpace 3) C.Carrier := by
  cases C with
  | mk k A O =>
    cases hC
    exact inferInstance

private theorem sumHalfSmooth (C : CompactCarrier.{u}) (hC : C.kind = .withBoundary) :
    letI := sumHalfCharts C hC
    IsManifold (𝓡∂ 3) ∞ C.Carrier := by
  cases C with
  | mk k A O =>
    cases hC
    exact inferInstance

private def sumHalfOrientation (C : CompactCarrier.{u}) (hC : C.kind = .withBoundary) :
    letI := sumHalfCharts C hC
    letI := sumHalfSmooth C hC
    ManifoldOrientation (𝓡∂ 3) C.Carrier 3 := by
  cases C with
  | mk k A O =>
    cases hC
    exact O


def withBoundarySum (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
    (hD : D.kind = .withBoundary) : CompactCarrier.{u} := by
  letI := sumHalfCharts C hC
  letI := sumHalfCharts D hD
  letI := sumHalfSmooth C hC
  letI := sumHalfSmooth D hD
  exact
    { kind := .withBoundary
      Carrier := C.Carrier ⊕ D.Carrier
      charts := inferInstance
      smooth := inferInstance
      orientation := ManifoldOrientation.sum (sumHalfOrientation C hC) (sumHalfOrientation D hD) }

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)

private instance sumCarrierCharts :
    ChartedSpace (withBoundarySum C D hC hD).kind.Space (C.Carrier ⊕ D.Carrier) :=
  (withBoundarySum C D hC hD).charts

private instance sumCarrierSmooth :
    IsManifold (withBoundarySum C D hC hD).model ∞ (C.Carrier ⊕ D.Carrier) :=
  (withBoundarySum C D hC hD).smooth

theorem withBoundarySum_kind : (withBoundarySum C D hC hD).kind = .withBoundary := rfl

private theorem withBoundarySum_inl_local :
    IsLocalDiffeomorph C.model (withBoundarySum C D hC hD).model ∞
      (Sum.inl : C.Carrier → (withBoundarySum C D hC hD).Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact isLocalDiffeomorph_sum_inl (I := 𝓡∂ 3) (M := A) (N := B)

private theorem withBoundarySum_inr_local :
    IsLocalDiffeomorph D.model (withBoundarySum C D hC hD).model ∞
      (Sum.inr : D.Carrier → (withBoundarySum C D hC hD).Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact isLocalDiffeomorph_sum_inr (I := 𝓡∂ 3) (M := B) (N := A)

private theorem withBoundarySum_left_exists [Nonempty C.Carrier] :
    ∃ e : PartialDiffeomorph C.model (withBoundarySum C D hC hD).model
      C.Carrier (withBoundarySum C D hC hD).Carrier ∞,
      e.source = univ ∧ e.target = range Sum.inl ∧ e.toFun = Sum.inl := by
  have hl : IsLocalDiffeomorphOn C.model (withBoundarySum C D hC hD).model ∞
      (Sum.inl : C.Carrier → (withBoundarySum C D hC hD).Carrier) univ :=
    (withBoundarySum_inl_local C D hC hD).isLocalDiffeomorphOn univ
  obtain ⟨e, hs, ht, he⟩ := hl.exists_partialDiffeomorph_of_injOn
    isOpen_univ (by simp) Sum.inl_injective.injOn
  refine ⟨e, hs, ?_, he⟩
  exact ht.trans (image_univ)

private theorem withBoundarySum_right_exists [Nonempty D.Carrier] :
    ∃ e : PartialDiffeomorph D.model (withBoundarySum C D hC hD).model
      D.Carrier (withBoundarySum C D hC hD).Carrier ∞,
      e.source = univ ∧ e.target = range Sum.inr ∧ e.toFun = Sum.inr := by
  have hl : IsLocalDiffeomorphOn D.model (withBoundarySum C D hC hD).model ∞
      (Sum.inr : D.Carrier → (withBoundarySum C D hC hD).Carrier) univ :=
    (withBoundarySum_inr_local C D hC hD).isLocalDiffeomorphOn univ
  obtain ⟨e, hs, ht, he⟩ := hl.exists_partialDiffeomorph_of_injOn
    isOpen_univ (by simp) Sum.inr_injective.injOn
  refine ⟨e, hs, ?_, he⟩
  exact ht.trans (image_univ)


def withBoundarySumLeft [Nonempty C.Carrier] :
    PartialDiffeomorph C.model (withBoundarySum C D hC hD).model
      C.Carrier (withBoundarySum C D hC hD).Carrier ∞ :=
  Classical.choose (withBoundarySum_left_exists C D hC hD)

def withBoundarySumRight [Nonempty D.Carrier] :
    PartialDiffeomorph D.model (withBoundarySum C D hC hD).model
      D.Carrier (withBoundarySum C D hC hD).Carrier ∞ :=
  Classical.choose (withBoundarySum_right_exists C D hC hD)

theorem withBoundarySumLeft_source [Nonempty C.Carrier] :
    (withBoundarySumLeft C D hC hD).source = univ :=
  (Classical.choose_spec (withBoundarySum_left_exists C D hC hD)).1

theorem withBoundarySumRight_source [Nonempty D.Carrier] :
    (withBoundarySumRight C D hC hD).source = univ :=
  (Classical.choose_spec (withBoundarySum_right_exists C D hC hD)).1

theorem withBoundarySumLeft_target [Nonempty C.Carrier] :
    (withBoundarySumLeft C D hC hD).target = range Sum.inl :=
  (Classical.choose_spec (withBoundarySum_left_exists C D hC hD)).2.1

theorem withBoundarySumRight_target [Nonempty D.Carrier] :
    (withBoundarySumRight C D hC hD).target = range Sum.inr :=
  (Classical.choose_spec (withBoundarySum_right_exists C D hC hD)).2.1

theorem withBoundarySumLeft_apply [Nonempty C.Carrier] (x : C.Carrier) :
    withBoundarySumLeft C D hC hD x = Sum.inl x :=
  congrFun (Classical.choose_spec (withBoundarySum_left_exists C D hC hD)).2.2 x

theorem withBoundarySumRight_apply [Nonempty D.Carrier] (x : D.Carrier) :
    withBoundarySumRight C D hC hD x = Sum.inr x :=
  congrFun (Classical.choose_spec (withBoundarySum_right_exists C D hC hD)).2.2 x

theorem withBoundarySum_boundary :
    (withBoundarySum C D hC hD).model.boundary (withBoundarySum C D hC hD).Carrier =
      Sum.inl '' (C.model.boundary C.Carrier) ∪ Sum.inr '' (D.model.boundary D.Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact ModelWithCorners.boundary_disjointUnion (I := 𝓡∂ 3) (M := A) (M' := B)

theorem withBoundarySum_interior :
    ((withBoundarySum C D hC hD).interior : Set (withBoundarySum C D hC hD).Carrier) =
      Sum.inl '' (C.interior : Set C.Carrier) ∪ Sum.inr '' (D.interior : Set D.Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact ModelWithCorners.interior_disjointUnion (I := 𝓡∂ 3) (M := A) (M' := B)


def withBoundarySumInlTangentEquiv (x : C.Carrier) :
    TangentSpace C.model x ≃L[ℝ]
      TangentSpace (withBoundarySum C D hC hD).model
        (Sum.inl x : (withBoundarySum C D hC hD).Carrier) :=
  (withBoundarySum_inl_local C D hC hD).mfderivToContinuousLinearEquiv (by simp) x

def withBoundarySumInrTangentEquiv (x : D.Carrier) :
    TangentSpace D.model x ≃L[ℝ]
      TangentSpace (withBoundarySum C D hC hD).model
        (Sum.inr x : (withBoundarySum C D hC hD).Carrier) :=
  (withBoundarySum_inr_local C D hC hD).mfderivToContinuousLinearEquiv (by simp) x

theorem withBoundarySumInlTangentEquiv_apply (x : C.Carrier) (v : TangentSpace C.model x) :
    withBoundarySumInlTangentEquiv C D hC hD x v =
      mfderiv C.model (withBoundarySum C D hC hD).model
        (Sum.inl : C.Carrier → (withBoundarySum C D hC hD).Carrier) x v := rfl

theorem withBoundarySumInrTangentEquiv_apply (x : D.Carrier) (v : TangentSpace D.model x) :
    withBoundarySumInrTangentEquiv C D hC hD x v =
      mfderiv D.model (withBoundarySum C D hC hD).model
        (Sum.inr : D.Carrier → (withBoundarySum C D hC hD).Carrier) x v := rfl

theorem withBoundarySumInl_positive (x : C.Carrier) :
    Orientation.map (Fin 3) (withBoundarySumInlTangentEquiv C D hC hD x).toLinearEquiv
      (C.orientation.orientation x) =
        (withBoundarySum C D hC hD).orientation.orientation (Sum.inl x) := by
  have he : (withBoundarySumInlTangentEquiv C D hC hD x).toLinearEquiv =
      LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)) := by
    cases C with
    | mk k A O =>
      cases D with
      | mk l B O' =>
        cases hC
        cases hD
        ext v
        change mfderiv (𝓡∂ 3) (𝓡∂ 3) (@Sum.inl A B) x v = v
        rw [mfderiv_sumInl (p := (Sum.inl x : A ⊕ B))]
        rfl
  rw [he]
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)))
        (O.orientation x) = O.orientation x
      erw [Orientation.map_refl]
      rfl

theorem withBoundarySumInr_positive (x : D.Carrier) :
    Orientation.map (Fin 3) (withBoundarySumInrTangentEquiv C D hC hD x).toLinearEquiv
      (D.orientation.orientation x) =
        (withBoundarySum C D hC hD).orientation.orientation (Sum.inr x) := by
  have he : (withBoundarySumInrTangentEquiv C D hC hD x).toLinearEquiv =
      LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)) := by
    cases C with
    | mk k A O =>
      cases D with
      | mk l B O' =>
        cases hC
        cases hD
        ext v
        change mfderiv (𝓡∂ 3) (𝓡∂ 3) (@Sum.inr A B) x v = v
        rw [mfderiv_sumInr (q' := x)]
        rfl
  rw [he]
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)))
        (O'.orientation x) = O'.orientation x
      erw [Orientation.map_refl]
      rfl

theorem withBoundarySumLeft_positive [Nonempty C.Carrier] (x : C.Carrier) :
    ∃ L : TangentSpace C.model x ≃ₗ[ℝ]
      TangentSpace (withBoundarySum C D hC hD).model (withBoundarySumLeft C D hC hD x),
      (∀ v, L v = mfderiv C.model (withBoundarySum C D hC hD).model
        (withBoundarySumLeft C D hC hD) x v) ∧
      Orientation.map (Fin 3) L (C.orientation.orientation x) =
        (withBoundarySum C D hC hD).orientation.orientation (withBoundarySumLeft C D hC hD x) := by
  rw [withBoundarySumLeft_apply]
  refine ⟨(withBoundarySumInlTangentEquiv C D hC hD x).toLinearEquiv, ?_,
    withBoundarySumInl_positive C D hC hD x⟩
  intro v
  have he : (withBoundarySumLeft C D hC hD).toFun = Sum.inl :=
    funext (withBoundarySumLeft_apply C D hC hD)
  change withBoundarySumInlTangentEquiv C D hC hD x v =
    mfderiv C.model (withBoundarySum C D hC hD).model
      (withBoundarySumLeft C D hC hD).toFun x v
  rw [he]
  rfl

theorem withBoundarySumRight_positive [Nonempty D.Carrier] (x : D.Carrier) :
    ∃ L : TangentSpace D.model x ≃ₗ[ℝ]
      TangentSpace (withBoundarySum C D hC hD).model (withBoundarySumRight C D hC hD x),
      (∀ v, L v = mfderiv D.model (withBoundarySum C D hC hD).model
        (withBoundarySumRight C D hC hD) x v) ∧
      Orientation.map (Fin 3) L (D.orientation.orientation x) =
        (withBoundarySum C D hC hD).orientation.orientation (withBoundarySumRight C D hC hD x) := by
  rw [withBoundarySumRight_apply]
  refine ⟨(withBoundarySumInrTangentEquiv C D hC hD x).toLinearEquiv, ?_,
    withBoundarySumInr_positive C D hC hD x⟩
  intro v
  have he : (withBoundarySumRight C D hC hD).toFun = Sum.inr :=
    funext (withBoundarySumRight_apply C D hC hD)
  change withBoundarySumInrTangentEquiv C D hC hD x v =
    mfderiv D.model (withBoundarySum C D hC hD).model
      (withBoundarySumRight C D hC hD).toFun x v
  rw [he]
  rfl

theorem components_nonempty (DC : C.Components) : Nonempty C.Carrier := by
  let i : Fin DC.count := ⟨0, DC.count_pos⟩
  let := DC.connected i
  exact ⟨(Classical.choice (inferInstance : Nonempty (DC.piece i))).val⟩

def withBoundarySumPieceLeft (U : TopologicalSpace.Opens C.Carrier) :
    TopologicalSpace.Opens (withBoundarySum C D hC hD).Carrier :=
  ⟨Sum.inl '' (U : Set C.Carrier), isOpenMap_inl _ U.isOpen⟩

def withBoundarySumPieceRight (U : TopologicalSpace.Opens D.Carrier) :
    TopologicalSpace.Opens (withBoundarySum C D hC hD).Carrier :=
  ⟨Sum.inr '' (U : Set D.Carrier), isOpenMap_inr _ U.isOpen⟩

theorem withBoundarySumPieceLeft_interior (U : TopologicalSpace.Opens C.Carrier) :
    ((withBoundarySum C D hC hD).pieceInterior (withBoundarySumPieceLeft C D hC hD U) :
      Set (withBoundarySum C D hC hD).Carrier) =
        Sum.inl '' (C.pieceInterior U : Set C.Carrier) := by
  change (Sum.inl '' (U : Set C.Carrier)) ∩
    ((withBoundarySum C D hC hD).interior : Set (withBoundarySum C D hC hD).Carrier) = _
  rw [withBoundarySum_interior]
  ext x
  cases x <;> simp [Set.mem_image, pieceInterior]

theorem withBoundarySumPieceRight_interior (U : TopologicalSpace.Opens D.Carrier) :
    ((withBoundarySum C D hC hD).pieceInterior (withBoundarySumPieceRight C D hC hD U) :
      Set (withBoundarySum C D hC hD).Carrier) =
        Sum.inr '' (D.pieceInterior U : Set D.Carrier) := by
  change (Sum.inr '' (U : Set D.Carrier)) ∩
    ((withBoundarySum C D hC hD).interior : Set (withBoundarySum C D hC hD).Carrier) = _
  rw [withBoundarySum_interior]
  ext x
  cases x <;> simp [Set.mem_image, pieceInterior]

private def sumComponentPiece (DC : C.Components) (DD : D.Components) :
    Fin DC.count ⊕ Fin DD.count → TopologicalSpace.Opens (withBoundarySum C D hC hD).Carrier
  | Sum.inl i => withBoundarySumPieceLeft C D hC hD (DC.piece i)
  | Sum.inr j => withBoundarySumPieceRight C D hC hD (DD.piece j)

private theorem sumComponentPiece_closed (DC : C.Components) (DD : D.Components)
    (i : Fin DC.count ⊕ Fin DD.count) :
    IsClosed (sumComponentPiece C D hC hD DC DD i :
      Set (withBoundarySum C D hC hD).Carrier) := by
  cases i with
  | inl i => exact isClosedMap_inl _ (DC.closed i)
  | inr j => exact isClosedMap_inr _ (DD.closed j)

private theorem sumComponentPiece_connected (DC : C.Components) (DD : D.Components)
    (i : Fin DC.count ⊕ Fin DD.count) :
    ConnectedSpace (sumComponentPiece C D hC hD DC DD i) := by
  apply isConnected_iff_connectedSpace.mp
  cases i with
  | inl i =>
    exact (isConnected_iff_connectedSpace.mpr (DC.connected i)).image Sum.inl
      continuous_inl.continuousOn
  | inr j =>
    exact (isConnected_iff_connectedSpace.mpr (DD.connected j)).image Sum.inr
      continuous_inr.continuousOn

private theorem sumComponentPiece_interior_connected (DC : C.Components) (DD : D.Components)
    (i : Fin DC.count ⊕ Fin DD.count) :
    ConnectedSpace ((withBoundarySum C D hC hD).pieceInterior
      (sumComponentPiece C D hC hD DC DD i)) := by
  apply isConnected_iff_connectedSpace.mp
  cases i with
  | inl i =>
    change IsConnected (((withBoundarySum C D hC hD).pieceInterior
      (withBoundarySumPieceLeft C D hC hD (DC.piece i))) :
        Set (withBoundarySum C D hC hD).Carrier)
    rw [withBoundarySumPieceLeft_interior]
    exact (isConnected_iff_connectedSpace.mpr (DC.interior_connected i)).image Sum.inl
      continuous_inl.continuousOn
  | inr j =>
    change IsConnected (((withBoundarySum C D hC hD).pieceInterior
      (withBoundarySumPieceRight C D hC hD (DD.piece j))) :
        Set (withBoundarySum C D hC hD).Carrier)
    rw [withBoundarySumPieceRight_interior]
    exact (isConnected_iff_connectedSpace.mpr (DD.interior_connected j)).image Sum.inr
      continuous_inr.continuousOn

private theorem sumComponentPiece_disjoint (DC : C.Components) (DD : D.Components) :
    Pairwise fun i j => Disjoint
      (sumComponentPiece C D hC hD DC DD i : Set (withBoundarySum C D hC hD).Carrier)
      (sumComponentPiece C D hC hD DC DD j : Set (withBoundarySum C D hC hD).Carrier) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases i with
  | inl i =>
    obtain ⟨a, ha, rfl⟩ := hx
    cases j with
    | inl j =>
      obtain ⟨b, hb, heq⟩ := hy
      have hab : b = a := Sum.inl.inj heq
      exact (DC.disjoint (fun h => hij (congrArg Sum.inl h))).le_bot ⟨ha, hab ▸ hb⟩
    | inr j =>
      obtain ⟨b, hb, heq⟩ := hy
      exact Sum.inr_ne_inl heq
  | inr i =>
    obtain ⟨a, ha, rfl⟩ := hx
    cases j with
    | inl j =>
      obtain ⟨b, hb, heq⟩ := hy
      exact Sum.inl_ne_inr heq
    | inr j =>
      obtain ⟨b, hb, heq⟩ := hy
      have hab : b = a := Sum.inr.inj heq
      exact (DD.disjoint (fun h => hij (congrArg Sum.inr h))).le_bot ⟨ha, hab ▸ hb⟩

def withBoundarySumComponents (DC : C.Components) (DD : D.Components) :
    (withBoundarySum C D hC hD).Components where
  count := DC.count + DD.count
  count_pos := by have h := DC.count_pos; omega
  piece i := sumComponentPiece C D hC hD DC DD (finSumFinEquiv.symm i)
  closed i := sumComponentPiece_closed C D hC hD DC DD _
  connected i := sumComponentPiece_connected C D hC hD DC DD _
  disjoint i j hij := sumComponentPiece_disjoint C D hC hD DC DD
    (fun h => hij (finSumFinEquiv.symm.injective h))
  covers := by
    apply subset_antisymm (subset_univ _)
    intro x hx
    cases x with
    | inl x =>
      have hx' : x ∈ ⋃ i, (DC.piece i : Set C.Carrier) := by rw [DC.covers]; exact mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
      apply mem_iUnion.mpr
      refine ⟨finSumFinEquiv (.inl i), ?_⟩
      rw [Equiv.symm_apply_apply]
      exact ⟨x, hi, rfl⟩
    | inr x =>
      have hx' : x ∈ ⋃ i, (DD.piece i : Set D.Carrier) := by rw [DD.covers]; exact mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
      apply mem_iUnion.mpr
      refine ⟨finSumFinEquiv (.inr i), ?_⟩
      rw [Equiv.symm_apply_apply]
      exact ⟨x, hi, rfl⟩
  interior_connected i := sumComponentPiece_interior_connected C D hC hD DC DD _

theorem withBoundarySumComponents_count (DC : C.Components) (DD : D.Components) :
    (withBoundarySumComponents C D hC hD DC DD).count = DC.count + DD.count := rfl

theorem withBoundarySumComponents_piece_left (DC : C.Components) (DD : D.Components)
    (i : Fin DC.count) :
    ((withBoundarySumComponents C D hC hD DC DD).piece (finSumFinEquiv (.inl i)) :
      Set (withBoundarySum C D hC hD).Carrier) = Sum.inl '' (DC.piece i : Set C.Carrier) := by
  change (sumComponentPiece C D hC hD DC DD (finSumFinEquiv.symm
    (finSumFinEquiv (.inl i))) : Set (withBoundarySum C D hC hD).Carrier) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem withBoundarySumComponents_piece_right (DC : C.Components) (DD : D.Components)
    (j : Fin DD.count) :
    ((withBoundarySumComponents C D hC hD DC DD).piece (finSumFinEquiv (.inr j)) :
      Set (withBoundarySum C D hC hD).Carrier) = Sum.inr '' (DD.piece j : Set D.Carrier) := by
  change (sumComponentPiece C D hC hD DC DD (finSumFinEquiv.symm
    (finSumFinEquiv (.inr j))) : Set (withBoundarySum C D hC hD).Carrier) = _
  rw [Equiv.symm_apply_apply]
  rfl


theorem withBoundarySumComponents_mem_left (DC : C.Components) (DD : D.Components)
    (i : Fin DC.count) (x : C.Carrier) :
    Sum.inl x ∈ (withBoundarySumComponents C D hC hD DC DD).piece
      (finSumFinEquiv (.inl i)) ↔ x ∈ DC.piece i := by
  change Sum.inl x ∈ ((withBoundarySumComponents C D hC hD DC DD).piece
    (finSumFinEquiv (.inl i)) : Set (withBoundarySum C D hC hD).Carrier) ↔ _
  rw [withBoundarySumComponents_piece_left]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact Sum.inl.inj heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem withBoundarySumComponents_mem_right (DC : C.Components) (DD : D.Components)
    (j : Fin DD.count) (x : D.Carrier) :
    Sum.inr x ∈ (withBoundarySumComponents C D hC hD DC DD).piece
      (finSumFinEquiv (.inr j)) ↔ x ∈ DD.piece j := by
  change Sum.inr x ∈ ((withBoundarySumComponents C D hC hD DC DD).piece
    (finSumFinEquiv (.inr j)) : Set (withBoundarySum C D hC hD).Carrier) ↔ _
  rw [withBoundarySumComponents_piece_right]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact Sum.inr.inj heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem withBoundarySumComponents_inr_not_left (DC : C.Components) (DD : D.Components)
    (i : Fin DC.count) (x : D.Carrier) :
    Sum.inr x ∉ (withBoundarySumComponents C D hC hD DC DD).piece
      (finSumFinEquiv (.inl i)) := by
  change Sum.inr x ∉ ((withBoundarySumComponents C D hC hD DC DD).piece
    (finSumFinEquiv (.inl i)) : Set (withBoundarySum C D hC hD).Carrier)
  rw [withBoundarySumComponents_piece_left]
  rintro ⟨y, hy, heq⟩
  exact Sum.inl_ne_inr heq

theorem withBoundarySumComponents_inl_not_right (DC : C.Components) (DD : D.Components)
    (j : Fin DD.count) (x : C.Carrier) :
    Sum.inl x ∉ (withBoundarySumComponents C D hC hD DC DD).piece
      (finSumFinEquiv (.inr j)) := by
  change Sum.inl x ∉ ((withBoundarySumComponents C D hC hD DC DD).piece
    (finSumFinEquiv (.inr j)) : Set (withBoundarySum C D hC hD).Carrier)
  rw [withBoundarySumComponents_piece_right]
  rintro ⟨y, hy, heq⟩
  exact Sum.inr_ne_inl heq

end GC.Endpoint.CompactCarrier
