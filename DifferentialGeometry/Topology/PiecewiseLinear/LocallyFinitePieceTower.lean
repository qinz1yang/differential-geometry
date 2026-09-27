import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifold
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
structure LocallyFinitePieceTower (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (U : Set X) where
  N : ℕ → Set X
  piece : ∀ i, PLPiece n X (N i)
  subset_nhdsWithin : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[U] x
  iUnion_eq : ⋃ i, N i = U
  core : ∀ i, Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (piece i).ambientDim))
  core_le : ∀ i, (core i).faces ⊆ (piece i).piece.complex.faces
  subset_core : ∀ i, N i ⊆ (piece (i + 1)).piece.map '' (core (i + 1)).space
  coreImage : ∀ i,
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (piece (i + 1)).ambientDim))
  coreImage_le : ∀ i, (coreImage i).faces ⊆ (core (i + 1)).faces
  embed : ∀ i, EuclideanSpace ℝ (Fin (piece i).ambientDim) →
    EuclideanSpace ℝ (Fin (piece (i + 1)).ambientDim)
  embedInv : ∀ i, EuclideanSpace ℝ (Fin (piece (i + 1)).ambientDim) →
    EuclideanSpace ℝ (Fin (piece i).ambientDim)
  embed_isGlueIso : ∀ i, IsGlueIso (core i) (coreImage i) (embed i) (embedInv i)
  map_embed : ∀ i, ∀ x ∈ (core i).space,
    (piece (i + 1)).piece.map (simplicialMap (core i) (embed i) x) = (piece i).piece.map x

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}

namespace LocallyFinitePieceTower

variable (T : LocallyFinitePieceTower n X U)

def coreSpace (i : ℕ) : Set X := (T.piece i).piece.map '' (T.core i).space

theorem subset (i : ℕ) : T.N i ⊆ U :=
  (subset_iUnion T.N i).trans T.iUnion_eq.subset

theorem core_space_subset (i : ℕ) : T.coreSpace i ⊆ T.N i := by
  rintro x ⟨y, hy, rfl⟩
  exact (T.piece i).piece.bijOn.mapsTo (space_mono_of_faces_subset (T.core_le i) hy)

theorem core_space_subset_union (i : ℕ) : T.coreSpace i ⊆ U :=
  (T.core_space_subset i).trans (T.subset i)

theorem monotone : Monotone T.N :=
  monotone_nat_of_le_succ fun i => (T.subset_core i).trans (T.core_space_subset (i + 1))

theorem core_space_monotone : Monotone T.coreSpace :=
  monotone_nat_of_le_succ fun i => (T.core_space_subset i).trans (T.subset_core i)

theorem iUnion_core_space : ⋃ i, T.coreSpace i = U := by
  apply Subset.antisymm
  · exact iUnion_subset T.core_space_subset_union
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (T.iUnion_eq.symm ▸ hx)
    exact mem_iUnion.mpr ⟨i + 1, T.subset_core i hi⟩

theorem exists_mem_core_space {x : X} (hx : x ∈ U) : ∃ i, x ∈ T.coreSpace i :=
  mem_iUnion.mp (T.iUnion_core_space.symm ▸ hx)

theorem core_faces_finite (i : ℕ) : (T.core i).faces.Finite :=
  (T.piece i).piece.finite_faces.subset (T.core_le i)

theorem coreImage_faces_finite (i : ℕ) : (T.coreImage i).faces.Finite :=
  (T.core_faces_finite (i + 1)).subset (T.coreImage_le i)

theorem isCompact (i : ℕ) : IsCompact (T.N i) := (T.piece i).piece.isCompact

theorem isCompact_core_space (i : ℕ) : IsCompact (T.coreSpace i) :=
  ((T.piece i).piece.restrict (T.core i) (T.core_le i)).isCompact

open Classical in
theorem embed_isPLHomeomorphOn (i : ℕ) :
    IsPLHomeomorphOn (simplicialMap (T.core i) (T.embed i))
      (T.core i).space (T.coreImage i).space := by
  have := (T.core_faces_finite i).to_subtype
  have := (T.coreImage_faces_finite i).to_subtype
  exact (T.embed_isGlueIso i).isPLHomeomorphOn

open Classical in
theorem embed_mapsTo_core (i : ℕ) :
    MapsTo (simplicialMap (T.core i) (T.embed i)) (T.core i).space (T.core (i + 1)).space :=
  fun _ hx => space_mono_of_faces_subset (T.coreImage_le i)
    ((T.embed_isGlueIso i).mapsTo_left hx)

theorem core_space_mem_nhdsWithin {i : ℕ} {x : X} (hx : x ∈ T.N i) :
    T.coreSpace (i + 2) ∈ 𝓝[U] x :=
  Filter.mem_of_superset (T.subset_nhdsWithin i x hx) (T.subset_core (i + 1))

theorem subset_interior (hU : IsOpen U) (i : ℕ) : T.N i ⊆ interior (T.N (i + 1)) := by
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  have h := T.subset_nhdsWithin i x hx
  rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds (T.subset i hx))] at h

theorem exists_core_of_isCompact {C : Set X} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ i, C ⊆ (T.piece i).piece.map '' (T.core i).space := by
  classical
  let O : ℕ → Set X := fun i => interior (T.N (i + 1) ∪ Uᶜ)
  have hO (i : ℕ) : T.N i ⊆ O i := by
    intro x hx
    obtain ⟨V, hV, hVN⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (T.subset_nhdsWithin i x hx)
    apply mem_interior_iff_mem_nhds.mpr
    refine Filter.mem_of_superset hV fun y hy => ?_
    by_cases hyU : y ∈ U
    · exact Or.inl (hVN ⟨hy, hyU⟩)
    · exact Or.inr hyU
  have hcover : C ⊆ ⋃ i, O i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (T.iUnion_eq.symm ▸ hCU hx)
    exact mem_iUnion.mpr ⟨i, hO i hi⟩
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover O (fun _ => isOpen_interior) hcover
  refine ⟨s.sup id + 2, fun x hx => T.subset_core (s.sup id + 1) ?_⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  rcases interior_subset hxi with hxi | hxi
  · exact T.monotone (Nat.add_le_add_right (Finset.le_sup hi) 1) hxi
  · exact (hxi (hCU hx)).elim

theorem core_space_eventually {C : Set X} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∀ᶠ i in Filter.atTop, C ⊆ T.coreSpace i := by
  obtain ⟨i, hi⟩ := T.exists_core_of_isCompact hC hCU
  exact Filter.eventually_atTop.mpr ⟨i, fun j hij => hi.trans (T.core_space_monotone hij)⟩

theorem exists_glue_of_eqOn {Y : Type*} (f : ℕ → X → Y)
    (hf : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) :
    ∃ g : U → Y, ∀ i, ∀ x (hx : x ∈ T.coreSpace i),
      g ⟨x, T.core_space_subset_union i hx⟩ = f i x := by
  classical
  have hmono {i j : ℕ} (hij : i ≤ j) : EqOn (f j) (f i) (T.coreSpace i) := by
    induction j, hij using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ j hij ih =>
      intro x hx
      exact (hf j (T.core_space_monotone hij hx)).trans (ih hx)
  refine ⟨fun x => f (Nat.find (T.exists_mem_core_space x.property)) x, ?_⟩
  intro i x hx
  have hle := Nat.find_min' (T.exists_mem_core_space (T.core_space_subset_union i hx)) hx
  exact (hmono hle (Nat.find_spec
    (T.exists_mem_core_space (T.core_space_subset_union i hx)))).symm

open Classical in
theorem exists_glue {Y : Type*}
    (f : ∀ i, EuclideanSpace ℝ (Fin (T.piece i).ambientDim) → Y)
    (hf : ∀ i, ∀ x ∈ (T.core i).space,
      f (i + 1) (simplicialMap (T.core i) (T.embed i) x) = f i x) :
    ∃ g : U → Y, ∀ i, ∀ x (hx : x ∈ (T.core i).space),
      g ⟨(T.piece i).piece.map x, T.core_space_subset_union i ⟨x, hx, rfl⟩⟩ = f i x := by
  let a (i : ℕ) := Function.invFunOn (T.piece i).piece.map (T.piece i).piece.complex.space
  have ha (i : ℕ) {x} (hx : x ∈ (T.core i).space) : a i ((T.piece i).piece.map x) = x :=
    (T.piece i).piece.bijOn.injOn.leftInvOn_invFunOn (space_mono_of_faces_subset (T.core_le i) hx)
  have hfa (i : ℕ) : EqOn (f (i + 1) ∘ a (i + 1)) (f i ∘ a i) (T.coreSpace i) := by
    rintro y ⟨x, hx, rfl⟩
    change f (i + 1) (a (i + 1) ((T.piece i).piece.map x)) = f i (a i ((T.piece i).piece.map x))
    rw [ha i hx, ← T.map_embed i x hx, ha (i + 1) (T.embed_mapsTo_core i hx)]
    exact hf i x hx
  obtain ⟨g, hg⟩ := T.exists_glue_of_eqOn (fun i => f i ∘ a i) hfa
  refine ⟨g, fun i x hx => ?_⟩
  exact (hg i _ ⟨x, hx, rfl⟩).trans (congrArg (f i) (ha i hx))

open Classical in
def ofPiece (P : PLPiece n X U) : LocallyFinitePieceTower n X U where
  N := fun _ => U
  piece := fun _ => P
  subset_nhdsWithin := fun _ _ _ => self_mem_nhdsWithin
  iUnion_eq := iUnion_const _
  core := fun _ => P.piece.complex
  core_le := fun _ => Subset.refl _
  subset_core := fun _ => P.piece.bijOn.image_eq.symm.subset
  coreImage := fun _ => P.piece.complex
  coreImage_le := fun _ => Subset.refl _
  embed := fun _ => id
  embedInv := fun _ => id
  embed_isGlueIso := fun _ => ⟨fun s hs => by simpa using hs,
    fun s hs => by simpa using hs, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  map_embed := by
    intro i x hx
    exact congrArg P.piece.map (simplicialMap_eq_of_forall_affineOn P.piece.complex id
      (fun _ _ => ⟨AffineMap.id ℝ _, fun _ _ => rfl⟩) hx)

end LocallyFinitePieceTower

open Classical in
def IsLocallyFinitePolyhedralManifoldWithBoundary (m : ℕ) (U : Set X) : Prop :=
  ∃ T : LocallyFinitePieceTower n X U,
    ∀ i, IsCombinatorialManifoldWithBoundary m (T.piece i).piece.complex

open Classical in
theorem IsPolyhedralManifoldWithBoundary.isLocallyFinite {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n) m P) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m P := by
  obtain ⟨T, hT⟩ := hP
  exact ⟨LocallyFinitePieceTower.ofPiece T, fun _ => hT⟩

open Classical in
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.isPolyhedralManifoldWithBoundary
    {m : ℕ} {P : Set X} (hP : IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) m P)
    (hPc : IsCompact P) : IsPolyhedralManifoldWithBoundary (n := n) m P := by
  obtain ⟨T, hT⟩ := hP
  obtain ⟨i, hi⟩ := T.exists_core_of_isCompact hPc (Subset.refl P)
  have heq : T.N i = P := Subset.antisymm (T.subset i) (hi.trans (T.core_space_subset i))
  exact heq ▸ (show IsPolyhedralManifoldWithBoundary (n := n) m (T.N i) from ⟨T.piece i, hT i⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
