import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanMembrane
import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexEngulfingChart
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.PolyhedralIntersection
import DifferentialGeometry.Topology.SimplicialComplex.Expansion.ElementaryCollapse
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.FinitePolyhedra

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology
open scoped ContinuousMap BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def simplexBoundary (v : ι → E) : Set E := ⋃ i, simplexFacet v i

omit [DecidableEq ι] [Fintype ι] in
theorem simplexFacet_subset_convexHull [Finite ι] (v : ι → E) (i : ι) :
    simplexFacet v i ⊆ convexHull ℝ (range v) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact convexHull_mono (image_subset_range _ _)

omit [DecidableEq ι] [Fintype ι] in
theorem simplexBoundary_subset_convexHull [Finite ι] (v : ι → E) :
    simplexBoundary v ⊆ convexHull ℝ (range v) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact iUnion_subset (simplexFacet_subset_convexHull v)

omit [DecidableEq ι] [Fintype ι] in
theorem isCompact_simplexBoundary [Finite ι] (v : ι → E) : IsCompact (simplexBoundary v) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact isCompact_iUnion (fun i => ((toFinite ({i}ᶜ : Set ι)).image v).isCompact_convexHull ℝ)

def simplexHullHomeomorph (v : ι → E) (hv : AffineIndependent ℝ v) :
    standardBarycentricSimplex ι ≃ₜ convexHull ℝ (range v) := by
  let f : standardBarycentricSimplex ι → convexHull ℝ (range v) := fun x =>
    ⟨simplexPoint v x, (simplexPoint_image_simplex v) ▸ mem_image_of_mem _ x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (simplexPoint_injective_on_hyperplane v hv x.2.2 y.2.2
      (congrArg Subtype.val hxy))
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y.1 ∈ simplexPoint v '' standardBarycentricSimplex ι := by
      rw [simplexPoint_image_simplex]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let : CompactSpace (standardBarycentricSimplex ι) :=
    isCompact_iff_compactSpace.mp isCompact_standardBarycentricSimplex
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩)
    (((continuous_simplexPoint v).comp continuous_subtype_val).subtype_mk _)

omit [DecidableEq ι] in
@[simp] theorem simplexHullHomeomorph_apply (v : ι → E) (hv : AffineIndependent ℝ v)
    (x : standardBarycentricSimplex ι) :
    (simplexHullHomeomorph v hv x).1 = simplexPoint v x := by
  classical
  exact rfl

omit [DecidableEq ι] in
theorem simplexPoint_mem_boundary_iff (v : ι → E) (hv : AffineIndependent ℝ v)
    (x : standardBarycentricSimplex ι) :
    simplexPoint v x ∈ simplexBoundary v ↔ ∃ i, x.1 i = 0 := by
  classical
  simp only [simplexBoundary, mem_iUnion]
  exact exists_congr (fun i => simplexPoint_mem_facet_iff v hv x.2 i)

omit [DecidableEq ι] in
theorem affineBasis_coord_simplexPoint (b : AffineBasis ι ℝ E)
    (x : standardBarycentricSimplex ι) (i : ι) : b.coord i (simplexPoint b x) = x.1 i := by
  classical
  rw [simplexPoint, ← Finset.affineCombination_eq_linear_combination _ _ _ x.2.2]
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) x.2.2

omit [DecidableEq ι] [Fintype ι] in
theorem affineBasis_frontier_eq_simplexBoundary [Finite ι] (b : AffineBasis ι ℝ E) :
    frontier (convexHull ℝ (range b)) = simplexBoundary b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hclosed := ((finite_range b).isCompact_convexHull ℝ).isClosed
  ext y
  by_cases hy : y ∈ convexHull ℝ (range b)
  · obtain ⟨x, hx⟩ := (simplexHullHomeomorph b b.ind).surjective ⟨y, hy⟩
    have hxy : simplexPoint b x = y := congrArg Subtype.val hx
    rw [← hxy, simplexPoint_mem_boundary_iff b b.ind x]
    rw [frontier, hclosed.closure_eq, mem_sdiff, b.interior_convexHull]
    have hmem : simplexPoint b x ∈ convexHull ℝ (range b) :=
      (simplexHullHomeomorph b b.ind x).2
    simp only [hmem, true_and, mem_ofPred_eq, affineBasis_coord_simplexPoint]
    push Not
    exact exists_congr (fun i => ⟨fun hi => le_antisymm hi (x.2.1 i), fun hi => hi.le⟩)
  · have hn : y ∉ simplexBoundary b := fun h => hy (simplexBoundary_subset_convexHull b h)
    have hn' : y ∉ frontier (convexHull ℝ (range b)) := fun h =>
      hy (hclosed.closure_eq ▸ frontier_subset_closure h)
    simp [hn, hn']

omit [DecidableEq ι] in
theorem exists_simplex_disk_parameterization_of_card {q : ℕ}
    (v : ι → E) (hv : AffineIndependent ℝ v) (hcard : Fintype.card ι = q + 1) :
    ∃ e : Disk q ≃ₜ convexHull ℝ (range v),
      ∀ x, x ∈ diskSphere q ↔ (e x).1 ∈ simplexBoundary v := by
  classical
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (k := ℝ) (V := EuclideanSpace ℝ (Fin q)) (P := EuclideanSpace ℝ (Fin q))
    (ι := ι) (by simpa using hcard)
  obtain ⟨d, hd⟩ := exists_disk_homeomorph_convex_body
    ((finite_range b).isCompact_convexHull ℝ) (convex_convexHull ℝ _)
    ⟨_, b.centroid_mem_interior_convexHull⟩
  let h := (simplexHullHomeomorph b b.ind).symm.trans (simplexHullHomeomorph v hv)
  refine ⟨d.trans h, fun x => ?_⟩
  rw [hd, affineBasis_frontier_eq_simplexBoundary]
  let w := (simplexHullHomeomorph b b.ind).symm (d x)
  have hw : simplexPoint b w = (d x).1 :=
    congrArg Subtype.val ((simplexHullHomeomorph b b.ind).apply_symm_apply (d x))
  change (d x).1 ∈ simplexBoundary b ↔ simplexPoint v w ∈ simplexBoundary v
  rw [← hw, simplexPoint_mem_boundary_iff b b.ind w, simplexPoint_mem_boundary_iff v hv w]

theorem exists_simplex_disk_parameterization {q : ℕ}
    (v : Fin (q + 1) → E) (hv : AffineIndependent ℝ v) :
    ∃ e : Disk q ≃ₜ convexHull ℝ (range v),
      ∀ x, x ∈ diskSphere q ↔ (e x).1 ∈ simplexBoundary v :=
  exists_simplex_disk_parameterization_of_card v hv (by simp)

omit [DecidableEq ι] in
theorem exists_simplex_boundary_extension_of_card {q : ℕ} {M : Type*} [TopologicalSpace M]
    (v : ι → E) (hv : AffineIndependent ℝ v) (hcard : Fintype.card ι = q + 2)
    (f : C(simplexBoundary v, M))
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, M), b.Nullhomotopic) :
    ∃ F : C(convexHull ℝ (range v), M), ∀ x : simplexBoundary v,
      F ⟨x.1, simplexBoundary_subset_convexHull v x.2⟩ = f x := by
  classical
  obtain ⟨e, he⟩ := exists_simplex_disk_parameterization_of_card v hv hcard
  let a : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, M) :=
    ⟨fun s => f ⟨(e (sphereToDisk (q + 1) s)).1,
        (he _).mp s.2⟩,
      f.continuous.comp ((continuous_subtype_val.comp
        (e.continuous.comp (sphereToDisk (q + 1)).continuous)).subtype_mk _)⟩
  obtain ⟨G, hG⟩ := exists_disk_extension_of_nullhomotopic a (hM a)
  refine ⟨G.comp ⟨e.symm, e.symm.continuous⟩, fun x => ?_⟩
  let y : convexHull ℝ (range v) := ⟨x.1, simplexBoundary_subset_convexHull v x.2⟩
  have hy : e.symm y ∈ diskSphere (q + 1) :=
    (he _).mpr (by simpa only [e.apply_symm_apply] using x.2)
  have h := hG ⟨e.symm y, hy⟩
  change G (e.symm y) = f x
  rw [h]
  change f ⟨(e (e.symm y)).1, _⟩ = f x
  congr 1
  exact Subtype.ext (congrArg (fun z : convexHull ℝ (range v) => z.1) (e.apply_symm_apply y))

theorem exists_simplex_boundary_extension {q : ℕ} {M : Type*} [TopologicalSpace M]
    (v : Fin (q + 2) → E) (hv : AffineIndependent ℝ v)
    (f : C(simplexBoundary v, M))
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, M), b.Nullhomotopic) :
    ∃ F : C(convexHull ℝ (range v), M), ∀ x : simplexBoundary v,
      F ⟨x.1, simplexBoundary_subset_convexHull v x.2⟩ = f x :=
  exists_simplex_boundary_extension_of_card v hv (by simp) f hM

omit [Fintype ι] in
theorem convexHull_image_inter_of_independent [Finite ι] (v : ι → E) (hv : AffineIndependent ℝ v)
    (s t : Finset ι) :
    convexHull ℝ (v '' (s : Set ι)) ∩ convexHull ℝ (v '' (t : Set ι)) =
      convexHull ℝ (v '' ((s ∩ t : Finset ι) : Set ι)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hv' : AffineIndependent ℝ ((↑) : ↑(Finset.univ.image v) → E) := by
    have h := hv.range
    have heq : range v = (Finset.univ.image v : Set E) := by simp
    rw [heq] at h
    exact h
  have h := hv'.convexHull_inter
    (Finset.image_subset_image (Finset.subset_univ s))
    (Finset.image_subset_image (Finset.subset_univ t))
  simpa only [Finset.coe_inter, Finset.coe_image, ← image_inter hv.injective] using h.symm

def facetVertices (v : ι → E) (a : ι) : {i : ι // i ≠ a} → E := fun i => v i.1

omit [DecidableEq ι] [Fintype ι] in
theorem convexHull_facetVertices [Finite ι] (v : ι → E) (a : ι) :
    convexHull ℝ (range (facetVertices v a)) = simplexFacet v a := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [simplexFacet, image_eq_range]
  rfl

omit [DecidableEq ι] [Fintype ι] in
theorem facetVertices_independent [Finite ι] (v : ι → E) (hv : AffineIndependent ℝ v) (a : ι) :
    AffineIndependent ℝ (facetVertices v a) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact hv.comp_embedding (.subtype _)

omit [DecidableEq ι] [Fintype ι] in
theorem simplexFacet_facetVertices [Finite ι] (v : ι → E) (hv : AffineIndependent ℝ v) (a : ι)
    (j : {i : ι // i ≠ a}) :
    simplexFacet (facetVertices v a) j = simplexFacet v a ∩ simplexFacet v j.1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have h := convexHull_image_inter_of_independent v hv (Finset.univ.erase a)
    (Finset.univ.erase j.1)
  have hsets : facetVertices v a '' ({j}ᶜ : Set {i : ι // i ≠ a}) =
      v '' (((Finset.univ.erase a) ∩ (Finset.univ.erase j.1) : Finset ι) : Set ι) := by
    ext x
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, Finset.mem_coe,
      Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true, Subtype.exists,
      facetVertices]
    constructor
    · rintro ⟨i, hi, hji, rfl⟩
      exact ⟨i, ⟨hi, fun h => hji (Subtype.ext h)⟩, rfl⟩
    · rintro ⟨i, ⟨hia, hij⟩, rfl⟩
      exact ⟨i, hia, fun h => hij (congrArg Subtype.val h), rfl⟩
  rw [simplexFacet, hsets, ← h]
  congr 1 <;> congr 1 <;> ext i <;> simp

namespace SimplexSplit

def upperRoof (s : SimplexSplit ι) (v : ι → E) : Set E :=
  ⋃ i ∈ s.left, simplexFacet v i

theorem lowerRoof_subset_simplex (s : SimplexSplit ι) (v : ι → E) :
    s.lowerRoof v ⊆ convexHull ℝ (range v) :=
  iUnion_subset (fun i => iUnion_subset (fun _ => simplexFacet_subset_convexHull v i))

theorem upperRoof_subset_simplex (s : SimplexSplit ι) (v : ι → E) :
    s.upperRoof v ⊆ convexHull ℝ (range v) :=
  iUnion_subset (fun i => iUnion_subset (fun _ => simplexFacet_subset_convexHull v i))

theorem lowerRoof_union_upperRoof (s : SimplexSplit ι) (v : ι → E) :
    s.lowerRoof v ∪ s.upperRoof v = simplexBoundary v := by
  ext x
  simp only [lowerRoof, upperRoof, simplexBoundary, mem_union, mem_iUnion]
  constructor
  · rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;> exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    by_cases hl : i ∈ s.left
    · exact Or.inr ⟨i, hl, hi⟩
    · exact Or.inl ⟨i, Finset.mem_compl.mpr hl, hi⟩

def roofReflection (s : SimplexSplit ι) (v : ι → E) (hv : AffineIndependent ℝ v) : E ≃ₜ E := by
  let e := s.ambientPrismHomeomorph v hv
  let a : (simplexTransverse v × s.horizontal) → ℝ := fun z => s.lower z.2 + s.upper z.2
  have ha : Continuous a :=
    (s.continuous_lower.comp (continuous_subtype_val.comp continuous_snd)).add
      (s.continuous_upper.comp (continuous_subtype_val.comp continuous_snd))
  let r : ((simplexTransverse v × s.horizontal) × ℝ) ≃ₜ
      ((simplexTransverse v × s.horizontal) × ℝ) :=
    { toFun := fun p => (p.1, a p.1 - p.2)
      invFun := fun p => (p.1, a p.1 - p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp
      continuous_toFun := continuous_fst.prodMk ((ha.comp continuous_fst).sub continuous_snd)
      continuous_invFun := continuous_fst.prodMk ((ha.comp continuous_fst).sub continuous_snd) }
  exact (e.trans r).trans e.symm

theorem roofReflection_coordinates (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) (x : E) :
    s.ambientPrismHomeomorph v hv (s.roofReflection v hv x) =
      ((s.ambientPrismHomeomorph v hv x).1,
        s.lower (s.ambientPrismHomeomorph v hv x).1.2 +
        s.upper (s.ambientPrismHomeomorph v hv x).1.2 -
        (s.ambientPrismHomeomorph v hv x).2) := by
  simp [roofReflection]

theorem roofReflection_mem_simplex (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {x : E} (hx : x ∈ convexHull ℝ (range v)) :
    s.roofReflection v hv x ∈ convexHull ℝ (range v) := by
  obtain ⟨hz, hl, hu⟩ := (s.ambientPrismHomeomorph_simplex_iff v hv x).mp hx
  rw [s.ambientPrismHomeomorph_simplex_iff v hv _, s.roofReflection_coordinates]
  exact ⟨hz, by dsimp; linarith, by dsimp; linarith⟩

theorem roofReflection_mem_upperRoof_iff (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {x : E} (hx : x ∈ convexHull ℝ (range v)) :
    s.roofReflection v hv x ∈ s.upperRoof v ↔ x ∈ s.lowerRoof v := by
  have h₁ := s.ambientPrismHomeomorph_upper_graph_iff v hv (s.roofReflection_mem_simplex v hv hx)
  have h₂ := s.ambientPrismHomeomorph_lower_graph_iff v hv hx
  simp only [upperRoof, lowerRoof, mem_iUnion, exists_prop]
  rw [← h₁, ← h₂, s.roofReflection_coordinates]
  dsimp
  constructor <;> intro h <;> linarith

theorem roofReflection_eq_self_of_mem_both (s : SimplexSplit ι) (v : ι → E)
    (hv : AffineIndependent ℝ v) {x : E} (hl : x ∈ s.lowerRoof v) (hu : x ∈ s.upperRoof v) :
    s.roofReflection v hv x = x := by
  have hx := s.lowerRoof_subset_simplex v hl
  have h₁ := (s.ambientPrismHomeomorph_lower_graph_iff v hv hx).mpr (by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hl
    exact ⟨i, hi, hxi⟩)
  have h₂ := (s.ambientPrismHomeomorph_upper_graph_iff v hv hx).mpr (by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hu
    exact ⟨i, hi, hxi⟩)
  apply (s.ambientPrismHomeomorph v hv).injective
  rw [s.roofReflection_coordinates]
  apply Prod.ext
  · rfl
  · dsimp
    linarith

end SimplexSplit

def coneSplit [Nontrivial ι] (a : ι) : SimplexSplit ι where
  left := {a}
  left_nonempty := Finset.singleton_nonempty a
  right_nonempty := by
    obtain ⟨b, hb⟩ := exists_ne a
    exact ⟨b, by simpa using hb⟩

theorem coneSplit_upperRoof [Nontrivial ι] (v : ι → E) (a : ι) :
    (coneSplit a).upperRoof v = simplexFacet v a := by
  ext x
  simp [SimplexSplit.upperRoof, coneSplit]

theorem facet_boundary_eq_inter_roof [Nontrivial ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (a : ι) :
    simplexBoundary (facetVertices v a) = simplexFacet v a ∩ (coneSplit a).lowerRoof v := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    rw [simplexFacet_facetVertices v hv a j] at hj
    refine ⟨hj.1, mem_iUnion₂.mpr ⟨j.1, ?_, hj.2⟩⟩
    simpa [coneSplit, SimplexSplit.right] using j.2
  · rintro ⟨hxa, hx⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
    have hja : j ≠ a := by simpa [coneSplit, SimplexSplit.right] using hj
    apply mem_iUnion.mpr
    refine ⟨⟨j, hja⟩, ?_⟩
    rw [simplexFacet_facetVertices v hv a]
    exact ⟨hxa, hxj⟩

omit [DecidableEq ι] [Fintype ι] in
theorem isCompact_simplexFacet [Finite ι] (v : ι → E) (a : ι) : IsCompact (simplexFacet v a) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  exact ((toFinite ({a}ᶜ : Set ι)).image v).isCompact_convexHull ℝ

theorem SimplexSplit.isCompact_lowerRoof (s : SimplexSplit ι) (v : ι → E) :
    IsCompact (s.lowerRoof v) :=
  s.right.finite_toSet.isCompact_biUnion (fun i _ => isCompact_simplexFacet v i)

theorem exists_continuousMap_compact_union {X M : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace M]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (f : C(A, M)) (g : C(B, M))
    (hfg : ∀ (x : X) (hxA : x ∈ A) (hxB : x ∈ B), f ⟨x, hxA⟩ = g ⟨x, hxB⟩) :
    ∃ F : C(↥(A ∪ B), M),
      (∀ x : A, F ⟨x.1, Or.inl x.2⟩ = f x) ∧
      (∀ x : B, F ⟨x.1, Or.inr x.2⟩ = g x) := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let q : C(A ⊕ B, ↥(A ∪ B)) :=
    ⟨Sum.elim (fun x => ⟨x.1, Or.inl x.2⟩) (fun x => ⟨x.1, Or.inr x.2⟩),
      (continuous_subtype_val.subtype_mk _).sumElim (continuous_subtype_val.subtype_mk _)⟩
  have hqs : Function.Surjective q := by
    intro x
    rcases x.2 with hx | hx
    · exact ⟨Sum.inl ⟨x.1, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x.1, hx⟩, rfl⟩
  have hq : IsQuotientMap q := .of_surjective_continuous hqs q.continuous
  let a : C(A ⊕ B, M) := ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩
  have ha : Function.FactorsThrough a q := by
    intro x y hxy
    have hval := congrArg (fun z : ↥(A ∪ B) => z.1) hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg f (Subtype.ext hval)
    · change f x = g y
      have hyB : x.1 ∈ B := hval ▸ y.2
      exact (hfg x.1 x.2 hyB).trans (congrArg g (Subtype.ext hval))
    · change g x = f y
      have hyA : x.1 ∈ A := hval ▸ y.2
      exact (hfg x.1 hyA x.2).symm.trans (congrArg f (Subtype.ext hval))
    · exact congrArg g (Subtype.ext hval)
  refine ⟨hq.lift a ha, fun x => ?_, fun x => ?_⟩
  · exact congrArg (fun c => c (Sum.inl x)) (hq.lift_comp a ha)
  · exact congrArg (fun c => c (Sum.inr x)) (hq.lift_comp a ha)

theorem exists_affine_cone_membrane {q : ℕ} {M : Type*} [TopologicalSpace M]
    (v : Fin (q + 3) → E) (hv : AffineIndependent ℝ v) (a : Fin (q + 3))
    (U : Set M) (f : C(simplexFacet v a, M))
    (hboundary : ∀ x : simplexFacet v a, x.1 ∈ (coneSplit a).lowerRoof v → f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 2))) 1, M), b.Nullhomotopic) :
    ∃ F : C(convexHull ℝ (range v), M),
      (∀ x : simplexFacet v a, F ⟨x.1, simplexFacet_subset_convexHull v a x.2⟩ = f x) ∧
      (∀ x : (coneSplit a).lowerRoof v,
        F ⟨x.1, (coneSplit a).lowerRoof_subset_simplex v x.2⟩ ∈ U) := by
  let w := facetVertices v a
  let s := coneSplit a
  have : Nonempty {i : Fin (q + 3) // i ≠ a} := by
    obtain ⟨i, hi⟩ := exists_ne a
    exact ⟨⟨i, hi⟩⟩
  have hcard : Fintype.card {i : Fin (q + 3) // i ≠ a} = q + 2 := by
    simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
    omega
  have hwb : simplexBoundary w = simplexFacet v a ∩ s.lowerRoof v :=
    facet_boundary_eq_inter_roof v hv a
  have hwh : convexHull ℝ (range w) = simplexFacet v a := convexHull_facetVertices v a
  have hbmem (x : simplexBoundary w) : x.1 ∈ simplexFacet v a ∩ s.lowerRoof v := by
    rw [← hwb]
    exact x.2
  let b : C(simplexBoundary w, U) :=
    ⟨fun x => ⟨f ⟨x.1, (hbmem x).1⟩,
        hboundary ⟨x.1, (hbmem x).1⟩ (hbmem x).2⟩,
      (f.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  obtain ⟨g, hg⟩ := exists_simplex_boundary_extension_of_card w
    (facetVertices_independent v hv a) hcard b hU
  let g' : C(simplexFacet v a, U) :=
    g.comp ⟨fun x => ⟨x.1, hwh.symm ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hg' (x : E) (hx : x ∈ simplexFacet v a) (hr : x ∈ s.lowerRoof v) :
      (g' ⟨x, hx⟩ : M) = f ⟨x, hx⟩ := by
    have hxb : x ∈ simplexBoundary w := hwb.symm ▸ (show x ∈ simplexFacet v a ∩ s.lowerRoof v
      from ⟨hx, hr⟩)
    exact congrArg (fun z : U => (z : M)) (hg ⟨x, hxb⟩)
  have hr (x : E) (hx : x ∈ s.lowerRoof v) : s.roofReflection v hv x ∈ simplexFacet v a := by
    rw [← coneSplit_upperRoof v a]
    exact (s.roofReflection_mem_upperRoof_iff v hv (s.lowerRoof_subset_simplex v hx)).mpr hx
  let r : C(s.lowerRoof v, M) :=
    ⟨fun x => g' ⟨s.roofReflection v hv x.1, hr x.1 x.2⟩,
      continuous_subtype_val.comp (g'.continuous.comp
        (((s.roofReflection v hv).continuous.comp continuous_subtype_val).subtype_mk _))⟩
  obtain ⟨c, hc₀, hc₁⟩ := exists_continuousMap_compact_union
    (isCompact_simplexFacet v a) (s.isCompact_lowerRoof v) f r (by
      intro x hx hxR
      have hxU : x ∈ s.upperRoof v := (coneSplit_upperRoof v a).symm ▸ hx
      have hfix := s.roofReflection_eq_self_of_mem_both v hv hxR hxU
      calc
        f ⟨x, hx⟩ = (g' ⟨x, hx⟩ : M) := (hg' x hx hxR).symm
        _ = r ⟨x, hxR⟩ := by
          change (g' ⟨x, hx⟩ : M) = (g' ⟨s.roofReflection v hv x, _⟩ : M)
          congr 2
          exact Subtype.ext hfix.symm)
  have hcov : simplexFacet v a ∪ s.lowerRoof v = simplexBoundary v := by
    rw [← coneSplit_upperRoof v a, union_comm]
    exact s.lowerRoof_union_upperRoof v
  let d : C(simplexBoundary v, M) :=
    c.comp ⟨fun x => ⟨x.1, hcov.symm ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  obtain ⟨F, hF⟩ := exists_simplex_boundary_extension v hv d hM
  refine ⟨F, fun x => ?_, fun x => ?_⟩
  · have hx : x.1 ∈ simplexBoundary v := hcov ▸ (show x.1 ∈ simplexFacet v a ∪ s.lowerRoof v
      from Or.inl x.2)
    exact (hF ⟨x.1, hx⟩).trans (hc₀ x)
  · have hx : x.1 ∈ simplexBoundary v := hcov ▸ (show x.1 ∈ simplexFacet v a ∪ s.lowerRoof v
      from Or.inr x.2)
    rw [hF ⟨x.1, hx⟩]
    change c ⟨x.1, _⟩ ∈ U
    rw [hc₁ x]
    exact (g' ⟨s.roofReflection v hv x.1, hr x.1 x.2⟩).2

theorem exists_affine_cone_membrane_glue {q : ℕ} {M : Type*} [TopologicalSpace M]
    (v : Fin (q + 3) → E) (hv : AffineIndependent ℝ v) (a : Fin (q + 3))
    {A : Set E} (hA : IsCompact A)
    (hattach : A ∩ convexHull ℝ (range v) = simplexFacet v a)
    (U : Set M) (f : C(A, M))
    (hboundary : ∀ x : A, x.1 ∈ simplexBoundary (facetVertices v a) → f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 2))) 1, M), b.Nullhomotopic) :
    ∃ F : C(↥(A ∪ convexHull ℝ (range v)), M),
      (∀ x : A, F ⟨x.1, Or.inl x.2⟩ = f x) ∧
      (∀ x : (coneSplit a).lowerRoof v,
        F ⟨x.1, Or.inr ((coneSplit a).lowerRoof_subset_simplex v x.2)⟩ ∈ U) := by
  have hfa : simplexFacet v a ⊆ A := by
    rw [← hattach]
    exact inter_subset_left
  let b : C(simplexFacet v a, M) :=
    f.comp ⟨fun x => ⟨x.1, hfa x.2⟩, continuous_subtype_val.subtype_mk _⟩
  obtain ⟨G, hGb, hGr⟩ := exists_affine_cone_membrane v hv a U b (by
    intro x hx
    apply hboundary ⟨x.1, hfa x.2⟩
    rw [facet_boundary_eq_inter_roof v hv a]
    exact ⟨x.2, hx⟩) hU hM
  obtain ⟨F, hF₀, hF₁⟩ := exists_continuousMap_compact_union hA
    ((finite_range v).isCompact_convexHull ℝ) f G (by
      intro x hxA hxS
      have hxB : x ∈ simplexFacet v a := hattach ▸ (show x ∈ A ∩ convexHull ℝ (range v)
        from ⟨hxA, hxS⟩)
      exact (hGb ⟨x, hxB⟩).symm)
  refine ⟨F, hF₀, fun x => ?_⟩
  rw [hF₁ ⟨x.1, (coneSplit a).lowerRoof_subset_simplex v x.2⟩]
  exact hGr x

variable [DecidableEq E]

omit [DecidableEq ι] in
theorem convexHull_erase_vertex_image (v : ι → E) (hv : AffineIndependent ℝ v) (i : ι) :
    convexHull ℝ (((Finset.univ.image v).erase (v i) : Finset E) : Set E) =
      simplexFacet v i := by
  classical
  apply congrArg (convexHull ℝ)
  rw [Finset.coe_erase, Finset.coe_image, Finset.coe_univ, image_univ]
  rw [← image_univ, ← image_singleton, ← image_sdiff hv.injective]
  rw [← compl_eq_univ_sdiff]

omit [DecidableEq ι] in
theorem simplexRoof_image_vertices (v : ι → E) (hv : AffineIndependent ℝ v) (B : Finset ι) :
    simplexRoof (Finset.univ.image v) (B.image v) = ⋃ i ∈ B, simplexFacet v i := by
  classical
  ext x
  simp only [simplexRoof, mem_iUnion, exists_prop, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, hi, (convexHull_erase_vertex_image v hv i) ▸ hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨v i, ⟨i, hi, rfl⟩, (convexHull_erase_vertex_image v hv i).symm ▸ hx⟩

theorem SimplexSplit.finiteSimplexExpansion_roof (s : SimplexSplit ι)
    (v : ι → E) (hv : AffineIndependent ℝ v) :
    FiniteSimplexExpansion (s.lowerRoof v) (convexHull ℝ (range v)) := by
  classical
  have hv' : AffineIndependent ℝ ((↑) : ↑(Finset.univ.image v) → E) := by
    have h := hv.range
    have heq : range v = (Finset.univ.image v : Set E) := by simp
    rw [heq] at h
    exact h
  have hB : ProperSimplexRoof (Finset.univ.image v) (s.right.image v) := by
    refine ⟨Finset.image_subset_image (Finset.subset_univ _), s.right_nonempty.image v, ?_⟩
    obtain ⟨i, hi⟩ := s.left_nonempty
    refine ⟨v i, Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩⟩
    intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    have heq := hv.injective hji
    subst j
    exact (Finset.mem_compl.mp hj) hi
  have h := FiniteSimplexExpansion.simplex_of_properRoof hv' hB
  rw [simplexRoof_image_vertices v hv, Finset.coe_image, Finset.coe_univ, image_univ] at h
  exact h

omit [DecidableEq E] in
theorem exists_finite_complex_adjoin_simplex {q d : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (v : Fin (q + 3) → E) :
    ∃ T J : Geometry.SimplicialComplex ℝ E,
      T.faces.Finite ∧ T.space = K.space ∪ convexHull ℝ (range v) ∧
      (∀ s ∈ T.faces, s.card ≤ max d (q + 2) + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ T.faces ∧ J.space = K.space ∧ simplicialRefines J K := by
  classical
  let : Fintype K.faces := hK.fintype
  let V : K.faces ⊕ Unit → Finset E :=
    Sum.elim (fun s => s.1) (fun _ => Finset.univ.image v)
  obtain ⟨T₀, hT₀, hspace₀, hparent⟩ := exists_complex_finite_convexHulls V
  have hnew : convexHull ℝ (V (Sum.inr ()) : Set E) = convexHull ℝ (range v) := by
    simp only [V, Sum.elim_inr, Finset.coe_image, Finset.coe_univ, image_univ]
  have hspace : T₀.space = K.space ∪ convexHull ℝ (range v) := by
    rw [hspace₀]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases i with s | u
      · exact Or.inl (K.convexHull_subset_space s.2 hi)
      · cases u
        exact Or.inr (hnew ▸ hi)
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
        exact mem_iUnion.mpr ⟨Sum.inl ⟨s, hs⟩, hxs⟩
      · exact mem_iUnion.mpr ⟨Sum.inr (), hnew.symm ▸ hx⟩
  have hdim : ∀ s ∈ T₀.faces, s.card ≤ max d (q + 2) + 1 := by
    intro s hs
    obtain ⟨i, hi⟩ := hparent s hs
    have hcard := (T₀.indep hs).card_le_card_of_subset_affineSpan
      (fun x hx => convexHull_subset_affineSpan _ (hi (subset_convexHull ℝ _ hx)))
    apply hcard.trans
    rcases i with t | u
    · exact (hd t.1 t.2).trans (Nat.add_le_add_right (le_max_left _ _) 1)
    · change (Finset.univ.image v).card ≤ _
      exact Finset.card_image_le.trans (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨T, J, hT, hTS, -, hdimT, hJ, hJT, hJS, hJref⟩ :=
    exists_subdivision_containing_complex T₀ K hT₀ hK
      (hspace.symm ▸ (subset_union_left : K.space ⊆ K.space ∪ convexHull ℝ (range v))) hdim
  exact ⟨T, J, hT, hTS.trans hspace, hdimT, hJ, hJT, hJS, hJref⟩

omit [DecidableEq E] in
theorem exists_affine_cone_membrane_on_finite_complex {q d : ℕ}
    {M : Type*} [TopologicalSpace M]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (v : Fin (q + 3) → E) (hv : AffineIndependent ℝ v) (a : Fin (q + 3))
    (hattach : K.space ∩ convexHull ℝ (range v) = simplexFacet v a)
    (U : Set M) (f : C(K.space, M))
    (hboundary : ∀ x : K.space, x.1 ∈ simplexBoundary (facetVertices v a) → f x ∈ U)
    (hU : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1, U), b.Nullhomotopic)
    (hM : ∀ b : C(sphere (0 : EuclideanSpace ℝ (Fin (q + 2))) 1, M), b.Nullhomotopic) :
    ∃ T J : Geometry.SimplicialComplex ℝ E,
      T.faces.Finite ∧ (∀ s ∈ T.faces, s.card ≤ max d (q + 2) + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ T.faces ∧ J.space = K.space ∧ simplicialRefines J K ∧
      ∃ (hspace : T.space = K.space ∪ convexHull ℝ (range v)) (F : C(T.space, M)),
        (∀ x : K.space, F ⟨x.1, hspace.symm ▸ (show x.1 ∈ K.space ∪ convexHull ℝ (range v)
          from Or.inl x.2)⟩ = f x) ∧
        (∀ x : (coneSplit a).lowerRoof v,
          F ⟨x.1, hspace.symm ▸ (show x.1 ∈ K.space ∪ convexHull ℝ (range v)
            from Or.inr ((coneSplit a).lowerRoof_subset_simplex v x.2))⟩ ∈ U) := by
  classical
  obtain ⟨G, hG₀, hG₁⟩ := exists_affine_cone_membrane_glue v hv a
    (hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ))
    hattach U f hboundary hU hM
  obtain ⟨T, J, hT, hspace, hdim, hJ, hJT, hJS, hJref⟩ :=
    exists_finite_complex_adjoin_simplex K hK hd v
  let F : C(T.space, M) := G.comp
    ⟨fun x => ⟨x.1, hspace ▸ x.2⟩, continuous_subtype_val.subtype_mk _⟩
  exact ⟨T, J, hT, hdim, hJ, hJT, hJS, hJref, hspace, F, hG₀, hG₁⟩

end

end DifferentialGeometry.Topology.Engulfing
