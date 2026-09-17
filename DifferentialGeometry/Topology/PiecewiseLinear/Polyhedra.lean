import DifferentialGeometry.Topology.PiecewiseLinear.Polytope
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsPolyhedron (P : Set E) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E), (∀ i, IsHPolytope (C i)) ∧ P = ⋃ i, C i

theorem IsHPolytope.isPolyhedron {C : Set E} (hC : IsHPolytope C) : IsPolyhedron C :=
  ⟨Unit, inferInstance, fun _ => C, fun _ => hC, (iUnion_const C).symm⟩

namespace IsPolyhedron

variable {P Q : Set E}

theorem isCompact (hP : IsPolyhedron P) : IsCompact P := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  have := hι
  exact isCompact_iUnion fun i => (hC i).isCompact

theorem isClosed (hP : IsPolyhedron P) : IsClosed P := hP.isCompact.isClosed

theorem empty : IsPolyhedron (∅ : Set E) :=
  ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, by simp⟩

theorem union (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) : IsPolyhedron (P ∪ Q) := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hQ
  have := hι
  have := hκ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim C D, fun i => ?_, ?_⟩
  · cases i <;> simp [hC, hD]
  · rw [iUnion_sum]
    simp

theorem iUnion {ι : Type*} [Finite ι] {P : ι → Set E} (hP : ∀ i, IsPolyhedron (P i)) :
    IsPolyhedron (⋃ i, P i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  choose κ hκ C hC hP using hP
  have : ∀ i, Finite (κ i) := hκ
  refine ⟨Σ k : Fin n, κ (e.symm k), inferInstance, fun p => C (e.symm p.1) p.2,
    fun p => hC _ _, ?_⟩
  rw [iUnion_sigma]
  simp_rw [← hP]
  exact (e.symm.surjective.iUnion_comp P).symm

theorem finsetBiUnion {ι : Type*} (t : Finset ι) {P : ι → Set E} (hP : ∀ i, IsPolyhedron (P i)) :
    IsPolyhedron (⋃ i ∈ t, P i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using IsPolyhedron.empty
  | insert j t hj ih =>
    rw [Finset.set_biUnion_insert]
    exact (hP j).union ih

theorem prod {P : Set E} {Q : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ×ˢ Q) := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hQ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ×ˢ D p.2,
    fun p => (hC p.1).prod (hD p.2), ?_⟩
  ext p
  simp only [Set.mem_prod, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨(i, j), hi, hj⟩
  · rintro ⟨⟨i, j⟩, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

theorem inter (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) : IsPolyhedron (P ∩ Q) := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hQ
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ∩ D p.2, fun p => (hC p.1).inter (hD p.2), ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iUnion, Prod.exists]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨i, j, hi, hj⟩
  · rintro ⟨i, j, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

theorem image_affineEquiv [FiniteDimensional ℝ E] (hP : IsPolyhedron P) (T : E ≃ᵃ[ℝ] F) :
    IsPolyhedron (T '' P) := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  have := hι
  exact ⟨ι, inferInstance, fun i => T '' C i, fun i => (hC i).image_affineEquiv T, image_iUnion⟩

theorem inter_preimage [FiniteDimensional ℝ E] (hP : IsPolyhedron P) {Q : Set F}
    (hQ : IsPolyhedron Q) (A : E →ᵃ[ℝ] F) : IsPolyhedron (P ∩ A ⁻¹' Q) := by
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hQ
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ∩ A ⁻¹' D p.2,
    fun p => (hC p.1).inter_preimage (hD p.2) A, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iUnion, mem_preimage, Prod.exists]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨i, j, hi, hj⟩
  · rintro ⟨i, j, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

end IsPolyhedron

theorem mem_convexHull_image_affineBasis_iff {ι : Type*} [Finite ι] (b : AffineBasis ι ℝ E)
    (S : Finset ι) {x : E} :
    x ∈ convexHull ℝ (b '' (S : Set ι)) ↔
      (∀ i, 0 ≤ b.coord i x) ∧ ∀ i, i ∉ S → b.coord i x = 0 := by
  classical
  cases nonempty_fintype ι
  constructor
  · intro hx
    rw [← Finset.coe_image, Finset.mem_convexHull] at hx
    obtain ⟨w, hw₀, hw₁, rfl⟩ := hx
    have hinj : Function.Injective b := b.ind.injective
    have hsum : ∑ i ∈ S, (w ∘ b) i = 1 := by
      rw [← hw₁, Finset.sum_image fun x _ y _ h => hinj h]
      rfl
    have hcm : (S.image b).centerMass w id = S.affineCombination ℝ b (w ∘ b) := by
      rw [Finset.centerMass_eq_of_sum_1 (S.image b) id hw₁,
        Finset.affineCombination_eq_linear_combination _ _ _ hsum,
        Finset.sum_image fun x _ y _ h => hinj h]
      rfl
    rw [hcm]
    refine ⟨fun i => ?_, fun i hi => b.coord_apply_combination_of_notMem hi hsum⟩
    by_cases hi : i ∈ S
    · rw [b.coord_apply_combination_of_mem hi hsum]
      exact hw₀ _ (Finset.mem_image_of_mem b hi)
    · rw [b.coord_apply_combination_of_notMem hi hsum]
  · rintro ⟨h0, hS⟩
    have hsum : ∑ i ∈ S, b.coord i x = 1 := by
      rw [← b.sum_coord_apply_eq_one x]
      exact Finset.sum_subset (Finset.subset_univ S) fun i _ hi => hS i hi
    have hind : (S : Set ι).indicator (fun i => b.coord i x) = fun i => b.coord i x := by
      funext i
      by_cases hi : i ∈ S
      · rw [indicator_of_mem (Finset.mem_coe.mpr hi)]
      · rw [indicator_of_notMem (fun h => hi (Finset.mem_coe.mp h)), hS i hi]
    have hx : S.affineCombination ℝ b (fun i => b.coord i x) = x := by
      rw [Finset.affineCombination_indicator_subset _ _ (Finset.subset_univ S), hind,
        b.affineCombination_coord_eq_self]
    have hmem : S.centerMass (fun i => b.coord i x) b ∈ convexHull ℝ (b '' (S : Set ι)) :=
      Finset.centerMass_mem_convexHull S (fun i _ => h0 i) (by rw [hsum]; exact one_pos)
        fun i hi => mem_image_of_mem b (Finset.mem_coe.mpr hi)
    rw [Finset.centerMass_eq_of_sum_1 S b hsum] at hmem
    rw [← hx, Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    exact hmem

theorem isHPolytope_convexHull_of_affineIndependent [FiniteDimensional ℝ E] (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) : IsHPolytope (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨t, hst, hti, htop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  have htf : t.Finite := finite_set_of_fin_dim_affineIndependent ℝ hti
  have : Finite t := htf.to_subtype
  let : Fintype t := Fintype.ofFinite t
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin t
  let b : AffineBasis t ℝ E := ⟨((↑) : t → E), hti, by rw [Subtype.range_coe]; exact htop⟩
  let S : Finset t := Finset.univ.filter fun i : t => (i : E) ∈ s
  have hmemS : ∀ i : t, i ∈ S ↔ (i : E) ∈ s := fun i => by simp [S]
  have himage : b '' (S : Set t) = (s : Set E) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (hmemS i).mp (Finset.mem_coe.mp hi)
    · intro hy
      exact ⟨⟨y, hst hy⟩, Finset.mem_coe.mpr ((hmemS _).mpr hy), rfl⟩
  have hcoord : ∀ (i : t) (y : E), b.coord i y = (b.coord i).linear y + b.coord i 0 :=
    fun i y => by simpa using (b.coord i).map_vadd 0 y
  refine ⟨s.finite_toSet.isCompact_convexHull ℝ, Fin m ⊕ Fin m, inferInstance,
    Sum.elim (fun j => -(b.coord (e.symm j)).linear)
      (fun j => if ((e.symm j : t) : E) ∈ s then 0 else (b.coord (e.symm j)).linear),
    Sum.elim (fun j => b.coord (e.symm j) 0)
      (fun j => if ((e.symm j : t) : E) ∈ s then 0 else -(b.coord (e.symm j) 0)), ?_⟩
  ext x
  rw [← himage, mem_convexHull_image_affineBasis_iff]
  simp only [mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr, LinearMap.neg_apply]
  constructor
  · rintro ⟨h0, hS⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := h0 (e.symm j)
      rw [hcoord] at this
      linarith
    · by_cases hj : ((e.symm j : t) : E) ∈ s
      · rw [if_pos hj, if_pos hj]
        simp
      · have := hS (e.symm j) (fun h => hj ((hmemS _).mp h))
        rw [hcoord] at this
        rw [if_neg hj, if_neg hj]
        linarith
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · have := h1 (e i)
      rw [Equiv.symm_apply_apply] at this
      rw [hcoord]
      linarith
    · have hi' : (i : E) ∉ s := fun h => hi ((hmemS i).mpr h)
      have h2i := h2 (e i)
      rw [Equiv.symm_apply_apply, if_neg hi', if_neg hi'] at h2i
      have h1i := h1 (e i)
      rw [Equiv.symm_apply_apply] at h1i
      rw [hcoord]
      linarith

theorem isPolyhedron_convexHull_of_affineIndependent [FiniteDimensional ℝ E] (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) : IsPolyhedron (convexHull ℝ (s : Set E)) :=
  (isHPolytope_convexHull_of_affineIndependent s hs).isPolyhedron

theorem isPolyhedron_space [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] : IsPolyhedron K.space := by
  have h : K.space = ⋃ s : K.faces, convexHull ℝ ((s : Finset E) : Set E) := by
    rw [Geometry.SimplicialComplex.space, biUnion_eq_iUnion]
  rw [h]
  exact IsPolyhedron.iUnion fun s =>
    isPolyhedron_convexHull_of_affineIndependent _ (K.indep s.2)

end DifferentialGeometry.Topology.PiecewiseLinear
