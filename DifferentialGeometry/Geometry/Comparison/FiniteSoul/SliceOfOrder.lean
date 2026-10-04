import DifferentialGeometry.Geometry.Comparison.Soul.SliceTangent
import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

/-!
# Finite-order embedded slices (S3-SLICE definitions of the package CM-S-three)

Lane CMS3-SLICE, design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §1. The
definitions are the frozen texts of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean` §1:

* `IsEmbeddedSliceOfOrder I k d S`: `S` is covered by `C^k` partial diffeomorphisms of the ambient
  carrier onto open sets of `E` carrying `S` onto a `d`-dimensional affine subspace (the `C^k`
  submanifold notion shared with lane W-SUB); `IsEmbeddedSlice I d S` is definitionally the case
  `k = ∞` (`isEmbeddedSliceOfOrder_top_iff`);
* `sliceDimsOfOrder`, `maxSliceDimOfOrder`, `maxSliceLocusOfOrder` (the relative interior: union of the
  top-dimensional `C^k` slices inside `C`), `relBoundaryOfOrder`;
* `IsTotallyGeodesicFinite g Z`: geodesics of the finite-order metric `g` with initial vector in
  `sliceTangent I Z x` stay in `Z` for a short time, in both directions.

Elementary closure properties of order-`k` slices (restriction of the order, open subsets, images under
partial diffeomorphisms, germs, points, open sets, full dimension) and the existence of a top slice
inside a nonempty set are proved here; the analytic part (IFT, cones, the relative interior of a
totally convex set) is in later files of the lane.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section SliceDefs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **S3-SLICE, the `C^k` submanifold notion** (aligned with lane W-SUB): `S` is covered by `C^k` partial
diffeomorphisms of the ambient carrier onto open sets of `E` that carry `S` onto a `d`-dimensional affine
subspace. `IsEmbeddedSlice I d S` (smooth suite) is definitionally `IsEmbeddedSliceOfOrder I ∞ d S`. -/
def IsEmbeddedSliceOfOrder (I : ModelWithCorners ℝ E H) (k : WithTop ℕ∞) (d : ℕ) (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (A : AffineSubspace ℝ E),
    FiniteDimensional ℝ A.direction ∧ x ∈ c.source ∧
      Module.finrank ℝ A.direction = d ∧ c.toPartialEquiv.IsImage S (A : Set E)

/-- Dimensions of the nonempty `C^k` slices contained in `C`. -/
def sliceDimsOfOrder (I : ModelWithCorners ℝ E H) (k : WithTop ℕ∞) (C : Set M) : Set ℕ :=
  {d | ∃ S : Set M, S.Nonempty ∧ S ⊆ C ∧ IsEmbeddedSliceOfOrder I k d S}

/-- The relative dimension of `C` (finite analogue of the smooth `maxSliceDim`). -/
def maxSliceDimOfOrder (I : ModelWithCorners ℝ E H) (k : WithTop ℕ∞) (C : Set M) : ℕ :=
  sSup (sliceDimsOfOrder I k C)

/-- The relative interior: the union of the top-dimensional `C^k` slices contained in `C`. -/
def maxSliceLocusOfOrder (I : ModelWithCorners ℝ E H) (k : WithTop ℕ∞) (C : Set M) : Set M :=
  {x | ∃ S : Set M, x ∈ S ∧ S ⊆ C ∧ IsEmbeddedSliceOfOrder I k (maxSliceDimOfOrder I k C) S}

/-- The relative boundary `C \ relint C`. -/
def relBoundaryOfOrder (I : ModelWithCorners ℝ E H) (k : WithTop ℕ∞) (C : Set M) : Set M :=
  C \ maxSliceLocusOfOrder I k C

example (d : ℕ) (S : Set M) (h : IsEmbeddedSlice I d S) : IsEmbeddedSliceOfOrder I ∞ d S := h

/-- The smooth slices are exactly the slices of order `∞`. -/
theorem isEmbeddedSliceOfOrder_top_iff {d : ℕ} {S : Set M} :
    IsEmbeddedSliceOfOrder I ∞ d S ↔ IsEmbeddedSlice I d S :=
  Iff.rfl

/-- Restriction of a partial diffeomorphism to an open set (local helper). -/
private def restrictChart {k : WithTop ℕ∞} (c : PartialDiffeomorph I 𝓘(ℝ, E) M E k) (U : Set M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E k where
  __ := c.toOpenPartialHomeomorph.restr U
  contMDiffOn_toFun := c.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := c.contMDiffOn_invFun.mono inter_subset_left

namespace IsEmbeddedSliceOfOrder

variable {k : WithTop ℕ∞} {d : ℕ} {S : Set M}

/-- A slice of order `k` is a slice of every lower order. -/
theorem of_le {k' : WithTop ℕ∞} (hS : IsEmbeddedSliceOfOrder I k d S) (h : k' ≤ k) :
    IsEmbeddedSliceOfOrder I k' d S := by
  intro x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  exact ⟨DifferentialGeometry.PartialDiffeomorph.ofLE c h, A, hA, hxc, hdim, himage⟩

/-- A smooth slice is a slice of every order `k ≤ ∞`. -/
theorem of_isEmbeddedSlice {k : ℕ∞} (hS : IsEmbeddedSlice I d S) :
    IsEmbeddedSliceOfOrder I (k : WithTop ℕ∞) d S :=
  of_le (k := ∞) hS (by exact_mod_cast le_top)

/-- An affine subspace of the model space is a slice of every order. -/
theorem of_affineSubspace (A : AffineSubspace ℝ E) [FiniteDimensional ℝ A.direction] :
    IsEmbeddedSliceOfOrder 𝓘(ℝ, E) k (Module.finrank ℝ A.direction) (A : Set E) := by
  intro x _
  exact ⟨(Diffeomorph.refl 𝓘(ℝ, E) E k).toPartialDiffeomorph, A, inferInstance, mem_univ x, rfl,
    fun _ _ => Iff.rfl⟩

/-- The intersection of a slice with an open set is a slice. -/
theorem inter_open {U : Set M} (hS : IsEmbeddedSliceOfOrder I k d S) (hU : IsOpen U) :
    IsEmbeddedSliceOfOrder I k d (S ∩ U) := by
  intro x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx.1
  refine ⟨restrictChart c U, A, hA, ⟨hxc, ?_⟩, hdim, ?_⟩
  · rw [hU.interior_eq]
    exact hx.2
  · intro y hy
    change c y ∈ (A : Set E) ↔ y ∈ S ∩ U
    have hyU : y ∈ U := interior_subset hy.2
    simpa only [mem_inter_iff, hyU, and_true] using himage.apply_mem_iff hy.1

/-- The image of a slice under a partial diffeomorphism of the same order is a slice. -/
theorem image {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (hS : IsEmbeddedSliceOfOrder I k d S) (f : PartialDiffeomorph I J M N k)
    (hsub : S ⊆ f.source) : IsEmbeddedSliceOfOrder J k d (f '' S) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hS x hx
  refine ⟨f.symm.trans c, A, hA, ?_, hdim, ?_⟩
  · refine ⟨f.map_source' (hsub hx), ?_⟩
    change f.toPartialEquiv.symm (f.toPartialEquiv x) ∈ c.source
    rw [f.toPartialEquiv.left_inv (hsub hx)]
    exact hxc
  · intro z hz
    change c (f.symm z) ∈ (A : Set E) ↔ z ∈ f '' S
    have hzc : f.toPartialEquiv.symm z ∈ c.source := hz.2
    constructor
    · intro h
      exact ⟨f.symm z, (himage.apply_mem_iff hzc).1 h, f.toPartialEquiv.right_inv hz.1⟩
    · rintro ⟨w, hw, rfl⟩
      apply (himage.apply_mem_iff hzc).2
      rw [f.toPartialEquiv.left_inv (hsub hw)]
      exact hw

/-- A set that agrees near each of its points with some slice is a slice. -/
theorem of_germ
    (h : ∀ x ∈ S, ∃ N U : Set M, IsEmbeddedSliceOfOrder I k d N ∧ IsOpen U ∧
      x ∈ U ∧ x ∈ N ∧ U ∩ S = U ∩ N) : IsEmbeddedSliceOfOrder I k d S := by
  intro x hx
  obtain ⟨N, U, hN, hU, hxU, hxN, heq⟩ := h x hx
  obtain ⟨c, A, hA, hxc, hdim, himage⟩ := hN x hxN
  refine ⟨restrictChart c U, A, hA, ⟨hxc, ?_⟩, hdim, ?_⟩
  · rwa [hU.interior_eq]
  · intro y hy
    change c y ∈ (A : Set E) ↔ y ∈ S
    have hyU : y ∈ U := interior_subset hy.2
    have he : y ∈ S ↔ y ∈ N := by
      simpa only [mem_inter_iff, hyU, true_and] using Set.ext_iff.1 heq y
    exact (himage.apply_mem_iff hy.1).trans he.symm

/-- The dimension of a nonempty slice is at most the dimension of the model. -/
theorem dim_le [FiniteDimensional ℝ E] (hS : IsEmbeddedSliceOfOrder I k d S) (hne : S.Nonempty) :
    d ≤ Module.finrank ℝ E := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨c, A, -, -, hdim, -⟩ := hS x hx
  rw [← hdim]
  exact A.direction.finrank_le

/-- A full-dimensional slice is open. -/
theorem isOpen [FiniteDimensional ℝ E] (hS : IsEmbeddedSliceOfOrder I k (Module.finrank ℝ E) S) :
    IsOpen S := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨c, A, -, hxc, hdim, himage⟩ := hS x hx
  have hxA : c x ∈ A := (himage.apply_mem_iff hxc).2 hx
  have hdir : A.direction = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  have htop : A = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨c x, hxA⟩).1 hdir
  apply Filter.mem_of_superset (c.open_source.mem_nhds hxc)
  intro y hy
  apply (himage.apply_mem_iff hy).1
  rw [htop]
  exact AffineSubspace.mem_top ℝ E (c y)

/-- A slice is locally closed. -/
theorem isLocallyClosed (hS : IsEmbeddedSliceOfOrder I k d S) : IsLocallyClosed S := by
  apply isLocallyClosed_iff_isLocallyClosedAt.mpr
  intro x hx
  apply isLocallyClosedAt_iff_exists_isClosed_preimage_val.mpr
  obtain ⟨c, A, hA, hxc, -, himage⟩ := hS x hx
  let : FiniteDimensional ℝ A.direction := hA
  refine ⟨c.source, c.open_source.mem_nhds hxc, ?_⟩
  have heq : (Subtype.val : c.source → M) ⁻¹' S =
      (c.source.domRestrict (c : M → E)) ⁻¹' (A : Set E) := by
    ext y
    exact (himage.apply_mem_iff y.property).symm
  rw [heq]
  exact A.closed_of_finiteDimensional.preimage c.contMDiffOn_toFun.continuousOn.domRestrict

section Chart

variable [I.Boundaryless] [IsManifold I ∞ M]

/-- A point is a `0`-dimensional slice of every order `k ≤ ∞`. -/
theorem singleton {k : ℕ∞} (x : M) : IsEmbeddedSliceOfOrder I (k : WithTop ℕ∞) 0 ({x} : Set M) := by
  intro y hy
  have hyx : y = x := hy
  subst y
  let c : PartialDiffeomorph I 𝓘(ℝ, E) M E (k : WithTop ℕ∞) :=
    DifferentialGeometry.PartialDiffeomorph.ofLE
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ x) (by exact_mod_cast le_top)
  let A := AffineSubspace.mk' (c x) (⊥ : Submodule ℝ E)
  have hx : x ∈ c.source := mem_extChartAt_source x
  refine ⟨c, A, ?_, hx, ?_, ?_⟩
  · dsimp [A]
    rw [AffineSubspace.direction_mk']
    infer_instance
  · rw [AffineSubspace.direction_mk', finrank_bot]
  · intro y hy
    change c y ∈ AffineSubspace.mk' (c x) (⊥ : Submodule ℝ E) ↔ y ∈ ({x} : Set M)
    rw [AffineSubspace.mem_mk', Submodule.mem_bot, vsub_eq_zero_iff_eq, mem_singleton_iff]
    exact ⟨c.toPartialEquiv.injOn hy hx, congrArg c⟩

/-- An open set is a full-dimensional slice of every order `k ≤ ∞`. -/
theorem of_isOpen [FiniteDimensional ℝ E] {k : ℕ∞} (hS : IsOpen S) :
    IsEmbeddedSliceOfOrder I (k : WithTop ℕ∞) (Module.finrank ℝ E) S := by
  intro x hx
  let c : PartialDiffeomorph I 𝓘(ℝ, E) M E (k : WithTop ℕ∞) :=
    DifferentialGeometry.PartialDiffeomorph.ofLE
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ x) (by exact_mod_cast le_top)
  refine ⟨restrictChart c S, ⊤, inferInstance, ⟨mem_extChartAt_source x, ?_⟩, ?_, ?_⟩
  · rwa [hS.interior_eq]
  · rw [AffineSubspace.direction_top, finrank_top]
  · intro y hy
    exact ⟨fun _ => interior_subset hy.2, fun _ => AffineSubspace.mem_top ℝ E _⟩

end Chart

end IsEmbeddedSliceOfOrder

section MaxSlice

variable [FiniteDimensional ℝ E] {k : WithTop ℕ∞}

omit [FiniteDimensional ℝ E] in
theorem maxSliceLocusOfOrder_subset {C : Set M} : maxSliceLocusOfOrder I k C ⊆ C := by
  rintro x ⟨S, hx, hsub, -⟩
  exact hsub hx

omit [FiniteDimensional ℝ E] in
/-- A slice of the top dimension inside `C` lies in the relative interior. -/
theorem subset_maxSliceLocusOfOrder {C S : Set M} (hSC : S ⊆ C)
    (hS : IsEmbeddedSliceOfOrder I k (maxSliceDimOfOrder I k C) S) :
    S ⊆ maxSliceLocusOfOrder I k C :=
  fun _ hx => ⟨S, hx, hSC, hS⟩

theorem sliceDimsOfOrder_bddAbove (C : Set M) : BddAbove (sliceDimsOfOrder I k C) := by
  refine ⟨Module.finrank ℝ E, ?_⟩
  rintro d ⟨S, hne, -, hS⟩
  exact hS.dim_le hne

theorem le_maxSliceDimOfOrder {C : Set M} {d : ℕ} (hd : d ∈ sliceDimsOfOrder I k C) :
    d ≤ maxSliceDimOfOrder I k C :=
  le_csSup (sliceDimsOfOrder_bddAbove (I := I) C) hd

theorem maxSliceDimOfOrder_le (C : Set M) : maxSliceDimOfOrder I k C ≤ Module.finrank ℝ E := by
  apply csSup_le'
  rintro d ⟨S, hne, -, hS⟩
  exact hS.dim_le hne

theorem maxSliceDimOfOrder_mono {C D : Set M} (h : C ⊆ D) :
    maxSliceDimOfOrder I k C ≤ maxSliceDimOfOrder I k D := by
  apply csSup_le' (fun d hd => ?_)
  obtain ⟨S, hne, hSC, hS⟩ := hd
  exact le_maxSliceDimOfOrder (I := I) ⟨S, hne, hSC.trans h, hS⟩

section Chart

variable [I.Boundaryless] [IsManifold I ∞ M] {k : ℕ∞}

omit [FiniteDimensional ℝ E] in
theorem sliceDimsOfOrder_nonempty {C : Set M} (hC : C.Nonempty) :
    (sliceDimsOfOrder I (k : WithTop ℕ∞) C).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  exact ⟨0, {x}, singleton_nonempty x, singleton_subset_iff.2 hx,
    IsEmbeddedSliceOfOrder.singleton x⟩

/-- A nonempty set contains a nonempty slice of its relative dimension. -/
theorem exists_maxSliceOfOrder {C : Set M} (hC : C.Nonempty) :
    ∃ S : Set M, S.Nonempty ∧ S ⊆ C ∧
      IsEmbeddedSliceOfOrder I (k : WithTop ℕ∞) (maxSliceDimOfOrder I (k : WithTop ℕ∞) C) S :=
  Nat.sSup_mem (sliceDimsOfOrder_nonempty (I := I) hC) (sliceDimsOfOrder_bddAbove (I := I) C)

theorem maxSliceLocusOfOrder_nonempty {C : Set M} (hC : C.Nonempty) :
    (maxSliceLocusOfOrder I (k : WithTop ℕ∞) C).Nonempty := by
  obtain ⟨S, ⟨x, hx⟩, hsub, hS⟩ := exists_maxSliceOfOrder (I := I) (k := k) hC
  exact ⟨x, S, hx, hsub, hS⟩

end Chart

end MaxSlice

section RelBoundary

variable {k : WithTop ℕ∞}

theorem mem_relBoundaryOfOrder {C : Set M} {x : M} :
    x ∈ relBoundaryOfOrder I k C ↔ x ∈ C ∧ x ∉ maxSliceLocusOfOrder I k C :=
  Iff.rfl

theorem relBoundaryOfOrder_subset {C : Set M} : relBoundaryOfOrder I k C ⊆ C :=
  sdiff_subset

theorem union_maxSliceLocusOfOrder_relBoundaryOfOrder {C : Set M} :
    maxSliceLocusOfOrder I k C ∪ relBoundaryOfOrder I k C = C :=
  union_sdiff_cancel maxSliceLocusOfOrder_subset

theorem relBoundaryOfOrder_eq_empty_iff {C : Set M} :
    relBoundaryOfOrder I k C = ∅ ↔ maxSliceLocusOfOrder I k C = C :=
  Set.sdiff_eq_empty.trans
    ⟨fun h => Subset.antisymm maxSliceLocusOfOrder_subset h, fun h => h.ge⟩

end RelBoundary

end SliceDefs

section TotallyGeodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Geodesics tangent to `Z` stay in `Z` for a short time (both directions). -/
def IsTotallyGeodesicFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (Z : Set M) : Prop :=
  ∀ x ∈ Z, ∀ v ∈ sliceTangent I Z x, ∃ δ > 0, ∀ t ∈ Ioo (-δ) δ,
    (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj ∈ Z

omit [I.Boundaryless] in
/-- The empty set is totally geodesic. -/
theorem isTotallyGeodesicFinite_empty {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    IsTotallyGeodesicFinite g (∅ : Set M) :=
  fun _ hx => hx.elim

/-- An open set is totally geodesic (complete metric of class `C²` at least: the flow is continuous in
time at `0`). -/
theorem IsTotallyGeodesicFinite.of_isOpen [T2Space M] {r : ℕ∞} (hr : 1 ≤ r)
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {Z : Set M} (hZ : IsOpen Z) : IsTotallyGeodesicFinite g Z := by
  intro x hx v _
  have hcont : ContinuousAt (fun t : ℝ => (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj) 0 :=
    (g.hasMFDerivAt_geodesicFlow_proj hr (g.mem_geodesicFlowDomain_zero hr _)).continuousAt
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj ∈ Z := by
    apply hcont.preimage_mem_nhds
    rw [g.geodesicFlow_zero hr]
    exact hZ.mem_nhds hx
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨δ, hδ, fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  exact ht

end TotallyGeodesic

end DifferentialGeometry.Geometry.FiniteSoul
