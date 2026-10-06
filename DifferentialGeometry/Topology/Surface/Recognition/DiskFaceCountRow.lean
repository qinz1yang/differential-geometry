import DifferentialGeometry.Topology.Connected.DiskFaceDegree
import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalOrCircle
import DifferentialGeometry.Topology.Surface.Recognition.CircleOpenMap
import DifferentialGeometry.Topology.Surface.Recognition.IntervalBundleTrivial

/-!
# FC40, the number of disk faces, for an actual compact circle-bundle surface

Lane C14-ROWS-S. Blueprint `master207B.tex`, FC40 (`lem:fibration-euler-faces`, B:7457–7463):
"Let a connected closed surface `Y` be either `S²` or `T²`. Suppose `Y = A ∪ B`, where `A` is a
finite disjoint union of `d` closed disks, `B` is a compact circle-bundle surface, and
`A ∩ B = ∂A = ∂B` is a disjoint union of fiber circles. Then `d = 2` for `S²` and `d = 0` for
`T²`."

The row's data, stated without any face-data hypothesis:
* `Y ≃ₜ S²` (`SphereTwo`) or `Y ≃ₜ T² = Circle × Circle`;
* `A = ⋃ᵢ range hᵢ`, `hᵢ : D² → Y` continuous and injective (closed disks), pairwise disjoint,
  `∂A = ⋃ᵢ hᵢ(S¹)`;
* `B ⊆ Y` compact with a continuous `π : B → C` onto a smooth one-manifold with boundary `C`
  (`𝓡∂ 1`), locally trivial with fibre `Circle` (every `c` has `U ∈ 𝓝 c` and
  `π⁻¹(U) ≃ₜ U × Circle` over `U`); `∂B = π⁻¹(∂C)` (a union of whole fibre circles);
* `A ∪ B = Y`, `A ∩ B = ∂A`, `∂A = ∂B`.

Route (no Euler characteristic): every disk boundary circle is one whole fibre over a boundary
point of `C` (`fc40_disk_boundary_fibre_RWS`); the pieces of `B` over the components of `C` carry
`0` or `2` disks (`hdeg_of_boundary_equiv`, components of a compact one-manifold), so FC40a
(`disk_face_count_dichotomy`) makes `C` connected and `d ∈ {0, 2}` (`fc40_dichotomy_RWS`). FC40b
then decides: on `S²`, `d = 0` would make `Y = B` a bundle over a circle (open projection,
`disk_face_count_sphereTwo`); on `T²`, `d = 2` makes `C ≅ [0, 1]`, `B` an annulus
(`exists_homeomorph_prod_of_homeomorph_unitInterval_RWS`) and `Y` a sphere
(`disk_face_count_torus`).

* `fc40_sphere_RWS`, `fc40_torus_RWS`, ROW `fc40_row_RWS`.

Consumer: `fc40_torus_eq_bundle_RWS` (on a torus face the circle-bundle surface is everything).
-/

set_option autoImplicit false

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold.OneManifold

section Helpers

/-- A preconnected subset of a finite set in a `T₁` space has at most one point. -/
theorem subsingleton_of_isPreconnected_of_finite_RWS {α : Type*} [TopologicalSpace α]
    [T1Space α] {s t : Set α} (ht : t.Finite) (hst : s ⊆ t) (hs : IsPreconnected s) :
    s.Subsingleton := by
  have : Finite s := (ht.subset hst).to_subtype
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  intro x hx y hy
  have h := (isPreconnected_univ : IsPreconnected (univ : Set s)).subsingleton (mem_univ ⟨x, hx⟩)
    (mem_univ ⟨y, hy⟩)
  exact congrArg Subtype.val h

/-- A preconnected set covered by finitely many pairwise disjoint closed sets, meeting one of
them, lies in it. -/
theorem subset_of_isPreconnected_of_closed_cover_RWS {α κ : Type*} [TopologicalSpace α]
    [Finite κ] {K : κ → Set α} (hK : ∀ k, IsClosed (K k)) (hdisj : Pairwise (Disjoint on K))
    {s : Set α} (hs : IsPreconnected s) (hsub : s ⊆ ⋃ k, K k) {i : κ}
    (hi : (s ∩ K i).Nonempty) : s ⊆ K i := by
  have hv : IsClosed (⋃ k : {k // k ≠ i}, K k.1) := isClosed_iUnion_of_finite fun k => hK k.1
  have hcov : s ⊆ K i ∪ ⋃ k : {k // k ≠ i}, K k.1 := fun y hy => by
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsub hy)
    by_cases hki : k = i
    · exact Or.inl (hki ▸ hk)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hki⟩, hk⟩)
  have hemp : s ∩ (K i ∩ ⋃ k : {k // k ≠ i}, K k.1) = ∅ := by
    refine eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨-, hy1, hy2⟩ := hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy2
    exact Set.disjoint_left.mp (hdisj k.2) hk hy1
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hs _ _ (hK i) hv hcov hemp with h | h
  · exact h
  · obtain ⟨y, hys, hyi⟩ := hi
    obtain ⟨k, hk⟩ := mem_iUnion.mp (h hys)
    exact absurd hyi (Set.disjoint_left.mp (hdisj k.2) hk)

/-- The boundary circle of a parametrized closed disk is connected. -/
theorem isConnected_image_diskSphere_RWS {Y : Type*} [TopologicalSpace Y] {h : Disk 2 → Y}
    (hh : Continuous h) : IsConnected (h '' diskSphere 2) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  let k : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → Disk 2 :=
    fun s => ⟨s.1, Metric.sphere_subset_closedBall s.2⟩
  have hk : Continuous k := Continuous.subtype_mk continuous_subtype_val _
  have heq : h '' diskSphere 2 = range (h ∘ k) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, hx⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨k s, s.2, rfl⟩
  rw [heq]
  exact isConnected_range (hh.comp hk)

/-- **The fibres of a locally trivial circle bundle on `B ⊆ Y` are connected subsets of `Y`.** -/
theorem isConnected_fibre_RWS {Y C : Type*} [TopologicalSpace Y] [TopologicalSpace C]
    {B : Set Y} (π : B → C)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x) (c : C) :
    IsConnected (Subtype.val '' (π ⁻¹' {c})) := by
  obtain ⟨U, hU, e, he⟩ := hloc c
  have hc : c ∈ U := mem_of_mem_nhds hU
  have hkey : ∀ (u : U) f, π (e.symm (u, f)).1 = u := fun u f => by
    have h := he (e.symm (u, f))
    rw [e.apply_symm_apply] at h
    exact h.symm
  have heq : Subtype.val '' (π ⁻¹' {c}) = range fun f : Circle => (e.symm (⟨c, hc⟩, f)).1.1 := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : π b ∈ U := by
        rw [mem_preimage, mem_singleton_iff] at hb
        rw [hb]
        exact hc
      refine ⟨(e ⟨b, hb'⟩).2, ?_⟩
      have hq : e ⟨b, hb'⟩ = (⟨c, hc⟩, (e ⟨b, hb'⟩).2) :=
        Prod.ext (Subtype.ext ((he ⟨b, hb'⟩).trans hb)) rfl
      change (e.symm (⟨c, hc⟩, (e ⟨b, hb'⟩).2)).1.1 = b.1
      rw [← hq, e.symm_apply_apply]
    · rintro ⟨f, rfl⟩
      exact ⟨(e.symm (⟨c, hc⟩, f)).1, hkey ⟨c, hc⟩ f, rfl⟩
  rw [heq]
  exact isConnected_range (continuous_subtype_val.comp
    (continuous_subtype_val.comp (e.symm.continuous.comp (continuous_const.prodMk continuous_id))))

/-- A locally trivial circle bundle is onto its base. -/
theorem surjective_of_localTrivialization_RWS {Y C : Type*} [TopologicalSpace Y]
    [TopologicalSpace C] {B : Set Y} (π : B → C)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x) : Surjective π := fun c => by
  obtain ⟨_, ⟨b, hb, -⟩⟩ := (isConnected_fibre_RWS π hloc c).nonempty
  exact ⟨b, hb⟩

end Helpers

section Row

variable {Y ι C : Type*} [TopologicalSpace Y] [Fintype ι] [TopologicalSpace C] [T2Space C]
  [ChartedSpace (EuclideanHalfSpace 1) C] [IsManifold (𝓡∂ 1) ∞ C]

/-- **Every disk boundary circle is one whole fibre over a boundary point of the base**, and the
disk meets `B` exactly in it. -/
theorem fc40_disk_boundary_fibre_RWS [T2Space Y] [CompactSpace C] (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    ∃ c : ι → C, Injective c ∧ (∀ i, c i ∈ (𝓡∂ 1).boundary C) ∧
      (∀ b ∈ (𝓡∂ 1).boundary C, ∃ i, c i = b) ∧
      (∀ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' {c i})) ∧
      ∀ i, range (h i) ∩ B = h i '' diskSphere 2 := by
  classical
  have hsubB : ∀ i, h i '' diskSphere 2 ⊆ B := fun i y hy =>
    (hAB.symm.subset (mem_iUnion.mpr ⟨i, hy⟩)).2
  have hsubA : ∀ i, h i '' diskSphere 2 ⊆ range (h i) := fun i => image_subset_range _ _
  have hconn : ∀ i, IsConnected (h i '' diskSphere 2) := fun i =>
    isConnected_image_diskSphere_RWS (hh i)
  have hclosedA : ∀ i, IsClosed (h i '' diskSphere 2) := fun i =>
    ((isClosed_diskSphere 2).isCompact.image (hh i)).isClosed
  have hdisjA : Pairwise (Disjoint on fun i => h i '' diskSphere 2) := fun i k hik =>
    (hdisj hik).mono (hsubA i) (hsubA k)
  -- the preimage in `B` of a disk boundary circle
  have hTconn : ∀ i, IsConnected (Subtype.val ⁻¹' (h i '' diskSphere 2) : Set B) := fun i => by
    have himg : Subtype.val '' (Subtype.val ⁻¹' (h i '' diskSphere 2) : Set B) =
        h i '' diskSphere 2 := by
      rw [image_preimage_eq_inter_range, Subtype.range_coe]
      exact inter_eq_left.mpr (hsubB i)
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := (hconn i).nonempty
      exact ⟨⟨y, hsubB i hy⟩, hy⟩
    · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
      exact (hconn i).isPreconnected
  have hTbd : ∀ i, ∀ b ∈ (Subtype.val ⁻¹' (h i '' diskSphere 2) : Set B),
      π b ∈ (𝓡∂ 1).boundary C := fun i b hb => by
    have hy : b.1 ∈ Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C) := by
      rw [← hbd]
      exact mem_iUnion.mpr ⟨i, hb⟩
    obtain ⟨b', hb', hbb'⟩ := hy
    rw [← Subtype.ext hbb']
    exact hb'
  have hsing : ∀ i, (π '' (Subtype.val ⁻¹' (h i '' diskSphere 2) : Set B)).Subsingleton :=
    fun i => subsingleton_of_isPreconnected_of_finite_RWS finite_boundary
      (by rintro _ ⟨b, hb, rfl⟩; exact hTbd i b hb) ((hTconn i).isPreconnected.image _
        hπ.continuousOn)
  -- the boundary point under each disk
  have hTne : ∀ i, ∃ b : B, b ∈ (Subtype.val ⁻¹' (h i '' diskSphere 2) : Set B) := fun i =>
    (hTconn i).nonempty
  choose b₀ hb₀ using hTne
  let c : ι → C := fun i => π (b₀ i)
  have hcT : ∀ i, ∀ b ∈ (Subtype.val ⁻¹' (h i '' diskSphere 2) : Set B), π b = c i :=
    fun i b hb => hsing i (mem_image_of_mem π hb) (mem_image_of_mem π (hb₀ i))
  have hcbd : ∀ i, c i ∈ (𝓡∂ 1).boundary C := fun i => hTbd i (b₀ i) (hb₀ i)
  -- each disk boundary circle is the whole fibre over its point
  have hfib : ∀ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' {c i}) := fun i => by
    apply Subset.antisymm
    · intro y hy
      exact ⟨⟨y, hsubB i hy⟩, hcT i ⟨y, hsubB i hy⟩ hy, rfl⟩
    · have hF := isConnected_fibre_RWS π hloc (c i)
      refine subset_of_isPreconnected_of_closed_cover_RWS hclosedA hdisjA hF.isPreconnected
        ?_ ⟨(b₀ i).1, ⟨b₀ i, rfl, rfl⟩, hb₀ i⟩
      rintro _ ⟨b, hb, rfl⟩
      rw [hbd]
      refine ⟨b, ?_, rfl⟩
      rw [mem_preimage, mem_singleton_iff.mp hb]
      exact hcbd i
  have hcinj : Injective c := fun i k hik => by
    by_contra hne
    obtain ⟨y, hy⟩ := (hconn i).nonempty
    have hy' : y ∈ h k '' diskSphere 2 := by
      rw [hfib k, ← hik, ← hfib i]
      exact hy
    exact Set.disjoint_left.mp (hdisjA hne) hy hy'
  refine ⟨c, hcinj, hcbd, fun b hb => ?_, hfib, fun i => ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := (isConnected_fibre_RWS π hloc b).nonempty
    have hx' : x.1 ∈ ⋃ i, h i '' diskSphere 2 := by
      rw [hbd]
      exact ⟨x, by rw [mem_preimage, mem_singleton_iff.mp hx]; exact hb, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    refine ⟨i, ?_⟩
    rw [← mem_singleton_iff.mp hx]
    exact (hcT i x hi).symm
  · apply Subset.antisymm
    · intro y hy
      have hy' : y ∈ ⋃ k, h k '' diskSphere 2 := by
        rw [← hAB]
        exact ⟨mem_iUnion.mpr ⟨i, hy.1⟩, hy.2⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy'
      by_cases hki : k = i
      · exact hki ▸ hk
      · exact absurd hy.1 (Set.disjoint_left.mp (hdisj hki) (hsubA k hk))
    · exact subset_inter (hsubA i) (hsubB i)

/-- **FC40a on the actual data**: the base is connected and the number of disks is `0` or `2`
(with the disk-to-boundary-point correspondence of `fc40_disk_boundary_fibre_RWS`). -/
theorem fc40_dichotomy_RWS [T2Space Y] [ConnectedSpace Y] (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    (Fintype.card ι = 0 ∨ Fintype.card ι = 2) ∧ ConnectedSpace C ∧ CompactSpace C ∧
      Surjective π ∧ ∃ c : ι → C, Injective c ∧ (∀ i, c i ∈ (𝓡∂ 1).boundary C) ∧
        (∀ b ∈ (𝓡∂ 1).boundary C, ∃ i, c i = b) ∧
        (∀ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' {c i})) ∧
        ∀ i, range (h i) ∩ B = h i '' diskSphere 2 := by
  classical
  have : CompactSpace B := isCompact_iff_compactSpace.mp hBc
  have hsurj := surjective_of_localTrivialization_RWS π hloc
  have : CompactSpace C := ⟨by rw [← hsurj.range_eq]; exact isCompact_range hπ⟩
  obtain ⟨c, hcinj, hcbd, hcsurj, hfib, hAB'⟩ :=
    fc40_disk_boundary_fibre_RWS h hh hdisj B π hπ hloc hAB hbd
  have : Finite (ConnectedComponents C) := finite_connectedComponents_of_oneManifold
  let _ : Fintype (ConnectedComponents C) := Fintype.ofFinite _
  let K : ConnectedComponents C → Set C := fun j => ConnectedComponents.mk ⁻¹' {j}
  have hK : ∀ x : C, K (ConnectedComponents.mk x) = connectedComponent x := fun x =>
    connectedComponents_preimage_singleton
  have hKcl : ∀ j, IsClosed (K j) := fun j => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe j
    rw [hK]
    exact isClosed_connectedComponent
  let D : ι → Set Y := fun i => range (h i)
  let Bj : ConnectedComponents C → Set Y := fun j => Subtype.val '' (π ⁻¹' K j)
  let side : ι → ConnectedComponents C := fun i => ConnectedComponents.mk (c i)
  have hD : ∀ i, IsClosed (D i) := fun i => (isCompact_range (hh i)).isClosed
  have hB : ∀ j, IsClosed (Bj j) := fun j =>
    (((hKcl j).preimage hπ).isCompact.image continuous_subtype_val).isClosed
  have hBne : ∀ j, (Bj j).Nonempty := fun j => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe j
    obtain ⟨b, hb⟩ := hsurj x
    exact ⟨b.1, b, by rw [mem_preimage, hb]; exact rfl, rfl⟩
  have hcov : (⋃ i, D i) ∪ (⋃ j, Bj j) = univ := by
    refine eq_univ_of_forall fun y => ?_
    rcases (hcover ▸ mem_univ y : y ∈ (⋃ i, range (h i)) ∪ B) with hy | hy
    · exact Or.inl hy
    · exact Or.inr (mem_iUnion.mpr ⟨ConnectedComponents.mk (π ⟨y, hy⟩), ⟨y, hy⟩, rfl, rfl⟩)
  have hBB : Pairwise (Disjoint on Bj) := fun j j' hjj => by
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', hbb⟩
    rw [Subtype.ext hbb] at hb'
    exact hjj ((mem_singleton_iff.mp hb).symm.trans (mem_singleton_iff.mp hb'))
  have hDB : ∀ i j, (D i ∩ Bj j).Nonempty → side i = j := by
    rintro i j ⟨y, hyD, ⟨b, hb, rfl⟩⟩
    have hy : b.1 ∈ Subtype.val '' (π ⁻¹' {c i}) := by
      rw [← hfib i, ← hAB' i]
      exact ⟨hyD, b.2⟩
    obtain ⟨b', hb', hbb⟩ := hy
    rw [Subtype.ext hbb] at hb'
    change ConnectedComponents.mk (c i) = j
    rw [← mem_singleton_iff.mp hb']
    exact mem_singleton_iff.mp hb
  -- the components of the base and the degree of each piece
  let rep : ConnectedComponents C → C := fun j => (ConnectedComponents.surjective_coe j).choose
  have hrep : ∀ j, ConnectedComponents.mk (rep j) = j := fun j =>
    (ConnectedComponents.surjective_coe j).choose_spec
  let Cc : ConnectedComponents C → Type _ := fun j => componentOpens (rep j)
  have hCcomp : ∀ j, CompactSpace (Cc j) := fun j =>
    isCompact_iff_compactSpace.mp (isClosed_connectedComponent (x := rep j)).isCompact
  have hCconn : ∀ j, ConnectedSpace (Cc j) := fun j =>
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := rep j))
  have hmem : ∀ i j, side i = j → c i ∈ componentOpens (rep j) := fun i j hij => by
    change c i ∈ connectedComponent (rep j)
    rw [← ConnectedComponents.coe_eq_coe', hrep]
    exact hij
  have hbdc : ∀ j (z : Cc j), z ∈ (𝓡∂ 1).boundary (Cc j) ↔ z.1 ∈ (𝓡∂ 1).boundary C :=
    fun j z => by rw [ModelWithCorners.boundary_open]; rfl
  let e : ∀ j, {i // side i = j} ≃ (𝓡∂ 1).boundary (Cc j) := fun j =>
    Equiv.ofBijective (fun i => ⟨⟨c i.1, hmem i.1 j i.2⟩, (hbdc j _).mpr (hcbd i.1)⟩)
      ⟨fun i k hik => Subtype.ext (hcinj (congrArg (fun z : (𝓡∂ 1).boundary (Cc j) => z.1.1) hik)),
        fun z => by
          obtain ⟨i, hi⟩ := hcsurj z.1.1 ((hbdc j z.1).mp z.2)
          have hside : side i = j := by
            exact (congrArg ConnectedComponents.mk hi).trans
              ((ConnectedComponents.coe_eq_coe'.mpr z.1.2).trans (hrep j))
          exact ⟨⟨i, hside⟩, Subtype.ext (Subtype.ext hi)⟩⟩
  have hdeg := hdeg_of_boundary_equiv side Cc e
  obtain ⟨hκ, hι⟩ := disk_face_count_dichotomy D Bj hD hB hBne hcov hdisj hBB side hDB hdeg
  -- one component: the base is connected
  have hCne : Nonempty C := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    rcases (hcover ▸ mem_univ y : y ∈ (⋃ i, range (h i)) ∪ B) with hy | hy
    · obtain ⟨i, -⟩ := mem_iUnion.mp hy
      exact ⟨c i⟩
    · exact ⟨π ⟨y, hy⟩⟩
  obtain ⟨j₀, hj₀⟩ := Fintype.card_eq_one_iff.mp hκ
  have hCconn' : ConnectedSpace C := by
    obtain ⟨x⟩ := hCne
    have hcc : connectedComponent x = univ := eq_univ_of_forall fun y => by
      rw [← ConnectedComponents.coe_eq_coe', hj₀ (ConnectedComponents.mk y),
        hj₀ (ConnectedComponents.mk x)]
    rw [connectedSpace_iff_univ, ← hcc]
    exact isConnected_connectedComponent
  exact ⟨hι, hCconn', inferInstance, hsurj, c, hcinj, hcbd, hcsurj, hfib, hAB'⟩

/-- `S¹ ⊆ ℝ²` and `Circle ⊆ ℂ` (the identification `ℂ ≃ ℝ²` of `Complex.orthonormalBasisOneI`). -/
noncomputable def sphereTwoCircleHomeomorph_RWS :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]).symm

/-- **FC40, sphere case**: a two-sphere cut as in FC40 has exactly two disks. -/
theorem fc40_sphere_RWS (φ : Y ≃ₜ SphereTwo) (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    Fintype.card ι = 2 := by
  classical
  have : T2Space Y := φ.isEmbedding.t2Space
  have : ConnectedSpace Y := φ.symm.surjective.connectedSpace φ.symm.continuous
  obtain ⟨hι, hCc, hCk, hsurj, c, -, -, hcsurj, -, -⟩ :=
    fc40_dichotomy_RWS h hh hdisj B hBc π hπ hloc hcover hAB hbd
  have hBne : B.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty C)
    obtain ⟨b, -⟩ := hsurj x
    exact ⟨b.1, b.2⟩
  have hfil : ∀ j : Unit, Finset.univ.filter (fun _ : ι => () = j) = Finset.univ := fun j =>
    Finset.filter_true_of_mem fun _ _ => rfl
  have hdeg : ∀ j : Unit, (Finset.univ.filter (fun _ : ι => () = j)).card = 0 ∨
      (Finset.univ.filter (fun _ : ι => () = j)).card = 2 := fun j => by
    rw [hfil, Finset.card_univ]
    exact hι
  have hbase : ∀ j : Unit, (Finset.univ.filter (fun _ : ι => () = j)).card = 0 →
      ∃ p : B → Circle, Continuous p ∧ IsOpenMap p := fun j h0 => by
    rw [hfil, Finset.card_univ, Fintype.card_eq_zero_iff] at h0
    have hbd0 : (𝓡∂ 1).boundary C = ∅ := eq_empty_of_forall_notMem fun b hb => by
      obtain ⟨i, -⟩ := hcsurj b hb
      exact h0.elim i
    obtain ⟨Φ⟩ := nonempty_circle_diffeomorph_of_boundary_eq_empty hbd0
    exact ⟨Φ.toHomeomorph.symm ∘ π, Φ.toHomeomorph.symm.continuous.comp hπ,
      Φ.toHomeomorph.symm.isOpenMap.comp (isOpenMap_of_localTrivialization π hloc)⟩
  have hcov : (⋃ i, range (h i)) ∪ (⋃ _ : Unit, B) = univ := by rw [iUnion_const]; exact hcover
  exact (disk_face_count_sphereTwo φ (fun i => range (h i)) (fun _ : Unit => B)
    (fun i => (isCompact_range (hh i)).isClosed) (fun _ => hBc.isClosed) (fun _ => hBne) hcov
    hdisj (Subsingleton.pairwise) (fun _ => ()) (fun _ _ _ => rfl) hdeg hbase).2

/-- **FC40, torus case**: a two-torus cut as in FC40 has no disk. -/
theorem fc40_torus_RWS (φ : Y ≃ₜ Circle × Circle) (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hinj : ∀ i, Injective (h i))
    (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    Fintype.card ι = 0 := by
  classical
  have : T2Space Y := φ.isEmbedding.t2Space
  have : ConnectedSpace Y := φ.symm.surjective.connectedSpace φ.symm.continuous
  obtain ⟨hι, hCc, hCk, hsurj, c, -, hcbd, -, hfib, hAB'⟩ :=
    fc40_dichotomy_RWS h hh hdisj B hBc π hπ hloc hcover hAB hbd
  have hBne : B.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty C)
    obtain ⟨b, -⟩ := hsurj x
    exact ⟨b.1, b.2⟩
  have hfil : ∀ j : Unit, Finset.univ.filter (fun _ : ι => () = j) = Finset.univ := fun j =>
    Finset.filter_true_of_mem fun _ _ => rfl
  have hdeg : ∀ j : Unit, (Finset.univ.filter (fun _ : ι => () = j)).card = 0 ∨
      (Finset.univ.filter (fun _ : ι => () = j)).card = 2 := fun j => by
    rw [hfil, Finset.card_univ]
    exact hι
  have hdisk : ∀ i, ∃ k : Disk 2 → Y, Continuous k ∧ Injective k ∧ range k = range (h i) ∧
      k '' diskSphere 2 = range (h i) ∩ (fun _ : Unit => B) ((fun _ : ι => ()) i) :=
    fun i => ⟨h i, hh i, hinj i, rfl, (hAB' i).symm⟩
  have hann : ∀ j : Unit, (Finset.univ.filter (fun _ : ι => () = j)).card = 2 →
      ∃ a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y,
        Continuous a ∧ Injective a ∧ range a = (fun _ : Unit => B) j ∧
        ∀ i, (fun _ : ι => ()) i = j →
          range (h i) ∩ (fun _ : Unit => B) j = a '' {q | (q.2 : ℝ) = 0} ∨
            range (h i) ∩ (fun _ : Unit => B) j = a '' {q | (q.2 : ℝ) = 1} := fun j h2 => by
    rw [hfil, Finset.card_univ] at h2
    have hne : Nonempty ι := Fintype.card_pos_iff.mp (by rw [h2]; norm_num)
    obtain ⟨i₀⟩ := hne
    obtain ⟨Ψ⟩ := nonempty_diffeomorph_Icc_of_boundary_nonempty ⟨c i₀, hcbd i₀⟩
    obtain ⟨Θ, hΘ⟩ := exists_homeomorph_prod_of_homeomorph_unitInterval_RWS Ψ.toHomeomorph π hπ
      hloc
    let σ := sphereTwoCircleHomeomorph_RWS
    let a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → Y :=
      fun q => (Θ.symm (Ψ.symm q.2, σ q.1)).1
    have hπΘ : ∀ w, π (Θ.symm w) = w.1 := fun w => by
      rw [← hΘ, Θ.apply_symm_apply]
    have hfibre : ∀ t : Icc (0 : ℝ) 1, Subtype.val '' (π ⁻¹' {Ψ.symm t}) = a '' {q | q.2 = t} :=
      fun t => by
        ext y
        constructor
        · rintro ⟨b, hb, rfl⟩
          refine ⟨(σ.symm (Θ b).2, t), rfl, ?_⟩
          change (Θ.symm (Ψ.symm t, σ (σ.symm (Θ b).2))).1 = b.1
          have hq : (Ψ.symm t, σ (σ.symm (Θ b).2)) = Θ b := by
            rw [σ.apply_symm_apply]
            exact Prod.ext ((hΘ b).trans (mem_singleton_iff.mp hb)).symm rfl
          rw [hq, Θ.symm_apply_apply]
        · rintro ⟨q, hq, rfl⟩
          refine ⟨Θ.symm (Ψ.symm q.2, σ q.1), ?_, rfl⟩
          rw [mem_preimage, hπΘ, mem_singleton_iff]
          exact congrArg Ψ.symm hq
    have hcont : Continuous a :=
      continuous_subtype_val.comp (Θ.symm.continuous.comp
        ((Ψ.symm.continuous.comp continuous_snd).prodMk (σ.continuous.comp continuous_fst)))
    have hinja : Injective a := fun q q' hqq => by
      have h1 := Θ.symm.injective (Subtype.ext hqq)
      exact Prod.ext (σ.injective (congrArg Prod.snd h1)) (Ψ.symm.injective (congrArg Prod.fst h1))
    have hrange : range a = B := by
      apply Subset.antisymm
      · rintro _ ⟨q, rfl⟩
        exact (Θ.symm (Ψ.symm q.2, σ q.1)).2
      · intro y hy
        have hy' := (hfibre (Ψ (π ⟨y, hy⟩))).subset ⟨⟨y, hy⟩, by
          rw [mem_preimage, Ψ.symm_apply_apply]; exact rfl, rfl⟩
        obtain ⟨q, -, hq⟩ := hy'
        exact ⟨q, hq⟩
    have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
    refine ⟨a, hcont, hinja, hrange, fun i _ => ?_⟩
    have hbdi : Ψ (c i) ∈ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) := by
      have h := hcbd i
      rw [← Ψ.preimage_boundary (by simp)] at h
      exact h
    rw [boundary_Icc] at hbdi
    have hset : range (h i) ∩ B = a '' {q | q.2 = Ψ (c i)} := by
      rw [hAB' i, hfib i, ← hfibre, Ψ.symm_apply_apply]
    rcases hbdi with h0 | h1
    · left
      rw [hset, h0]
      congr 1
      ext q
      simp only [mem_ofPred_eq]
      rw [Subtype.ext_iff, Set.Icc.coe_bot]
    · right
      rw [mem_singleton_iff] at h1
      rw [hset, h1]
      congr 1
      ext q
      simp only [mem_ofPred_eq]
      rw [Subtype.ext_iff, Set.Icc.coe_top]
  have hcov : (⋃ i, range (h i)) ∪ (⋃ _ : Unit, B) = univ := by rw [iUnion_const]; exact hcover
  exact (disk_face_count_torus φ (fun i => range (h i)) (fun _ : Unit => B)
    (fun i => (isCompact_range (hh i)).isClosed) (fun _ => hBc.isClosed) (fun _ => hBne) hcov
    hdisj (Subsingleton.pairwise) (fun _ => ()) (fun _ _ _ => rfl) hdeg hdisk hann).2

/-- **FC40** (`lem:fibration-euler-faces`, B:7457–7463). Let `Y` be a connected closed surface
that is `S²` or `T²`, `Y = A ∪ B` with `A = ⋃ᵢ hᵢ(D²)` a finite disjoint union of `d = |ι|`
closed disks and `B` a compact circle-bundle surface (`π : B → C` locally trivial with fibre
`Circle` over a smooth one-manifold with boundary `C`), and `A ∩ B = ∂A = ∂B = π⁻¹(∂C)` a union
of fibre circles. Then `d = 2` for `S²` and `d = 0` for `T²`. -/
theorem fc40_row_RWS (h : ι → Disk 2 → Y) (hh : ∀ i, Continuous (h i))
    (hinj : ∀ i, Injective (h i)) (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    (Nonempty (Y ≃ₜ SphereTwo) → Fintype.card ι = 2) ∧
      (Nonempty (Y ≃ₜ Circle × Circle) → Fintype.card ι = 0) :=
  ⟨fun ⟨φ⟩ => fc40_sphere_RWS φ h hh hdisj B hBc π hπ hloc hcover hAB hbd,
    fun ⟨φ⟩ => fc40_torus_RWS φ h hh hinj hdisj B hBc π hπ hloc hcover hAB hbd⟩

/-- **Consumer: on a torus face the circle-bundle surface is the whole face** (the cusp branch
of BCF03 / FC42: no horizontal disk, `B = Y`). -/
theorem fc40_torus_eq_bundle_RWS (φ : Y ≃ₜ Circle × Circle) (h : ι → Disk 2 → Y)
    (hh : ∀ i, Continuous (h i)) (hinj : ∀ i, Injective (h i))
    (hdisj : Pairwise (Disjoint on fun i => range (h i)))
    (B : Set Y) (hBc : IsCompact B) (π : B → C) (hπ : Continuous π)
    (hloc : ∀ c : C, ∃ U ∈ 𝓝 c, ∃ e : π ⁻¹' U ≃ₜ U × Circle,
      ∀ x : π ⁻¹' U, ((e x).1 : C) = π x)
    (hcover : (⋃ i, range (h i)) ∪ B = univ)
    (hAB : (⋃ i, range (h i)) ∩ B = ⋃ i, h i '' diskSphere 2)
    (hbd : ⋃ i, h i '' diskSphere 2 = Subtype.val '' (π ⁻¹' (𝓡∂ 1).boundary C)) :
    B = univ := by
  have h0 := (fc40_row_RWS h hh hinj hdisj B hBc π hπ hloc hcover hAB hbd).2 ⟨φ⟩
  have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
  rw [iUnion_of_empty, empty_union] at hcover
  exact hcover

end Row

end DifferentialGeometry.Topology.Surface
