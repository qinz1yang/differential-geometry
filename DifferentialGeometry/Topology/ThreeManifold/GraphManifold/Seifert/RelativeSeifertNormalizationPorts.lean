import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
# Matching two families of boundary tori, and elementary presentations with given ports

Lane BR, tier R6, first step (review 26 §2.2). Two families of boundary tori of one compact carrier
that both exhaust its boundary are the same tori: there is a bijection `σ` of their indices and
torus diffeomorphisms `ψ` with `B₀.collar i (t, 0) = B₁.collar (σ i) (ψ i t, 0)`
(`exists_boundaryTori_match`); each torus of one family is connected, the tori of the other are
closed and pairwise disjoint, so each lies in exactly one torus of the other family, and the two
inclusions give the diffeomorphism. Hence an elementary presentation of a compact carrier can be
moved, by an orientation-preserving diffeomorphism straightening the collars (CS2's
`exists_transport_subCollar`), to one whose external collars are those of any exhausting family
`P`, up to the bijection `σ` and torus diffeomorphisms, on a sub-collar
(`exists_elementary_subCollar_of_boundaryTori`). `reindexBoundaryTori` renumbers a family along an
equivalence.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization

def reindexBoundaryTori {C : CompactCarrier.{u}} {n m : ℕ} (B : BoundaryTori C m)
    (σ : Fin n ≃ Fin m) : BoundaryTori C n where
  collar l := B.collar (σ l)
  source_eq l := B.source_eq (σ l)
  boundary_zero l t := B.boundary_zero (σ l) t
  disjoint _ _ h := B.disjoint (σ.injective.ne h)

theorem reindexBoundaryTori_collar {C : CompactCarrier.{u}} {n m : ℕ} (B : BoundaryTori C m)
    (σ : Fin n ≃ Fin m) (l : Fin n) : (reindexBoundaryTori B σ).collar l = B.collar (σ l) := rfl

private theorem zero_mem_source' {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n)
    (i : Fin n) (t : Torus) : (t, halfZero) ∈ (B.collar i).source := by
  rw [B.source_eq]
  exact zero_mem_halfCollarSource t

private theorem pairwise_disjoint_range {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n) :
    Pairwise fun i j => Disjoint (range (B.torusMap i)) (range (B.torusMap j)) := by
  intro i j h
  rw [Set.disjoint_left]
  rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
  have h2 : B.torusMap j t' ∈ (B.collar j).target :=
    (B.collar j).map_source' (zero_mem_source' B j t')
  rw [ht'] at h2
  exact (B.disjoint h).le_bot ⟨(B.collar i).map_source' (zero_mem_source' B i t), h2⟩

private theorem range_subset_iUnion {C : CompactCarrier.{u}} {n m : ℕ} (B₀ : BoundaryTori C n)
    (B₁ : BoundaryTori C m) (h₁ : C.model.boundary C.Carrier = B₁.image) (i : Fin n) :
    range (B₀.torusMap i) ⊆ ⋃ r, range (B₁.torusMap r) := by
  rintro _ ⟨t, rfl⟩
  have hx : B₀.torusMap i t ∈ C.model.boundary C.Carrier := B₀.boundary_zero i t
  rw [h₁] at hx
  exact hx

theorem exists_boundaryTori_match {C : CompactCarrier.{u}} {n m : ℕ} (B₀ : BoundaryTori C n)
    (B₁ : BoundaryTori C m) (h₀ : C.model.boundary C.Carrier = B₀.image)
    (h₁ : C.model.boundary C.Carrier = B₁.image) :
    ∃ σ : Fin n ≃ Fin m, ∃ ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      ∀ i t, B₀.collar i (t, halfZero) = B₁.collar (σ i) (ψ i t, halfZero) := by
  classical
  have hc₀ (i : Fin n) : IsClosed (range (B₀.torusMap i)) :=
    (isCompact_range (B₀.torusMap_smooth i).continuous).isClosed
  have hc₁ (r : Fin m) : IsClosed (range (B₁.torusMap r)) :=
    (isCompact_range (B₁.torusMap_smooth r).continuous).isClosed
  have hpt (i : Fin n) : B₀.torusMap i 1 ∈ ⋃ r, range (B₁.torusMap r) :=
    range_subset_iUnion B₀ B₁ h₁ i ⟨1, rfl⟩
  choose r hr using fun i => Set.mem_iUnion.mp (hpt i)
  have hsub1 (i : Fin n) : range (B₀.torusMap i) ⊆ range (B₁.torusMap (r i)) :=
    subset_of_isPreconnected_of_subset_iUnion hc₁ (pairwise_disjoint_range B₁)
      (isPreconnected_range (B₀.torusMap_smooth i).continuous) (range_subset_iUnion B₀ B₁ h₁ i)
      ⟨_, ⟨1, rfl⟩, hr i⟩
  have hsub2 (i : Fin n) : range (B₁.torusMap (r i)) ⊆ range (B₀.torusMap i) :=
    subset_of_isPreconnected_of_subset_iUnion hc₀ (pairwise_disjoint_range B₀)
      (isPreconnected_range (B₁.torusMap_smooth (r i)).continuous)
      (range_subset_iUnion B₁ B₀ h₀ (r i)) ⟨_, hr i, ⟨1, rfl⟩⟩
  have hinj : Injective r := by
    intro i i' h
    by_contra hne
    have h1 : range (B₀.torusMap i) ⊆ range (B₀.torusMap i') := (hsub1 i).trans (h ▸ hsub2 i')
    exact (pairwise_disjoint_range B₀ hne).le_bot ⟨⟨1, rfl⟩, h1 ⟨1, rfl⟩⟩
  have hsurj : Surjective r := by
    intro r'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (range_subset_iUnion B₁ B₀ h₀ r' ⟨1, rfl⟩)
    by_contra hne
    have hne' : r i ≠ r' := fun h => hne ⟨i, h⟩
    exact (pairwise_disjoint_range B₁ hne').le_bot ⟨hsub1 i hi, ⟨1, rfl⟩⟩
  refine ⟨Equiv.ofBijective r ⟨hinj, hsurj⟩, ?_⟩
  have hψ : ∀ i : Fin n, ∃ φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus,
      ∀ t, B₀.collar i (t, halfZero) = B₁.collar (r i) (φ t, halfZero) := by
    intro i
    let c := B₁.collar (r i)
    let d := B₀.collar i
    have K1 (t : Torus) : ∃ t', d (t, halfZero) = c (t', halfZero) := by
      obtain ⟨t', ht'⟩ := hsub1 i ⟨t, rfl⟩
      exact ⟨t', ht'.symm⟩
    have K2 (t' : Torus) : ∃ t, c (t', halfZero) = d (t, halfZero) := by
      obtain ⟨t, ht⟩ := hsub2 i ⟨t', rfl⟩
      exact ⟨t, ht.symm⟩
    let f : Torus → Torus := fun t => (c.symm (d (t, halfZero))).1
    let g : Torus → Torus := fun t' => (d.symm (c (t', halfZero))).1
    have hf (t : Torus) : c.symm (d (t, halfZero)) = (f t, halfZero) := by
      obtain ⟨t', ht'⟩ := K1 t
      change c.symm (d (t, halfZero)) = ((c.symm (d (t, halfZero))).1, halfZero)
      rw [ht', c.symm_apply_apply (zero_mem_source' B₁ _ t')]
    have hg (t' : Torus) : d.symm (c (t', halfZero)) = (g t', halfZero) := by
      obtain ⟨t, ht⟩ := K2 t'
      change d.symm (c (t', halfZero)) = ((d.symm (c (t', halfZero))).1, halfZero)
      rw [ht, d.symm_apply_apply (zero_mem_source' B₀ _ t)]
    have hfe (t : Torus) : d (t, halfZero) = c (f t, halfZero) := by
      obtain ⟨t', ht'⟩ := K1 t
      rw [← hf t, ht', c.symm_apply_apply (zero_mem_source' B₁ _ t')]
    have hge (t' : Torus) : c (t', halfZero) = d (g t', halfZero) := by
      obtain ⟨t, ht⟩ := K2 t'
      rw [← hg t', ht, d.symm_apply_apply (zero_mem_source' B₀ _ t)]
    have hleft (t : Torus) : g (f t) = t := by
      have h1 : d.symm (c (f t, halfZero)) = (t, halfZero) := by
        rw [← hfe t, d.symm_apply_apply (zero_mem_source' B₀ _ t)]
      change (d.symm (c (f t, halfZero))).1 = t
      rw [h1]
    have hright (t' : Torus) : f (g t') = t' := by
      have h1 : c.symm (d (g t', halfZero)) = (t', halfZero) := by
        rw [← hge t', c.symm_apply_apply (zero_mem_source' B₁ _ t')]
      change (c.symm (d (g t', halfZero))).1 = t'
      rw [h1]
    have hfs : ContMDiff torusModel torusModel ∞ f :=
      contMDiff_fst.comp (c.symm.contMDiffOn.comp_contMDiff (B₀.torusMap_smooth i)
        fun t => (hfe t) ▸ c.map_source' (zero_mem_source' B₁ _ _))
    have hgs : ContMDiff torusModel torusModel ∞ g :=
      contMDiff_fst.comp (d.symm.contMDiffOn.comp_contMDiff (B₁.torusMap_smooth (r i))
        fun t' => (hge t') ▸ d.map_source' (zero_mem_source' B₀ _ _))
    refine ⟨
      { toFun := f
        invFun := g
        left_inv := hleft
        right_inv := hright
        contMDiff_toFun := hfs
        contMDiff_invFun := hgs }, hfe⟩
  choose ψ hψ using hψ
  exact ⟨ψ, fun i t => hψ i t⟩

theorem exists_elementary_subCollar_of_boundaryTori {C : CompactCarrier.{u}} {m : ℕ}
    (P : BoundaryTori C m) (hP : C.model.boundary C.Carrier = P.image)
    (E : ElementaryPresentation C) :
    ∃ (E' : ElementaryPresentation C) (σ : Fin E'.toTorus.externalCount ≃ Fin m)
      (ψ : Fin E'.toTorus.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) (δ : ℝ),
      0 < δ ∧ ∀ l p, p ∈ halfCollarSource → p.2.val 0 < δ →
        E'.toTorus.external.collar l p = P.collar (σ l) (ψ l p.1, p.2) := by
  obtain ⟨σ, ψ, h₀⟩ := exists_boundaryTori_match E.toTorus.external P
    E.toTorus.external_exhausted hP
  obtain ⟨δ, hδ, Φ, hΦ, hagree⟩ := E.exists_transport_subCollar (reindexBoundaryTori P σ) rfl ψ
    (fun i t => h₀ i t)
  exact ⟨E.transport Φ hΦ, σ, ψ, δ, hδ, fun l p hp hlt => hagree l p hp hlt⟩

end GC.Seifert.RelativeNormalization
