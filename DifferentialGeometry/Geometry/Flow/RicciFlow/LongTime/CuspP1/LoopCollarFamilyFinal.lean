import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarFamilyMain

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint GC.GraphManifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic

universe u v

section FamilyFinal

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
  {I : Type v} {H : I → FiniteVolumeHyperbolicModel.{u}}
  (T : ∀ i, HyperbolicTruncation (H i)) (D : ∀ i, Set (H i).Carrier)
  (f : ∀ i, (H i).Carrier → M)

theorem isOpen_familyRegion_compl_LTP1 (hcont : ∀ i, ContinuousOn (f i) (D i))
    (hinj : ∀ i, InjOn (f i) (D i)) (hr : ∀ i, range (T i).inclusion ⊆ D i) :
    IsClosed (familyRegion_LTP1 T f) := by
  unfold familyRegion_LTP1
  rw [isClosed_compl_iff]
  refine isOpen_iUnion fun i => ?_
  have hsub : (T i).inclusion '' ((T i).core.interior : Set (T i).core.Carrier) ⊆ D i :=
    (image_subset_range _ _).trans (hr i)
  exact isOpen_image_of_injOn_LTP1 (E₁ := EuclideanSpace ℝ (Fin 3)) (by simp)
    (T i).interior_image ((hcont i).mono hsub) ((hinj i).mono hsub)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem familyRegion_frontier_LTP1 [Finite I] (hcont : ∀ i, ContinuousOn (f i) (D i))
    (hr : ∀ i, range (T i).inclusion ⊆ D i) {y : M} (hy : y ∈ familyRegion_LTP1 T f)
    (hy' : ∀ (i : I) (j : Fin (T i).count) (z : Torus),
      y ≠ f i ((T i).cuspMap j (z, halfZero))) : y ∈ interior (familyRegion_LTP1 T f) := by
  unfold familyRegion_LTP1 at *
  rw [interior_compl]
  intro hcl
  rw [closure_iUnion_of_finite] at hcl
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcl
  have hK : IsCompact (f i '' range (T i).inclusion) :=
    (isCompact_range (T i).inclusion.continuous).image_of_continuousOn ((hcont i).mono (hr i))
  have hsub : f i '' ((T i).inclusion '' ((T i).core.interior : Set (T i).core.Carrier)) ⊆
      f i '' range (T i).inclusion := image_mono (image_subset_range _ _)
  have := closure_minimal hsub hK.isClosed hi
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := this
  by_cases hx : x ∈ ((T i).core.interior : Set (T i).core.Carrier)
  · exact hy (mem_iUnion.mpr ⟨i, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩)
  · have hb : x ∈ (T i).core.model.boundary (T i).core.Carrier := by
      rw [← (T i).core.model.compl_interior]; exact hx
    rw [(T i).boundary_exhausted] at hb
    obtain ⟨_, ⟨j, rfl⟩, z, rfl⟩ := hb
    exact hy' i j z (by rw [← (T i).cusp_zero])

/-- **P1b (abstract form).** A finite family of hyperbolic truncations pushed into `M` by maps
`f i` that are continuous and injective on open sets `D i ⊇ range inclusion`, with disjoint
images, yields one bicollar `σ` of all boundary tori, on `(ι × Torus) × ℝ` with source
`-1 < s < 1`, such that the region outside the pushed cores is exactly the side `s ≥ 0`. -/
theorem exists_family_bicollar_LTP1 [Finite I] [Nonempty (TorusIdx_LTP1 T)]
    (hDo : ∀ i, IsOpen (D i)) (hcont : ∀ i, ContinuousOn (f i) (D i))
    (hinj : ∀ i, InjOn (f i) (D i))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (f i '' D i) (f i' '' D i'))
    (hr : ∀ i, range (T i).inclusion ⊆ D i) :
    ∃ σ : OpenPartialHomeomorph ((TorusIdx_LTP1 T × Torus) × ℝ) M,
      σ.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      (∀ (j : TorusIdx_LTP1 T) (z : Torus),
        σ ((j, z), 0) = f j.1 ((T j.1).cuspMap j.2 (z, halfZero))) ∧
      (∀ p ∈ σ.source, σ p ∈ familyRegion_LTP1 T f ↔ 0 ≤ p.2) ∧
      IsClosed (familyRegion_LTP1 T f) ∧
      familyRegion_LTP1 T f \ range (fun x : TorusIdx_LTP1 T × Torus => σ (x, 0)) ⊆
        interior (familyRegion_LTP1 T f) := by
  obtain ⟨c, hc0, hc1, hcD⟩ := exists_uniform_scale_LTP1 T D hDo hr
  haveI : Nonempty ((TorusIdx_LTP1 T × Torus) × ℝ) := ⟨((Classical.arbitrary _, (1, 1)), 0)⟩
  let σ : OpenPartialHomeomorph ((TorusIdx_LTP1 T × Torus) × ℝ) M :=
    ofInjOnSigma_LTP1 (sigmaFun_LTP1 T f c) (sigmaSource_LTP1 T) (isOpen_sigmaSource_LTP1 T)
      (continuousOn_sigmaFun_LTP1 hcont hc0 hc1 hcD)
      (injOn_sigmaFun_LTP1 hinj hdisj hc0 hc1 hcD)
  have hσ : ∀ p, σ p = sigmaFun_LTP1 T f c p := fun _ => rfl
  have hzero : ∀ (j : TorusIdx_LTP1 T) (z : Torus),
      σ ((j, z), 0) = f j.1 ((T j.1).cuspMap j.2 (z, halfZero)) := by
    intro j z
    rw [hσ]
    change f j.1 (bicollar_LTP1 (T j.1) j.2 (z, c * 0)) = _
    rw [mul_zero, bicollar_zero_eq_cusp_LTP1]
  refine ⟨σ, rfl, hzero, ?_, isOpen_familyRegion_compl_LTP1 T D f hcont hinj hr, ?_⟩
  · rintro ⟨⟨⟨i, q⟩, z⟩, s⟩ hp
    rw [hσ]
    change f i (bicollar_LTP1 (T i) q (z, c * s)) ∈ familyRegion_LTP1 T f ↔ 0 ≤ s
    have hsrc : (z, c * s) ∈ (bicollar_LTP1 (T i) q).source :=
      scaled_mem_source_LTP1 hc0 hc1 hp
    have ha := hcD ⟨i, q⟩ z (c * s) (abs_scaled_lt_LTP1 hc0 hp)
    constructor
    · intro hmem
      by_contra hneg
      have hs : s < 0 := not_le.1 hneg
      have hcs : (z, c * s).2 < 0 := by change c * s < 0; nlinarith
      obtain ⟨y, hy, hyeq⟩ := bicollar_neg_mem_LTP1 (T i) q hsrc hcs
      exact hmem (mem_iUnion.mpr ⟨i, ⟨_, ⟨y, hy, rfl⟩, by rw [hyeq]⟩⟩)
    · intro hs
      rintro hmem
      obtain ⟨i', ⟨_, ⟨y, hy, rfl⟩, h⟩⟩ := mem_iUnion.mp hmem
      have hyD : (T i').inclusion y ∈ D i' := hr i' ⟨y, rfl⟩
      by_cases hii : i' = i
      · subst hii
        have := hinj i' hyD ha h
        refine bicollar_nonneg_not_mem_LTP1 (T i') q (p := (z, c * s)) (by
          change 0 ≤ c * s; positivity) ⟨y, hy, this⟩
      · exact Set.disjoint_left.mp (hdisj i' i hii) ⟨_, hyD, rfl⟩ ⟨_, ha, h.symm⟩
  · rintro y ⟨hy, hy'⟩
    refine familyRegion_frontier_LTP1 T D f hcont hr hy (fun i j z hyz => hy' ?_)
    exact ⟨((⟨i, j⟩, z)), (hzero ⟨i, j⟩ z).trans hyz.symm⟩

end FamilyFinal

end GC.LongTime.CuspP1
