import DifferentialGeometry.Geometry.Boundary.CollarCoordinates
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Boundary

private theorem exists_halfStrip_subset
    {X : Type*} [TopologicalSpace X] {K : Set X} {S : Set (X × EuclideanHalfSpace 1)}
    (hK : IsCompact K) (hS : IsOpen S) (hzero : K ×ˢ {(0 : EuclideanHalfSpace 1)} ⊆ S)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ ε > 0, ε < τ ∧ K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε} ⊆ S := by
  obtain ⟨U, V, _, hV, hKU, h0V, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hS hzero
  let T : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let j : ℝ → EuclideanHalfSpace 1 := fun t ↦
    ⟨T.symm (max 0 t), by change 0 ≤ max 0 t; exact le_max_left _ _⟩
  have hj : Continuous j :=
    (T.symm.continuous.comp (continuous_const.max continuous_id)).subtype_mk _
  have hj0 : j 0 = 0 := by
    apply Subtype.ext
    change T.symm (max 0 (0 : ℝ)) = 0
    simp
  have hn : j ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
    hj.continuousAt.preimage_mem_nhds (hV.mem_nhds (by rw [hj0]; exact h0V rfl))
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hn
  let ε := min (τ / 2) δ
  refine ⟨ε, lt_min (half_pos hτ) hδ,
    (min_le_left _ _).trans_lt (half_lt_self hτ), ?_⟩
  intro z hz
  apply hUV
  refine ⟨hKU hz.1, ?_⟩
  have hh : j (z.2.1 0) ∈ V := hδV (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg z.2.2]
    exact hz.2.trans_le (min_le_right _ _))
  have hleft : j (z.2.1 0) = z.2 := by
    apply Subtype.ext
    apply T.injective
    change T (T.symm (max 0 (z.2.1 0))) = T z.2.1
    rw [T.apply_symm_apply, max_eq_right z.2.2]
    rfl
  rwa [hleft] at hh

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_collar_of_one_sided
    {φ : BoundaryManifold I M × ℝ → M} {K : Set (BoundaryManifold I M)} {τ : ℝ}
    (hK : IsCompact K) (hKo : IsOpen K) (hKne : K.Nonempty) (hτ : 0 < τ)
    (hφ : ContMDiffOn (hI.boundaryI.prod 𝓘(ℝ)) I ∞ φ (K ×ˢ Icc 0 τ))
    (hzero : ∀ y ∈ K, φ (y, 0) = y.1)
    (hinj : InjOn φ (K ×ˢ Icc 0 τ))
    (hderiv : ∀ x ∈ K, ∃ v : TangentSpace I x.1,
      HasMFDerivWithinAt 𝓘(ℝ) I (fun t ↦ φ (x, t)) (Icc 0 τ) 0
        (ContinuousLinearMap.toSpanSingleton ℝ v) ∧
      ∃ (w : TangentSpace hI.boundaryI x) (c : ℝ), 0 < c ∧
        v = boundaryInclusionMfderiv x w + c • inwardCoord x) :
    ∃ ε > 0, ε < τ ∧
      ∃ d : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
          (BoundaryManifold I M × EuclideanHalfSpace 1) M ∞,
        d.source = K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε} ∧
        (∀ z, d z = φ (z.1, z.2.1 0)) ∧
        (Subtype.val '' K) ⊆ d.target := by
  classical
  have hlocal : ∀ x : K,
      ∃ d : OpenPartialHomeomorph (BoundaryManifold I M × EuclideanHalfSpace 1) M,
        (x.1, 0) ∈ d.source ∧
        d.source ⊆ K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < τ} ∧
        ContMDiffOn (hI.boundaryI.prod (𝓡∂ 1)) I ∞ d d.source ∧
        ContMDiffOn I (hI.boundaryI.prod (𝓡∂ 1)) ∞ d.symm d.target ∧
        ∀ z ∈ d.source, d z = φ (z.1, z.2.1 0) := by
    intro x
    obtain ⟨v, hv, hvin⟩ := hderiv x.1 x.2
    exact exists_collar_coordinates_of_one_sided hKo x.2 hτ hφ hzero hv hvin
  choose d hxd hdK hd hdi hdeq using hlocal
  let S := ⋃ x : K, (d x).source
  have hS : IsOpen S := isOpen_iUnion (fun x ↦ (d x).open_source)
  have hzeroS : K ×ˢ {(0 : EuclideanHalfSpace 1)} ⊆ S := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht' : t = 0 := ht
    rw [ht']
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxd ⟨x, hx⟩⟩
  obtain ⟨ε, hε, hετ, hstrip⟩ := exists_halfStrip_subset hK hS hzeroS hτ
  let A := K ×ˢ {t : EuclideanHalfSpace 1 | t.1 0 < ε}
  have hA : IsOpen A := hKo.prod
    (isOpen_lt ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val) continuous_const)
  let F : BoundaryManifold I M × EuclideanHalfSpace 1 → M := fun z ↦ φ (z.1, z.2.1 0)
  have hFlocal : IsLocalDiffeomorphOn (hI.boundaryI.prod (𝓡∂ 1)) I ∞ F A := by
    intro z
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hstrip z.2)
    exact ⟨{ toPartialEquiv := (d x).toPartialEquiv
             open_source := (d x).open_source
             open_target := (d x).open_target
             contMDiffOn_toFun := hd x
             contMDiffOn_invFun := hdi x }, hx, fun q hq ↦ (hdeq x q hq).symm⟩
  have hFinj : InjOn F A := by
    intro z hz w hw heq
    have hh := hinj ⟨hz.1, z.2.2, hz.2.le.trans hετ.le⟩
      ⟨hw.1, w.2.2, hw.2.le.trans hετ.le⟩ heq
    apply Prod.ext (Prod.mk.inj hh).1
    apply Subtype.ext
    apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).injective
    exact (Prod.mk.inj hh).2
  let : Nonempty (BoundaryManifold I M × EuclideanHalfSpace 1) :=
    ⟨hKne.choose, 0⟩
  obtain ⟨D, hDA, _, hDF⟩ := exists_partialDiffeomorph_of_injOn hA hFlocal hFinj
  refine ⟨ε, hε, hετ, D, hDA, (fun z ↦ congrFun hDF z), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxD : (x, (0 : EuclideanHalfSpace 1)) ∈ D.source := by
    rw [hDA]
    exact ⟨hx, hε⟩
  have hh := D.toOpenPartialHomeomorph.map_source hxD
  change D (x, (0 : EuclideanHalfSpace 1)) ∈ D.target at hh
  rw [hDF] at hh
  change φ (x, 0) ∈ D.target at hh
  rwa [hzero x hx] at hh

end DifferentialGeometry.Geometry.Boundary
