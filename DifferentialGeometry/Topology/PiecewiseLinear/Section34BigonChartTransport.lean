import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Topology

namespace DifferentialGeometry.Topology

theorem exists_openPartialHomeomorph_of_continuousOn_injOn_finrank
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U) (hi : InjOn f U) :
    ∃ e : OpenPartialHomeomorph E F, e.source = U ∧ ∀ x, e x = f x := by
  have hopen : IsOpenMap (U.domRestrict f) := by
    intro W hW
    have hval := hU.isOpenMap_subtype_val W hW
    have hsub : ((↑) : U → E) '' W ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have heq : U.domRestrict f '' W = f '' (((↑) : U → E) '' W) := by
      rw [image_image]
      rfl
    rw [heq]
    exact invariance_of_domain_isOpen_image_of_finrank_eq hdim hval
      (hf.mono hsub) (hi.mono hsub)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U) hf hopen hU,
    rfl, fun _ => rfl⟩

theorem OpenPartialHomeomorph.exists_square_image_subset_of_nhdsWithin
    {X : Type*} [TopologicalSpace X] {S N : Set X}
    (e : OpenPartialHomeomorph (ℝ × ℝ) S) {ε : ℝ} (hε : 0 < ε)
    (hsource : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hN : N ∈ 𝓝[S] (e (0, 0) : X)) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      (fun p => (e p : X)) '' (Ioo (-η) η ×ˢ Ioo (-η) η) ⊆ N := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have he : ContinuousAt e (0, 0) :=
    e.continuousOn.continuousAt (e.open_source.mem_nhds (hsource ⟨hzero, hzero⟩))
  have hN' : ((↑) : S → X) ⁻¹' N ∈ 𝓝 (e (0, 0)) := by
    rwa [← map_nhds_subtype_val (e (0, 0))] at hN
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.mp (he.preimage_mem_nhds hN')
  refine ⟨min ε ρ, lt_min hε hρ, min_le_left _ _, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  apply hρN
  have hle := min_le_right ε ρ
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff, abs_lt]
  exact ⟨⟨by linarith [hp.1.1], lt_of_lt_of_le hp.1.2 hle⟩,
    ⟨by linarith [hp.2.1], lt_of_lt_of_le hp.2.2 hle⟩⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.mem_nhdsWithin_of_mem_image_openSimplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {N : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) N) (hNK : N ⊆ K.space)
    {x : E} (hx : x ∈ r '' openSimplex (stdVertices 1)) : N ∈ 𝓝[K.space] x := by
  rw [hr.image_openSimplex_stdVertices] at hx
  have hbd := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK
  have hxnot : x ∉ closure (K.space \ N) := fun h => hx.2 (hbd.subset ⟨hx.1, h⟩)
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    ⟨(closure (K.space \ N))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxnot, ?_⟩
  intro y hy
  by_contra h
  exact hy.1 (subset_closure ⟨hy.2, h⟩)

theorem IsPLHomeomorphOn.exists_surface_chart_in_planar_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S N : Set E} {D : Set (EuclideanSpace ℝ (Fin 2))}
    {σ : E → EuclideanSpace ℝ (Fin 2)} (hσ : IsPLHomeomorphOn σ N D)
    (e : OpenPartialHomeomorph (ℝ × ℝ) S) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hsource : U ⊆ e.source)
    (hUN : (fun p => (e p : E)) '' U ⊆ N) :
    ∃ d : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      d.source = U ∧ (∀ p, d p = σ (e p)) ∧
      ∀ p ∈ U, ∀ A ⊆ N, d p ∈ σ '' A ↔ (e p : E) ∈ A := by
  have hcont : ContinuousOn (fun p => σ (e p)) U :=
    hσ.isPiecewiseAffineOn.continuousOn.comp
      (continuous_subtype_val.comp_continuousOn (e.continuousOn.mono hsource))
      (fun p hp => hUN ⟨p, hp, rfl⟩)
  have hinj : InjOn (fun p => σ (e p)) U := by
    intro p hp q hq hpq
    apply e.injOn (hsource hp) (hsource hq)
    exact Subtype.ext (hσ.bijOn.injOn (hUN ⟨p, hp, rfl⟩) (hUN ⟨q, hq, rfl⟩) hpq)
  obtain ⟨d, hd, hdeq⟩ := Topology.exists_openPartialHomeomorph_of_continuousOn_injOn_finrank
    (by simp [Module.finrank_prod]) hU hcont hinj
  refine ⟨d, hd, hdeq, ?_⟩
  intro p hp A hAN
  rw [hdeq p]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hxE : x = (e p : E) := hσ.bijOn.injOn (hAN hx) (hUN ⟨p, hp, rfl⟩) heq
    exact hxE ▸ hx
  · intro hpA
    exact ⟨e p, hpA, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
