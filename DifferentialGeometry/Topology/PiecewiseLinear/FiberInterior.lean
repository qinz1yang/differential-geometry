import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.FiberCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.TransverseHeight
import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.mem_nhdsWithin_fiber_of_notMem_image_boundary {n : ℕ}
    (hdimE : Module.finrank ℝ E = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {D : Set E} {g : (Fin (n + 2) → ℝ) → E} (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) D)
    {r : ℝ} (hDr : D ⊆ {x | ℓ x = r}) {q : E} (hq : q ∈ D) (hqJ : q ∉ g '' stdSimplexBoundary (n + 1)) :
    D ∈ 𝓝[{x | ℓ x = r}] q := by
  have hD : IsPLBall (n + 1) D := ⟨g, hg⟩
  obtain ⟨e, π, -, hfixed, -⟩ := exists_affine_coordinates_of_linear_fiber
    (show Module.finrank ℝ E = (n + 1) + 1 by omega) ℓ hℓ r
  have hπinj : InjOn π D := by
    intro x hx y hy heq
    have h := congrArg e heq
    rwa [(hfixed x).mpr (hDr hx), (hfixed y).mpr (hDr hy)] at h
  have hπ : IsPLHomeomorphOn π D (π '' D) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD.isPolyhedron
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron hD.isPolyhedron (subset_univ D))
      ⟨fun x hx => mem_image_of_mem π hx, hπinj, fun _ hy => hy⟩
  have hboundary := (hg.trans hπ).image_stdSimplexBoundary
  have hnot : π q ∉ frontier (π '' D) := by
    rw [← hboundary]
    rintro ⟨z, hz, heq⟩
    exact hqJ ⟨z, hz, hπinj (hg.bijOn.mapsTo hz.1) hq heq⟩
  have hinside : π q ∈ interior (π '' D) := by
    by_contra h
    exact hnot ⟨subset_closure (mem_image_of_mem π hq), h⟩
  have hcont : Filter.Tendsto π (𝓝[{x | ℓ x = r}] q) (𝓝 (π q)) :=
    π.continuous_of_finiteDimensional.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hcont (mem_interior_iff_mem_nhds.mp hinside), self_mem_nhdsWithin] with y hy hyr
  obtain ⟨x, hx, hxy⟩ := hy
  have heq := congrArg e hxy
  rw [(hfixed x).mpr (hDr hx), (hfixed y).mpr hyr] at heq
  exact heq ▸ hx

theorem hasPLCrossingAt_union_fiber_of_mem_nhdsWithin
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {A D : Set E} (hA : IsClosed A) {r : ℝ} (hDr : D ⊆ {x | ℓ x = r})
    {q : E} (hqr : ℓ q = r) (hqD : D ∈ 𝓝[{x | ℓ x = r}] q) (hqA : q ∉ A)
    (f : E →ₗ[ℝ] ℝ) {d : E} (hd : d ∈ LinearMap.ker ℓ) (hfd : f d ≠ 0) :
    HasPLCrossingAt (A ∪ D) {x | f x = f q} q := by
  have hdim : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
    omega
  obtain ⟨U, hU, hUD⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hqD
  have hlocal : ∀ᶠ x in 𝓝 q, x - q ∈ LinearMap.ker ℓ ↔ x ∈ A ∪ D := by
    filter_upwards [hU, hA.isOpen_compl.mem_nhds hqA] with x hxU hxA
    have hplane : x - q ∈ LinearMap.ker ℓ ↔ ℓ x = r := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero, hqr]
    rw [hplane]
    constructor
    · intro hx
      exact Or.inr (hUD ⟨hxU, hx⟩)
    · intro hx
      exact hDr (hx.resolve_left hxA)
  exact (hasPLCrossingAt_affineSubspace_fiber (LinearMap.ker ℓ) hdim hdimE f hd hfd q).congr
    hlocal (Filter.Eventually.of_forall fun _ => Iff.rfl)

theorem hasPLCrossingAt_cap_fiber_of_notMem_image_boundary
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {A D : Set E} (hA : IsClosed A) {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D) {r : ℝ} (hDr : D ⊆ {x | ℓ x = r})
    (hAD : A ∩ D ⊆ g '' stdSimplexBoundary 2) {q p : E} (hq : q ∈ D)
    (hqJ : q ∉ g '' stdSimplexBoundary 2) (hpr : ℓ p = r) (f : E →ₗ[ℝ] ℝ) (hf : f q ≠ f p) :
    HasPLCrossingAt (A ∪ D) {x | f x = f q} q := by
  have hd : q - p ∈ LinearMap.ker ℓ := by
    rw [LinearMap.mem_ker, map_sub, hDr hq, hpr, sub_self]
  have hfd : f (q - p) ≠ 0 := by rwa [map_sub, sub_ne_zero]
  exact hasPLCrossingAt_union_fiber_of_mem_nhdsWithin hdimE ℓ hℓ hA hDr (hDr hq)
    (hg.mem_nhdsWithin_fiber_of_notMem_image_boundary hdimE ℓ hℓ hDr hq hqJ)
    (fun hqA => hqJ (hAD ⟨hqA, hq⟩)) f hd hfd

theorem heightSingularPoints_cap_inter_subset_image_boundary
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {A D : Set E} (hA : IsClosed A) {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D) {r : ℝ} (hDr : D ⊆ {x | ℓ x = r})
    (hAD : A ∩ D ⊆ g '' stdSimplexBoundary 2) {p : E} (hpr : ℓ p = r)
    (f : E →ₗ[ℝ] ℝ) (hside : ∀ q ∈ D \ {p}, f q ≠ f p) :
    heightSingularPoints (A ∪ D) f ∩ D ⊆ g '' stdSimplexBoundary 2 ∪ {p} := by
  rintro q ⟨hq, hqD⟩
  by_cases hqJ : q ∈ g '' stdSimplexBoundary 2
  · exact Or.inl hqJ
  by_cases hqp : q = p
  · exact Or.inr hqp
  exact (hq.2.1 (hasPLCrossingAt_cap_fiber_of_notMem_image_boundary hdimE ℓ hℓ hA hg hDr hAD
    hqD hqJ hpr f (hside q ⟨hqD, hqp⟩))).elim

end DifferentialGeometry.Topology.PiecewiseLinear
