import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinConvergence
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinCompactification
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicBoundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryStabilizer

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem boundaryHomeomorph_eq_self_of_tendsto_kleinHomeomorph_of_dist_bounded
    {α : Type*} {l : Filter α} [l.NeBot]
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) {x : α → Hyperboloid E}
    {ξ : Metric.sphere (0 : E) 1} {C : ℝ}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ξ : E)))
    (hdisp : ∀ᶠ i in l, dist (x i) (f (x i)) ≤ C) :
    boundaryHomeomorph f ξ = ξ := by
  apply Subtype.ext
  exact tendsto_nhds_unique (tendsto_kleinHomeomorph_isometry f hx)
    (tendsto_kleinHomeomorph_of_dist_bounded hdisp hx)

theorem tendsto_dist_isometry_atTop_of_tendsto_kleinHomeomorph
    {α : Type*} {l : Filter α}
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) {x : α → Hyperboloid E}
    {ξ : Metric.sphere (0 : E) 1}
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ξ : E)))
    (hne : boundaryHomeomorph f ξ ≠ ξ) :
    Filter.Tendsto (fun i => dist (x i) (f (x i))) l Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro C
  by_contra h
  have hfreq : ∃ᶠ i in l, dist (x i) (f (x i)) < C := by
    simpa only [Filter.Frequently, not_lt] using h
  let l' := l ⊓ Filter.principal {i | dist (x i) (f (x i)) < C}
  have : l'.NeBot := Filter.frequently_iff_neBot.mp hfreq
  have hx' : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l' (𝓝 (ξ : E)) :=
    hx.mono_left inf_le_left
  have hd : ∀ᶠ i in l', dist (x i) (f (x i)) ≤ C := by
    apply Filter.eventually_inf_principal.mpr
    exact Filter.Eventually.of_forall fun i hi => hi.le
  exact hne (boundaryHomeomorph_eq_self_of_tendsto_kleinHomeomorph_of_dist_bounded f hx' hd)

theorem tendsto_dist_geodesicLine_isometry_atTop
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (hne : boundaryHomeomorph f
      ⟨(x.time + v.1)⁻¹ • (x.space + v.2), by
        simpa only [Metric.mem_sphere, dist_zero_right] using
          norm_geodesicLine_forward_endpoint x v hv ho⟩ ≠
      ⟨(x.time + v.1)⁻¹ • (x.space + v.2), by
        simpa only [Metric.mem_sphere, dist_zero_right] using
          norm_geodesicLine_forward_endpoint x v hv ho⟩) :
    Filter.Tendsto (fun t => dist (geodesicLine x v hv ho t)
      (f (geodesicLine x v hv ho t))) Filter.atTop Filter.atTop := by
  exact tendsto_dist_isometry_atTop_of_tendsto_kleinHomeomorph f
    (tendsto_kleinHomeomorph_geodesicLine_atTop x v hv ho) hne

theorem eventually_forall_le_dist_of_two_boundary_fixed
    [FiniteDimensional ℝ E]
    (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ y : Hyperboloid E,
      (γ : Hyperboloid E ≃ᵢ Hyperboloid E) y ≠ y)
    (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η)
    (hξ : ∀ g : Γ, boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) ξ = ξ)
    (hη : ∀ g : Γ, boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) η = η)
    {α : Type*} {l : Filter α} {x : α → Hyperboloid E}
    {ζ : Metric.sphere (0 : E) 1} (hζξ : ζ ≠ ξ) (hζη : ζ ≠ η)
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ζ : E)))
    (R : ℝ) :
    ∀ᶠ i in l, ∀ g : Γ, g ≠ 1 → R ≤ dist (x i) ((g : Hyperboloid E ≃ᵢ Hyperboloid E) (x i)) := by
  have hfix (g : Γ) (hg : g ≠ 1) :
      boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E) ζ ≠ ζ := by
    intro heq
    have hcard := fixedPoints_boundaryHomeomorph_encard_le_two
      (g : Hyperboloid E ≃ᵢ Hyperboloid E) (hfree g hg)
    have hpair : ({ξ, η} : Set (Metric.sphere (0 : E) 1)) =
        Function.fixedPoints (boundaryHomeomorph (g : Hyperboloid E ≃ᵢ Hyperboloid E)) :=
      ((Set.finite_singleton η).insert ξ).eq_of_subset_of_encard_le
        (Set.pair_subset (hξ g) (hη g)) (by simpa only [Set.encard_pair hne] using hcard)
    have hmem : ζ ∈ ({ξ, η} : Set (Metric.sphere (0 : E) 1)) := by
      rw [hpair]
      exact heq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hζξ, hζη, or_self] at hmem
  let S : Set Γ := {g | ∃ y : Hyperboloid E,
    dist y ((g : Hyperboloid E ≃ᵢ Hyperboloid E) y) ≤ R}
  have hS : S.Finite := finite_setOf_exists_dist_apply_le_of_boundary_fixed Γ ξ η hne hξ hη R
  have hevent : ∀ᶠ i in l, ∀ g ∈ S, g ≠ 1 →
      R ≤ dist (x i) ((g : Hyperboloid E ≃ᵢ Hyperboloid E) (x i)) := by
    apply hS.eventually_all.mpr
    intro g _
    by_cases hg : g = 1
    · exact Filter.Eventually.of_forall fun _ h => (h hg).elim
    · exact ((tendsto_dist_isometry_atTop_of_tendsto_kleinHomeomorph
        (g : Hyperboloid E ≃ᵢ Hyperboloid E) hx
        (hfix g hg)).eventually (Filter.eventually_ge_atTop R)).mono fun _ hi _ => hi
  filter_upwards [hevent] with i hi g hg
  by_cases hgs : g ∈ S
  · exact hi g hgs hg
  · apply le_of_not_ge
    intro hle
    exact hgs ⟨x i, hle⟩

end DifferentialGeometry.Hyperboloid
