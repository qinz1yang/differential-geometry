import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopCollarModel

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1

open GC.Endpoint GC.GraphManifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Geometry.Hyperbolic

universe u v

section Family

variable {M : Type u} [TopologicalSpace M] {I : Type v}
  {H : I → FiniteVolumeHyperbolicModel.{u}}

/-- Index of all boundary tori of a finite family of truncations. -/
abbrev TorusIdx_LTP1 (T : ∀ i, HyperbolicTruncation (H i)) : Type v := Σ i : I, Fin (T i).count

/-- The part of `M` outside the images of the truncation cores. -/
def familyRegion_LTP1 (T : ∀ i, HyperbolicTruncation (H i)) (f : ∀ i, (H i).Carrier → M) : Set M :=
  (⋃ i, f i '' ((T i).inclusion '' ((T i).core.interior : Set (T i).core.Carrier)))ᶜ

variable (T : ∀ i, HyperbolicTruncation (H i)) (D : ∀ i, Set (H i).Carrier)

/-- Uniform scale: the bicollars restricted to `|s| < c` stay in the domains `D i`. -/
theorem exists_uniform_scale_LTP1 [Finite I] (hDo : ∀ i, IsOpen (D i))
    (hr : ∀ i, range (T i).inclusion ⊆ D i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (j : TorusIdx_LTP1 T) (z : Torus) (s : ℝ), |s| < c →
      bicollar_LTP1 (T j.1) j.2 (z, s) ∈ D j.1 := by
  have hj : ∀ j : TorusIdx_LTP1 T, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ z : Torus,
      (z, s) ∈ (bicollar_LTP1 (T j.1) j.2).source ∧ bicollar_LTP1 (T j.1) j.2 (z, s) ∈ D j.1 := by
    intro j
    let b := bicollar_LTP1 (T j.1) j.2
    have hA : IsOpen (b.source ∩ b ⁻¹' D j.1) :=
      b.continuousOn.isOpen_inter_preimage b.open_source (hDo j.1)
    have hsub : (univ : Set Torus) ×ˢ ({0} : Set ℝ) ⊆ b.source ∩ b ⁻¹' D j.1 := by
      rintro ⟨z, s⟩ ⟨-, hs⟩
      have hs0 : s = 0 := hs
      subst hs0
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      change b (z, 0) ∈ D j.1
      rw [bicollar_zero_LTP1]
      exact hr j.1 ⟨_, rfl⟩
    obtain ⟨u, v, hu, hv, hzu, hsv, huv⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton hA hsub
    filter_upwards [hv.mem_nhds (hsv rfl)] with s hs z
    exact huv ⟨hzu (mem_univ z), hs⟩
  have hall := Filter.eventually_all.mpr hj
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun j z s hs => ?_⟩
  have : dist s 0 < ε := by
    rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hs (min_le_left _ _)
  exact (hεP this j z).2

end Family

end GC.LongTime.CuspP1
