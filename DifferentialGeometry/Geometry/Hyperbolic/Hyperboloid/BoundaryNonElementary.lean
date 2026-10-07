import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereDisplacement
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HoroballBoundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.DisplacementBoundary
import DifferentialGeometry.Topology.GroupAction.CompactLifting
import Mathlib.Topology.Order.Compact

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "H₃" => Hyperboloid E₃

private theorem not_compact_thick_of_invariant_unbounded
    (Γ : Subgroup (H₃ ≃ᵢ H₃)) (δ : ℝ)
    (F : H₃ → ℝ) (hF : Continuous F)
    (hinv : ∀ (γ : Γ) (x : H₃), F ((γ : H₃ ≃ᵢ H₃) x) = F x)
    (c : ℝ → H₃) (hc : Filter.Tendsto (F ∘ c) Filter.atTop Filter.atTop)
    (hthick : ∀ᶠ t in Filter.atTop, ∀ γ : Γ, γ ≠ 1 →
      δ ≤ dist (c t) ((γ : H₃ ≃ᵢ H₃) (c t))) :
    ¬ IsCompact ((Quotient.mk (MulAction.orbitRel Γ H₃)) ''
      {x : H₃ | ∀ γ : Γ, γ ≠ 1 → δ ≤ dist x ((γ : H₃ ≃ᵢ H₃) x)}) := by
  intro hcompact
  obtain ⟨S, hS, hrep⟩ := MulAction.exists_compact_representatives hcompact
  obtain ⟨R, hR⟩ := hS.bddAbove_image hF.continuousOn
  obtain ⟨t, htlarge, htthick⟩ :=
    ((hc.eventually (Filter.eventually_gt_atTop R)).and hthick).exists
  obtain ⟨γ, hγ⟩ := hrep (c t) ⟨c t, htthick, rfl⟩
  have hbound : F ((γ : H₃ ≃ᵢ H₃) (c t)) ≤ R := hR ⟨γ • c t, hγ, rfl⟩
  rw [hinv] at hbound
  exact (not_lt_of_ge hbound) htlarge

private theorem exists_ideal_point_ne_pair (ξ η : Metric.sphere (0 : E₃) 1) :
    ∃ ζ : Metric.sphere (0 : E₃) 1, ζ ≠ ξ ∧ ζ ≠ η := by
  let u : ℂ → Metric.sphere (0 : E₃) 1 := fun z => (stereographicComplex.symm z).val
  have hu : Function.Injective u := fun z w h => stereographicComplex.symm.injective (Subtype.ext h)
  obtain ⟨ζ, _, hζ⟩ := (Set.infinite_range_of_injective hu).exists_notMem_finite
    ((Set.finite_singleton η).insert ξ)
  exact ⟨ζ, fun h => hζ (by simp [h]),
    fun h => hζ (by simp [h])⟩

private theorem exists_curve_tendsto_ideal (ζ : Metric.sphere (0 : E₃) 1) :
    ∃ c : ℝ → H₃, Filter.Tendsto (fun t => (kleinHomeomorph (c t) : E₃))
      Filter.atTop (𝓝 (ζ : E₃)) := by
  let v : ℝ × E₃ := (0, (ζ : E₃))
  have hv : lorentzForm E₃ v v = 1 := by simp [v, lorentzForm_apply, norm_eq_of_mem_sphere]
  have ho : lorentzForm E₃ ((origin : H₃).time, origin.space) v = 0 := by
    simp [v, lorentzForm_apply]
  refine ⟨geodesicLine origin v hv ho, ?_⟩
  simpa only [v, origin_time, origin_space, add_zero, zero_add, inv_one, one_smul] using
    tendsto_kleinHomeomorph_geodesicLine_atTop origin v hv ho

theorem not_exists_common_boundary_fixed_of_isCompact_thick_part
    (Γ : Subgroup (H₃ ≃ᵢ H₃)) [DiscreteTopology Γ]
    (hfree : ∀ γ : Γ, γ ≠ 1 → ∀ x : H₃, (γ : H₃ ≃ᵢ H₃) x ≠ x)
    (δ : ℝ)
    (hcompact : IsCompact ((Quotient.mk (MulAction.orbitRel Γ H₃)) ''
      {x : H₃ | ∀ γ : Γ, γ ≠ 1 → δ ≤ dist x ((γ : H₃ ≃ᵢ H₃) x)})) :
    ¬ ∃ ξ : Metric.sphere (0 : E₃) 1,
      ∀ γ : Γ, boundaryHomeomorph (γ : H₃ ≃ᵢ H₃) ξ = ξ := by
  rintro ⟨ξ, hξ⟩
  let height (η : Metric.sphere (0 : E₃) 1) (x : H₃) :=
    x.time - inner ℝ x.space (η : E₃)
  have hcontinuous (η : Metric.sphere (0 : E₃) 1) : Continuous (height η) :=
    continuous_time.sub (continuous_space.inner continuous_const)
  by_cases hscale : ∀ γ : Γ, (lorentzExtension (γ : H₃ ≃ᵢ H₃) (1, (ξ : E₃))).1 = 1
  · obtain ⟨ζ, hζξ, _⟩ := exists_ideal_point_ne_pair ξ ξ
    obtain ⟨c, hc⟩ := exists_curve_tendsto_ideal ζ
    have hh := tendsto_time_sub_inner_atTop_of_tendsto_kleinHomeomorph hc ξ hζξ
    obtain ⟨C, hC⟩ := exists_bound_time_sub_inner_of_small_displacement Γ hfree ξ hξ hscale δ
    have hthick : ∀ᶠ t in Filter.atTop, ∀ γ : Γ, γ ≠ 1 →
        δ ≤ dist (c t) ((γ : H₃ ≃ᵢ H₃) (c t)) := by
      filter_upwards [hh.eventually (Filter.eventually_gt_atTop C)] with t ht γ hγ
      apply le_of_not_gt
      intro hsmall
      have hb := hC (c t) ⟨γ, hγ, by simpa only [dist_comm] using hsmall⟩
      exact (not_lt_of_ge hb) ht
    have hinv (γ : Γ) (x : H₃) : height ξ ((γ : H₃ ≃ᵢ H₃) x) = height ξ x := by
      have h := time_sub_inner_boundaryHomeomorph (γ : H₃ ≃ᵢ H₃) ξ x
      rwa [hξ γ, hscale γ, div_one] at h
    exact not_compact_thick_of_invariant_unbounded Γ δ (height ξ) (hcontinuous ξ)
      hinv c hh hthick hcompact
  · push Not at hscale
    obtain ⟨γ, hγscale⟩ := hscale
    obtain ⟨η, hηξ, hη⟩ :=
      exists_common_boundary_fixed_ne_of_discrete_of_lorentzExtension_time_ne_one Γ ξ hξ γ hγscale
    obtain ⟨ζ, hζξ, hζη⟩ := exists_ideal_point_ne_pair ξ η
    obtain ⟨c, hc⟩ := exists_curve_tendsto_ideal ζ
    let F : H₃ → ℝ := fun x => height ξ x * height η x
    have hF : Continuous F := (hcontinuous ξ).mul (hcontinuous η)
    have hinv (g : Γ) (x : H₃) : F ((g : H₃ ≃ᵢ H₃) x) = F x := by
      have hfirst := time_sub_inner_boundaryHomeomorph (g : H₃ ≃ᵢ H₃) ξ x
      have hsecond := time_sub_inner_boundaryHomeomorph (g : H₃ ≃ᵢ H₃) η x
      rw [hξ g] at hfirst
      rw [hη g] at hsecond
      dsimp only [F, height]
      rw [hfirst, hsecond, div_mul_div_comm,
        boundary_time_mul_eq_one_of_fixed (g : H₃ ≃ᵢ H₃) ξ η (hξ g) (hη g) hηξ.symm, div_one]
    have hlim : Filter.Tendsto (F ∘ c) Filter.atTop Filter.atTop :=
      (tendsto_time_sub_inner_atTop_of_tendsto_kleinHomeomorph hc ξ hζξ).atTop_mul_atTop₀
        (tendsto_time_sub_inner_atTop_of_tendsto_kleinHomeomorph hc η hζη)
    have hthick := eventually_forall_le_dist_of_two_boundary_fixed Γ hfree ξ η hηξ.symm
      hξ hη hζξ hζη hc δ
    exact not_compact_thick_of_invariant_unbounded Γ δ F hF hinv c hlim hthick hcompact

end DifferentialGeometry.Hyperboloid
