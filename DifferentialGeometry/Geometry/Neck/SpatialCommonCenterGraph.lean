import DifferentialGeometry.Geometry.Neck.SpatialIsotopy

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_spatial_neck_common_center_graph_tolerance :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p : M)
          (nk₀ nk₁ : SpatialNeck g eps p),
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧
            (∀ q, |h q| ≤ C * eps) ∧
            h nk₁.center = 0 ∧
            (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
            ∀ q, nk₁.map (q, h q) = nk₀.map (η q, 0) := by
  obtain ⟨eta₀, C, heta₀, _, hC, hbound⟩ :=
    exists_spatial_neck_anchored_overlap_estimates.{u}
  obtain ⟨eta₁, heta₁, hgraph⟩ := exists_spatial_neck_center_graph_tolerance.{u}
  refine ⟨min eta₀ eta₁, C, lt_min heta₀ heta₁, hC, ?_⟩
  intro eps heps M _ _ _ _ g p nk₀ nk₁
  have h₀ : p ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(nk₀.center, 0), ⟨mem_univ _, by norm_num⟩, nk₀.center_eq⟩
  have h₁ : p ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(nk₁.center, 0), ⟨mem_univ _, by norm_num⟩, nk₁.center_eq⟩
  obtain ⟨η, h, hh, hmem, heq⟩ :=
    hgraph eps (heps.trans (min_le_right _ _)) M g p p nk₀ nk₁ ⟨p, h₀, h₁⟩
  obtain ⟨σ, hσ, hest⟩ :=
    hbound eps (heps.trans (min_le_left _ _)) M g p p nk₀ nk₁ p h₀ h₁
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hzero (q : Sphere 2) : (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨mem_univ _, by constructor <;> linarith⟩
  have hfull (q : Sphere 2) : (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hx := hmem q
    exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have hax (nk : SpatialNeck g eps p) (z : Cylinder)
      (hz : z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
      nk.cylindricalChart.axial (nk.map z) =
        (Real.sqrt (metricScalarAt g p))⁻¹ * z.2 :=
    nk.cylindricalChart.axial_chart ⟨z, hz⟩
  have hax₀ : nk₀.cylindricalChart.axial p = 0 := by
    simpa only [nk₀.center_eq, mul_zero] using hax nk₀ (nk₀.center, 0) (hzero _)
  have hax₁ : nk₁.cylindricalChart.axial p = 0 := by
    simpa only [nk₁.center_eq, mul_zero] using hax nk₁ (nk₁.center, 0) (hzero _)
  refine ⟨η, h, hh, ?_, ?_, hmem, heq⟩
  · intro q
    have hv := (hest (nk₀.map (η q, 0))
      (Or.inl ⟨(η q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩)).1
    rw [hax nk₀ (η q, 0) (hzero _), mul_zero, hax₀, hax₁,
      ← heq q, hax nk₁ (q, h q) (hfull q)] at hv
    have hsign : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hpos := Real.sqrt_pos.mpr nk₀.Q_pos
    have habs : (Real.sqrt (metricScalarAt g p))⁻¹ * |h q| ≤
        C * eps / Real.sqrt (metricScalarAt g p) := by
      simpa only [Prod.snd, mul_zero, sub_zero, zero_sub, abs_neg, abs_mul,
        hsign, one_mul, abs_of_pos (inv_pos.mpr hpos)] using hv
    have hmul := mul_le_mul_of_nonneg_left habs hpos.le
    have hl : Real.sqrt (metricScalarAt g p) *
        ((Real.sqrt (metricScalarAt g p))⁻¹ * |h q|) = |h q| := by
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    have hr : Real.sqrt (metricScalarAt g p) *
        (C * eps / Real.sqrt (metricScalarAt g p)) = C * eps := by
      field_simp
    rwa [hl, hr] at hmul
  · have he := nk₁.map.injOn (nk₁.domain (hfull (η.symm nk₀.center)))
      (nk₁.domain (hzero nk₁.center))
      ((heq (η.symm nk₀.center)).trans (by rw [η.apply_symm_apply, nk₀.center_eq, nk₁.center_eq]))
    have hq := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    change η.symm nk₀.center = nk₁.center at hq
    change h (η.symm nk₀.center) = 0 at hh
    rwa [hq] at hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
