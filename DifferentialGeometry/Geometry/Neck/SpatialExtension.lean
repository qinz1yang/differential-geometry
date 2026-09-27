import DifferentialGeometry.Geometry.Neck.SpatialIsotopy
import DifferentialGeometry.Topology.Manifold.GraphBand

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem SpatialNeck.axial_map
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p) {z : Cylinder}
    (hz : z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
    nk.cylindricalChart.axial (nk.map z) =
      (Real.sqrt (metricScalarAt g p))⁻¹ * z.2 :=
  nk.cylindricalChart.axial_chart ⟨z, hz⟩

universe u

theorem exists_spatial_neck_frontier_step_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (u : Sphere 2), nk₀.map (u, 1) = p₁ →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧
            (∀ q, (1 / 2 : ℝ) < h q ∧ h q < 3 / 2) ∧
            (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
            ∀ q, nk₀.map (q, h q) = nk₁.map (η q, 0) := by
  obtain ⟨eta₀, C, heta₀, hsmall₀, hC, hbound⟩ :=
    exists_spatial_neck_anchored_overlap_estimates.{u}
  obtain ⟨eta₁, heta₁, hgraph⟩ := exists_spatial_neck_center_graph_tolerance.{u}
  let eta : ℝ := min eta₀ (min eta₁ (1 / (8 * C)))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ u hcenter
  have heps₀ : eps ≤ eta₀ := heps.trans (min_le_left _ _)
  have heps₁ : eps ≤ eta₁ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsC : eps ≤ 1 / (8 * C) := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hunit : (univ ×ˢ Icc (-1 : ℝ) 1 : Set Cylinder) ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, (neg_lt_neg hlen).trans_le hz.2.1, hz.2.2.trans_lt hlen⟩
  have h₀ : p₁ ∈ nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(u, 1), ⟨mem_univ _, by norm_num⟩, hcenter⟩
  have h₁ : p₁ ∈ nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨(nk₁.center, 0), ⟨mem_univ _, by norm_num⟩, nk₁.center_eq⟩
  obtain ⟨η, h, hh, hmem, heq⟩ := hgraph eps heps₁ M g p₁ p₀ nk₁ nk₀ ⟨p₁, h₁, h₀⟩
  obtain ⟨σ, hσ, hest⟩ := hbound eps heps₀ M g p₁ p₀ nk₁ nk₀ p₁ h₁ h₀
  have hax₁ : nk₁.cylindricalChart.axial p₁ = 0 := by
    have hh := nk₁.axial_map (hunit (show (nk₁.center, (0 : ℝ)) ∈ univ ×ˢ Icc (-1 : ℝ) 1 from
      ⟨mem_univ _, by norm_num⟩))
    simpa only [nk₁.center_eq, mul_zero] using hh
  have hax₀ : nk₀.cylindricalChart.axial p₁ = (Real.sqrt (metricScalarAt g p₀))⁻¹ := by
    rw [← hcenter, nk₀.axial_map (hunit ⟨mem_univ _, by norm_num⟩), mul_one]
  have hratio := nk₀.scalar_ratio_of_common_point nk₁ (heps₀.trans_lt hsmall₀)
    ((image_mono hunit) h₀) ((image_mono hunit) h₁)
  have hQ : metricScalarAt g p₀ ≤ 4 * metricScalarAt g p₁ := by
    apply (div_le_iff₀ nk₁.Q_pos).mp
    have hh := (abs_le.mp hratio).2
    linarith [heps₀.trans_lt hsmall₀]
  have hsqrt : Real.sqrt (metricScalarAt g p₀) ≤ 2 * Real.sqrt (metricScalarAt g p₁) := by
    nlinarith [Real.sq_sqrt nk₀.Q_pos.le, Real.sq_sqrt nk₁.Q_pos.le,
      Real.sqrt_nonneg (metricScalarAt g p₀), Real.sqrt_nonneg (metricScalarAt g p₁)]
  have hepspos := nk₀.eps_pos
  have hCeps : C * eps ≤ 1 / 8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * C)).mp hepsC
    nlinarith
  refine ⟨η, h, hh, ?_, hmem, heq⟩
  intro q
  have hv := (hest (nk₁.map (η q, 0))
    (Or.inl ⟨(η q, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩)).1
  have hqfull : (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hx := hmem q
    exact ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  rw [nk₁.axial_map (hunit ⟨mem_univ _, by norm_num⟩), mul_zero,
    hax₁, hax₀, ← heq q, nk₀.axial_map hqfull] at hv
  have habs : |(Real.sqrt (metricScalarAt g p₀))⁻¹ * (h q - 1)| ≤
      C * eps / Real.sqrt (metricScalarAt g p₁) := by
    have he : 0 - σ * ((Real.sqrt (metricScalarAt g p₀))⁻¹ * h q) -
        (0 - σ * (Real.sqrt (metricScalarAt g p₀))⁻¹) =
        -σ * ((Real.sqrt (metricScalarAt g p₀))⁻¹ * (h q - 1)) := by ring
    change |0 - σ * ((Real.sqrt (metricScalarAt g p₀))⁻¹ * h q) -
        (0 - σ * (Real.sqrt (metricScalarAt g p₀))⁻¹)| ≤ _ at hv
    rw [he, abs_mul, abs_neg] at hv
    have hsign : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    simpa only [hsign, one_mul] using hv
  have hpos₀ := Real.sqrt_pos.mpr nk₀.Q_pos
  have hpos₁ := Real.sqrt_pos.mpr nk₁.Q_pos
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpos₀)] at habs
  have hmul := mul_le_mul_of_nonneg_left habs hpos₀.le
  have hcancel : Real.sqrt (metricScalarAt g p₀) *
      ((Real.sqrt (metricScalarAt g p₀))⁻¹ * |h q - 1|) = |h q - 1| := by
    rw [← mul_assoc, mul_inv_cancel₀ hpos₀.ne', one_mul]
  rw [hcancel] at hmul
  have hupper : Real.sqrt (metricScalarAt g p₀) *
      (C * eps / Real.sqrt (metricScalarAt g p₁)) ≤ 2 * C * eps := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpos₁).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ C * eps by positivity)]
  have hfinal := hmul.trans hupper
  constructor <;> linarith [(abs_le.mp hfinal).1, (abs_le.mp hfinal).2]

theorem exists_spatial_neck_frontier_annulus_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (u : Sphere 2), nk₀.map (u, 1) = p₁ →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ)
            (A : PartialDiffeomorph IC I3 Cylinder M ∞),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧ (∀ q, 1 / 2 < h q ∧ h q < 3 / 2) ∧
            (univ ×ˢ Icc (0 : ℝ) 1 ⊆ A.source) ∧
            (∀ q s, A (q, s) = nk₀.map (q, h q * s)) ∧
            (∀ q, A (q, 0) = nk₀.map (q, 0)) ∧
            (∀ q, A (q, 1) = nk₁.map (η q, 0)) ∧
            IsCompact (A '' (univ ×ˢ Icc (0 : ℝ) 1)) ∧
            frontier (A '' (univ ×ˢ Icc (0 : ℝ) 1)) =
              range (fun q : Sphere 2 => nk₀.map (q, 0)) ∪
              range (fun q : Sphere 2 => nk₁.map (q, 0)) ∧
            (nk₀.map '' (univ ×ˢ Icc (0 : ℝ) (1 / 2))) ⊆
              A '' (univ ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨eta, heta, hstep⟩ := exists_spatial_neck_frontier_step_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ u hcenter
  obtain ⟨η, h, hh, hpos, hmem, heq⟩ := hstep eps heps M g p₀ p₁ nk₀ nk₁ u hcenter
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hdomain : {x : Cylinder | x.2 ∈ uIcc (0 : ℝ) (h x.1)} ⊆ nk₀.map.source := by
    intro x hx
    change x.2 ∈ uIcc (0 : ℝ) (h x.1) at hx
    rw [uIcc_of_le (by linarith [(hpos x.1).1] : (0 : ℝ) ≤ h x.1)] at hx
    have hm := hmem x.1
    exact nk₀.domain ⟨mem_univ _, by constructor <;> linarith [hx.1, hx.2, hm.2.2]⟩
  obtain ⟨A, hA, hformula, hrange, hcompact, hfront⟩ :=
    DifferentialGeometry.Topology.exists_graphBand_partialDiffeomorph nk₀.map
      (fun _ => 0) h contMDiff_const hh (fun q => by linarith [(hpos q).1]) hdomain
  have hmap (q : Sphere 2) (s : ℝ) : A (q, s) = nk₀.map (q, h q * s) := by
    simpa only [zero_add, sub_zero] using hformula (q, s)
  have hupper : range (fun q : Sphere 2 => nk₀.map (q, h q)) =
      range (fun q : Sphere 2 => nk₁.map (q, 0)) := by
    rw [show (fun q : Sphere 2 => nk₀.map (q, h q)) =
      (fun q => nk₁.map (q, 0)) ∘ η from funext heq]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨η q, rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨w, rfl⟩ := η.surjective q
      exact ⟨w, rfl⟩
  refine ⟨η, h, A, hh, hpos, hA, hmap, ?_, ?_, hcompact, ?_, ?_⟩
  · intro q
    rw [hmap, mul_zero]
  · intro q
    rw [hmap, mul_one, heq]
  · simpa only [hupper] using hfront
  · rw [hrange]
    apply image_mono
    intro x hx
    change x.2 ∈ uIcc (0 : ℝ) (h x.1)
    rw [uIcc_of_le (by linarith [(hpos x.1).1] : (0 : ℝ) ≤ h x.1)]
    exact ⟨hx.2.1, hx.2.2.trans (hpos x.1).1.le⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
