import DifferentialGeometry.Geometry.Neck.SpatialCommonCenterGraph
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Metric (cylinderAxialDiffeomorph)

private theorem translated_spatial_neck_map
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p q : M} {eps alpha a : ℝ}
    (nk : SpatialNeck g eps p) (out : SpatialNeck g alpha q)
    (hmap : out.map = partialDiffeomorphTransMixed
      (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
      nk.map) (z : Cylinder) : out.map z = nk.map (z.1, a + z.2) := by
  rw [hmap]
  change nk.map (z.1, a + 1 * z.2) = _
  rw [one_mul]

private theorem spatial_neck_map_cast
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {p q : M} {eps : ℝ}
    (h : p = q) (nk : SpatialNeck g eps p) : (h ▸ nk).map = nk.map := by
  cases h
  rfl

universe u

theorem exists_spatial_neck_level_graph_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (u₀ u₁ : Sphere 2) (a b : ℝ), |a| ≤ 4 → |b| ≤ 4 →
          nk₀.map (u₀, a) = nk₁.map (u₁, b) →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧
            (∀ q, |h q - b| < 1 / 10) ∧ h u₁ = b ∧
            (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ∧
            ∀ q, nk₁.map (q, h q) = nk₀.map (η q, a) := by
  obtain ⟨eta₀, C, heta₀, hC, hgraph⟩ := exists_spatial_neck_common_center_graph_tolerance.{u}
  let eta : ℝ := min (eta₀ / 13000) (min (1 / 156000) (1 / (260000 * C)))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ u₀ u₁ a b ha hb hmeet
  let alpha := 13000 * eps
  have halpha : alpha ≤ eta₀ := by
    have hh := heps.trans (min_le_left _ _)
    dsimp only [alpha]
    linarith
  have hasmall : alpha < 1 / 11 := by
    have hh := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp only [alpha]
    linarith
  have hbound : C * alpha < 1 / 10 := by
    have hh := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (show 0 < 260000 * C by positivity)).mp hh
    dsimp only [alpha]
    nlinarith
  obtain ⟨out₀, hc₀, hm₀⟩ := nk₀.exists_at_coordinate
    hasmall (show 13000 * eps ≤ alpha from le_rfl) u₀ ha
  obtain ⟨out₁, hc₁, hm₁⟩ := nk₁.exists_at_coordinate
    hasmall (show 13000 * eps ≤ alpha from le_rfl) u₁ hb
  let out₀' : SpatialNeck g alpha (nk₁.map (u₁, b)) := hmeet ▸ out₀
  have hm₀' : out₀'.map = partialDiffeomorphTransMixed
      (cylinderAxialDiffeomorph (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
      nk₀.map := by
    exact (spatial_neck_map_cast hmeet out₀).trans hm₀
  obtain ⟨η, k, hk, hkbound, hkzero, hkmem, hkeq⟩ :=
    hgraph alpha halpha M g (nk₁.map (u₁, b)) out₀' out₁
  let h : Sphere 2 → ℝ := fun q => b + k q
  have hmap₀ := translated_spatial_neck_map nk₀ out₀' hm₀'
  have hmap₁ := translated_spatial_neck_map nk₁ out₁ hm₁
  refine ⟨η, h, contMDiff_const.add hk, ?_, ?_, ?_, ?_⟩
  · intro q
    change |b + k q - b| < 1 / 10
    rw [add_sub_cancel_left]
    exact (hkbound q).trans_lt hbound
  · change b + k u₁ = b
    rw [← hc₁, hkzero, add_zero]
  · intro q
    have hepssmall := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hlen : (5 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk₀.eps_pos).mpr (by linarith)
    have hkq : |k q| < 1 / 10 := (hkbound q).trans_lt hbound
    change True ∧ -eps⁻¹ < b + k q ∧ b + k q < eps⁻¹
    exact ⟨trivial, by linarith [(abs_le.mp hb).1, (abs_lt.mp hkq).1],
      by linarith [(abs_le.mp hb).2, (abs_lt.mp hkq).2]⟩
  · intro q
    have hh := hkeq q
    rw [hmap₁, hmap₀, add_zero] at hh
    exact hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
