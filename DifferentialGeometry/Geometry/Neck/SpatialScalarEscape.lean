import DifferentialGeometry.Geometry.Neck.SpatialBandEscape
import DifferentialGeometry.Topology.Compactness.SublevelEscape

open Set Manifold Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ}

theorem tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (hescape : Tendsto (fun n => (neck n).map ((neck n).center, 3 / 2))
      atTop (cocompact M)) :
    Tendsto (fun n => metricScalarAt g (p n)) atTop atTop := by
  have hmid : Tendsto (fun n => metricScalarAt g
      ((neck n).map ((neck n).center, 3 / 2))) atTop atTop :=
    (tendsto_atTop_of_isCompact_sublevel hcompact).comp hescape
  have hbound (n : ℕ) : metricScalarAt g ((neck n).map ((neck n).center, 3 / 2)) ≤
      (1 + 4323 * eps) * metricScalarAt g (p n) := by
    have hinv : (3 / 2 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck n).eps_pos).mpr (by linarith [(neck n).eps_small])
    have hsrc : ((neck n).center, 3 / 2) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
      ⟨mem_univ _, by constructor <;> linarith⟩
    exact ((neck n).scalar_bounds_on_image_window ⟨_, hsrc, rfl⟩).2
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hmid.eventually_ge_atTop ((1 + 4323 * eps) * B)] with n hn
  have hpos : 0 < 1 + 4323 * eps := by linarith [(neck n).eps_pos]
  exact (mul_le_mul_iff_right₀ hpos).mp (hn.trans (hbound n))

theorem eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop
    (hsmall : 4323 * eps < 1) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hscalar : Tendsto (fun n => metricScalarAt g (p n)) atTop atTop)
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ n in atTop, Disjoint K ((neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (metricScalar_smooth g).continuous.continuousOn
  have hpos : 0 < 1 - 4323 * eps := by linarith
  filter_upwards [hscalar.eventually_ge_atTop ((B + 1) / (1 - 4323 * eps))] with n hn
  apply disjoint_left.mpr
  intro y hyK hy
  have hl := ((neck n).scalar_bounds_on_image_window hy).1
  have hlo : B + 1 ≤ (1 - 4323 * eps) * metricScalarAt g (p n) := by
    have h := (div_le_iff₀ hpos).mp hn
    simpa only [mul_comm] using h
  have hup := hB ⟨y, hyK, rfl⟩
  linarith

theorem eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band
    (heps : eps ≤ 1 / 156000) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (havoid : ∀ i j : ℕ, i < j →
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (univ ×ˢ Icc (1 : ℝ) 2))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ n in atTop, Disjoint K ((neck n).map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) := by
  apply eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop
    (by linarith) p neck _ hK
  exact tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact p neck hcompact
    (tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band g heps p neck havoid)

theorem eventually_disjoint_spatial_neck_central_band_of_midpoint_avoids_earlier_band
    (heps : eps ≤ 1 / 156000) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (havoid : ∀ i j : ℕ, i < j →
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (univ ×ˢ Icc (1 : ℝ) 2))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ n in atTop, Disjoint K ((neck n).map '' (univ ×ˢ Icc (-4 : ℝ) 4)) := by
  filter_upwards [eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band
    heps p neck hcompact havoid hK] with n hn
  apply hn.mono_right
  apply image_mono
  rintro ⟨q, t⟩ ⟨hq, ht⟩
  have hinv : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (neck n).eps_pos).mpr (by linarith)
  exact ⟨hq, by constructor <;> linarith [ht.1, ht.2]⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
