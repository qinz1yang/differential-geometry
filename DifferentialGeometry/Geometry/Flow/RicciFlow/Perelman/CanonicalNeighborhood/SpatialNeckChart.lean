import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Neck.ScaleComparison

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance spatialNeckChartSphereDimension :
    Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}

def SpatialNeck.cylindricalChart (nk : SpatialNeck g eps x) :
    DifferentialGeometry.Geometry.Neck.cylindricalChart I3 (M := M) where
  domain := ⟨univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  target := ⟨nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹), image_opens_isOpen nk.map
    (U := ⟨univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩) nk.domain⟩
  chart := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo nk.map
    (U := ⟨univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩) nk.domain
  scale := metricScalarAt g x
  scale_pos := nk.Q_pos

theorem SpatialNeck.cylindricalChart_region (nk : SpatialNeck g eps x)
    (A : Set nk.cylindricalChart.domain) :
    nk.cylindricalChart.region A = nk.map '' (Subtype.val '' A) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨nk.cylindricalChart.chart w, ⟨w, hw, rfl⟩, rfl⟩

variable [T2Space M]

theorem SpatialNeck.cylindricalChart_metricCloseOn (nk : SpatialNeck g eps x) :
    nk.cylindricalChart.metricCloseOn g eps univ := by
  intro y _ a ha
  have horder : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have hh := (lt_inv_comm₀ (by norm_num : (0 : ℝ) < 11) nk.eps_pos).mpr (by simpa only [one_div] using nk.eps_small)
    have hh' : (2 : ℝ) ≤ eps⁻¹ := by linarith
    exact_mod_cast hh'.trans (Nat.le_ceil eps⁻¹)
  let G := Diffeomorph.pullbackMetricCross
    (scaleMetric nk.cylindricalChart.scale nk.cylindricalChart.scale_pos
      (g.restrictOpen nk.cylindricalChart.target)) nk.cylindricalChart.chart
  have hG (z : nk.cylindricalChart.domain) (v w : TangentSpace IC z) :
      G.inner z v w = (scaleMetric (metricScalarAt g x) nk.Q_pos g).inner (nk.map z)
        (mfderiv IC I3 nk.map (z : Cylinder) v) (mfderiv IC I3 nk.map (z : Cylinder) w) := by
    rw [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner, scaleMetric_inner]
    have hd (v : TangentSpace IC z) :
        mfderiv IC I3 nk.cylindricalChart.chart z v =
          mfderiv IC I3 nk.map (z : Cylinder) v :=
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo nk.map
        (U := nk.cylindricalChart.domain) nk.domain z v
    rw [hd v, hd w]
    rfl
  have hh := nk.comparison.metricDerivNorm_of_local_metric
    nk.cylindricalChart.domain (subset_refl _) 0 G hG a y
  have hb := nk.comparison.close a 0 (by omega) 0 (by simp) (y : Cylinder) y.property
  rw [← hh] at hb
  simpa only [nk.cylinder.metric_zero_eq_roundCylinder] using hb

theorem SpatialNeck.abs_scalar_ratio_sub_one_le (nk : SpatialNeck g eps x)
    {y : Cylinder} (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
    |metricScalarAt g (nk.map y) / metricScalarAt g x - 1| ≤ 4323 * eps := by
  apply nk.cylindricalChart.scalar_comparison_of_metricCloseOn g eps
    (by linarith [nk.eps_small]) nk.cylindricalChart_metricCloseOn
  rw [nk.cylindricalChart_region]
  exact ⟨y, ⟨⟨y, hy⟩, mem_univ _, rfl⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
