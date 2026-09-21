import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Neck.ScaleComparison
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import DifferentialGeometry.Geometry.Neck.OverlapOrientation

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

def SpatialNeck.cylindricalChart (nk : SpatialNeck g eps p) :
    Geometry.Neck.cylindricalChart I3 (M := M) :=
  let U : TopologicalSpace.Opens Cylinder :=
    ⟨univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  { domain := U
    target := ⟨nk.map '' (U : Set Cylinder), image_opens_isOpen nk.map nk.domain⟩
    chart := PartialDiffeomorph.toOpensDiffeo nk.map nk.domain
    scale := metricScalarAt g p
    scale_pos := nk.Q_pos }

@[simp] theorem SpatialNeck.cylindricalChart_domain (nk : SpatialNeck g eps p) :
    (nk.cylindricalChart.domain : Set Cylinder) = univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := rfl

@[simp] theorem SpatialNeck.cylindricalChart_target (nk : SpatialNeck g eps p) :
    (nk.cylindricalChart.target : Set M) = nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := rfl

@[simp] theorem SpatialNeck.cylindricalChart_scale (nk : SpatialNeck g eps p) :
    nk.cylindricalChart.scale = metricScalarAt g p := rfl

@[simp] theorem SpatialNeck.cylindricalChart_apply (nk : SpatialNeck g eps p)
    (z : nk.cylindricalChart.domain) :
    (nk.cylindricalChart.chart z : M) = nk.map z := rfl

@[simp] theorem SpatialNeck.cylindricalChart_symm_apply (nk : SpatialNeck g eps p)
    (z : nk.cylindricalChart.target) :
    (nk.cylindricalChart.chart.symm z : Cylinder) = nk.map.symm z := rfl

private theorem cylinderReference_zero_eq_round (C : CylinderReference) :
    C.metric 0 = Geometry.Metric.roundCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hC := C.inner_eq 0 le_rfl z v w
  apply hC.trans
  rw [Geometry.Metric.roundCylinderMetric_inner]
  simp only [sub_zero, mul_one]
  rfl

variable [T2Space M]

theorem SpatialNeck.cylindricalChart_metricCloseOn (nk : SpatialNeck g eps p) :
    nk.cylindricalChart.metricCloseOn g eps univ := by
  let C := nk.cylindricalChart
  let G := Diffeomorph.pullbackMetricCross
    (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart
  let h := nk.cylinder.metric 0
  have herror : metricTensorField G - metricTensorField (h.restrictOpen C.domain) =
      restrictOpen0S 2 (V := C.domain) (nk.comparison.jet 0 0) := by
    ext z v
    change (metricTensorField G - metricTensorField (h.restrictOpen C.domain)) z v =
      nk.comparison.jet 0 0 z.val v
    erw [nk.comparison.jet_zero, nk.comparison.pullback_eq 0 z.val z.property]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
      metricTensorField_apply, G, Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change metricScalarAt g p * g.inner (nk.map z.val)
        (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map nk.domain) z (v 0))
        (mfderiv IC I3 (PartialDiffeomorph.toOpensDiffeo nk.map nk.domain) z (v 1)) -
        h.inner z.val (v 0) (v 1) = _
    erw [PartialDiffeomorph.mfderiv_toOpensDiffeo, PartialDiffeomorph.mfderiv_toOpensDiffeo]
  intro z _ a ha
  have href : Geometry.Metric.roundCylinderMetric = h :=
    (cylinderReference_zero_eq_round nk.cylinder).symm
  change metricDerivNorm a G _ _ z ≤ eps
  rw [href, ← tensor02CovDerivNormWith_metricTensorField_sub_eq_metricDerivNorm,
    herror, KappaSolutions.tensor02CovDerivNormWith_restrictOpen0S]
  apply nk.comparison.close a 0 _ 0 (by simp) z.val z.property
  have hinv : (2 : ℝ) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ nk.eps_pos).2
    linarith [nk.eps_small]
  have hceil : 2 ≤ Nat.ceil eps⁻¹ := by exact_mod_cast hinv.trans (Nat.le_ceil eps⁻¹)
  simpa only [add_zero, mul_zero] using ha.trans hceil


omit [T2Space M] in
@[simp] theorem SpatialNeck.cylindricalChart_region_univ (nk : SpatialNeck g eps p) :
    nk.cylindricalChart.region univ = nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, _, rfl⟩, rfl⟩
    exact ⟨z.val, z.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨nk.cylindricalChart.chart ⟨z, hz⟩, ⟨⟨z, hz⟩, mem_univ _, rfl⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature Surgery.Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

theorem SpatialNeck.exists_sign_axial_gradient_bound_on_preconnected
    {eps₀ eps₁ : ℝ} {p₀ p₁ : M}
    (nk₀ : SpatialNeck g eps₀ p₀) (nk₁ : SpatialNeck g eps₁ p₁)
    (hε₀ : eps₀ < 1 / 200000) (hε₁ : eps₁ < 1 / 200000)
    {S : Set M} (hS : IsPreconnected S)
    (hS₀ : S ⊆ nk₀.map '' (univ ×ˢ Ioo (-eps₀⁻¹) eps₀⁻¹))
    (hS₁ : S ⊆ nk₁.map '' (univ ×ˢ Ioo (-eps₁⁻¹) eps₁⁻¹)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S,
      Real.sqrt (g.inner x
        (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
          σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)
        (Geometry.Operator.gradFun g nk₀.cylindricalChart.axial x -
          σ • Geometry.Operator.gradFun g nk₁.cylindricalChart.axial x)) ≤
        184712 * (eps₀ + eps₁) := by
  apply nk₀.cylindricalChart.exists_sign_axial_gradient_bound_on_preconnected
    nk₁.cylindricalChart g isOpen_univ isOpen_univ eps₀ eps₁ hε₀ hε₁
    nk₀.cylindricalChart_metricCloseOn nk₁.cylindricalChart_metricCloseOn hS
  · simpa only [nk₀.cylindricalChart_region_univ] using hS₀
  · simpa only [nk₁.cylindricalChart_region_univ] using hS₁

theorem SpatialNeck.scalar_ratio_of_common_point {p₀ p₁ : M}
    (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
    (hε : eps < 1 / 200000) {x : M}
    (hx₀ : x ∈ nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hx₁ : x ∈ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :
    |metricScalarAt g p₀ / metricScalarAt g p₁ - 1| ≤ 17292 * eps := by
  apply nk₀.cylindricalChart.scale_ratio_of_metricCloseOn nk₁.cylindricalChart g eps hε
    nk₀.cylindricalChart_metricCloseOn nk₁.cylindricalChart_metricCloseOn x
  · simpa only [nk₀.cylindricalChart_region_univ] using hx₀
  · simpa only [nk₁.cylindricalChart_region_univ] using hx₁

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
