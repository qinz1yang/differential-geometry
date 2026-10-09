import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

/-!
# CH12-O5 / LTF01b, group A: three-dimensional Einstein algebra

* `ricciEq_constSec_O5`: in dimension three, `Ric = c g` forces sectional curvature `c / 2`.
* `volumeDeficit_of_ricci_O5`: the `VolumeDeficitHyperbolicLimit_S13` shape follows from its Ricci
  half alone (`-(2 s)⁻¹ / 2 = -(4 s)⁻¹`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

section Algebra

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The scalar curvature of a three-dimensional metric with `Ric = c g` is `3 c`. -/
theorem scalar_of_ricciEq_O5 (g : SmoothRiemannianMetric ThreeModel M) (c : ℝ)
    (h : RicciEqualsMetricMultiple_S13 g c) (p : M) :
    metricScalarAt g p = 3 * c := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel p) = 3 := finrank_euclideanSpace_fin
  obtain ⟨basis, -, -, -, horth, -⟩ := exists_orthonormal_curvature_eigenframe g p hdim
  have hON : ∀ i j, g.inner p (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [horth i j]
    fin_cases i <;> fin_cases j <;> simp [delta3]
  rw [metricScalarAt_eq_orthonormal_trace g p basis hON]
  rw [Fin.sum_univ_three, h, h, h, hON, hON, hON]
  simp only [ite_true]
  ring

/-- **A1.** Three-dimensional Einstein algebra: `Ric = c g` gives constant sectional curvature
`c / 2`. -/
theorem ricciEq_constSec_O5 (g : SmoothRiemannianMetric ThreeModel M) (c : ℝ)
    (h : RicciEqualsMetricMultiple_S13 g c) :
    hasConstantSectionalCurvature g (c / 2) := by
  intro p v w hvw
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel p) = 3 := finrank_euclideanSpace_fin
  have hS := scalar_of_ricciEq_O5 g c h p
  have hEin : ∀ v w : TangentSpace ThreeModel p,
      metricRicciAt g p (vec2 v w) = (metricScalarAt g p / 3) * g.inner p v w := by
    intro v w
    rw [metricRicciAt_apply_eq_ricciTensor, h, hS]
    ring
  have hRm := metricRm04StdAt_eq_scalar_div_six_of_finrank_eq_three_of_einstein g p hdim hEin v w
  have hden := Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g p v w hvw
  rw [Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div, hRm, hS]
  simp only [Geometry.Riemannian.sectionalCurvatureDenominator_def] at hden
  field_simp
  ring

end Algebra

/-- **A2.** The LTF01b shape reduces to its Ricci half. -/
theorem volumeDeficit_of_ricci_O5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hric : ∀ Q : ActualUnscathedParabolicLimit_S13 F, ∀ s ∈ Q.timeInterval,
      letI : TopologicalSpace Q.Carrier := Q.topology
      letI : ChartedSpace ThreeSpace Q.Carrier := Q.charts
      letI : IsManifold ThreeModel ∞ Q.Carrier := Q.smooth
      letI : T2Space Q.Carrier := Q.hausdorff
      letI : SigmaCompactSpace Q.Carrier := Q.sigmaCompact
      RicciEqualsMetricMultiple_S13 (Q.metric s) (-(2 * s)⁻¹)) :
    VolumeDeficitHyperbolicLimit_S13 H hdec hneg := by
  intro Q s hs
  let : TopologicalSpace Q.Carrier := Q.topology
  let : ChartedSpace ThreeSpace Q.Carrier := Q.charts
  let : IsManifold ThreeModel ∞ Q.Carrier := Q.smooth
  let : T2Space Q.Carrier := Q.hausdorff
  let : SigmaCompactSpace Q.Carrier := Q.sigmaCompact
  have h := hric Q s hs
  refine ⟨h, ?_⟩
  have hc := ricciEq_constSec_O5 (Q.metric s) _ h
  have he : -(2 * s)⁻¹ / 2 = -(4 * s)⁻¹ := by
    rw [neg_div, div_eq_mul_inv, ← mul_inv, show 2 * s * 2 = 4 * s by ring]
  rwa [he] at hc

end GC.LongTime.Ch12
