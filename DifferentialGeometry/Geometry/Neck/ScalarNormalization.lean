import DifferentialGeometry.Geometry.Neck.ScalarControl
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Neck
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private local instance (δ : ℝ) : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_normalizedDatum_of_cylinder_pullback_close
    (g : SmoothRiemannianMetric I M) {δ η q : ℝ} {k : ℕ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) (hηsmall : η ≤ 1 / 40000)
    (hηδ : 20000 * η ≤ δ) (hq : 0 < q) (hk : 2 ≤ k)
    (Φ : bufferedCylinder δ → M) (hΦ : IsLocalDiffeomorph IC I ∞ Φ)
    (hinj : Injective Φ)
    (hclose : metricDerivENormSupOn (controlledCylinder δ) k
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ hΦ hinj)
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal η) :
    ∃ d : normalizedDatum g (Φ (cylinderCenter δ hδ)) δ k,
      d.map = Φ ∧ d.retainedSide = true ∧
      |metricScalarAt g (Φ (cylinderCenter δ hδ)) / q - 1| ≤ 4323 * η := by
  let p := Φ (cylinderCenter δ hδ)
  let c := metricScalarAt g p / q
  have hratio : |c-1| ≤ 4323 * η :=
    abs_scalar_ratio_sub_one_le_of_cylinder_pullback_enorm_lt
      (bufferedCylinder δ) g Φ hΦ hinj q hq (controlledCylinder δ) k hk
      η (by linarith) hclose (cylinderCenter δ hδ) (cylinderCenter_mem_controlledCylinder δ hδ)
  have hc : 0 < c := by linarith [(abs_le.mp hratio).1]
  have hp : 0 < metricScalarAt g p := (div_pos_iff.mp hc).resolve_right (fun h => hq.not_gt h.2)
    |>.1
  let G := pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric q hq g) Φ hΦ hinj
  have hscaled : scaleMetric c hc G =
      pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric (metricScalarAt g p) hp g) Φ hΦ hinj
        := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner,pullbackMetricOfInjectiveLocalDiffeomorph_inner,
      pullbackMetricOfInjectiveLocalDiffeomorph_inner,scaleMetric_inner,scaleMetric_inner]
    dsimp only [c]
    field_simp
  have herr := metricDerivENormSupOn_scaleMetric_left_lt (controlledCylinder δ) k c hc
    G (referenceMetric δ) hclose
  have hsqrt : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_iff];norm_num
  have hbound : c * η + |c - 1| *Real.sqrt 3 < δ := by
    have hcle : c ≤ 2 := by linarith [(abs_le.mp hratio).2]
    have hh := mul_le_mul_of_nonneg_right hcle hη.le
    have hi := mul_le_mul_of_nonneg_left hsqrt (abs_nonneg (c-1))
    nlinarith
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ) = 3 := by norm_num
  rw [hscaled,hdim] at herr
  let hsm := hΦ.contMDiff
  let hm : ∀ x, Injective (mfderiv IC I Φ x) :=
    fun x => (hΦ x).mfderivToContinuousLinearEquiv (by simp) |>.injective
  let out : normalizedDatum g p δ k :=
    { precision_pos := hδ
      precision_lt_one := hδ1
      map := Φ
      smooth := hsm
      injective := hinj
      immersion := hm
      center_eq := rfl
      scalar_pos := hp
      error_lt := ?_
      retainedSide := true }
  case refine_1 =>
    exact herr.trans (ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr hbound)
  exact ⟨out,rfl,rfl,hratio⟩

end DifferentialGeometry.Geometry.Neck
