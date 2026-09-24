import DifferentialGeometry.Geometry.Metric.CylinderRotation
import DifferentialGeometry.Geometry.Metric.Pullback.Completeness
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace (Metric.sphere (0 : E) 1 × ℝ) := borel _
private local instance : BorelSpace (Metric.sphere (0 : E) 1 × ℝ) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem roundCylinder_ball_isOpen (p : Metric.sphere (0 : E) 1 × ℝ) (r : ℝ) :
    IsOpen (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) p r) :=
  isOpen_lt (by
    unfold riemannianEDistOf
    exact Riemannian.continuous_riemannianEDist _ p) continuous_const

theorem riemannianVolumeMeasure_roundCylinder_ball_eq
    (p q : Metric.sphere (0 : E) 1 × ℝ) (r : ℝ) :
    riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
        (roundCylinderMetric (E := E) (n := n))
        (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) p r) =
      riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
        (roundCylinderMetric (E := E) (n := n))
        (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) q r) := by
  let e := (ℝ ∙ ((p.1 : E) - q.1))ᗮ.reflection
  let Φ := roundCylinderDiffeomorph (n := n) e (q.2 - p.2)
  have hΦ : Φ p = q := by
    rw [roundCylinderDiffeomorph_apply]
    apply Prod.ext
    · apply Subtype.ext
      exact Submodule.reflection_sub
        ((mem_sphere_zero_iff_norm.mp p.1.property).trans
          (mem_sphere_zero_iff_norm.mp q.1.property).symm)
    · dsimp only
      ring
  let g := roundCylinderMetric (E := E) (n := n)
  have hmetric : Diffeomorph.pullbackMetric g Φ = g :=
    pullback_roundCylinderMetric_roundCylinderDiffeomorph e _
  have hpre : Φ.symm ⁻¹' riemannianBallOf g p r = riemannianBallOf g q r := by
    ext x
    have hd := Diffeomorph.pullbackMetric_edist g Φ p (Φ.symm x)
    rw [hmetric, hΦ, Φ.apply_symm_apply] at hd
    change riemannianEDistOf g p (Φ.symm x) < ENNReal.ofReal r ↔
      riemannianEDistOf g q x < ENNReal.ofReal r
    rw [hd]
  have hμ := riemannianVolumeMeasure_pullback g Φ
  rw [hmetric] at hμ
  have hh := congrArg (fun μ => μ (riemannianBallOf g p r)) hμ
  rw [Measure.map_apply Φ.symm.continuous.measurable (roundCylinder_ball_isOpen p r).measurableSet,
    hpre] at hh
  exact hh

theorem exists_pos_le_riemannianVolumeMeasure_roundCylinder_ball
    {r : ℝ} (hr : 0 < r) :
    ∃ v : ℝ, 0 < v ∧ ∀ p : Metric.sphere (0 : E) 1 × ℝ,
      ENNReal.ofReal v ≤
        riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ)
          (roundCylinderMetric (E := E) (n := n))
          (riemannianBallOf (roundCylinderMetric (E := E) (n := n)) p r) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank ℝ E by rw [show Module.finrank ℝ E = n + 1 from Fact.out]; omega)
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1)).mpr zero_le_one
  let p : Metric.sphere (0 : E) 1 × ℝ := (⟨u, hu⟩, 0)
  let g := roundCylinderMetric (E := E) (n := n)
  let μ := riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ) g
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hpos : 0 < μ (riemannianBallOf g p r) := by
    apply (roundCylinder_ball_isOpen p r).measure_pos μ
    refine ⟨p, ?_⟩
    change riemannianEDistOf g p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨v, _, hv, hbound⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  refine ⟨v, ENNReal.ofReal_pos.mp hv, ?_⟩
  intro q
  exact hbound.le.trans_eq (riemannianVolumeMeasure_roundCylinder_ball_eq p q r)

end DifferentialGeometry.Geometry.Measure
