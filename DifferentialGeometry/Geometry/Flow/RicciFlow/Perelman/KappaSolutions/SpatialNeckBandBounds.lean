import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckAmbientDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BufferedNeckNumerics
import Mathlib.Topology.EMetricSpace.Diam

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff _root_.Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance bandBoundsSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance bandBoundsC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)

private theorem band_point_mem_core (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x : spatialNeckBuffer epsilon) (hx : |x.val.2| ≤ 5 * Real.pi) :
    x ∈ spatialNeckClosedCore epsilon := by
  have hgap := spatialNeckControlEpsilon_inverse_gap hepsilon hsmall
  have hbounds := abs_le.mp hx
  change -epsilon⁻¹ ≤ x.val.2 ∧ x.val.2 ≤ epsilon⁻¹
  constructor <;> linarith [Real.pi_pos]

theorem marked_antipodal_edist_lower (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (z : spatialNeckBuffer epsilon) (hz : |z.val.2| ≤ 5 * Real.pi)
    (hanti : z.val.1 = -yStar) :
    ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
      riemannianEDistOf (I := I) h p (W.embedding z) := by
  let c := spatialNeckCentralPoint epsilon W.epsilon_pos yStar
  have hc : |c.val.2| ≤ 5 * Real.pi := by
    change |(0 : ℝ)| ≤ 5 * Real.pi
    rw [abs_zero]
    positivity
  have hlower := W.band_antipodal_edist_lower hsmall c z hc hz hanti
  change ENNReal.ofReal (11 / 12 * spatialNeckScale h p * Real.pi) ≤
    riemannianEDistOf (I := I) h
      (W.embedding (spatialNeckCentralPoint epsilon W.epsilon_pos yStar)) (W.embedding z) at hlower
  rwa [W.marked] at hlower

theorem outward_slice_comparisonAngle_lt (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x y : spatialNeckBuffer epsilon)
    (hx : x.val.2 = 5 * Real.pi) (hy : y.val.2 = 5 * Real.pi) :
    comparisonAngle
      (riemannianEDistOf (I := I) h p (W.embedding x)).toReal
      (riemannianEDistOf (I := I) h p (W.embedding y)).toReal
      (riemannianEDistOf (I := I) h (W.embedding x) (W.embedding y)).toReal < Real.pi / 6 := by
  let c := spatialNeckCentralPoint epsilon W.epsilon_pos yStar
  have hc : |c.val.2| ≤ 5 * Real.pi := by
    change |(0 : ℝ)| ≤ 5 * Real.pi
    rw [abs_zero]
    positivity
  have hxb : |x.val.2| ≤ 5 * Real.pi := by rw [hx, abs_of_pos (by positivity)]
  have hyb : |y.val.2| ≤ 5 * Real.pi := by rw [hy, abs_of_pos (by positivity)]
  have hcmark : W.embedding c = p := W.marked
  have hlower (z : spatialNeckBuffer epsilon) (hz : z.val.2 = 5 * Real.pi)
      (hzb : |z.val.2| ≤ 5 * Real.pi) :
      (11 / 12 : ℝ) * (5 * Real.pi) * spatialNeckScale h p ≤
        (riemannianEDistOf (I := I) h p (W.embedding z)).toReal := by
    have hedist := W.band_axial_edist_lower hsmall c z hc hzb
    have hfin : riemannianEDistOf (I := I) h (W.embedding c) (W.embedding z) ≠ ⊤ :=
      ne_of_lt ((W.band_edist_lt hsmall c z hc hzb).trans_le le_top)
    have hr := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hedist
    change 11 / 12 * spatialNeckScale h p * |z.val.2 - 0| ≤
      (riemannianEDistOf (I := I) h (W.embedding c) (W.embedding z)).toReal at hr
    rw [sub_zero, hz, abs_of_pos (by positivity), hcmark] at hr
    nlinarith
  have hscale := spatialNeckScale_pos h p W.scalar_pos
  have hpair := W.slice_edist_upper hsmall x y (band_point_mem_core W.epsilon_pos hsmall x hxb)
    (band_point_mem_core W.epsilon_pos hsmall y hyb) (hy.trans hx.symm)
  have hpairReal := ENNReal.toReal_le_of_le_ofReal
    (by positivity : 0 ≤ 13 / 12 * spatialNeckScale h p * Real.pi) hpair
  apply bufferedNeck_comparisonAngle_lt_pi_div_six hscale
    (hlower x hx hxb) (hlower y hy hyb) ENNReal.toReal_nonneg
  nlinarith

section CompatibleMetric

variable [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [PseudoEMetricSpace N] [IsRiemannianManifold I N]

omit [I.Boundaryless] in
theorem band_ediam_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) :
    Metric.ediam (W.embedding '' {x : spatialNeckBuffer epsilon | |x.val.2| ≤ 5 * Real.pi}) ≤
      ENNReal.ofReal (11 * Real.pi * spatialNeckScale h p) := by
  apply Metric.ediam_image_le_iff.mpr
  intro x hx y hy
  rw [IsRiemannianManifold.out (I := I),
    ← riemannianEDistOf_eq_riemannianEDist h hEnorm]
  exact (W.band_edist_lt hsmall x y hx hy).le

omit [I.Boundaryless] in
theorem slice_ediam_le (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) (s : ℝ) (hs : |s| ≤ 5 * Real.pi) :
    Metric.ediam (W.embedding '' {x : spatialNeckBuffer epsilon | x.val.2 = s}) ≤
      ENNReal.ofReal (13 / 12 * spatialNeckScale h p * Real.pi) := by
  apply Metric.ediam_image_le_iff.mpr
  intro x hx y hy
  have hxb : |x.val.2| ≤ 5 * Real.pi := by rw [hx]; exact hs
  have hyb : |y.val.2| ≤ 5 * Real.pi := by rw [hy]; exact hs
  rw [IsRiemannianManifold.out (I := I),
    ← riemannianEDistOf_eq_riemannianEDist h hEnorm]
  exact W.slice_edist_upper hsmall x y (band_point_mem_core W.epsilon_pos hsmall x hxb)
    (band_point_mem_core W.epsilon_pos hsmall y hyb) (hy.trans hx.symm)

end CompatibleMetric

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
