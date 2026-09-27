import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannDiameter
import DifferentialGeometry.Geometry.Comparison.Soul.SbrBusemannDiameter

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open scoped Manifold ContDiff _root_.Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

namespace SpatialNeckSideData

variable {h : SmoothRiemannianMetric I N} {y1 y2 : SpatialNeckSphere}
  {p1 p2 : N} {epsilon : ℝ}
  {W1 : SpatialNeckWitness h y1 p1 epsilon} {W2 : SpatialNeckWitness h y2 p2 epsilon}
  (D1 : SpatialNeckSideData W1) (D2 : SpatialNeckSideData W2)

theorem outer_center_mem_upper (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hcores : Disjoint W1.core W2.core)
    (horder : closure (D1.lower 0) ⊆ D2.lower 0) : p2 ∈ D1.upper (5 * Real.pi) := by
  have hgap := spatialNeckControlEpsilon_inverse_gap W1.epsilon_pos hsmall
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    rw [abs_zero]
    linarith [Real.pi_pos]
  have hA : |5 * Real.pi| < epsilon⁻¹ + 1 := by
    rw [abs_of_pos (by positivity : 0 < 5 * Real.pi)]
    linarith [Real.pi_pos]
  have hp2slice : p2 ∈ W2.embedding '' {z : spatialNeckBuffer epsilon | z.val.2 = 0} :=
    ⟨spatialNeckCentralPoint epsilon W2.epsilon_pos y2, rfl, W2.marked⟩
  have hp2notlower : p2 ∉ D2.lower 0 := by
    intro hp2
    have havoid : p2 ∉ W2.embedding '' {z : spatialNeckBuffer epsilon | z.val.2 = 0} := by
      change p2 ∈ (W2.embedding '' {z : spatialNeckBuffer epsilon | z.val.2 = 0})ᶜ
      rw [← (D2.slice_spec 0 hzero).2.2.2.2.2.1]
      exact Or.inl hp2
    exact havoid hp2slice
  have hp2notzero : p2 ∉ closure (D1.lower 0) := fun hx => hp2notlower (horder hx)
  have hp2core : p2 ∈ W2.core :=
    ⟨spatialNeckCentralPoint epsilon W2.epsilon_pos y2,
      spatialNeckCentralDomain_subset_core epsilon W2.epsilon_pos rfl, W2.marked⟩
  have hp2notcore : p2 ∉ W1.core := fun hx => Set.disjoint_left.mp hcores hx hp2core
  have hp2notA : p2 ∉ closure (D1.lower (5 * Real.pi)) := by
    rw [(D1.ordered_band 0 (5 * Real.pi) hzero hA (by positivity)).2.1]
    rintro (hx | ⟨z, hz, heq⟩)
    · exact hp2notzero hx
    · apply hp2notcore
      refine ⟨z, ?_, heq⟩
      change -epsilon⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ epsilon⁻¹
      constructor <;> linarith [hz.1, hz.2, Real.pi_pos]
  simpa only [D1.closure_lower_eq_compl_upper (5 * Real.pi) hA,
    mem_compl_iff, not_not] using hp2notA

section CompatibleMetric

variable [I.Boundaryless] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

private local instance outwardComparisonC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem exists_ray_of_neck [NoncompactSpace N]
    (W1 : SpatialNeckWitness h y1 p1 epsilon) (hEnorm : IsMetricNorm (I := I) h)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h) :
    ∃ c : ℝ≥0 → N, Isometry c := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W1.dimension_three]; norm_num⟩
  let _ : CompleteSpace N := completeMetric_compatible_completeSpace h hEnorm W1.complete
  by_contra! hno
  have hcompact := isCompact_rayBusemannSublevel h hEnorm hsec p1 (k := 0)
  have heq : rayBusemannSublevel p1 0 = univ := by
    apply eq_univ_of_forall
    intro q c hc _hc0
    exact False.elim (hno c hc)
  rw [heq] at hcompact
  exact noncompact_univ N hcompact

theorem outward_scalar_le [NoncompactSpace N]
    (hEnorm : IsMetricNorm (I := I) h)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature (I := I) h)
    (hcores : Disjoint W1.core W2.core)
    (horder : closure (D1.lower 0) ⊆ D2.lower 0) :
    metricScalarAt (I := I) h p2 ≤ 144 * metricScalarAt (I := I) h p1 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [W1.dimension_three]; norm_num⟩
  let _ : CompleteSpace N := completeMetric_compatible_completeSpace h hEnorm W1.complete
  obtain ⟨c, hc⟩ := exists_ray_of_neck W1 hEnorm hsec
  have hp2out := D1.outer_center_mem_upper D2 hsmall hcores horder
  have hlevels := D1.busemann_outward_lt hEnorm hsmall hsec hc hp2out
  have hproper := D1.busemann_isProperMap hEnorm hsmall hsec hc
  have hbelow := D1.busemann_bddBelow hEnorm hsmall hsec hc
  have hmono := busemann_level_diameter_le h hEnorm hsec hc hproper hbelow
    (ciInf_le hbelow p1) hlevels.le
  have hlower := (D1.busemann_level_diam_bounds hEnorm hsmall hsec hc).1
  have hupper := (D2.busemann_level_diam_bounds hEnorm hsmall hsec hc).2
  have hscales : spatialNeckScale h p1 ≤ 12 * spatialNeckScale h p2 := by
    have hmul : (11 * Real.pi) * spatialNeckScale h p1 ≤
        (11 * Real.pi) * (12 * spatialNeckScale h p2) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 11 * Real.pi)).mp hmul
  have hR1 := W1.scalar_pos
  have hR2 := W2.scalar_pos
  have hsqrt1 : 0 < Real.sqrt (metricScalarAt (I := I) h p1) := Real.sqrt_pos.mpr hR1
  have hsqrt2 : 0 < Real.sqrt (metricScalarAt (I := I) h p2) := Real.sqrt_pos.mpr hR2
  have hratio : Real.sqrt 2 / Real.sqrt (metricScalarAt (I := I) h p1) ≤
      (12 * Real.sqrt 2) / Real.sqrt (metricScalarAt (I := I) h p2) := by
    simpa only [spatialNeckScale, mul_div_assoc] using hscales
  have hcross := (div_le_div_iff₀ hsqrt1 hsqrt2).mp hratio
  have hsqrt : Real.sqrt (metricScalarAt (I := I) h p2) ≤
      12 * Real.sqrt (metricScalarAt (I := I) h p1) := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < Real.sqrt 2)).mp
    nlinarith
  have hsq := (sq_le_sq₀ hsqrt2.le (by positivity :
    0 ≤ 12 * Real.sqrt (metricScalarAt (I := I) h p1))).mpr hsqrt
  rw [mul_pow, Real.sq_sqrt hR2.le, Real.sq_sqrt hR1.le] at hsq
  norm_num at hsq
  exact hsq

end CompatibleMetric

end SpatialNeckSideData

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
