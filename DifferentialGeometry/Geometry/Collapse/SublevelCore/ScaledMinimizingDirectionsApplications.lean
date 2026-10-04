import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections

/-!
# Consumer: the point-direction pairing of a field at the rescaled metric

LC54's field `V` has `g(V, w) ≤ -a` against every inward unit minimizing direction `w` of `g`;
then `R • V` has `R⁻² g(R V, w) ≤ -a` against every inward unit minimizing direction of the
rescaled metric `R⁻² g` (rescaled instances). This is the `hVdir` input of the LC55/LC57 core
theorems at scale `R`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Consumer of `mem_inwardMinimizingDirections_radialScaled_iff`.** A pairing bound
`g(V, w) ≤ -a` over the inward unit minimizing directions of `g` gives
`R⁻² g(R V, w) ≤ -a` over those of the rescaled metric. -/
theorem radialScaled_field_pairing_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R : ℝ} (hR : 0 < R) (n q : M)
    (V : TangentSpace I q) {a : ℝ}
    (hV : ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm n q, g.inner q V w ≤ -a) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
    letI : IsRiemannianManifold I M :=
      radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    ∀ w ∈ inwardMinimizingDirections (I := I) gR hnR n q, gR.inner q (R • V) w ≤ -a) := by
  intro hmetric gR hnR w hw
  have hw' := (mem_inwardMinimizingDirections_radialScaled_iff (g := g) (hEnorm := hEnorm) hR (n := n)
    (q := q) (v := w)).mpr hw
  have h := hV _ hw'
  have heq : gR.inner q (R • V) w = g.inner q V (R⁻¹ • w) := by
    change (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner q (R • V) w = _
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [heq]
  exact h

end DifferentialGeometry.Geometry.Collapse
