import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem exists_finiteHorn_transverse_axis_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      ∃ i, ∀ x ∈ H.subend i, 0 < metricScalarAt g x ∧
        ∃ s ∈ Ioc (0 : ℝ) H.axial.length,
          dist x (H.axial.point s) ≤ D / Real.sqrt (metricScalarAt g x) := by
  obtain ⟨D, hD, hshortcuts⟩ := exists_uniform_transverse_shortcuts (M := W)
  refine ⟨D, hD, ?_⟩
  intro g H
  obtain ⟨i, htail⟩ := H.cylindrical_tail
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨C, F, p, hcenter, ⟨G⟩, hsource, hQ, ⟨cmp⟩⟩ := htail x hx
  obtain ⟨q, haxis⟩ := G.axis_crosses
  have hlevel : ∀ y : Sphere 2, (y, (0 : ℝ)) ∈
      univ ×ˢ Icc (-H.collar_depth) H.collar_depth := by
    intro y
    exact ⟨mem_univ _, by constructor <;> linarith [H.collar_depth_pos]⟩
  obtain ⟨gamma, hstart, hend, hsmooth, _hmem, hlength⟩ :=
    hshortcuts C (fun _ => C.metric 0)
      (fun _ => scaleMetric (metricScalarAt g x) hQ g) F
      (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
      (⌈H.neck_precision⁻¹⌉₊) H.neck_precision 0 cmp rfl H.neck_precision_pos.le
      (by linarith [H.neck_precision_small]) (by simp) hsource hlevel p q
  have hdist := (edistOf_le_metricPathELength
    (scaleMetric (metricScalarAt g x) hQ g) (by norm_num : (0 : ℝ) ≤ 1) hsmooth).trans hlength
  rw [hstart, hend, hcenter, haxis, edistOf_scale] at hdist
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal hD.le] at hreal
  change Real.sqrt (metricScalarAt g x) * metricDistance g x (H.axial.point G.crossing_parameter) ≤ D at hreal
  rw [← H.intrinsic] at hreal
  refine ⟨hQ, G.crossing_parameter, G.crossing_mem, ?_⟩
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
  nlinarith

theorem finiteHorn_subend_near_axis (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ i, ∀ x ∈ H.subend i, ∃ s ∈ Ioc (0 : ℝ) H.axial.length,
      dist x (H.axial.point s) < eta := by
  obtain ⟨D, hD, hbound⟩ := exists_finiteHorn_transverse_axis_bound (W := W)
  obtain ⟨i, hi⟩ := hbound g H
  obtain ⟨j, hj⟩ := H.curvature_diverges ((D / eta) ^ 2 + 1)
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max i j, ?_⟩
  intro x hx
  obtain ⟨hQ, s, hs, hdist⟩ := hi x (hmono (le_max_left i j) hx)
  have hlarge := hj x (hmono (le_max_right i j) hx)
  have hsqrt : D / eta < Real.sqrt (metricScalarAt g x) := by
    have hsq := Real.sq_sqrt hQ.le
    have hnonneg : 0 ≤ D / eta := (div_pos hD heta).le
    nlinarith [Real.sqrt_nonneg (metricScalarAt g x)]
  refine ⟨s, hs, hdist.trans_lt ?_⟩
  apply (div_lt_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
  have hmul := (div_lt_iff₀ heta).mp hsqrt
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
