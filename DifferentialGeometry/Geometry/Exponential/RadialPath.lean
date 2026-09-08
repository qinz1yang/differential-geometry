import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Length
import DifferentialGeometry.Geometry.Metric.Path.Reparametrization
import Mathlib.Analysis.Convex.PathConnected

noncomputable section

open Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

def radialPath (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hv : v ∈ expDomain g p) : Path p (expMap g p v) :=
  ((Path.segment (0 : E) (show E from v)).map'
    ((contMDiffOn_expMap g p).continuousOn.mono (by
      rw [Path.range_segment]
      exact (starConvex_expDomain g p).segment_subset hv))).cast
    (expMap_zero g p).symm rfl

@[simp] theorem radialPath_apply (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) (t : unitInterval) :
    radialPath g p v hv t = expMap g p ((t : ℝ) • v) := by
  have h (w : E) : (Path.segment (0 : E) w) t = (t : ℝ) • w := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]
  exact congrArg (fun w : E => expMap g p (show TangentSpace I p from w)) (h v)

theorem eqOn_extend_radialPath (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    EqOn (radialPath g p v hv).extend (fun t : ℝ => expMap g p (t • v)) (Icc 0 1) := by
  intro t ht
  rw [Path.extend_apply _ ht, radialPath_apply]

theorem range_radialPath (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    range (radialPath g p v hv) = expMap g p '' segment ℝ 0 v := by
  have h := range_comp
    (f := (Path.segment (0 : E) (show E from v)))
    (g := fun w : E => expMap g p (show TangentSpace I p from w))
  rw [Path.range_segment] at h
  exact h

theorem contMDiffOn_extend_radialPath (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (radialPath g p v hv).extend (Icc 0 1) := by
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => t • (show E from v)) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_id.smul contDiff_const
  have h := (contMDiffOn_expMap g p).comp hline.contMDiffOn
    (fun _ ht => smul_mem_expDomain hv ht)
  exact h.congr (eqOn_extend_radialPath g p v hv)

theorem extend_radialPath_withSittingInstants (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    (radialPath g p v hv).withSittingInstants.extend =
      fun t : ℝ => expMap g p (Real.smoothTransition (3 * t - 1) • v) := by
  rw [Path.extend_withSittingInstants]
  funext t
  exact eqOn_extend_radialPath g p v hv
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem riemannianELength_radialPath [(x : M) → ENorm (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (hv : v ∈ expDomain g p) :
    (radialPath g p v hv).riemannianELength (I := I) =
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t : ℝ => expMap g p (t • v)) (Icc 0 1) :=
    ((contMDiffOn_extend_radialPath g p v hv).of_le (by norm_num)).congr
      (eqOn_extend_radialPath g p v hv).symm
  rw [Path.riemannianELength,
    Manifold.pathELength_congr (eqOn_extend_radialPath g p v hv),
    Geodesic.pathELength_eq_arcLength_of_enorm_eq g zero_le_one
      ((Geodesic.speedSqrt_integrableOn_Icc_of_C1 g zero_le_one hγ).mono_set Ioo_subset_Icc_self)
      (fun t _ => hEnorm _ _)]
  have hdom : (show TangentSpace I p from (1 : ℝ) • (show E from v)) ∈ expDomain g p := by
    change (1 : ℝ) • (show E from v) ∈ expDomain g p
    rw [one_smul]
    exact hv
  simpa only [one_mul] using!
    congrArg ENNReal.ofReal (arcLength_expMap_smul g p (show E from v) hdom)

end DifferentialGeometry.Geometry.Riemannian.Exponential
