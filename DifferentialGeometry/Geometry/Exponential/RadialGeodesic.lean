import DifferentialGeometry.Geometry.Exponential.ChartFlow.Continuity
import DifferentialGeometry.Geometry.Geodesic.Reparametrization.Affine
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction
import DifferentialGeometry.Geometry.Exponential.Smoothness.AwayFromZero.ChartFlow

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

theorem expMap_smul_eventually_eq_maximalGeodesic
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (fun t : ℝ => expMap g p (t • v)) =ᶠ[𝓝 (0 : ℝ)] maximalGeodesic g p v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨f, hf0, hf⟩ := exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  obtain ⟨ε, hε, hfon, _, hsource⟩ :=
    exists_interval_isGeodesicOnWithInitial_of_integralCurveAt g p v hf0 hf
  have horig := maximalGeodesic_eqOn_lift_of_footInSource
    Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected (Metric.mem_ball_self hε)
    hf0 hfon hsource
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (half_pos hε)] with c hc
  have hcabs : |c| < ε / 2 := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hc
  have hmul (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) : c * s ∈ Metric.ball (0 : ℝ) ε := by
    have hsabs : |s| < 2 := abs_lt.mpr hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg c, abs_nonneg s]
  let L : ℝ → TangentBundle I M := fun s => ⟨(f (c * s + 0)).proj, c • (f (c * s + 0)).snd⟩
  have hL0 : L 0 = (⟨p, c • v⟩ : TangentBundle I M) := by
    dsimp only [L]
    rw [mul_zero, add_zero, hf0]
  have hLon : IsMIntegralCurveOn L (geodesicVectorFieldChart g p) (Ioo (-2 : ℝ) 2) := by
    have h := scaledTangentLift_transport g p hfon c 0
    exact h.mono (fun s hs => by simpa only [mem_ofPred_eq, add_zero] using hmul s hs)
  have hLsource : ∀ s ∈ Ioo (-2 : ℝ) 2, (L s).proj ∈ (chartAt H p).source := by
    intro s hs
    simpa only [L, add_zero] using hsource (c * s) (hmul s hs)
  have hscaled := maximalGeodesic_eqOn_lift_of_footInSource
    isOpen_Ioo isPreconnected_Ioo (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
    hL0 hLon hLsource (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hcball : c ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    linarith
  exact (show expMap g p (c • v) = (f c).proj by simpa only [expMap, L, mul_one, add_zero] using hscaled).trans
    (horig hcball).symm

theorem expMap_smul_eventually_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasGeodesicEquationAt g (fun s : ℝ => expMap g p (s • v)) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨f, hf0, hf⟩ := exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  obtain ⟨ε, hε, hfon, hgeo, hsource⟩ :=
    exists_interval_isGeodesicOnWithInitial_of_integralCurveAt g p v hf0 hf
  have horig := maximalGeodesic_eqOn_lift_of_footInSource
    Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected (Metric.mem_ball_self hε)
    hf0 hfon hsource
  have hmax : maximalGeodesic g p v =ᶠ[𝓝 (0 : ℝ)] projectCurve f := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
    exact horig hs
  have heq := (expMap_smul_eventually_eq_maximalGeodesic g p v).trans hmax
  filter_upwards [heq.eventuallyEq_nhds, Metric.ball_mem_nhds (0 : ℝ) hε] with t ht htball
  have hgeot := hgeo.isGeodesicAt (Metric.isOpen_ball.mem_nhds htball)
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at ht.eq_of_nhds ht
    (hgeot.hasGeodesicEquationAt g)

theorem exp_radial_geo_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    HasGeodesicEquationAt g (fun s : ℝ => expMap g p (s • v)) 0 :=
  (expMap_smul_eventually_hasGeodesicEquationAt g p v).self_of_nhds

theorem exp_radial_d2_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    CovariantDerivativeAlong.covDerivAlong g (fun s : ℝ => expMap g p (s • v))
      (fun s => mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => expMap g p (r • v)) s (1 : ℝ)) 0 = 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨δ, hδ, hexp⟩ := expMap_contMDiffAt_infty_of_norm_lt g p
  have hzero := hexp 0 (by simpa only [norm_zero] using hδ)
  let a : E := v
  have hC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun s : ℝ => expMap g p (s • v)) 0 := by
    change ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun s : ℝ => expMap g p (show TangentSpace I p from s • a)) 0
    have hzero2 := hzero.of_le (show (2 : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out)
    have hsmul : ContMDiffAt (M' := E) 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 (fun s : ℝ => s • a) 0 :=
      contMDiffAt_id.smul contMDiffAt_const
    exact hzero2.comp_of_eq hsmul (zero_smul ℝ a)
  exact CovariantDerivativeAlong.covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g _ 0 hC2
    (exp_radial_geo_zero g p v)

end DifferentialGeometry.Geometry.Riemannian.Exponential
