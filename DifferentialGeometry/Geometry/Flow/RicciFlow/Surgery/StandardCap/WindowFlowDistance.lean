import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowVolume

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

theorem exists_uniform_window_flow_edist_bound_of_local_curvature (K : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ζ : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1 / 2 → ∀ (J : RealTimeInterval) (θ : ℝ), θ ≤ τ →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ < D →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ t ∈ Icc 0 θ, ∀ x y : standardCapWindow D, ‖x.val‖ < D → ‖y.val‖ < D →
          riemannianEDistOf (L.base.metric t) x y ≤
            ENNReal.ofReal (2 * (‖x.val‖ + ‖y.val‖)) := by
  let τ := Real.log 2 / (18 * Real.sqrt K + 1)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 18 * Real.sqrt K + 1 := by positivity
  refine ⟨τ, div_pos hlog hden, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hζ
    J θ hθτ hcarrier hregular L hL hzero hcurv t ht x y hx hy
  have hexponent : 18 * Real.sqrt K * τ ≤ Real.log 2 := by
    have hτ0 : 0 ≤ τ := (div_pos hlog hden).le
    have he : (18 * Real.sqrt K + 1) * τ = Real.log 2 := by
      dsimp only [τ]
      field_simp
    nlinarith
  have hexp : Real.exp (18 * Real.sqrt K * τ) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hexponent
  have hid : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (@id (standardCapWindow D)) :=
    (Diffeomorph.refl ThreeModel (standardCapWindow D) ∞).isLocalDiffeomorph
  apply window_edist_map_le_of_metric_upper (L.base.metric t) (L := 2) (by norm_num)
    id hid injective_id ?_ x y hx hy
  intro z hz v
  rw [mfderiv_id]
  change (L.base.metric t).inner z v v ≤ 2 ^ 2 * metric.inner z.val v v
  have hinit (v : TangentSpace ThreeModel z) :
      (L.base.metric 0).inner z v v ≤
        (3 / 2 : ℝ) * (metric.restrictOpen (standardCapWindow D)).inner z v v := by
    rw [hzero]
    simpa only [standardCapMetric_eq_metric] using (w.window_inner_bounds hζ hz v).2
  have htime := metric_inner_le_reference_of_curvature_bound L hL
    (metric.restrictOpen (standardCapWindow D)) hθτ hcarrier hregular z
    (fun r hr => hcurv r hr z hz) hinit ht v
  have htime' : (L.base.metric t).inner z v v ≤
      ((3 / 2 : ℝ) * Real.exp (18 * Real.sqrt K * τ)) * metric.inner z.val v v := by
    simpa only [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat,
      show (2 : ℝ) * 3 ^ 2 = 18 by norm_num, SmoothRiemannianMetric.restrictOpen_inner] using htime
  have hn := metric_inner_self_nonneg metric z.val v
  exact htime'.trans (mul_le_mul_of_nonneg_right (by nlinarith [hexp]) hn)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
