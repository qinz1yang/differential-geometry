import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ShiScale_S122
import DifferentialGeometry.Geometry.Curvature.Bounds.MetricDerivatives
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PersistGeom_S50
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallCompact_S98

set_option autoImplicit false

/-!
# CH12-S122 / G2a: initial `∇^j Rm` from the metric jets (`∃ C_j`, `δ' ≤ 1`, `η₀ ≤ 1/2`), the reference-bundle bound
for the hyperbolic metric on a compact ball, and compactness of the scaled closed balls in `↥(ball 2R)`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open Set TopologicalSpace Manifold
open scoped Manifold ContDiff Topology ENNReal
universe u
namespace GC.LongTime.Ch12

section Init

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ X] [T2Space X]

theorem inner_equiv_of_half_S122 (G g : SmoothRiemannianMetric (𝓡 3) X) (y : X)
    (h : metricDerivNorm 0 g G G y ≤ 1 / 2) (v : TangentSpace (𝓡 3) y) :
    (2 : ℝ)⁻¹ * G.inner y v v ≤ g.inner y v v ∧ g.inner y v v ≤ 2 * G.inner y v v := by
  obtain ⟨hl, hu⟩ := inner_bounds_of_metricDerivNorm_le G g y h v
  have h0 := metric_inner_self_nonneg G y v
  constructor <;> nlinarith

theorem sqrt_iterCov_eq_curvDerivNorm_S122 (g : SmoothRiemannianMetric (𝓡 3) X) (s : ℕ) (y : X) :
    Real.sqrt (normSq0S g y (4 + s) (iterCov g 4 (metricRm04 g) s y)) = curvDerivNorm s g y := by
  unfold curvDerivNorm curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]

theorem exists_initCurv_S122 [BoundarylessManifold (𝓡 3) X] (j : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G g : SmoothRiemannianMetric (𝓡 3) X) (x : X),
      metricDerivNorm 0 g G G x ≤ 1 / 2 → (∀ s ≤ j + 2, metricDerivNorm s g G G x ≤ 1) →
      (∀ s ≤ j, Real.sqrt (normSq0S G x (4 + s) (iterCov G 4 (metricRm04 G) s x)) ≤ A) →
      Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets
    (I := 𝓡 3) (M := X) j 2 (Real.sqrt 3 + 1) A (by norm_num) (by positivity) hA
  refine ⟨C, hC, ?_⟩
  intro G g x h0 hs hR
  have hjets : ∀ s ≤ j + 2, metricCovDerivNorm s g G x ≤ Real.sqrt 3 + 1 := by
    intro s hs'
    have hself : metricCovDerivNorm s G G x ≤ Real.sqrt 3 := by
      cases s with
      | zero =>
        rw [metricCovDerivNorm_self_zero]
        simp
      | succ s => rw [covNorm_self_succ]; exact Real.sqrt_nonneg _
    have herr : metricDerivNorm s g G G x ≤ 1 := hs s hs'
    exact (covNorm_le_add s g G G x).trans (add_le_add hself herr)
  exact hbound G g x (fun v => inner_equiv_of_half_S122 G g x h0 v) hjets hR

end Init

section Ref

variable (H : FiniteVolumeHyperbolicModel.{u})

/-- the hyperbolic reference metric has bounded curvature derivatives (`∇^s Rm`, `s ≤ j`) on the compact ball. -/
theorem exists_refCurv_S122 (ρ : ℝ) (j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : H.Carrier, riemannianEDistOf H.metric H.basepoint z ≤ ENNReal.ofReal ρ →
      ∀ s ≤ j, curvDerivNorm s H.metric z ≤ A := by
  have hK := isCompact_closedBall_S98 H ρ
  have hb : ∀ s : ℕ, ∃ C : ℝ, ∀ z ∈ {x : H.Carrier | riemannianEDistOf H.metric H.basepoint x ≤
      ENNReal.ofReal ρ}, ‖curvDerivNorm s H.metric z‖ ≤ C := fun s => by
    have hcont : Continuous (fun z => curvDerivNorm s H.metric z) := by
      have : (fun z => curvDerivNorm s H.metric z) = curvatureDerivativeNorm H.metric s :=
        funext fun z => (curvatureDerivativeNorm_eq_curvDerivNorm H.metric s z).symm
      rw [this]; exact continuous_curvatureDerivativeNorm H.metric s
    exact hK.exists_bound_of_continuousOn hcont.continuousOn
  choose C hC using hb
  refine ⟨∑ s ∈ Finset.range (j + 1), max (C s) 0, Finset.sum_nonneg fun _ _ => le_max_right _ _, ?_⟩
  intro z hz s hs
  have h1 : curvDerivNorm s H.metric z ≤ C s := (le_abs_self _).trans (by simpa using hC s z hz)
  exact h1.trans ((le_max_left _ _).trans
    (Finset.single_le_sum (f := fun s => max (C s) 0) (fun _ _ => le_max_right _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hs))))

end Ref

section Ball

variable (H : FiniteVolumeHyperbolicModel.{u})

/-- the closed `g`-ball of radius `ρ/4` about a point of `ball (2R - ρ)` is compact in `↥(ball 2R)` when `g ≥ G/2`. -/
theorem isCompact_closedBall_scaled_S122 {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (g : SmoothRiemannianMetric (𝓡 3) (ballU_S98 H R))
    (hcomp : ∀ (y : ballU_S98 H R) (v : TangentSpace (𝓡 3) y),
      (H.metric.restrictOpen (ballU_S98 H R)).inner y v v ≤ 2 * g.inner y v v)
    (x : ballU_S98 H R)
    (hx : (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint (2 * R - ρ)) :
    IsCompact {y : ballU_S98 H R | riemannianEDistOf g x y ≤ ENNReal.ofReal (ρ / 4)} := by
  have hKc : IsCompact {y : ballU_S98 H R | riemannianEDistOf H.metric H.basepoint (y : H.Carrier) ≤
      ENNReal.ofReal (2 * R - ρ / 2)} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert isCompact_closedBall_S98 H (2 * R - ρ / 2) using 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hy
      refine ⟨⟨y, ?_⟩, hy, rfl⟩
      exact lt_of_le_of_lt hy (ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.2 (by linarith))
  have hclosed : IsClosed {y : ballU_S98 H R | riemannianEDistOf g x y ≤ ENNReal.ofReal (ρ / 4)} :=
    isClosed_le (by unfold riemannianEDistOf; exact continuous_riemannianEDist g x) continuous_const
  refine hKc.of_isClosed_subset hclosed ?_
  intro y hy
  change riemannianEDistOf g x y ≤ ENNReal.ofReal (ρ / 4) at hy
  change riemannianEDistOf H.metric H.basepoint (y : H.Carrier) ≤ ENNReal.ofReal (2 * R - ρ / 2)
  have h1 := riemannianEDistOf_le_of_inner_le_S50 g (H.metric.restrictOpen (ballU_S98 H R))
    (c := 2) (by norm_num) hcomp x y
  have h2 := riemannianEDistOf_le_restrictOpen H.metric (ballU_S98 H R) x y
  have h3 : riemannianEDistOf H.metric (x : H.Carrier) (y : H.Carrier) ≤ ENNReal.ofReal (ρ / 2) := by
    refine h2.trans (h1.trans ?_)
    calc ENNReal.ofReal (Real.sqrt 2) * riemannianEDistOf g x y
        ≤ ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (ρ / 4) := by gcongr
      _ = ENNReal.ofReal (Real.sqrt 2 * (ρ / 4)) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
      _ ≤ ENNReal.ofReal (ρ / 2) := by
        apply ENNReal.ofReal_le_ofReal
        have : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        nlinarith
  change riemannianEDistOf H.metric H.basepoint (x : H.Carrier) < ENNReal.ofReal (2 * R - ρ) at hx
  have hpos : 0 < 2 * R - ρ := ENNReal.ofReal_pos.1 ((show (0 : ℝ≥0∞) ≤ _ from bot_le).trans_lt hx)
  calc riemannianEDistOf H.metric H.basepoint (y : H.Carrier)
      ≤ riemannianEDistOf H.metric H.basepoint (x : H.Carrier) +
          riemannianEDistOf H.metric (x : H.Carrier) (y : H.Carrier) :=
        riemannianEDistOf_triangle H.metric _ _ _
    _ ≤ ENNReal.ofReal (2 * R - ρ) + ENNReal.ofReal (ρ / 2) := add_le_add hx.le h3
    _ = ENNReal.ofReal (2 * R - ρ / 2) := by
        rw [← ENNReal.ofReal_add hpos.le (by linarith)]; congr 1; ring

end Ball

end GC.LongTime.Ch12
