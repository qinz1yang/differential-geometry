import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Bounds
import DifferentialGeometry.Geometry.Geodesic.Local
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CompactBounds


noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor.Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem deriv_deriv_extChartAt_comp_eq_of_isGeodesicAt
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) (p : M)
    (hp : γ t ∈ (chartAt H p).source) :
    deriv (deriv ((extChartAt I p) ∘ γ)) t =
      -chartChristoffelContraction g p
        (deriv ((extChartAt I p) ∘ γ) t) (deriv ((extChartAt I p) ∘ γ) t)
        (extChartAt I p (γ t)) := by
  have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t :=
    (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hγ).of_le (by norm_cast)
  let V : ∀ s, TangentSpace I (γ s) := fun s => mfderiv 𝓘(ℝ, ℝ) I γ s 1
  let u : ℝ → E := (extChartAt I p) ∘ γ
  let Y : ℝ → E := chartRepAtBase (I := I) p γ V
  have hsource : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H p).source :=
    hγ2.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hp)
  have hrep : Y =ᶠ[𝓝 t] deriv u := by
    filter_upwards [DifferentialGeometry.Geometry.eventually_isGeodesicAt hγ, hsource]
      with s hs hsp
    have hsMD :=
      (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hs).mdifferentiableAt (by simp)
    change (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ s)
      (mfderiv 𝓘(ℝ, ℝ) I γ s 1) = deriv u s
    simpa only [u, fderiv_apply_one_eq_deriv] using!
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        hsMD p hsp
  have hacc : covDerivAlong g γ V t = 0 :=
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ t hγ2
      hγ.hasGeodesicEquationAt
  have hfixed := covDeriv_chartAt g γ V t p (hγ2.mdifferentiableAt (by norm_num)) hp
    (differentiableAt_chartRepAt_curveVelocity hγ2)
  rw [hacc] at hfixed
  have hbase : γ t ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  have hzero : chartCovDerivAlong g p γ Y t = 0 := by
    have h := congrArg
      ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ t)) hfixed
    simpa only [(trivializationAt E (TangentSpace I) p).continuousLinearMapAt_symmL
      (R := ℝ) hbase, map_zero] using h
  rw [chartCovDerivAlong_def, hrep.deriv_eq, hrep.eq_of_nhds] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

theorem norm_deriv_deriv_extChartAt_comp_le_of_isGeodesicAt
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) (p : M)
    (hp : γ t ∈ (chartAt H p).source) {C : ℝ} (hC : 0 ≤ C)
    (hΓ : ∀ i j k, ‖chartChristoffel g p i j k (extChartAt I p (γ t))‖ ≤ C) :
    ‖deriv (deriv ((extChartAt I p) ∘ γ)) t‖ ≤
      (C * (∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) ^ 2 *
        (∑ k, ‖chartModelBasis E k‖)) *
          ‖deriv ((extChartAt I p) ∘ γ) t‖ ^ 2 := by
  rw [deriv_deriv_extChartAt_comp_eq_of_isGeodesicAt g hγ p hp, norm_neg]
  simpa only [pow_two, mul_assoc] using
    norm_chartChristoffelContraction_le g p (extChartAt I p (γ t))
      (deriv ((extChartAt I p) ∘ γ) t) (deriv ((extChartAt I p) ∘ γ) t) hC hΓ

theorem exists_norm_deriv_deriv_extChartAt_comp_le_of_isCompact
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ interior (extChartAt I p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ → M) (t : ℝ),
      IsGeodesicAt (I := I) g γ t → γ t ∈ (chartAt H p).source →
      extChartAt I p (γ t) ∈ K →
      ‖deriv (deriv ((extChartAt I p) ∘ γ)) t‖ ≤
        C * ‖deriv ((extChartAt I p) ∘ γ) t‖ ^ 2 := by
  obtain ⟨B, hB, hΓ⟩ := exists_norm_chartChristoffel_le_of_isCompact g p hK hKt
  refine ⟨B * (∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) ^ 2 *
    (∑ k, ‖chartModelBasis E k‖), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hB (sq_nonneg _))
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  · intro γ t hγ hp hx
    exact norm_deriv_deriv_extChartAt_comp_le_of_isGeodesicAt g hγ p hp hB
      (hΓ _ hx)

end DifferentialGeometry.Geometry.Riemannian.Geodesic
