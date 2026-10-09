import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCurvatureBounds

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_uniform_windowed_source_curvature_bounds :
    ∃ C : ℝ → ℝ, (∀ r, 0 < C r) ∧ ∀ r : ℝ, 0 ≤ r →
      ∃ epsStar : ℝ, 0 < epsStar ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] (D : RealTimeInterval)
          (S : SolutionOn (I := I3) (M := M) D) (eps kappa : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness eps kappa S x t), eps ≤ epsStar →
          ∀ a ∈ Icc (-modelDepth eps) 0,
            IsCompact (riemannianClosedBallOf
              (rescaledMetric S t (S.scalar t x) W.scalar_pos a) x r) ∧
            ∀ s ∈ Icc (-modelDepth eps) 0,
              ∀ z ∈ riemannianClosedBallOf
                (rescaledMetric S t (S.scalar t x) W.scalar_pos a) x r,
                normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z 4
                  (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z) ≤
                  C r := by
  obtain ⟨B, hB, hmodel⟩ := KappaSolutions.exists_universal_normalized_ancient_curvature_bounds.{u}
  refine ⟨fun r => sourceCurvatureBound 3 (Real.sqrt (B (2 * r + 1))) ^ 2,
    fun r => sq_pos_of_pos (sourceCurvatureBound_pos 3 (Real.sqrt_nonneg _)), ?_⟩
  intro r hr
  let R := 2 * r + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  refine ⟨min (1 / 4) (R⁻¹ ^ 2), lt_min (by norm_num) (sq_pos_of_pos (inv_pos.mpr hR)), ?_⟩
  intro M _ _ _ _ D S eps kappa x t W heps a ha
  have heps4 : eps ≤ 1 / 4 := heps.trans (min_le_left _ _)
  have hbuffer : R ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos (heps.trans (min_le_right _ _))
    rwa [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hR.le), inv_inv] at hh
  have hroot : (1 / 2 : ℝ) < Real.sqrt (1 - eps) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    linarith
  have hradius : r < Real.sqrt (1 - eps) * R := by
    have hh := mul_lt_mul_of_pos_right hroot hR
    dsimp only [R] at hh ⊢
    linarith
  exact W.closedBall_compact_curvature_bound heps4 (Real.sqrt_nonneg _) hR hbuffer hradius
    (subset_refl _) (fun s hs y hy => by
      rw [Real.sq_sqrt (hB R).le]
      exact hmodel kappa W.model W.model_ancient W.model_scalar_base R y hy s hs.2) ha

theorem exists_uniform_windowed_source_scalar_bounds :
    ∃ C : ℝ → ℝ, (∀ r, 0 < C r) ∧ ∀ r : ℝ, 0 ≤ r →
      ∃ epsStar : ℝ, 0 < epsStar ∧
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M] (D : RealTimeInterval)
          (S : SolutionOn (I := I3) (M := M) D) (eps kappa : ℝ) (x : M) (t : ℝ),
          WindowedModelWitness eps kappa S x t → eps ≤ epsStar →
          ∀ y : M, riemannianEDistOf (S.base.metric t) x y ≤
            ENNReal.ofReal (r / Real.sqrt (S.scalar t x)) →
            |S.scalar t y| ≤ C r * S.scalar t x := by
  obtain ⟨B, hB, hbounds⟩ := exists_uniform_windowed_source_curvature_bounds.{u}
  refine ⟨fun r => 9 * Real.sqrt (B r), fun r => mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (hB r)), ?_⟩
  intro r hr
  obtain ⟨epsStar, hepsStar, hbound⟩ := hbounds r hr
  refine ⟨epsStar, hepsStar, ?_⟩
  intro M _ _ _ _ D S eps kappa x t W heps y hy
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hzero : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hres : rescaledMetric S t (S.scalar t x) W.scalar_pos 0 =
      scaleMetric (S.scalar t x) W.scalar_pos (S.base.metric t) := by
    simp only [rescaledMetric, parabolicTime_zero]
  have hy' : y ∈ riemannianClosedBallOf
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r := by
    have heq : r = Real.sqrt (S.scalar t x) * (r / Real.sqrt (S.scalar t x)) := by
      exact (mul_div_cancel₀ r (Real.sqrt_pos.mpr W.scalar_pos).ne').symm
    rw [hres, heq, riemannianClosedBallOf_scaleMetric]
    exact hy
  have hb := (hbound M D S eps kappa x t W heps 0 hzero).2 0 hzero y hy'
  have hs := scalar_abs_le_rm (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) y
  have hdim : Module.finrank ℝ (TangentSpace I3 y) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  rw [hdim] at hs
  have hscalar : metricScalarAt (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) y =
      (S.scalar t x)⁻¹ * S.scalar t y := by
    rw [hres, metricScalarAt_scaleMetric]
    rfl
  rw [hscalar, abs_mul, abs_of_pos (inv_pos.mpr W.scalar_pos)] at hs
  have hh : (S.scalar t x)⁻¹ * |S.scalar t y| ≤ 9 * Real.sqrt (B r) :=
    hs.trans (by
      norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (by norm_num : (0 : ℝ) ≤ 9))
  have hm := mul_le_mul_of_nonneg_left hh W.scalar_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ W.scalar_pos.ne', one_mul] at hm
  simpa only [mul_comm] using hm


theorem exists_windowed_curvature_radius_lower_bound_of_scalar_tendsto_atTop
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] (D : ℕ → RealTimeInterval)
        (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i))
        (eps kappa t : ℕ → ℝ) (x y : ∀ i, M i) (Q d : ℝ) (ell : ℕ → ℝ),
        (∀ᶠ i in atTop, Nonempty (WindowedModelWitness (eps i) (kappa i) (S i) (x i) (t i))) →
        (∀ᶠ i in atTop, eps i ≤ epsStar) → 0 < Q →
        Tendsto (fun i => (S i).scalar (t i) (x i)) atTop (𝓝 Q) →
        Tendsto (fun i => (S i).scalar (t i) (y i)) atTop atTop →
        Tendsto ell atTop (𝓝 d) →
        (∀ᶠ i in atTop, riemannianEDistOf ((S i).base.metric (t i)) (x i) (y i) ≤
          ENNReal.ofReal (ell i)) → r / Real.sqrt Q ≤ d := by
  obtain ⟨C, hC, hbounds⟩ := exists_uniform_windowed_source_scalar_bounds.{u}
  obtain ⟨epsStar, hepsStar, hbound⟩ := hbounds r hr
  refine ⟨epsStar, hepsStar, ?_⟩
  intro M _ _ _ _ D S eps kappa t x y Q d ell hw heps hQ hx hy hell hdist
  have hsep : ∀ᶠ i in atTop,
      ENNReal.ofReal (r / Real.sqrt ((S i).scalar (t i) (x i))) < ENNReal.ofReal (ell i) := by
    filter_upwards [hw, heps, hx.eventually_lt_const (lt_add_one Q),
      hy.eventually_gt_atTop (C r * (Q + 1)), hdist] with i hwi hepsi hxi hyi hdi
    obtain ⟨W⟩ := hwi
    have hfar : ENNReal.ofReal (r / Real.sqrt ((S i).scalar (t i) (x i))) <
        riemannianEDistOf ((S i).base.metric (t i)) (x i) (y i) := by
      by_contra hh
      have hb := hbound (M i) (D i) (S i) (eps i) (kappa i) (x i) (t i)
        W hepsi (y i) (not_lt.mp hh)
      have hmul := mul_le_mul_of_nonneg_left hxi.le (hC r).le
      exact (not_le.mpr hyi) ((le_abs_self _).trans (hb.trans hmul))
    exact hfar.trans_le hdi
  have hleft : Tendsto (fun i => ENNReal.ofReal
      (r / Real.sqrt ((S i).scalar (t i) (x i)))) atTop (𝓝 (ENNReal.ofReal (r / Real.sqrt Q))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.div
      (Real.continuous_sqrt.tendsto Q |>.comp hx) (Real.sqrt_pos.mpr hQ).ne')
  have hd : 0 ≤ d := ge_of_tendsto hell (hsep.mono fun _ hi =>
    (ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hi)).le)
  exact (ENNReal.ofReal_le_ofReal_iff hd).mp
    (le_of_tendsto_of_tendsto hleft (ENNReal.tendsto_ofReal hell) (hsep.mono fun _ hi => hi.le))

theorem exists_windowed_scalar_mul_sq_distance_limit_lower_bound {r : ℝ} (hr : 0 ≤ r) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] (D : ℕ → RealTimeInterval)
        (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i))
        (eps kappa t : ℕ → ℝ) (x y : ∀ i, M i) (Q d : ℝ) (ell : ℕ → ℝ),
        (∀ᶠ i in atTop, Nonempty (WindowedModelWitness (eps i) (kappa i) (S i) (x i) (t i))) →
        (∀ᶠ i in atTop, eps i ≤ epsStar) → 0 < Q →
        Tendsto (fun i => (S i).scalar (t i) (x i)) atTop (𝓝 Q) →
        Tendsto (fun i => (S i).scalar (t i) (y i)) atTop atTop →
        Tendsto ell atTop (𝓝 d) →
        (∀ᶠ i in atTop, riemannianEDistOf ((S i).base.metric (t i)) (x i) (y i) ≤
          ENNReal.ofReal (ell i)) → r ^ 2 ≤ Q * d ^ 2 := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_windowed_curvature_radius_lower_bound_of_scalar_tendsto_atTop.{u} hr
  refine ⟨epsStar, hepsStar, ?_⟩
  intro M _ _ _ _ D S eps kappa t x y Q d ell hw heps hQ hx hy hell hdist
  have hle := hbound M D S eps kappa t x y Q d ell hw heps hQ hx hy hell hdist
  have hmul : r ≤ Real.sqrt Q * d := by
    simpa only [mul_comm] using (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mp hle
  calc
    r ^ 2 ≤ (Real.sqrt Q * d) ^ 2 := pow_le_pow_left₀ hr hmul 2
    _ = Q * d ^ 2 := by rw [mul_pow, Real.sq_sqrt hQ.le]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
