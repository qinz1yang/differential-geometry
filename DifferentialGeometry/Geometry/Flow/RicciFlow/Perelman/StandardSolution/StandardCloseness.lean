import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowShiftConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SelectedCountersequenceAdapter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

private local instance windowSigmaCompact (V : TopologicalSpace.Opens ThreeSpace) :
    SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)

section WitnessGeometry

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

omit [T2Space M] in
private theorem edist_embedding_le_of_lt_modelRadius {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) {ρ : ℝ} (hρ : ρ < modelRadius eps)
    {y : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint ρ) :
    riemannianEDistOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (W.embedding y) ≤
      ENNReal.ofReal (Real.sqrt (1 + eps) * ρ) := by
  have hR : 0 < modelRadius eps := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have hL : 0 < Real.sqrt (1 + eps) := Real.sqrt_pos.mpr (by linarith [W.eps_pos])
  have hsource : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (by linarith)).trans W.buffered_ball
  have hupper : ∀ z ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius eps), ∀ v : TangentSpace I3 z,
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner (W.embedding z)
        (mfderiv I3 I3 W.embedding z v) (mfderiv I3 I3 W.embedding z v) ≤
        Real.sqrt (1 + eps) ^ 2 * (W.model.S.base.metric 0).inner z v v := by
    intro z hz v
    have h0 : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
      ⟨neg_nonpos.mpr (inv_pos.mpr W.eps_pos).le, le_rfl⟩
    have heq := W.comparison.pullback_eq 0 z hz (fun _ => v)
    have hle := (W.comparison.equivalence 0 h0 z hz v).2
    rw [Real.sq_sqrt (by linarith [W.eps_pos])]
    rw [heq] at hle
    exact hle
  have hy' : riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint y <
      ENNReal.ofReal (modelRadius eps) :=
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hρ)
  have hmap := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    (W.model.S.base.metric 0) (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) W.embedding
    W.model.basepoint y hR hL hsource hupper hy'
  rw [W.base_map] at hmap
  refine hmap.trans ?_
  rw [ENNReal.ofReal_mul hL.le]
  exact mul_le_mul_right hy _

end WitnessGeometry

section StandardAge

open DifferentialGeometry.Tensor0SBundle

theorem StandardSolution.exists_oriented_witness_of_age {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ τQ : ℝ, 1 ≤ τQ ∧ ∀ (Q : StandardSolution) (o : TangentOrientationSection ThreeSpace)
      (x : ThreeSpace) (t : ℝ), 0 ≤ t → t < 1 → τQ ≤ t * Q.val.toSolutionOn.scalar t x →
        OrientedWitness Q.val.toSolutionOn o ε standardModelKappa x t := by
  obtain ⟨α, hα, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  obtain ⟨Q₀, hQ₀, hmodel⟩ := exists_standard_high_scalar_model_threshold hε hε1 hα
  have hmax := le_max_left Q₀ (α * (9 * K))
  refine ⟨max Q₀ (α * (9 * K)) + 1, by linarith, ?_⟩
  intro Q o x t ht0 ht1 hage
  have hlt : ENNReal.ofReal t < Q.val.lifetime := by
    rw [Q.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr ht1
  have ht : t ∈ Q.val.domain :=
    (mem_lifetimeInterval_carrier Q.val.lifetime Q.val.lifetime_pos t).mpr ⟨ht0, hlt⟩
  have hαt : α ≤ t := by
    by_contra hlt'
    have hlt'' : t < α := lt_of_not_ge hlt'
    have hR : Q.val.toSolutionOn.scalar t x ≤ 9 * K := by
      have hrm := hcurv Q.val t ht0 hlt''.le hlt t ⟨ht0, le_rfl⟩ x
      rw [metricRm04_apply] at hrm
      have habs := scalar_abs_le_rm (Q.val.metric t) x
      have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) x) : ℝ) = 3 := by
        rw [show Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 from finrank_euclideanSpace_fin]
        norm_num
      rw [hdim] at habs
      change metricScalarAt (Q.val.metric t) x ≤ 9 * K
      have hle : (3 : ℝ) ^ 2 *
          Real.sqrt (normSq0S (Q.val.metric t) x 4 (metricRm04At (Q.val.metric t) x)) ≤
            9 * K := by
        nlinarith
      exact (le_abs_self _).trans (habs.trans hle)
    have h1 := mul_le_mul_of_nonneg_left hR ht0
    have h2 := mul_le_mul_of_nonneg_right hlt''.le (by positivity : (0 : ℝ) ≤ 9 * K)
    linarith [le_max_right Q₀ (α * (9 * K))]
  refine hmodel Q.val o x t ht hαt ht1 ?_
  change Q₀ ≤ Q.val.toSolutionOn.scalar t x
  rcases le_or_gt 0 (Q.val.toSolutionOn.scalar t x) with hR0 | hR0
  · have h1 := mul_le_mul_of_nonneg_right ht1.le hR0
    linarith
  · have h1 := mul_nonpos_of_nonneg_of_nonpos ht0 hR0.le
    linarith

end StandardAge

section WindowConvergence

private theorem exists_standard_time_lipschitz {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ Q : StandardSolution, ∀ i ≤ 2, ∀ s ∈ Icc 0 Θ, ∀ t ∈ Icc 0 Θ,
      ∀ x : ThreeSpace, metricDerivNorm i (Q.val.metric s) (Q.val.metric t) StandardCap.metric x ≤
        L * |s - t| := by
  have hlt : ENNReal.ofReal Θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hΘ
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab Θ hΘ0 hlt
  obtain ⟨Λ, -, C, L, -, hL, hstd⟩ := standard_metric_bounds_on_shorter_windows Θ K hΘ0 hK
  refine ⟨L 0 + L 1 + L 2, by linarith [hL 0, hL 1, hL 2], ?_⟩
  intro Q i hi s hs t ht x
  obtain ⟨-, -, hlip⟩ := hstd Q.val Θ hΘ0 le_rfl (hlife Q) (hRm Q)
  refine (hlip i s hs t ht x).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  interval_cases i <;> linarith [hL 0, hL 1, hL 2]

theorem StandardSolution.tendsto_scalar_of_close {Θ D T₀ : ℝ} (hΘ : Θ < 1)
    {Q : ℕ → StandardSolution} {Q' : StandardSolution}
    (hQ : ∀ K : Set (standardCapWindow D), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
        metricDerivNormSupOn K p (((Q i).val.metric t).restrictOpen (standardCapWindow D))
          ((Q'.val.metric t).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) < e)
    {T : ℕ → ℝ} (hTΘ : ∀ n, T n ∈ Icc 0 Θ) (hT : Tendsto T atTop (𝓝 T₀))
    {g : ℕ → SmoothRiemannianMetric (𝓡 3) (standardCapWindow D)}
    (hclose : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ i ≤ p, ∀ v : standardCapWindow D,
      metricDerivNorm i (g n) (((Q n).val.metric (T n)).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e)
    {z : ℕ → standardCapWindow D} {z₀ : standardCapWindow D} (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n => metricScalarAt (g n) (z n)) atTop
      (𝓝 (metricScalarAt (Q'.val.metric T₀) z₀.val)) := by
  have hT₀ : T₀ ∈ Icc 0 Θ := isClosed_Icc.mem_of_tendsto hT (Eventually.of_forall hTΘ)
  obtain ⟨L, hL, hlip⟩ := exists_standard_time_lipschitz (hT₀.1.trans hT₀.2) hΘ
  rw [← metricScalarAt_restrictOpen (Q'.val.metric T₀) (standardCapWindow D) z₀]
  refine tendsto_metricScalarAt_of_metricDerivNormSupOn
    (R := StandardCap.metric.restrictOpen (standardCapWindow D)) (fun K hK e he => ?_) hz
  obtain ⟨j, hj⟩ := hQ K hK 2 (e / 4) (by positivity)
  have hδ : 0 < e / (4 * (L + 1)) := by positivity
  have hsmall : ∀ᶠ n in atTop, |T n - T₀| < e / (4 * (L + 1)) := by
    filter_upwards [Metric.tendsto_nhds.mp hT _ hδ] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hclose 2 (e / 4) (by positivity), eventually_ge_atTop j, hsmall]
    with n hn hnj hns
  have hLs : L * |T n - T₀| ≤ e / 4 := by
    have hL1 : 0 < L + 1 := by linarith
    have hmul : (L + 1) * |T n - T₀| ≤ (L + 1) * (e / (4 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hns.le hL1.le
    have heq : (L + 1) * (e / (4 * (L + 1))) = e / 4 := by field_simp
    nlinarith [abs_nonneg (T n - T₀)]
  refine (metricDerivNormSupOn_le_of_forall K 2 _ _ _ (3 * (e / 4)) (by positivity)
    fun i hi v hv => ?_).trans_lt (by linarith)
  have h1 := (hn i hi v).le
  have h2 := (derivNorm_le_sup hK hi _ _ _ hv).trans (hj n hnj (T n) (hTΘ n)).le
  have h3 : metricDerivNorm i ((Q'.val.metric (T n)).restrictOpen (standardCapWindow D))
      ((Q'.val.metric T₀).restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) v ≤ e / 4 := by
    rw [metricDerivNorm_restrictOpen]
    exact (hlip Q' i hi _ (hTΘ n) _ hT₀ v.val).trans hLs
  have t1 := metricDerivNorm_triangle i (g n)
    (((Q n).val.metric (T n)).restrictOpen (standardCapWindow D))
    ((Q'.val.metric T₀).restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) v
  have t2 := metricDerivNorm_triangle i
    (((Q n).val.metric (T n)).restrictOpen (standardCapWindow D))
    ((Q'.val.metric (T n)).restrictOpen (standardCapWindow D))
    ((Q'.val.metric T₀).restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D)) v
  linarith

end WindowConvergence

section StandardImage

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem modelRadius_add_one_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    modelRadius δ + 1 < modelRadius (δ / 4) := by
  have hs : Real.sqrt (δ / 4) = Real.sqrt δ / 2 := by
    rw [Real.sqrt_div' δ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hlt : Real.sqrt δ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hδ.le hδ1
  simp only [modelRadius, hs]
  rw [inv_div]
  have h1 : 1 < (Real.sqrt δ)⁻¹ := one_lt_inv₀ hpos |>.mpr hlt
  have h2 : 2 / Real.sqrt δ = 2 * (Real.sqrt δ)⁻¹ := by rw [div_eq_mul_inv]
  linarith

private theorem image_subset_standardCapWindow {Q : StandardSolution} {T₀ : ℝ}
    (hT₀ : T₀ ∈ Q.val.domain) {x : ThreeSpace} {δ kappa : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (W : WindowedModelWitness (δ / 4) kappa
      (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀) x 0)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q.val.metric T₀).inner y v v)
    (hR : 1 ≤ Q.val.toSolutionOn.scalar T₀ x) {r D : ℝ} (hx : ‖x‖ ≤ r)
    (hD : r + 2 * (modelRadius δ + 1) * Real.sqrt Λ ≤ D) :
    W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius δ + 1) ⊆ (standardCapWindow D : Set ThreeSpace) := by
  rintro _ ⟨y, hy, rfl⟩
  change ‖W.embedding y‖ < D + 1
  have hPs : (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x =
      Q.val.toSolutionOn.scalar T₀ x := by
    rw [parabolicSolution_scalar]
    simp [parabolicTime]
  have h1 := edist_embedding_le_of_lt_modelRadius W (modelRadius_add_one_lt hδ hδ1) hy
  have ht : parabolicTime T₀ 1 (parabolicTime 0
      ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x) 0) = T₀ := by
    simp [parabolicTime]
  change riemannianEDistOf (scaleMetric _ W.scalar_pos
    (scaleMetric 1 one_pos (Q.val.metric (parabolicTime T₀ 1 (parabolicTime 0
      ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x) 0)))))
    x (W.embedding y) ≤ _ at h1
  rw [ht, DifferentialGeometry.edistOf_scale, DifferentialGeometry.edistOf_scale,
    Real.sqrt_one, ENNReal.ofReal_one, one_mul] at h1
  have hΛ0 : 0 < Λ⁻¹ := inv_pos.mpr (by linarith)
  have h2 := DifferentialGeometry.le_edistOf_of_quad StandardCap.metric (Q.val.metric T₀) hΛ0
    hΛ x (W.embedding y)
  have h3 := StandardCap.radial_difference_le_edist x (W.embedding y)
  set u := |‖W.embedding y‖ - ‖x‖|
  set a := Real.sqrt ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀).scalar 0 x)
  set b := Real.sqrt Λ⁻¹
  set c := Real.sqrt (1 + δ / 4) * (modelRadius δ + 1)
  have hρ : 0 < modelRadius δ + 1 := by
    have : 0 < modelRadius δ := inv_pos.mpr (Real.sqrt_pos.mpr hδ)
    linarith
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha1 : 1 ≤ a := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by rw [hPs]; exact hR)
  have hc : c ≤ 2 * (modelRadius δ + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ hρ.le
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have hchain : ENNReal.ofReal (a * (b * u)) ≤ ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_mul hb]
    exact (mul_le_mul_right (mul_le_mul_right h3 _) _).trans
      ((mul_le_mul_right h2 _).trans h1)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  have hbΛ : b * Real.sqrt Λ = 1 := by
    rw [← Real.sqrt_mul hΛ0.le, inv_mul_cancel₀ (by linarith), Real.sqrt_one]
  have hu : u ≤ 2 * (modelRadius δ + 1) * Real.sqrt Λ := by
    have hsΛ : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
    have hu0 : 0 ≤ u := abs_nonneg _
    have hbu : b * u ≤ a * (b * u) := le_mul_of_one_le_left (mul_nonneg hb hu0) ha1
    calc u = b * u * Real.sqrt Λ := by rw [mul_comm b u, mul_assoc, hbΛ, mul_one]
      _ ≤ c * Real.sqrt Λ := mul_le_mul_of_nonneg_right (hbu.trans (hreal.trans le_rfl)) hsΛ
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hsΛ
  have hn : ‖W.embedding y‖ ≤ ‖x‖ + u := by
    have := le_abs_self (‖W.embedding y‖ - ‖x‖)
    linarith
  linarith

end StandardImage

section StrictWitness

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private theorem nonempty_euclidean_tangentOrientation :
    Nonempty (TangentOrientationSection ThreeSpace) := by
  let e := (finCongr (by simp : Module.finrank ℝ ThreeSpace = 3)).symm
  let o := DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation ThreeSpace
    (Orientation.reindex ℝ ThreeSpace e
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨O, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) o
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  let O₃ : DifferentialGeometry.ManifoldOrientation (𝓡 3) ThreeSpace 3 :=
    cast (congrArg (fun n =>
      DifferentialGeometry.ManifoldOrientation (𝓡 3) ThreeSpace n) hdim) O
  exact ⟨{ orientation := O₃.orientation, locally_constant := O₃.locally_constant }⟩

private theorem isPreconnected_standardCapWindow (D : ℝ) :
    IsPreconnected (standardCapWindow D : Set ThreeSpace) := by
  have h : (standardCapWindow D : Set ThreeSpace) = Metric.ball 0 (D + 1) := by
    ext x
    simp [standardCapWindow]
  rw [h]
  exact (convex_ball 0 (D + 1)).isPreconnected

theorem StandardSolution.exists_strict_oriented_witness
    {δ T₀ Λ r D : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {Q : StandardSolution}
    (hT₀mem : T₀ ∈ Q.val.domain) {x : standardCapWindow D}
    (hwit : ∀ o : TangentOrientationSection ThreeSpace,
      OrientedWitness Q.val.toSolutionOn o (δ / 4) standardModelKappa x.val T₀)
    (hR1 : 1 ≤ Q.val.toSolutionOn.scalar T₀ x.val) (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ y (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * StandardCap.metric.inner y v v ≤ (Q.val.metric T₀).inner y v v)
    (hx : ‖x.val‖ ≤ r) (hD : r + 2 * (modelRadius δ + 1) * Real.sqrt Λ ≤ D) :
    ∃ W : WindowedModelWitness δ standardModelKappa
        (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀mem) x.val 0,
      (∀ a b, a + 2 * b ≤ modelOrder δ → ∀ s ∈ Icc (-modelDepth δ) 0,
        ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius δ),
          tensor02CovDerivNormWith a (W.comparison.jet b s)
            (W.model.S.base.metric s) (W.model.S.base.metric s) y < δ) ∧
      ∃ hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
          (modelRadius δ + 1) ⊆ (standardCapWindow D : Set ThreeSpace),
        (∀ o : TangentOrientationSection (standardCapWindow D),
          ∃ oN : TangentOrientationSection W.model.M,
            ∀ y ∈ (W.toRestrictOpen (x := x) hU).embedding.source,
              ∃ hf : Function.Bijective
                  (mfderiv I3 I3 (W.toRestrictOpen (x := x) hU).embedding y),
                PreservesTangentOrientationAt oN o
                  (W.toRestrictOpen (x := x) hU).embedding y hf) ∧
        4 * (δ * (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 x.val)⁻¹ ≤
          T₀ := by
  have hT₀1 : T₀ < 1 := by
    have ht := ((mem_lifetimeInterval_carrier Q.val.lifetime Q.val.lifetime_pos T₀).mp hT₀mem).2
    rw [Q.lifetime_eq_one] at ht
    exact ENNReal.ofReal_lt_one.mp ht
  obtain ⟨oE⟩ := nonempty_euclidean_tangentOrientation
  have hP : IsSolutionOn (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀mem) :=
    parabolicSolution_isSolutionOn _ Q.val.isSolutionOn T₀ 1 one_pos hT₀mem
  have hwP : OrientedWitness (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀mem) oE
      (δ / 4) standardModelKappa x.val 0 := by
    refine (orientedWitness_paraSolution_iff Q.val.toSolutionOn oE one_pos hT₀mem 0 x.val
      (δ / 4) standardModelKappa).mpr ?_
    rw [parabolicTime_zero]
    exact hwit oE
  obtain ⟨W₄, oN, hO⟩ := hwP
  have hPs : (parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 x.val =
      Q.val.toSolutionOn.scalar T₀ x.val := by
    rw [parabolicSolution_scalar]
    simp [parabolicTime]
  have hR0 : 0 < Q.val.toSolutionOn.scalar T₀ x.val := by linarith
  have hwin4 : ((δ / 4) * Q.val.toSolutionOn.scalar T₀ x.val)⁻¹ ≤ T₀ := by
    have hl := W₄.window_mem ⟨le_rfl, by
      have := inv_pos.mpr (mul_pos (by positivity : (0 : ℝ) < δ / 4) W₄.scalar_pos)
      linarith⟩
    rw [hPs] at hl
    change parabolicTime T₀ 1 (0 - ((δ / 4) * Q.val.toSolutionOn.scalar T₀ x.val)⁻¹) ∈
      (lifetimeInterval Q.val.lifetime Q.val.lifetime_pos).carrier at hl
    rw [mem_lifetimeInterval_carrier] at hl
    simp only [parabolicTime, div_one] at hl
    linarith [hl.1]
  have hreg4 : ∀ s ∈ Ioo (-modelDepth (δ / 4)) 0, parabolicTime 0
      ((parabolicSolution Q.val.toSolutionOn T₀ 1 one_pos hT₀mem).scalar 0 x.val) s ∈
      (parabolicInterval (lifetimeInterval Q.val.lifetime Q.val.lifetime_pos) T₀ 1
        hT₀mem).regular := by
    intro s hs
    rw [hPs]
    change parabolicTime T₀ 1 (parabolicTime 0 (Q.val.toSolutionOn.scalar T₀ x.val) s) ∈
      (lifetimeInterval Q.val.lifetime Q.val.lifetime_pos).regular
    rw [mem_lifetimeInterval_regular]
    have hkey : -((δ / 4) * Q.val.toSolutionOn.scalar T₀ x.val)⁻¹ <
        s / Q.val.toSolutionOn.scalar T₀ x.val := by
      have h1 : -(δ / 4)⁻¹ < s := hs.1
      rw [lt_div_iff₀ hR0]
      have heq : -((δ / 4) * Q.val.toSolutionOn.scalar T₀ x.val)⁻¹ *
          Q.val.toSolutionOn.scalar T₀ x.val = -(δ / 4)⁻¹ := by
        field_simp
      rw [heq]
      exact h1
    have hneg : s / Q.val.toSolutionOn.scalar T₀ x.val < 0 := div_neg_of_neg_of_pos hs.2 hR0
    simp only [parabolicTime, div_one, zero_add]
    exact ⟨by linarith,
      (ENNReal.ofReal_lt_one.mpr (by linarith)).trans_eq Q.lifetime_eq_one.symm⟩
  have hlt : δ / 4 < δ := by linarith
  let W := W₄.monoOfRegular hP hlt.le hδ1 hreg4
  have hU : W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius δ + 1) ⊆ (standardCapWindow D : Set ThreeSpace) :=
    image_subset_standardCapWindow hT₀mem hδ hδ1 W₄ hΛ1 hΛ hR1 hx hD
  refine ⟨W, W₄.mono_of_regular_strict_of_lt hP hlt hδ1 hreg4, hU, ?_, ?_⟩
  · let : PreconnectedSpace (standardCapWindow D) :=
      Subtype.preconnectedSpace (isPreconnected_standardCapWindow D)
    intro o
    exact W.exists_toRestrictOpen_orientation (x := x) hU oE oN hO o
  · rw [hPs]
    have heq : 4 * (δ * Q.val.toSolutionOn.scalar T₀ x.val)⁻¹ =
        ((δ / 4) * Q.val.toSolutionOn.scalar T₀ x.val)⁻¹ := by
      field_simp
    rw [heq]
    exact hwin4

end StrictWitness

end DifferentialGeometry.PDE.RicciFlow
