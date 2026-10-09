import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.AncientPointedFlowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.ClosedWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction
import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Metric.Distance.MetricLocality
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem scaleMetric_restrictOpen {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Opens M) {c : ℝ} (hc : 0 < c) :
    scaleMetric c hc (g.restrictOpen U) = (scaleMetric c hc g).restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem scaleMetric_restrictOpenOfSubset {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] {U V : Opens M}
    (hUV : U ≤ V) (g : SmoothRiemannianMetric ThreeModel V) {c : ℝ} (hc : 0 < c) :
    (scaleMetric c hc g).restrictOpenOfSubset hUV =
      scaleMetric c hc (g.restrictOpenOfSubset hUV) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem comp_inclusion_eq_of_backward_maps (H : ObservedHistory.{u})
    {a b t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) (hbt : b ≤ t)
    {U V : Opens (H.stageAt t).Carrier}
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U → (H.stage j.val).Carrier)
    (hcf : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : U,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlf : ∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (g : (j : H.StageInterval (H.activeStage b) (H.activeStage t)) → V → (H.stage j.val).Carrier)
    (hcg : ∀ (i : Fin H.eventCount) (hi : H.activeStage b ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : V,
      (H.event i).RegularCrossing (g ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (g ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlg : ∀ x : V, g ⟨H.activeStage t, H.activeStage_mono hbt, le_rfl⟩ x = x.val)
    (j : Fin (H.eventCount + 1)) (hja : H.activeStage a ≤ j) (hjb : H.activeStage b ≤ j)
    (hjt : j ≤ H.activeStage t) :
    f ⟨j, hja, hjt⟩ ∘ Opens.inclusion (inf_le_left : U ⊓ V ≤ U) =
      g ⟨j, hjb, hjt⟩ ∘ Opens.inclusion (inf_le_right : U ⊓ V ≤ V) := by
  funext z
  let A : BackwardPointTrace H j (H.activeStage t) hjt (z : (H.stageAt t).Carrier) :=
    { point := fun i hi hl => f ⟨i, hja.trans hi, hl⟩ (Opens.inclusion inf_le_left z)
      endpoint_eq := hlf _
      crossing := fun i hi hl => hcf i (hja.trans hi) hl _ }
  let B : BackwardPointTrace H j (H.activeStage t) hjt (z : (H.stageAt t).Carrier) :=
    { point := fun i hi hl => g ⟨i, hjb.trans hi, hl⟩ (Opens.inclusion inf_le_right z)
      endpoint_eq := hlg _
      crossing := fun i hi hl => hcg i (hjb.trans hi) hl _ }
  exact A.point_unique B j le_rfl hjt

private def isScaledSurvivor (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (y : (H.stageAt t).Carrier) (R ρ θ K : ℝ) (hR : 0 < R) (W : Opens (H.stageAt t).Carrier)
    (g : ℝ → SmoothRiemannianMetric ThreeModel W) : Prop :=
  (W : Set (H.stageAt t).Carrier) = riemannianBallOf (H.stageMetric (H.activeStage t) t) y ρ ∧
  (∀ θ' : ℝ, ∀ hθ' : 0 ≤ θ', θ' ≤ θ → IsSolutionOn ({ base.metric := g } :
    SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed (-θ') 0 (neg_nonpos.mpr hθ')))) ∧
  g 0 = (scaleMetric R hR (H.stageMetric (H.activeStage t) t)).restrictOpen W ∧
  (∀ s ∈ Icc (-θ) 0, ∀ x : W, curvDerivNormSq 0 (g s) x ≤ K ^ 2) ∧
  (∀ s ∈ Icc (-θ) 0, (t : ℝ) + s / R ∈ H.stageDomain (H.activeStage t) →
    g s = scaleMetric R hR
      ((H.stageMetric (H.activeStage t) ((t : ℝ) + s / R)).restrictOpen W)) ∧
  ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = t - θ / R ∧
    ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
        (H.stage j.val).Carrier,
      ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
        (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
            (hl : i.succ ≤ H.activeStage t), ∀ x : W,
          (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
            (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
        (∀ x : W, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
        ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
          (t : ℝ) + s / R ∈ H.stageDomain j.val →
            g s = scaleMetric R hR
              (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j))

private theorem mem_Icc_of_mem_window {a t R θ s : ℝ} (hR : 0 < R) (ha : a = t - θ / R)
    (hs : s ∈ Icc (-θ) 0) : t + s / R ∈ Icc a t := by
  have h1 : -θ / R ≤ s / R := div_le_div_of_nonneg_right hs.1 hR.le
  have h2 : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
  rw [neg_div] at h1
  constructor <;> linarith

private theorem exists_isScaledSurvivor_of_isTracedRegion (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R ρ θ K : ℝ} (hR : 0 < R)
    (hθ : 0 < θ) (h : H.isTracedRegion t y ρ (θ / R) (K * R)) :
    ∃ (W : Opens (H.stageAt t).Carrier) (g : ℝ → SmoothRiemannianMetric ThreeModel W),
      H.isScaledSurvivor t y R ρ θ K hR W g := by
  obtain ⟨a, hat, ha, U, hU, f, hf, -, hcross, hlast, S, hS, hmetric, hRm, hcurrent, -⟩ :=
    H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t y h
  refine ⟨U, (S.parabolicClosedWindow t R θ hR hθ.le).base.metric, hU, ?_, ?_, ?_, ?_,
    a, hat, ha, f, hf, hcross, hlast, ?_⟩
  · intro θ' hθ' hle
    have hsub : θ' / R ≤ θ / R := div_le_div_of_nonneg_right hle hR.le
    have hsol := isSolutionOn_parabolicClosedWindow S hS (T := (t : ℝ)) hR hθ'
      (fun v hv => ⟨by linarith [hv.1], hv.2⟩) (fun v hv => ⟨by linarith [hv.1], hv.2⟩)
    exact hsol
  · change scaleMetric R hR (S.base.metric ((t : ℝ) + 0 / R)) = _
    rw [zero_div, add_zero, hcurrent t ⟨hat, le_rfl⟩ (H.activeStage_mem t),
      scaleMetric_restrictOpen]
  · intro s hs x
    change curvDerivNormSq 0 (scaleMetric R hR (S.base.metric ((t : ℝ) + s / R))) x ≤ K ^ 2
    rw [curvDerivNormSq_scaleMetric]
    have hb := hRm _ (mem_Icc_of_mem_window hR ha hs) x
    have hb' : curvDerivNormSq 0 (S.base.metric ((t : ℝ) + s / R)) x ≤ (K * R) ^ 2 := hb
    have hR2 : R⁻¹ ^ (0 + 2) * (K * R) ^ 2 = K ^ 2 := by
      rw [zero_add]
      field_simp
    calc R⁻¹ ^ (0 + 2) * curvDerivNormSq 0 (S.base.metric ((t : ℝ) + s / R)) x
        ≤ R⁻¹ ^ (0 + 2) * (K * R) ^ 2 := mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = K ^ 2 := hR2
  · intro s hs hdom
    change scaleMetric R hR (S.base.metric ((t : ℝ) + s / R)) = _
    rw [hcurrent _ (mem_Icc_of_mem_window hR ha hs) hdom]
  · intro s hs j hdom
    change scaleMetric R hR (S.base.metric ((t : ℝ) + s / R)) = _
    rw [hmetric j _ (mem_Icc_of_mem_window hR ha hs) hdom]

private theorem isCompact_riemannianClosedBallOf_restrictOpen {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : Opens M) (p : U) (r : ℝ)
    (hsub : riemannianClosedBallOf g (p : M) r ⊆ U) :
    IsCompact (riemannianClosedBallOf (g.restrictOpen U) p r) := by
  have hK : IsCompact (Subtype.val ⁻¹' riemannianClosedBallOf g (p : M) r : Set U) :=
    U.isOpenEmbedding'.isEmbedding.isInducing.isCompact_preimage'
      (Geometry.Metric.isClosed_riemannianClosedBallOf g _ r).isCompact
      (by rw [Subtype.range_coe]; exact hsub)
  refine hK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ p r) ?_
  intro x hx
  exact (riemannianEDistOf_le_restrictOpen g U p x).trans hx

private theorem exists_curvDerivNorm_bound_of_window {θ K : ℝ} (hθ : 0 < θ) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
        (g : ℝ → SmoothRiemannianMetric ThreeModel M),
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := M)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le))) →
        (∀ s ∈ Icc (-θ) 0, ∀ x : M, curvDerivNormSq 0 (g s) x ≤ K ^ 2) →
        ∀ p : M, IsCompact (riemannianClosedBallOf (g 0) p 1) →
        ∀ m : ℕ, ∀ s ∈ Icc (-θ / 2) 0, curvDerivNorm m (g s) p ≤ B m := by
  have hK' : 0 < |K| + 1 := by positivity
  refine ⟨fun m => shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m
      ((|K| + 1) * ((0 - -θ) / 4))
      ((1 / (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (|K| + 1) * (0 - -θ)))) *
        Real.sqrt (|K| + 1) /
        (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (|K| + 1) * ((0 - -θ) / 4)))) *
      (|K| + 1) / Real.sqrt ((0 - -θ) / 4) ^ m, fun m => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK'.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  intro M _ _ _ _ _ g hsol hcurv p hcompact m s hs
  have hKK : K ^ 2 ≤ (|K| + 1) ^ 2 := by
    rw [← sq_abs K]
    exact pow_le_pow_left₀ (abs_nonneg K) (by linarith) 2
  exact shi_curvDerivNorm_on_terminal_ball ({ base.metric := g } : SolutionOn (I := ThreeModel)
      (M := M) (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le))) hsol
    (a := -θ) (b := 0) (by linarith) hK' one_pos (fun v hv => hv) (fun v hv => hv) p hcompact
    (fun v hv z _ => (hcurv v hv z).trans hKK) m s ⟨by linarith [hs.1], hs.2⟩ p
    (by rw [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self]; exact bot_le)

private theorem isTracedRegion_of_mem_riemannianClosedBallOf {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {y x : (H.stageAt t).Carrier} {ρ τ K r ρ' : ℝ}
    (h : H.isTracedRegion t y ρ τ K)
    (hx : x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) y r) (hr : 0 ≤ r)
    (hρ' : 0 < ρ') (hle : r + ρ' ≤ ρ) : H.isTracedRegion t x ρ' τ K := by
  obtain ⟨-, hτ, a, hat, ha, htr⟩ := h
  refine ⟨hρ', hτ, a, hat, ha, fun z hz => htr z ?_⟩
  have hxt : riemannianEDistOf (H.stageMetric (H.activeStage t) t) y x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  change riemannianEDistOf _ y z < ENNReal.ofReal ρ
  calc riemannianEDistOf (H.stageMetric (H.activeStage t) t) y z
      ≤ riemannianEDistOf (H.stageMetric (H.activeStage t) t) y x +
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) x z :=
        riemannianEDistOf_triangle _ y x z
    _ < ENNReal.ofReal r + ENNReal.ofReal ρ' := ENNReal.add_lt_add_of_le_of_lt hxt hx hz
    _ = ENNReal.ofReal (r + ρ') := (ENNReal.ofReal_add hr hρ'.le).symm
    _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hle

private theorem scaled_volume_ball_ge_of_isTracedRegion (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) {R r a K κ ρ : ℝ} (hR : 0 < R)
    (hr : 0 ≤ r) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K) (haK : a ^ 2 * K ≤ 1) (hκ : 0 ≤ κ)
    (haρ : a / Real.sqrt R ≤ ρ)
    (htr : H.isTracedRegion t y ((r + 1) / Real.sqrt R) (1 / R) (K * R))
    (hvol : ∀ (p : (H.stageAt t).Carrier) (s : ℝ), s ≤ ρ →
      H.isParabolicallyRmControlledBall t p s →
      ENNReal.ofReal κ * ENNReal.ofReal s ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p s))
    (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianClosedBallOf (scaleMetric R hR (H.stageMetric (H.activeStage t) t)) y r) :
    ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
        (scaleMetric R hR (H.stageMetric (H.activeStage t) t))
        (riemannianBallOf (scaleMetric R hR (H.stageMetric (H.activeStage t) t)) x a) := by
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsqR : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hs : 0 < a / Real.sqrt R := div_pos ha hsq
  have hxr : Real.sqrt R * (r / Real.sqrt R) = r := by field_simp
  have hxa : Real.sqrt R * (a / Real.sqrt R) = a := by field_simp
  have hx' :
      x ∈ riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) y (r / Real.sqrt R) := by
    rw [← riemannianClosedBallOf_scaleMetric R hR, hxr]
    exact hx
  have hrad : r / Real.sqrt R + a / Real.sqrt R ≤ (r + 1) / Real.sqrt R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hsq.le
  have htr' := isTracedRegion_of_mem_riemannianClosedBallOf htr hx' (by positivity) hs hrad
  have hdepth : (a / Real.sqrt R) ^ 2 ≤ 1 / R := by
    rw [div_pow, hsqR]
    exact div_le_div_of_nonneg_right (by nlinarith) hR.le
  have hbound : K * R ≤ ((a / Real.sqrt R) ^ 2)⁻¹ := by
    rw [div_pow, hsqR, inv_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hpc : H.isParabolicallyRmControlledBall t x (a / Real.sqrt R) :=
    (H.isParabolicallyRmControlledBall_iff_isTracedRegion t x _).2
      (htr'.mono hs le_rfl (by positivity) hdepth (by positivity) hbound)
  have hv := hvol x _ haρ hpc
  have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hv' := (Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    (H.stageMetric (H.activeStage t) t) R hR x (a / Real.sqrt R) (ENNReal.ofReal κ)).2
      (by rw [hfin]; exact hv)
  rw [hxa] at hv'
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow ha.le]
  exact hv'

private theorem riemannianClosedBallOf_scaleMetric_eq {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ) :
    riemannianClosedBallOf (scaleMetric c hc g) x r =
      riemannianClosedBallOf g x (r / Real.sqrt c) := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  conv_lhs => rw [show r = Real.sqrt c * (r / Real.sqrt c) by field_simp]
  exact riemannianClosedBallOf_scaleMetric c hc g x _

private theorem riemannianBallOf_scaleMetric_eq {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) {c : ℝ} (hc : 0 < c) (x : M) (r : ℝ) :
    riemannianBallOf (scaleMetric c hc g) x r = riemannianBallOf g x (r / Real.sqrt c) := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  conv_lhs => rw [show r = Real.sqrt c * (r / Real.sqrt c) by field_simp]
  exact riemannianBallOf_scaleMetric c hc g x _

private theorem exists_small_volume_radius {r R' C K : ℝ} (hrR : r < R') (hC : 0 ≤ C)
    (hK : 0 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ r + a ≤ R' ∧ a ^ 4 * C ^ 2 ≤ 1 ∧ a ^ 2 * K ≤ 1 := by
  set a := min (min (R' - r) 1) (min (1 / (K + 1)) (1 / (C + 1))) with ha
  have ha0 : 0 < a :=
    lt_min (lt_min (by linarith) one_pos) (lt_min (by positivity) (by positivity))
  have ha1 : a ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have har : a ≤ R' - r := (min_le_left _ _).trans (min_le_left _ _)
  have haK : a * (K + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  have haC : a * (C + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a, ha0, ha1, by linarith, ?_, by nlinarith⟩
  have hac : a * C ≤ 1 := by nlinarith
  have hac0 : 0 ≤ a * C := by positivity
  have h1 : (a * C) ^ 2 ≤ 1 := by nlinarith
  have h2 : a ^ 2 ≤ 1 := by nlinarith
  calc a ^ 4 * C ^ 2 = a ^ 2 * (a * C) ^ 2 := by ring
    _ ≤ 1 * 1 := mul_le_mul h2 h1 (sq_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem exists_ancient_pointed_flow_limit_of_isTracedRegion
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hvol : ∀ n (p : ((H n).stageAt (t n)).Carrier) (r : ℝ), r ≤ ρ →
      (H n).isParabolicallyRmControlledBall (t n) p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) p r)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (R n) (hR n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M)
      (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)),
      (∀ k : ℕ, ∀ᶠ n in atTop,
        (W k n : Set (X.obj n).M) =
          riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) ∧
        ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
          (t n : ℝ) + s / R n ∈ (H n).stageDomain ((H n).activeStage (t n)) →
          h k n s = scaleMetric (R n) (hR n)
            (((H n).stageMetric ((H n).activeStage (t n)) ((t n : ℝ) + s / R n)).restrictOpen
              (W k n))) ∧
      ∃ (f : ℕ → ℕ), StrictMono f ∧
        ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
          (F : PointedRiemannianConvergenceMaps X P f),
          (∃ C : MetricConvergenceData F,
            ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n) ∧
          MetricComplete P ∧ ConnectedSpace P.M ∧
          (∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
            riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint R ⊆
              F.target n) ∧
          ∃ (V : ℕ → Opens P.M) (N : ℕ → ℕ),
            (∀ k, (V k : Set P.M) =
              riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
            (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) ∧
            ∃ (φ : ∀ k j, N k ≤ j → V k → W k (f j))
              (hφ : ∀ k j (hj : N k ≤ j),
                IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)),
              (∀ k j (hj : N k ≤ j) (z : V k), ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) =
                F.map j z) ∧
              ∃ G : ℝ → SmoothRiemannianMetric ThreeModel P.M,
                G 0 = P.metric ∧
                IsSolutionOn ({ base.metric := G } : SolutionOn (I := ThreeModel) (M := P.M)
                  (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
  intro X
  have hθ (k : ℕ) : 0 < 2 * ((k + 2 : ℕ) : ℝ) := by positivity
  choose K hK0 hKev using fun k : ℕ => htraced ((k + 3 : ℕ) : ℝ) (2 * ((k + 2 : ℕ) : ℝ))
    (by positivity) (hθ k)
  have hex : ∀ k n, ∃ (Wk : Opens (X.obj n).M) (g : ℝ → SmoothRiemannianMetric ThreeModel Wk),
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n) →
        (H n).isScaledSurvivor (t n) (y n) (R n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) Wk g := by
    intro k n
    by_cases htr : (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ) / R n) (K k * R n)
    · obtain ⟨Wk, g, hg⟩ :=
        (H n).exists_isScaledSurvivor_of_isTracedRegion (t n) (y n) (hR n) (hθ k) htr
      exact ⟨Wk, g, fun _ => hg⟩
    · exact ⟨⊤, fun _ => (X.obj n).metric.restrictOpen ⊤, fun hh => absurd hh htr⟩
  choose W h hWh using hex
  have hsurv (k : ℕ) : ∀ᶠ n in atTop,
      (H n).isScaledSurvivor (t n) (y n) (R n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
        (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n) (h k n) :=
    (hKev k).mono fun n hn => hWh k n hn
  have hWset (k n : ℕ) (hn : (H n).isScaledSurvivor (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n)
      (h k n)) :
      (W k n : Set (X.obj n).M) =
        riemannianBallOf (X.obj n).metric (X.obj n).basepoint ((k + 3 : ℕ) : ℝ) := by
    rw [hn.1]
    exact (riemannianBallOf_scaleMetric_eq _ (hR n) _ _).symm
  have hcompact : ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r) :=
    fun r _ => Eventually.of_forall fun n =>
      (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric _ r).isCompact
  have hsubW (k n : ℕ) (hn : (H n).isScaledSurvivor (t n) (y n) (R n)
      (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (2 * ((k + 2 : ℕ) : ℝ)) (K k) (hR n) (W k n)
      (h k n)) :
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) ⊆
        W k n := by
    intro z hz
    rw [hWset k n hn]
    exact lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by push_cast; linarith))
  have hball : ∀ k : ℕ, ∀ᶠ n in atTop,
      riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) ⊆
        W k n := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact (riemannianClosedBallOf_mono _ _ (by push_cast; linarith)).trans (hsubW k n hn)
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg _)))) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.1 ((k + 2 : ℕ) : ℝ) (Nat.cast_nonneg _)
      (by have := (Nat.cast_nonneg (k + 2) : (0 : ℝ) ≤ _); linarith)
  have hzero : ∀ k : ℕ, ∀ᶠ n in atTop, h k n 0 = (X.obj n).metric.restrictOpen (W k n) := by
    intro k
    filter_upwards [hsurv k] with n hn
    exact hn.2.2.1
  have hjets : ∀ k m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        (x : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        curvDerivNorm m (h k n s) x ≤ B := by
    intro k m
    obtain ⟨B, hB0, hB⟩ := exists_curvDerivNorm_bound_of_window (hθ k) (K := K k)
    refine ⟨B m, hB0 m, ?_⟩
    filter_upwards [hsurv k] with n hn s hs x hx
    let _ : SigmaCompactSpace (W k n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (W k n).isOpen)
    have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) x 1) := by
      rw [hn.2.2.1]
      apply isCompact_riemannianClosedBallOf_restrictOpen
      refine (riemannianClosedBallOf_subset_of_add_radius_le _ (Nat.cast_nonneg _) zero_le_one
        ?_ hx).trans (hsubW k n hn)
      push_cast
      linarith
    refine hB (h k n) (hn.2.1 _ (hθ k).le le_rfl) hn.2.2.2.1 x hcpt m s ⟨?_, hs.2⟩
    have := hs.1
    push_cast at this ⊢
    linarith
  have hcompat : ∀ k l : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((min k l + 1 : ℕ) : ℝ)) 0,
      (h k n s).restrictOpenOfSubset (inf_le_left : W k n ⊓ W l n ≤ W k n) =
        (h l n s).restrictOpenOfSubset (inf_le_right : W k n ⊓ W l n ≤ W l n) := by
    intro k l
    filter_upwards [hsurv k, hsurv l] with n hk hl s hs
    obtain ⟨a₁, hat₁, ha₁, f₁, hf₁, hc₁, hl₁, hp₁⟩ := hk.2.2.2.2.2
    obtain ⟨a₂, hat₂, ha₂, f₂, hf₂, hc₂, hl₂, hp₂⟩ := hl.2.2.2.2.2
    have hkl := min_le_left (k : ℝ) (l : ℝ)
    have hlk := min_le_right (k : ℝ) (l : ℝ)
    have hs1 := hs.1
    push_cast at hs1
    have hsk : s ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hsl : s ∈ Icc (-(2 * ((l + 2 : ℕ) : ℝ))) 0 := ⟨by push_cast; linarith, hs.2⟩
    have hv₁ := mem_Icc_of_mem_window (hR n) ha₁ hsk
    have hv₂ := mem_Icc_of_mem_window (hR n) ha₂ hsl
    let v : Icc (0 : ℝ) (H n).horizon :=
      ⟨(t n : ℝ) + s / R n, a₁.2.1.trans hv₁.1, hv₁.2.trans (t n).2.2⟩
    have hja₁ : (H n).activeStage a₁ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₁ ≤ v from hv₁.1)
    have hja₂ : (H n).activeStage a₂ ≤ (H n).activeStage v :=
      (H n).activeStage_mono (show a₂ ≤ v from hv₂.1)
    have hjt : (H n).activeStage v ≤ (H n).activeStage (t n) :=
      (H n).activeStage_mono (show v ≤ t n from hv₁.2)
    have hdom := (H n).activeStage_mem v
    rw [hp₁ s hsk ⟨_, hja₁, hjt⟩ hdom, hp₂ s hsl ⟨_, hja₂, hjt⟩ hdom,
      scaleMetric_restrictOpenOfSubset, scaleMetric_restrictOpenOfSubset]
    congr 1
    exact localPullMetric_restrictOpenOfSubset_eq_of_comp_eq _ _ _ _ _ _ _
      (comp_inclusion_eq_of_backward_maps (H n) hat₁ hat₂ f₁ hc₁ hl₁ f₂ hc₂ hl₂ _ hja₁ hja₂
        hjt)
  have hvolX : ∀ r R' : ℝ, 0 < r → r < R' → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R' ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
        ENNReal.ofReal (κ' * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a) := by
    intro r R' hr hrR' C hC
    obtain ⟨K', hK'0, hK'ev⟩ := htraced (r + 1) 1 (by linarith) one_pos
    obtain ⟨a, ha0, ha1, hra, haC, haK⟩ := exists_small_volume_radius hrR' hC hK'0
    refine ⟨a, κ, ha0, hκ, hra, haC, ?_⟩
    filter_upwards [hK'ev, hRlim.eventually_ge_atTop ((a / ρ) ^ 2)] with n htr hRn x hx
    have haρ : a / Real.sqrt (R n) ≤ ρ := by
      have hsq : a / ρ ≤ Real.sqrt (R n) := Real.le_sqrt_of_sq_le hRn
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (hR n))]
      rw [div_le_iff₀ hρ] at hsq
      linarith
    exact scaled_volume_ball_ge_of_isTracedRegion (H n) (t n) (y n) (hR n) hr.le ha0 ha1 hK'0
      haK hκ.le haρ htr (hvol n) x hx
  refine ⟨W, h, fun k => ?_, exists_ancient_pointed_flow_limit_of_local_solutions X hcompact
    hvolX W h hball hsol hzero hjets hcompat⟩
  filter_upwards [hsurv k] with n hn
  refine ⟨hWset k n hn, fun s hs hdom => hn.2.2.2.2.1 s ⟨?_, hs.2⟩ hdom⟩
  have := hs.1
  push_cast at this ⊢
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
