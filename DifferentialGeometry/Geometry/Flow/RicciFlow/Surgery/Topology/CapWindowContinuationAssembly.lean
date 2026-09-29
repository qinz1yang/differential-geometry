import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowFlowPushforward
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosenessWindowedWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowDerivativeTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance capWindowSigmaCompact (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace OrientedThreeStage.IncomingSlab

theorem exists_canonicalWitness_of_orientedWitness {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ C δ₀ : ℝ, 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
    ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) {δ κ : ℝ}
      (o : TangentOrientationSection P.Carrier) {y : P.Carrier} {t : ℝ}, δ ≤ δ₀ →
      Ioo (t - (δ * G.flow.scalar t y)⁻¹) t ⊆ Ioo a s → OrientedWitness G.flow o δ κ y t →
      ∀ C1 C2 : ℝ, C ≤ C1 → C ≤ C2 →
        ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε := by
  obtain ⟨C, δ₀, hC, hδ₀, hδ₁, hpipe⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{u} hε hε' 1
  refine ⟨C, δ₀, hC, hδ₀, hδ₁, ?_⟩
  intro P a s G δ κ o y t hδ hwin hw C1 C2 h1 h2
  obtain ⟨B, hB⟩ := hpipe κ P.Carrier (RealTimeInterval.closedOpen a s G.lt) G.flow G.equation δ
    o y t hδ hwin hw
  exact ⟨(B.canonicalWitnessMono B.tolerance_lt.le hε').enlargeConstants h1 h2,
    (hB.mono_eps B.tolerance_lt.le hε').enlarge_constants h1 h2⟩

theorem exists_scalar_derivative_bounds_of_scaled_localPull_witness :
    ∃ C : ℝ, 0 < C ∧
    ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (Gk : P.IncomingSlab a s)
      {N : Type} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
      [T2Space N] [SigmaCompactSpace N] {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := N) D), IsSolutionOn S →
      ∀ {Φ : N → P.Carrier} (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ) {q t T : ℝ}
        (hq : 0 < q), a < t → t < s →
      S.base.metric T = localPullMetric (scaleMetric q hq (Gk.flow.base.metric t)) Φ hΦ →
      ∀ {δ κ : ℝ} {z : N}, WindowedModelWitness δ κ S z T → δ ≤ 1 / 4 →
      Ioo (T - (δ * S.scalar T z)⁻¹) T ⊆ D.regular →
      ∀ Ctime Cgrad : ℝ≥0, C ≤ Ctime → C ≤ Cgrad →
        |derivWithin (fun v => Gk.flow.scalar v (Φ z)) (Iic t) t| ≤
            Ctime * Gk.flow.scalar t (Φ z) ^ 2 ∧
        ∀ v : TangentSpace I3 (Φ z),
          |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t (Φ z) v| ≤
            Cgrad * Gk.flow.scalar t (Φ z) * Real.sqrt (Gk.flow.scalar t (Φ z)) *
              Real.sqrt ((Gk.flow.base.metric t).inner (Φ z) v v) := by
  obtain ⟨Bf, hBf, hmodel⟩ := exists_universal_normalized_ancient_curvature_bounds.{0}
  set K := Real.sqrt (Bf 2)
  set B : ℝ := windowedShiConstant K 0 ^ 2 + windowedShiConstant K 1 ^ 2 +
    windowedShiConstant K 2 ^ 2 with hBdef
  have hB : 0 ≤ B := by positivity
  set n : ℝ := (Module.finrank ℝ ThreeSpace : ℝ)
  refine ⟨(n ^ 6 * Real.sqrt B + 2 * n ^ 4 * B) / 1 ^ 2 +
    n ^ 2 * Real.sqrt B / (1 * Real.sqrt 1) + 1, by positivity, ?_⟩
  intro P a s Gk N _ _ _ _ _ D S hS Φ hΦ q t T hq hat hts hST δ κ z W hδ hreg Ctime Cgrad hCt hCg
  have hbound : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2 := by
    intro s hs y hy
    rw [Real.sq_sqrt (hBf 2).le]
    exact hmodel κ W.model W.model_ancient W.model_scalar_base 2 y hy s hs.2
  have hscal : S.scalar T z = q⁻¹ * Gk.flow.scalar t (Φ z) := by
    change metricScalarAt (S.base.metric T) z = _
    rw [hST, metricScalarAt_localPullMetric_scaleMetric]
    rfl
  have hRS : 0 < S.scalar T z := W.scalar_pos
  set R := Gk.flow.scalar t (Φ z) with hRdef
  have hRq : R = q * S.scalar T z := by
    rw [hscal, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have hR : 0 < R := by rw [hRq]; positivity
  have hjets : ∀ j ≤ 2, curvDerivNormSq j (Gk.flow.base.metric t) (Φ z) ≤ R ^ (j + 2) * B := by
    intro j hj
    have hS' := W.terminal_curvature_derivative_bound hS hδ (Real.sqrt_nonneg _) hreg hbound j
    rw [← curvNormSq_eq S j T z] at hS'
    have h := curvDerivNormSq_localPullMetric_scaleMetric (Gk.flow.base.metric t) Φ hΦ hq j z
    rw [← hST] at h
    have h' : curvDerivNormSq j (Gk.flow.base.metric t) (Φ z) =
        q ^ (j + 2) * curvDerivNormSq j (S.base.metric T) z := by
      rw [h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq.ne', one_pow, one_mul]
    have hKj : windowedShiConstant K j ^ 2 ≤ B := by
      interval_cases j <;> simp only [hBdef] <;> nlinarith [sq_nonneg (windowedShiConstant K 0),
        sq_nonneg (windowedShiConstant K 1), sq_nonneg (windowedShiConstant K 2)]
    rw [h', hRq, mul_pow, mul_assoc, show j + 2 = 2 + j by ring]
    refine mul_le_mul_of_nonneg_left (hS'.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hKj (by positivity)
  have htreg : t ∈ (RealTimeInterval.closedOpen a s Gk.lt).regular := ⟨hat, hts⟩
  obtain ⟨hd, hg⟩ := abs_scalar_derivatives_le_of_scaled_curvature_jets Gk.flow Gk.equation htreg
    hR hB one_pos (Φ z) hjets (by rw [one_mul])
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right hCt (sq_nonneg _)), fun v => (hg v).trans ?_⟩
  gcongr

theorem exists_scalar_derivative_bounds_of_window_orientedWitness :
    ∃ C : ℝ, 0 < C ∧
    ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (Gk : P.IncomingSlab a s) {D T' : ℝ} {hT' : 0 ≤ T'}
      (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T' hT')), IsSolutionOn S →
      ∀ {Φ : standardCapWindow D → P.Carrier} (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ)
        {q t T : ℝ} (hq : 0 < q), a < t → t < s → T ≤ T' →
      S.base.metric T = localPullMetric (scaleMetric q hq (Gk.flow.base.metric t)) Φ hΦ →
      ∀ {δ κ : ℝ} {z : standardCapWindow D}, (∀ o, OrientedWitness S o δ κ z T) → δ ≤ 1 / 4 →
      ∀ Ctime Cgrad : ℝ≥0, C ≤ Ctime → C ≤ Cgrad →
        |derivWithin (fun v => Gk.flow.scalar v (Φ z)) (Iic t) t| ≤
            Ctime * Gk.flow.scalar t (Φ z) ^ 2 ∧
        ∀ v : TangentSpace I3 (Φ z),
          |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t (Φ z) v| ≤
            Cgrad * Gk.flow.scalar t (Φ z) * Real.sqrt (Gk.flow.scalar t (Φ z)) *
              Real.sqrt ((Gk.flow.base.metric t).inner (Φ z) v v) := by
  obtain ⟨C, hC, hA⟩ := exists_scalar_derivative_bounds_of_scaled_localPull_witness.{u}
  refine ⟨C, hC, ?_⟩
  intro P a s Gk D T' hT' S hS Φ hΦ q t T hq hat hts hTT' hST δ κ z hw hδ Ctime Cgrad hCt hCg
  obtain ⟨W, -⟩ := hw (P.orientation.pullback hΦ)
  have hreg : Ioo (T - (δ * S.scalar T z)⁻¹) T ⊆ (RealTimeInterval.closed 0 T' hT').regular := by
    intro σ hσ
    have hlo := (W.window_mem ⟨le_rfl, (sub_le_self_iff _).mpr (inv_nonneg.mpr
      (mul_pos W.eps_pos W.scalar_pos).le)⟩).1
    exact ⟨lt_of_le_of_lt hlo hσ.1, hσ.2.trans_le hTT'⟩
  exact hA Gk S hS hΦ hq hat hts hST W hδ hreg Ctime Cgrad hCt hCg

end OrientedThreeStage.IncomingSlab

theorem le_mul_of_half_standard_scalar_lower {τQ c₀ T RS RQ : ℝ} (hτQ : 0 ≤ τQ) (hc₀ : 0 < c₀)
    (hT1 : T < 1) (hQ : c₀ / (1 - T) ≤ RQ) (hS : 1 / 2 * RQ ≤ RS)
    (hT : 2 * τQ / (c₀ + 2 * τQ) ≤ T) : τQ ≤ T * RS := by
  have hden : 0 < c₀ + 2 * τQ := by linarith
  have h1T : 0 < 1 - T := by linarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hTc : 2 * τQ ≤ T * (c₀ + 2 * τQ) := by rwa [div_le_iff₀ hden] at hT
  have hQ' : c₀ ≤ RQ * (1 - T) := by rwa [div_le_iff₀ h1T] at hQ
  nlinarith [mul_le_mul_of_nonneg_left hS hT0, mul_le_mul_of_nonneg_left hQ' hT0]

namespace RetainedCoreHistory

theorem IsCanonicalCutoffRecordFamily.birth_scale_bounds
    {H : RetainedCoreHistory.{u}} {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records)
    (hΛδ : p₀.recenterConstant * δ₀ ≤ 1 / 2) (i : Fin H.eventCount)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) {qcan Cbirth a₀ ρmax : ℝ}
    (hqcan : 0 < qcan) (hCbirth : 0 < Cbirth) (ha₀ : 0 < a₀) (hρ : ρ₀ ≤ ρmax)
    (hρ₁ : ρmax ^ 2 ≤ Cbirth / (4 * qcan)) (hρ₂ : ρmax ^ 2 ≤ a₀ / 2) :
    2 * qcan ≤ Cbirth * ((records i).static b).neck.scale ∧
      1 ≤ a₀ * ((records i).static b).neck.scale := by
  have hq := hrec.inv_two_mul_sq_lt_static_scale hΛδ i b
  have hρpos : 0 < ρ₀ := (p.neckRadius_pos _ (H.toHistory.time_nonneg i.succ)).trans_le
    (hrec.2.2.2.2.2.2.2 i)
  have hsq : ρ₀ ^ 2 ≤ ρmax ^ 2 := pow_le_pow_left₀ hρpos.le hρ 2
  set q := ((records i).static b).neck.scale
  have h2 : 0 < 2 * ρ₀ ^ 2 := by positivity
  have hq' : 1 < q * (2 * ρ₀ ^ 2) := by rwa [inv_lt_iff_one_lt_mul₀ h2] at hq
  have hqpos : 0 < q := ((records i).static b).neck.scale_pos
  constructor
  · have h4 : ρ₀ ^ 2 * (4 * qcan) ≤ Cbirth := by
      have := hsq.trans hρ₁
      rwa [le_div_iff₀ (by positivity)] at this
    nlinarith
  · have h4 : 2 * ρ₀ ^ 2 ≤ a₀ := by linarith [hsq.trans hρ₂]
    nlinarith

end RetainedCoreHistory

namespace RetainedCoreHistory

section WindowFlow

variable (H : RetainedCoreHistory.{u})
  {k : Fin (H.eventCount + 1)} {s : ℝ} (Gk : (H.stage k).IncomingSlab (H.time k) s)
  {j : Fin H.eventCount} (hl : j.succ ≤ k) {t' : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) t'} {L : G.TerminalLimitMetric}
  {D : ℝ} {Ξ : standardCapWindow D → H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G}
  (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
  {gflow : ℝ → SmoothRiemannianMetric ThreeModel
    (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G)}
  {q : ℝ} (hq : 0 < q) {hT : 0 ≤ q * (t' - H.time j.succ)}
  {S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
    (RealTimeInterval.closed 0 (q * (t' - H.time j.succ)) hT)}

include hΞ in
theorem capWindow_flow_metric_eq
    (hG : ∀ v, G.flow.base.metric v = Gk.flow.base.metric v)
    (hL : L.metric = (Gk.flow.base.metric t').restrictOpen G.terminalRegularOpen)
    (hgflow : ∀ τ ∈ Icc (H.time k) t',
      gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ)
    (hS : ∀ τ, S.base.metric τ =
      localPullMetric (scaleMetric q hq (gflow (H.time j.succ + τ / q))) Ξ hΞ) :
    ∀ τ ∈ Icc 0 (q * (t' - H.time j.succ)), H.time k ≤ H.time j.succ + τ / q →
      S.base.metric τ = localPullMetric (scaleMetric q hq
        (Gk.flow.base.metric (H.time j.succ + τ / q))) (fun w => (Ξ w).val.val)
        (H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G
          hΞ) := by
  intro τ hτ hkτ
  refine H.toHistory.window_metric_eq_localPullMetric_scaleMetric j.succ k hl G L
    Gk.flow.base.metric hG hL hΞ gflow hgflow S hq hS ⟨hkτ, ?_⟩
  have h1 : τ / q ≤ t' - H.time j.succ := by
    rw [div_le_iff₀ hq]
    linarith [hτ.2]
  linarith

include hΞ in
theorem orientedWitness_of_capWindow_flow {t : ℝ} (hkt : H.time k < t) (htt' : t ≤ t')
    (hts : t < s) (hG : ∀ v, G.flow.base.metric v = Gk.flow.base.metric v)
    (hL : L.metric = (Gk.flow.base.metric t').restrictOpen G.terminalRegularOpen)
    (hgflow : ∀ τ ∈ Icc (H.time k) t',
      gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ)
    (hS : ∀ τ, S.base.metric τ =
      localPullMetric (scaleMetric q hq (gflow (H.time j.succ + τ / q))) Ξ hΞ)
    (hΞs : Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ) {y : (H.stage k).Carrier}
    {z : standardCapWindow D} (hyz : (Ξ z).val.val = y) {δ κ : ℝ}
    (hw : ∀ o, OrientedWitness S o δ κ z (q * (t - H.time j.succ)))
    (hage : (δ * Gk.flow.scalar t y)⁻¹ ≤ t - H.time k) :
    OrientedWitness Gk.flow (H.stage k).orientation δ κ y t := by
  have : Nonempty (standardCapWindow D) := ⟨z⟩
  have hinj := H.toHistory.injective_backwardSurvivorIncomingDomain_val_val j.succ k hl G
    hΞs.isEmbedding.injective
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  have hTT : q * (t - H.time j.succ) ≤ q * (t' - H.time j.succ) :=
    mul_le_mul_of_nonneg_left (by linarith) hq.le
  have h := Gk.orientedWitness_of_scaled_localPull_window S
    (H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ)
    hinj hq hba hkt hts hTT (H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hgflow hS) (hw _)
    (by rwa [hyz])
  rwa [hyz] at h

end WindowFlow

end RetainedCoreHistory

namespace RetainedCoreHistory

theorem eventSlabsDerivative_two_mul {H : RetainedCoreHistory.{u}}
    {k : Fin (H.eventCount + 1)} {Ctime : ℝ≥0} {qcan : ℝ} (hq : 0 < qcan)
    (h : H.EventSlabsDerivative Ctime qcan k) :
    H.EventSlabsDerivative (2 * Ctime) (2 * qcan) k := by
  intro i hi y τ hτ hR
  have h1 := h i hi y τ hτ (by linarith)
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  push_cast
  linarith [Ctime.coe_nonneg]

theorem exists_capWindowPoint_bounds_of_room (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (C₀ τ₀ : ℝ) (Ctime₀ : ℝ≥0), 1 ≤ C₀ ∧ 0 < τ₀ ∧
    ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), C₀ ≤ C1 → C₀ ≤ C2 → τ₀ ≤ τmin →
      Ctime₀ ≤ Ctime → Ctime₀ ≤ Cgrad →
    ∀ (Dcap θcap : ℝ), 0 < Dcap → θcap < 1 →
    ∃ (Rcap μ : ℝ) (mcap : ℕ), Dcap + 1 < Rcap ∧ 0 < μ ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
    ∀ t : ℝ, H.time k < t → t + 2 * ρmax ^ 2 * μ < s →
      Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t + 2 * ρmax ^ 2 * μ) →
    ∀ y : (H.stage k).Carrier, H.CapWindowPoint records k y t Dcap θcap →
      qcan < Gk.flow.scalar t y →
      (τmin ≤ Gk.flow.scalar t y * (t - H.time k) →
        ∃ W : CanonicalWitness Gk.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤ Ctime * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  obtain ⟨Cε, δ0, hCε, hδ0, hδ01, hpipe⟩ :=
    OrientedThreeStage.IncomingSlab.exists_canonicalWitness_of_orientedWitness.{u} hε hε'
  set δ := min δ0 (1 / 4) with hδdef
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδ1 : δ < 1 := hδ4.trans_lt (by norm_num)
  obtain ⟨τQ, hτQ, hL6⟩ := exists_uniform_orientedWitness_of_standard_close hδ hδ1
  obtain ⟨CA, hCA, hA⟩ :=
    OrientedThreeStage.IncomingSlab.exists_scalar_derivative_bounds_of_window_orientedWitness.{u}
  obtain ⟨c₀, hc₀, hQlow⟩ := exists_standard_scalar_lower_bound
  set Θ₃ := 2 * τQ / (c₀ + 2 * τQ) with hΘ₃def
  have hΘ₃ : 0 < Θ₃ := by positivity
  have hΘ₃1 : Θ₃ < 1 := by rw [hΘ₃def, div_lt_one (by positivity)]; linarith
  obtain ⟨cB, CB, -, hCB, hyoung⟩ :=
    exists_uniform_derivative_gradient_bounds_of_cap_window_trace.{u} Θ₃ hΘ₃ hΘ₃1
  refine ⟨Cε, max τQ δ⁻¹ + 1, ⟨max CA CB, le_max_of_le_left hCA.le⟩, hCε, by positivity, ?_⟩
  intro C1 C2 τmin Ctime Cgrad hC1 hC2 hτmin hCt hCg Dcap θcap hDcap hθcap
  have hCt' : max CA CB ≤ (Ctime : ℝ) := hCt
  have hCg' : max CA CB ≤ (Cgrad : ℝ) := hCg
  set Θ := max θcap (1 / 2) with hΘdef
  have hΘ1 : Θ < 1 := max_lt hθcap (by norm_num)
  have hΘ0 : 1 / 2 ≤ Θ := le_max_right _ _
  set μ := (1 - Θ) / 2 with hμdef
  have hμ : 0 < μ := by rw [hμdef]; linarith
  have hΘ'1 : Θ + μ < 1 := by rw [hμdef]; linarith
  have hΘ'0 : 0 < Θ + μ := by linarith
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison (Θ + μ) hΘ'0.le hΘ'1
  obtain ⟨DW, NW, eW, hDW, heW, hwit⟩ := hL6 (Θ + μ) (Dcap + 1) μ hΘ'1 hμ
  obtain ⟨Pb, Creset, Cb1, -, -, hCb1, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} (Θ + μ) (2 * Ctime) hΘ'0 hΘ'1
  obtain ⟨R1, hR1, m1, -, ζ1, δ1, hζ1, -, hδ1', hbr⟩ :=
    hbridge DW eW eta (by linarith) heW heta NW
  obtain ⟨Cb2, hCb2, hy2⟩ := hyoung (2 * Ctime)
  obtain ⟨R2, hR2, m2, -, ζ2, δ2, hζ2, -, hδ2, hyc⟩ := hy2 Dcap hDcap
  refine ⟨max R1 R2, μ, max m1 m2, hR2.trans_le (le_max_right _ _), hμ, ?_⟩
  intro qcan hqcan
  set Cb := min Cb1 Cb2 with hCbdef
  have hCb : 0 < Cb := lt_min hCb1 hCb2
  set ρmax := min (Real.sqrt (Cb / (4 * qcan))) (Real.sqrt (a₀ / 2)) with hρdef
  have hρmax : 0 < ρmax := lt_min (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
  have hρ₁ : ρmax ^ 2 ≤ Cb / (4 * qcan) := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_left _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hρ₂ : ρmax ^ 2 ≤ a₀ / 2 := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_right _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  refine ⟨min δ1 δ2, ρmax, min ζ1 ζ2, lt_min hδ1' hδ2, hρmax, lt_min hζ1 hζ2, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hderiv t hkt
    hroom hcur y hcap hR
  obtain ⟨j, hl, A, b, x, hanchor, hxD, hage⟩ := hcap
  obtain ⟨hHI1, hHI2⟩ := hHI H.toHistory hId.some
  set q := ((records j).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j).static b).neck.scale_pos
  obtain ⟨hbirth, haq⟩ := hrec.birth_scale_bounds hΛδ j b hqcan hCb ha₀ hρb hρ₁ hρ₂
  have hρbpos : 0 < ρbound := (p.neckRadius_pos _ (H.toHistory.time_nonneg j.succ)).trans_le
    (hrec.2.2.2.2.2.2.2 j)
  have hinvq : q⁻¹ < 2 * ρmax ^ 2 := by
    have h := hrec.inv_two_mul_sq_lt_static_scale hΛδ j b
    have h2 : q⁻¹ < 2 * ρbound ^ 2 := by
      rw [inv_lt_comm₀ hq (by positivity)]
      exact h
    have h3 : ρbound ^ 2 ≤ ρmax ^ 2 := pow_le_pow_left₀ hρbpos.le hρb 2
    linarith
  set t' := t + μ / q with ht'def
  have hμq : μ / q < 2 * ρmax ^ 2 * μ := by
    rw [div_eq_mul_inv, mul_comm μ]
    exact mul_lt_mul_of_pos_right hinvq hμ
  have ht't : t ≤ t' := by rw [ht'def]; have := div_pos hμ hq; linarith
  have ht's : t' < s := by rw [ht'def]; linarith
  have hts : t < s := ht't.trans_lt ht's
  have hkt' : H.time k < t' := hkt.trans_le ht't
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  have hderiv2 := eventSlabsDerivative_two_mul hqcan hderiv
  have hcur' : Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) t' :=
    fun y' τ hτ hR' => hcur y' τ ⟨hτ.1, hτ.2.trans (by linarith)⟩ hR'
  have hcurt : Gk.DerivativeBoundBefore (2 * Ctime) (2 * qcan) t :=
    fun y' τ hτ hR' => hcur' y' τ ⟨hτ.1, hτ.2.trans_le ht't⟩ hR'
  have hθΘ : θcap ≤ Θ := le_max_left _ _
  have hage' : t' - H.time j.succ ≤ (Θ + μ) * q⁻¹ := by
    have h1 : θcap * q⁻¹ ≤ Θ * q⁻¹ := mul_le_mul_of_nonneg_right hθΘ (inv_nonneg.mpr hq.le)
    rw [ht'def, add_mul, div_eq_mul_inv]
    linarith
  have hxD' : ‖x.val‖ < DW + 1 := by linarith
  have hbirth1 : 2 * qcan ≤ Cb1 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hbirth2 : 2 * qcan ≤ Cb2 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  obtain ⟨G, L, hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, hS3, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H p₀ δbound ρbound records hrec (hδb.trans (min_le_left _ _))
      ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hord) (hacc.trans (min_le_left _ _))
      (2 * qcan) a₀ (Θ + μ) (by positivity) le_rfl hHI1 hHI2 k s Gk hGk hderiv2 t' hkt' ht's hcur'
      j hl y A b x hanchor hage' hxD' hbirth1 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  set T := q * (t - H.time j.succ) with hTdef
  have hjt : H.time j.succ < t := hba.trans_lt hkt
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θcap := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θcap, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTT' : T + μ = q * (t' - H.time j.succ) := by
    rw [hTdef, ht'def]
    field_simp
    ring
  have hTmem : T ∈ Icc 0 (q * (t' - H.time j.succ)) := ⟨hT0, by linarith⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem (by rw [htT]; linarith)
  rw [htT] at hST
  have hRS : S.scalar T z = q⁻¹ * Gk.flow.scalar t y := by
    change metricScalarAt (S.base.metric T) z = _
    rw [hST, metricScalarAt_localPullMetric_scaleMetric, hyz]
    rfl
  have hRpos : 0 < Gk.flow.scalar t y := hqcan.trans hR
  have hTRS : T * S.scalar T z = Gk.flow.scalar t y * (t - H.time j.succ) := by
    rw [hRS, hTdef]
    field_simp
  have hwit' : τQ ≤ T * S.scalar T z →
      ∀ o, OrientedWitness S o δ standardModelKappa z T := by
    intro hτ o
    exact hwit Q T (q * (t' - H.time j.succ)) _ hT0 hTT'.le (by linarith) S hS3
      (fun τ hτ' => (hclose τ hτ').1) o z (by rw [hzx]; linarith) hτ
  have hΦ := H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ
  have hderivClause : |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤
        Ctime * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
    by_cases hyng : t - H.time j.succ ≤ Θ₃ * q⁻¹
    · obtain ⟨-, hd, hg⟩ := hyc H p₀ δbound ρbound records hrec (hδb.trans (min_le_right _ _))
        ((le_max_right _ _).trans hrad) ((le_max_right _ _).trans hord)
        (hacc.trans (min_le_right _ _)) (2 * qcan) a₀ Θ₃ (by positivity) le_rfl hHI1 hHI2 k s Gk
        hGk hderiv2 t hkt hts hcurt j hl y A b x hanchor hyng hxD hbirth2 haq
      have hCBt : CB ≤ (Ctime : ℝ) := (le_max_right _ _).trans hCt'
      have hCBg : CB ≤ (Cgrad : ℝ) := (le_max_right _ _).trans hCg'
      refine ⟨hd.trans (mul_le_mul_of_nonneg_right hCBt (sq_nonneg _)), fun v => (hg v).trans ?_⟩
      gcongr
    · have hTΘ₃ : Θ₃ ≤ T := by
        have h1 := mul_le_mul_of_nonneg_left (not_le.mp hyng).le hq.le
        rwa [mul_comm Θ₃, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
      have hT1 : T < 1 := by linarith only [hTθ, hθcap]
      have hlow := (hlower Q (standardCapWindow DW) (S.base.metric T) T
        ⟨hT0, by linarith only [hTθ, hθΘ, hμ]⟩ z (fun i hi => ((hclose T hTmem).2 i hi z).le)).2
      rw [metricScalarAt_restrictOpen] at hlow
      have hτ := le_mul_of_half_standard_scalar_lower hτQ.le hc₀ hT1
        (hQlow Q z.val T ⟨hT0, hT1⟩) hlow hTΘ₃
      have h := hA Gk S hS3 hΦ hq hkt hts (by linarith only [hTT', hμ]) hST (hwit' hτ) hδ4
        Ctime Cgrad ((le_max_left _ _).trans hCt') ((le_max_left _ _).trans hCg')
      subst hyz
      exact h
  refine ⟨fun hageC => ?_, hderivClause⟩
  have hτmin' : max τQ δ⁻¹ + 1 ≤ τmin := hτmin
  have hmono : Gk.flow.scalar t y * (t - H.time k) ≤
      Gk.flow.scalar t y * (t - H.time j.succ) :=
    mul_le_mul_of_nonneg_left (by linarith) hRpos.le
  have hτ : τQ ≤ T * S.scalar T z := by
    rw [hTRS]
    linarith only [hmono, hageC, hτmin', le_max_left τQ δ⁻¹]
  have hage2 : (δ * Gk.flow.scalar t y)⁻¹ ≤ t - H.time k := by
    have h1 : δ⁻¹ ≤ Gk.flow.scalar t y * (t - H.time k) := by
      linarith only [hageC, hτmin', le_max_right τQ δ⁻¹]
    rw [inv_le_iff_one_le_mul₀ (mul_pos hδ hRpos)]
    have h2 := mul_le_mul_of_nonneg_left h1 hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at h2
    have h3 : (t - H.time k) * (δ * Gk.flow.scalar t y) =
        δ * (Gk.flow.scalar t y * (t - H.time k)) := by ring
    rw [h3]
    exact h2
  have hOW := H.orientedWitness_of_capWindow_flow Gk hl hΞ hq hkt ht't hts hG hL hS2 hS5 hΞs hyz
    (hwit' hτ) hage2
  refine hpipe Gk (H.stage k).orientation (min_le_left _ _) ?_ hOW C1 C2 hC1 hC2
  intro σ hσ
  exact ⟨by linarith [hσ.1], hσ.2.trans hts⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
