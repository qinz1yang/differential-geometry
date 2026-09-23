import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTraceConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckShi

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

theorem NormalizedNeck.exists_backwardPointTrace_of_mem_chart_image
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (hk : 2 ≤ k) (hsmall : δ ≤ 1 / 8646) (F : Set (neckBuffer δ))
    (hF : F ⊆ neckClosedTest δ)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    (htime : 6 * C * (H.time i.succ - H.time first) * N.scale ≤ 1)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          2 * N.scale ≤ metricScalarAt (H.event j).outputMetric y)
    (x : (H.event i).incoming.terminalRegularOpen) (hx : x ∈ N.chart '' F) :
    ∃ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * N.scale := by
  have hs : metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * N.scale := by
    obtain ⟨z, hz, rfl⟩ := hx
    have hratio := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk
      (hsmall.trans (by norm_num)) z (hF hz))).2
    apply (div_le_iff₀ N.scale_pos).mp
    linarith
  exact H.exists_backwardPointTrace_to_terminal_of_scalar_le_three_halves i first hle x
    hq hqQ hs htime hderiv hOld hcap

theorem NormalizedNeck.chart_image_subset_backwardSurvivorTerminalFaceMap_range
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (hk : 2 ≤ k) (hsmall : δ ≤ 1 / 8646) (F : Set (neckBuffer δ))
    (hF : F ⊆ neckClosedTest δ)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    (htime : 6 * C * (H.time i.succ - H.time first) * N.scale ≤ 1)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          2 * N.scale ≤ metricScalarAt (H.event j).outputMetric y) :
    N.chart '' F ⊆ range (H.backwardSurvivorTerminalFaceMap first i hle) := by
  intro x hx
  obtain ⟨A, _⟩ := N.exists_backwardPointTrace_of_mem_chart_image hk hsmall F hF
    first hle hq hqQ htime hderiv hOld hcap x hx
  exact (H.mem_range_backwardSurvivorTerminalFaceMap_iff first i hle x).mpr ⟨A⟩

theorem NormalizedNeck.exists_backwardPointTrace_of_mem_footprint
    {δ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ k)
    (hprecision : δ ≤ eps) (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (hfit : 3 * a ≤ eps⁻¹)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    (htime : 6 * C * (H.time i.succ - H.time first) * N.scale ≤ 1)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          2 * N.scale ≤ metricScalarAt (H.event j).outputMetric y)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x ∈ N.chart '' {z : neckBuffer δ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}) :
    ∃ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * N.scale := by
  have heps : 0 < eps := N.delta_pos.trans_le hprecision
  have hk2 : 2 ≤ k := by
    have hi : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    have hh : (2 : ℝ) ≤ ⌈eps⁻¹⌉₊ := hi.trans (Nat.le_ceil _)
    exact (by exact_mod_cast hh : 2 ≤ ⌈eps⁻¹⌉₊).trans hk
  apply N.exists_backwardPointTrace_of_mem_chart_image hk2 (hprecision.trans hsmall)
    {z : neckBuffer δ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} _
    first hle hq hqQ htime hderiv hOld hcap x hx
  intro z hz
  have hi := inv_anti₀ N.delta_pos hprecision
  constructor <;> linarith [hz.1, hz.2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

theorem NormalizedNeck.exists_historical_curvature_derivative_bounds_of_cap_scalar_lower_bound
    {δ₀ δ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (hδ : δ₀ ≤ δ) (hδ1 : δ < 1) (hprecision : δ₀ ≤ eps)
    (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (ha : 24 < a) (hpublic : δ⁻¹ + 1 ≤ a) (hfit : 4 * a < eps⁻¹)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          2 * N.scale ≤ metricScalarAt (H.event j).outputMetric y)
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c < H.time i.succ)
    (htime : 6 * C * (H.time i.succ - H.time first) * N.scale ≤ 1) :
    let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
    let B := 4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)
    ∃ (p : H.backwardSurvivorFootprintInterior first i hle K)
      (G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K)),
      H.backwardSurvivorFootprintMap first i hle K p = N.center ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      G (H.time i.succ) = localPullMetric (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K)
        (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
          (RealTimeInterval.closed c (H.time i.succ) hcs.le)) ∧
      (∀ t ∈ Icc c (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤ B ^ 2) ∧
      IsCompact (riemannianClosedBallOf (G (H.time i.succ)) p
        (2*a / Real.sqrt N.scale)) ∧
      ∀ m : ℕ, ∀ t ∈ Icc ((c + H.time i.succ) / 2) (H.time i.succ),
        ∀ x ∈ riemannianClosedBallOf (G (H.time i.succ)) p
            ((2*a / Real.sqrt N.scale) / 4),
          curvDerivNorm m (G t) x ≤
            shiLocalUniformBound 3 m (B * ((H.time i.succ - c) / 4))
              (((2*a / Real.sqrt N.scale) /
                (4 * Real.exp (9 * B * (H.time i.succ - c)))) * Real.sqrt B /
                  (4 * Real.exp (9 * B * ((H.time i.succ - c) / 4)))) *
              B / Real.sqrt ((H.time i.succ - c) / 4) ^ m := by
  have htrace : ∀ x ∈ N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
      Nonempty (BackwardPointTrace H first i.castSucc hle x.val) := by
    intro x hx
    obtain ⟨A, _⟩ := N.exists_backwardPointTrace_of_mem_footprint hprecision hsmall hk
      a (by linarith) first hle hq hqQ htime hbound hOld hcap x hx
    exact ⟨A⟩
  have htime' : 6 * C * (H.time i.succ - c) * N.scale ≤ 1 := by
    apply le_trans _ htime
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hc _) (by positivity)) N.scale_pos.le
  exact N.exists_historical_footprint_curvature_derivative_bounds hδ hδ1 hprecision hsmall hk
    a ha hpublic hfit hq hqQ hPhi hbound hpinch htrace hc hcs htime'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
