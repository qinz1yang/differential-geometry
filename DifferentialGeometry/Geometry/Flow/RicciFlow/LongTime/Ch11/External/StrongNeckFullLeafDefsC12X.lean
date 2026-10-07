import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullCrossingC12X

/-!
# Strong spatial crossing continuation with full necks: statement and constants (C12X, S16 G2e)

* `εStrong_C12X` : the accuracy threshold `c` of `strongSpatialCrossingContinuation_holds`
  (`εbar = min ε₁ c` there, `c` independent of `ε₁`), with `crossingStrongEpsW_C12X` for the
  existential `epsW`.  Taking `ε₁ := ε` is legitimate as soon as `ε ≤ εStrong_C12X`.
* `StrongSpatialCrossingContinuationFull_C12X` : the tree statement
  `StrongSpatialCrossingContinuation` on the diagonal `ε₁ := ε` with `HistoryStrongNeckFull_C12X`.
* `strong_clause_full_of_extendAt_C12X` : untruncated private Leaf lemma.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem s16b_coneAccuracy_lt : coneAccuracy < 1 / 100 := by
  unfold coneAccuracy
  rw [div_lt_iff₀ (by norm_num)]
  exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

/-- Accuracy threshold for full strong necks (S16): `ε ≤ εStrong_C12X` lets the strong-neck
accuracy equal the witness accuracy (same family as `epsilon_cone`). -/
def εStrong_C12X : ℝ :=
  min coneAccuracy (min ObservedHistory.crossingStrongEpsW_C12X.{u}
    (min crossingNeckAccuracy.{u} crossingWindowNeckAccuracy.{u}))

theorem εStrong_C12X_pos : 0 < εStrong_C12X.{u} :=
  lt_min coneAccuracy_pos (lt_min ObservedHistory.crossingStrongEpsW_C12X_pos
    (lt_min crossingNeckAccuracy_pos crossingWindowNeckAccuracy_pos))

theorem εStrong_C12X_le_coneAccuracy : εStrong_C12X.{u} ≤ coneAccuracy :=
  min_le_left _ _

theorem εStrong_C12X_lt : εStrong_C12X.{u} < 1 / 100 :=
  εStrong_C12X_le_coneAccuracy.trans_lt s16b_coneAccuracy_lt

/-- `StrongSpatialCrossingContinuation` on the diagonal `ε₁ := ε`, with full history necks; the
accuracy constraint is the explicit binder `ε ≤ εStrong_C12X`. -/
def StrongSpatialCrossingContinuationFull_C12X (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ εStrong_C12X.{u} →
  ∃ Cx : ℝ, 1 ≤ Cx ∧
  ∀ B : ℝ, 0 < B →
  ∀ (C1 C2 τmin : ℝ) (Ctime Cgrad : ℝ≥0), 1 ≤ C1 → 1 ≤ C2 → 0 < τmin →
  ∀ (C1s C2s Cs : ℝ), 1 ≤ C1s → 1 ≤ C2s → 1 ≤ Cs →
  ∀ (κ : ℝ) (phi : ℝ → ℝ) (θ : ℝ), 0 < κ → Perelman.AdmissiblePinchingFunction phi → 0 < θ →
  ∃ (Dcap θcap q₀ : ℝ) (mcap : ℕ), 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
  ∀ qcan : ℝ, q₀ ≤ qcan →
  ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
  ∀ qs : ℝ, qcan ≤ qs → qs ≤ Cs * qcan →
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ j : Fin H.eventCount,
        H.EventSlabsCanonical ε C1 C2 qcan τmin j.castSucc →
        H.EventSlabsDerivative Ctime qcan j.castSucc →
        H.EventSlabsGradient Cgrad qcan j.castSucc →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs j.castSucc →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time j.castSucc) (H.time j.succ) →
          (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qcan τmin t₀ →
          (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t₀ →
          (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qcan t₀ →
          (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.NoncollapsedBefore κ ε t₀ →
          ∀ η₃ : ℝ, 0 < η₃ →
            (H.toHistory.event j).incoming.DerivativeBoundOn Ctime qcan t₀ η₃ →
            (H.toHistory.event j).incoming.GradientBoundOn Cgrad qcan t₀ η₃ →
            (H.toHistory.event j).incoming.CanonicalOn ε C1 C2 qcan τmin t₀ η₃ →
          ∃ η : ℝ, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ H.time j.succ ∧
            ∀ (y : (H.stage j.castSucc).Carrier) (t : ℝ),
            H.time j.castSucc < t → t₀ ≤ t → t < t₀ + η → t < H.time j.succ →
            qs < (H.toHistory.event j).incoming.flow.scalar t y →
            (H.toHistory.event j).incoming.flow.scalar t y * (t - H.time j.castSucc) < θ →
            ¬ H.CapWindowPoint records j.castSucc y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness
                ((H.toHistory.event j).incoming.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε ∧
                ((∃ n, W.alternative = .neck n) →
                  H.toHistory.HistoryStrongNeckFull_C12X j.castSucc
                    (H.toHistory.event j).incoming ε y t)) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
        H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
        H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
        H.EventSlabsSpatiallyCanonical ε C1s C2s qs (Fin.last H.eventCount) →
        H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
        ∀ t₀ : ℝ, t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s →
          G.CanonicalBefore ε C1 C2 qcan τmin t₀ → G.DerivativeBoundBefore Ctime qcan t₀ →
          G.GradientBoundBefore Cgrad qcan t₀ →
          G.SpatiallyCanonicalBefore ε C1s C2s qs t₀ →
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀ →
          ∀ η₃ : ℝ, 0 < η₃ → G.DerivativeBoundOn Ctime qcan t₀ η₃ →
            G.GradientBoundOn Cgrad qcan t₀ η₃ → G.CanonicalOn ε C1 C2 qcan τmin t₀ η₃ →
          ∃ η : ℝ, 0 < η ∧ η ≤ η₃ ∧ t₀ + η ≤ s ∧
            ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
            H.time (Fin.last H.eventCount) < t → t₀ ≤ t → t < t₀ + η → t < s →
            qs < G.flow.scalar t y →
            G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ →
            ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap →
            ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε Cx Cx y,
              W.capTubeHasNeckChart ε ∧
                ((∃ n, W.alternative = .neck n) →
                  H.toHistory.HistoryStrongNeckFull_C12X (Fin.last H.eventCount) G ε y t)

namespace RetainedCoreHistory

/-- Untruncated `strong_clause_of_extendAt` (Leaf, private there). -/
theorem strong_clause_full_of_extendAt_C12X (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (ŷ : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hŷ : HEq ŷ y) {ε C : ℝ}
    (Gs : ((H.extendAt hend G hG hat hts).toHistory.stage
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts))).IncomingSlab
      ((H.extendAt hend G hG hat hts).toHistory.time
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts))) s)
    (hGs : HEq Gs G)
    (W : SpatialCanonicalWitness ((H.extendAt hend G hG hat hts).toHistory.stageMetric
        ((H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts)) (H.extendAtTime hend G hG hat hts)) ε C C ŷ)
    (hW : W.capTubeHasNeckChart ε)
    (hneck : (∃ n, W.alternative = .neck n) →
      (H.extendAt hend G hG hat hts).toHistory.HistoryStrongNeckFull_C12X
        ((H.extendAt hend G hG hat hts).toHistory.activeStage (H.extendAtTime hend G hG hat hts))
        Gs ε ŷ (H.extendAtTime hend G hG hat hts)) :
    ∃ W' : SpatialCanonicalWitness (G.flow.base.metric t) ε C C y,
      W'.capTubeHasNeckChart ε ∧ ((∃ n, W'.alternative = .neck n) →
        H.toHistory.HistoryStrongNeckFull_C12X (Fin.last H.eventCount) G ε y t) := by
  have hlast : (H.extendAt hend G hG hat hts).toHistory.activeStage
      (H.extendAtTime hend G hG hat hts) = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      (H.extendAtTime hend G hG hat hts) hat.le
  have hmet : (H.extendAt hend G hG hat hts).toHistory.stageMetric (Fin.last H.eventCount)
      (H.extendAtTime hend G hG hat hts) = G.flow.base.metric t :=
    H.stageMetric_extendHorizon_last_of_mem_Icc (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      ⟨hat.le, le_rfl⟩
  revert W hW hneck Gs hGs ŷ
  change ∀ ŷ : ((H.extendAt hend G hG hat hts).toHistory.stage
      ((H.extendAt hend G hG hat hts).toHistory.activeStage
        (H.extendAtTime hend G hG hat hts))).Carrier, HEq ŷ y → _
  generalize (H.extendAt hend G hG hat hts).toHistory.activeStage
    (H.extendAtTime hend G hG hat hts) = k at hlast ⊢
  subst hlast
  intro ŷ hŷ Gs hGs
  have hŷy : ŷ = y := eq_of_heq hŷ
  subst ŷ
  have hGsG : Gs = G := eq_of_heq hGs
  subst Gs
  rw [hmet]
  intro W hW hneck
  exact ⟨W, hW, fun hn =>
    (historyStrongNeckFull_extendHorizon_iff_C12X (H := H) t (hend ▸ hat.le)
      (G.closedPrefix t hat hts) hG (k := Fin.last H.eventCount) (G := G) (eps := ε) (y := y)
      (t := t)).mp (hneck hn)⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
