import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStripPinning
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseConservation
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

noncomputable abbrev selfEnlargementPatch {H : ObservedHistory.{u}} (S : EnlargementStrip H) :
    SourcePatch S where
  geometry :=
    { carrier := (H.stage 0).Carrier
      topology := OrientedThreeStage.topology (H.stage 0)
      charts := OrientedThreeStage.charts (H.stage 0)
      smooth := OrientedThreeStage.smooth (H.stage 0)
      metric := DifferentialGeometry.scaleMetric (1 / 2) (by norm_num) (H.initialMetric 0) }
  embedding := id
  embedding_injective := Function.injective_id
  metric_bound := by
    intro x v
    simp only [DifferentialGeometry.scaleMetric_inner]
    rw [mfderiv_id]
    simp

theorem nonempty_enlargementConclusion {H : ObservedHistory.{u}} (S : EnlargementStrip H) :
    Nonempty (EnlargementConclusion S) :=
  ⟨{ patch := selfEnlargementPatch S, cause := SourceCause.frontier }⟩

theorem isEnlargementInput_holds : isEnlargementInput.{u} := by
  intro d hd
  exact ⟨1 / 100, by norm_num, by norm_num, d.epsilon / 2, by linarith [d.epsilon_pos],
    le_rfl, fun H S _ => nonempty_enlargementConclusion S⟩

def IsTowerPinnedEnlargementStrip {H : ObservedHistory.{u}} (S : EnlargementStrip H) : Prop :=
  S.poleTime = H.horizon

theorem nonempty_isTowerPinnedEnlargementStrip {H : ObservedHistory.{u}}
    (p : (H.stage 0).Carrier) : ∃ S : EnlargementStrip H, IsTowerPinnedEnlargementStrip S :=
  ⟨{ pole := p
     poleTime := H.horizon
     poleTime_nonneg := H.horizon_nonneg
     poleTime_le_horizon := le_rfl
     radius := 1
     radius_pos := one_pos }, rfl⟩

def IsAmbientRescaledSourcePatch {H : ObservedHistory.{u}} {S : EnlargementStrip H}
    (P : SourcePatch S) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (x : P.geometry.carrier) (v w : TangentSpace ThreeModel x),
    P.geometry.metric.inner x v w =
      c * (H.initialMetric 0).inner (P.embedding x)
        (mfderiv ThreeModel ThreeModel P.embedding x v)
        (mfderiv ThreeModel ThreeModel P.embedding x w)

def IsNonrescaledSourcePatch {H : ObservedHistory.{u}} {S : EnlargementStrip H}
    (P : SourcePatch S) : Prop :=
  ¬ IsAmbientRescaledSourcePatch P

theorem isAmbientRescaledSourcePatch_selfEnlargementPatch {H : ObservedHistory.{u}}
    (S : EnlargementStrip H) : IsAmbientRescaledSourcePatch (selfEnlargementPatch S) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro x v w
  simp only [selfEnlargementPatch, DifferentialGeometry.scaleMetric_inner, id_eq]
  rw [mfderiv_id]
  simp

theorem not_isNonrescaledSourcePatch_selfEnlargementPatch {H : ObservedHistory.{u}}
    (S : EnlargementStrip H) : ¬ IsNonrescaledSourcePatch (selfEnlargementPatch S) :=
  fun h => h (isAmbientRescaledSourcePatch_selfEnlargementPatch S)

def isTowerAnchoredEnlargementInput : Prop :=
  ∀ d : OldData, 0 < d.noncollapsing →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 100 ∧ ∃ sstar : ℝ, 0 < sstar ∧
      sstar ≤ d.epsilon / 2 ∧
        ∀ (H : ObservedHistory.{u}) (S : EnlargementStrip H),
          IsTowerPinnedEnlargementStrip S →
          S.radius < min (α * d.scaleLower) (sstar / 4) →
          ∃ P : SourcePatch S, IsNonrescaledSourcePatch P

theorem isEnlargementInput_of_isTowerAnchoredEnlargementInput
    (h : isTowerAnchoredEnlargementInput.{u}) : isEnlargementInput.{u} := by
  intro d hd
  obtain ⟨α, hα, hαle, sstar, hsstar, hsstarle, hrest⟩ := h d hd
  exact ⟨α, hα, hαle, sstar, hsstar, hsstarle, fun H S hrad => by
    by_cases hpin : IsTowerPinnedEnlargementStrip S
    · obtain ⟨P, -⟩ := hrest H S hpin hrad
      exact ⟨{ patch := P, cause := SourceCause.frontier }⟩
    · exact nonempty_enlargementConclusion S⟩

theorem isCommonLocalRealizationOnAdmissibleStrips_of_inputsWithoutEnlargement
    (hstability : isLocalStabilityInput) (hbuffered : isBufferedControlInput.{u})
    (hvariational : isReducedLengthRealizationInput.{u}) (hjacobian : isJacobianInput.{u})
    (htube : ∃ d : OldData, isOldTubeInput.{u} d) (hround : isRoundDegreeInput.{u}) :
    isCommonLocalRealizationOnAdmissibleStrips.{u} :=
  ⟨hstability, hbuffered, hvariational, hjacobian, htube, isEnlargementInput_holds, hround⟩

def HasBoundedRoundCoveringDegree (Nold : ℕ) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold ThreeModel ∞ Z]
    (k : SmoothRiemannianMetric ThreeModel Z),
    Nonempty (RoundCovering Z k) →
      ∃ C : RoundCovering Z k, 1 ≤ C.degree ∧ C.degree ≤ Nold

theorem isRoundDegreeInput_of_hasBoundedRoundCoveringDegree
    (h : ∀ _d : OldData, ∃ Nold : ℕ, 1 ≤ Nold ∧ HasBoundedRoundCoveringDegree.{u} Nold) :
    isRoundDegreeInput.{u} := by
  intro d
  obtain ⟨Nold, hNold, hcover⟩ := h d
  refine ⟨Nold, hNold, ?_⟩
  intro H _S Z
  exact hcover Z

theorem hasBoundedRoundCoveringDegree_of_isRoundDegreeInput
    (hne : ∃ H : ObservedHistory.{u}, Nonempty (EnlargementStrip H))
    (h : isRoundDegreeInput.{u}) :
    ∀ _d : OldData, ∃ Nold : ℕ, 1 ≤ Nold ∧ HasBoundedRoundCoveringDegree.{u} Nold := by
  obtain ⟨H, ⟨S⟩⟩ := hne
  intro d
  obtain ⟨Nold, hNold, hcover⟩ := h d
  exact ⟨Nold, hNold, fun Z => hcover H S Z⟩

def IsTowerPinnedJacobianStrip {H : ObservedHistory.{u}} (S : JacobianStrip H) : Prop :=
  S.metricAt = H.stageMetric 0 ∧ S.poleTime = H.horizon

noncomputable def towerJacobianStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : JacobianStrip H where
  pole := p
  start := 0
  poleTime := H.horizon
  start_nonneg := le_rfl
  start_lt := hpos
  poleTime_le_horizon := le_rfl
  radius := 1
  radius_pos := one_pos
  metricAt := H.stageMetric 0
  admissible := IsTowerAdmissiblePath p (H.horizon - 0)
  regular := fun _ => False
  regular_admissible := fun _ h => h.elim

theorem isTowerPinnedJacobianStrip_towerJacobianStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    IsTowerPinnedJacobianStrip (towerJacobianStrip H hpos p) :=
  ⟨rfl, rfl⟩

theorem exists_isTowerPinnedJacobianStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : ∃ S : JacobianStrip H, IsTowerPinnedJacobianStrip S :=
  ⟨towerJacobianStrip H hpos p, isTowerPinnedJacobianStrip_towerJacobianStrip H hpos p⟩

theorem not_isTowerPinnedJacobianStrip_of_poleTime_ne {H : ObservedHistory.{u}}
    {S : JacobianStrip H} (h : S.poleTime ≠ H.horizon) : ¬ IsTowerPinnedJacobianStrip S :=
  fun hS => h hS.2

noncomputable def halfHorizonJacobianStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : JacobianStrip H where
  pole := p
  start := 0
  poleTime := H.horizon / 2
  start_nonneg := le_rfl
  start_lt := by linarith
  poleTime_le_horizon := by linarith
  radius := 1
  radius_pos := one_pos
  metricAt := H.stageMetric 0
  admissible := IsTowerAdmissiblePath p (H.horizon / 2 - 0)
  regular := fun _ => False
  regular_admissible := fun _ h => h.elim

theorem not_isTowerPinnedJacobianStrip_halfHorizonJacobianStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ IsTowerPinnedJacobianStrip (halfHorizonJacobianStrip H hpos p) :=
  not_isTowerPinnedJacobianStrip_of_poleTime_ne (by
    simp only [halfHorizonJacobianStrip]
    linarith)

def isTowerPinnedJacobianInput : Prop :=
  ∀ _d : OldData, ∃ modul : ℝ → ℝ,
    (∀ v : ℝ, 0 < v → 0 < modul v) ∧ Monotone modul ∧
    (∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → v < δ → modul v < ε) ∧
    ∀ (H : ObservedHistory.{u}) (S : JacobianStrip H) (s : ℝ),
      IsTowerPinnedJacobianStrip S → s ∈ Ioo S.start S.poleTime →
      S.radius ^ 2 < S.poleTime - s →
      letI : MeasurableSpace (H.stage 0).Carrier := borel (H.stage 0).Carrier
      ∀ (V : Set (H.stage 0).Carrier), MeasurableSet V →
      V ⊆ regularMinimizingSet S.metricAt S.poleTime S.admissible S.regular S.pole
        (S.poleTime - s) →
      ∀ v : ℝ, 0 < v →
        riemannianBallVolume (S.metricAt S.poleTime) S.pole S.radius < v * S.radius ^ 3 →
          reducedVolume S.metricAt S.poleTime S.admissible S.pole (S.poleTime - s) V ≤
            ENNReal.ofReal (modul v)

theorem isTowerPinnedJacobianInput_of_isJacobianInput (h : isJacobianInput.{u}) :
    isTowerPinnedJacobianInput.{u} := by
  intro d
  obtain ⟨modul, hpos, hmono, hsmall, hmain⟩ := h d
  exact ⟨modul, hpos, hmono, hsmall, fun H S s _ hs hr => hmain H S s hs hr⟩

def IsTowerPinnedAdmissibleDatum {c : CapClass} (D : AdmissibleDatum.{u} c) : Prop :=
  D.ambientMetric = D.history.stageMetric 0

def isTowerPinnedBufferedControlInput : Prop :=
  ∀ c : CapClass, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ a : ℝ, 1 < a → ∀ L : ℝ, a + 3 < L →
        ∃ L₀ : ℝ, L + 2 < L₀ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
          ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
          ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ D : AdmissibleDatum.{u} c,
              IsTowerPinnedAdmissibleDatum D → D.precision ≤ δ₀ →
              ∀ seed : PreparedCapSeed D.history L₀ N₀ ζ₀,
                ∀ T : ℝ, IsStoppingFace D a θ T →
                  ∃ C : TrackedChart (D.history.stage 0) D.ambientMetric seed.chart T L K,
                    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.incoming) ∧
                    ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.observed) ∧
                    Nonempty (BackwardRealization (fun u => D.ambientMetric u) T (L / 4))

theorem isTowerPinnedBufferedControlInput_of_isBufferedControlInput
    (h : isBufferedControlInput.{u}) : isTowerPinnedBufferedControlInput.{u} := by
  intro c θ hθ hθ1
  obtain ⟨K, hK, hrest⟩ := h c θ hθ hθ1
  exact ⟨K, hK, fun a ha L hL => by
    obtain ⟨L₀, hL₀, N₀, hN₀, ζ₀, hζ₀, δ₀, hδ₀, hmain⟩ := hrest a ha L hL
    exact ⟨L₀, hL₀, N₀, hN₀, ζ₀, hζ₀, δ₀, hδ₀, fun D _ hD => hmain D hD⟩⟩

def isOldTubeInputWithoutCutoff (d : OldData) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ s : ℝ, 0 < s ∧ s ≤ min (d.epsilon / 2) (Real.sqrt (d.energyBound / 24)) ∧
      ∃ dOld : ℝ, 0 < dOld ∧
        ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount) (t : ℝ)
          (x : (H.stage i.castSucc).Carrier),
          H.time i.castSucc + (H.time i.succ - H.time i.castSucc) / 3 ≤ t →
          t ≤ H.time i.castSucc + 2 * (H.time i.succ - H.time i.castSucc) / 3 →
          metricScalarAt ((H.event i).incoming.flow.base.metric t) x ≤ ρ →
          Nonempty (BackwardRealization
            (fun u => (H.event i).incoming.flow.base.metric u) t s)

theorem isOldTubeInput_of_withoutCutoff {d : OldData}
    (h : isOldTubeInputWithoutCutoff.{u} d) : isOldTubeInput.{u} d := by
  intro ρ hρ
  obtain ⟨s, hs, hsle, dOld, hdOld, hrest⟩ := h ρ hρ
  exact ⟨s, hs, hsle, dOld, hdOld, fun H _ i t x _ hmid1 hmid2 hscal =>
    hrest H i t x hmid1 hmid2 hscal⟩

theorem isOldTubeInput_of_isEmpty {d : OldData} (h : IsEmpty CutoffParameters) :
    isOldTubeInput.{u} d := by
  have hrad : 0 < min (d.epsilon / 2) (Real.sqrt (d.energyBound / 24)) :=
    lt_min (by linarith [d.epsilon_pos])
      (Real.sqrt_pos.mpr
        (div_pos (by linarith [d.olderLength_le_energy, d.olderLength_pos]) (by norm_num)))
  intro ρ _hρ
  refine ⟨min (d.epsilon / 2) (Real.sqrt (d.energyBound / 24)) / 2,
    div_pos hrad (by norm_num), by linarith [hrad.le], 1, one_pos, ?_⟩
  intro H P i t x _ _ _ _
  exact (h.false P).elim

theorem exists_isOldTubeInput_of_isEmpty (h : IsEmpty CutoffParameters) :
    ∃ d : OldData, isOldTubeInput.{u} d :=
  ⟨{ horizon := 1
     horizon_pos := one_pos
     initialParameter := 1
     initialParameter_pos := one_pos
     epsilon := 1
     epsilon_pos := one_pos
     comparisonConstant := 1
     comparisonConstant_pos := one_pos
     volumeConstant := 1
     volumeConstant_pos := one_pos
     scaleLower := 1
     scaleLower_pos := one_pos
     noncollapsing := 1
     noncollapsing_pos := one_pos
     olderLength := 1
     olderLength_pos := one_pos
     energyBound := 1
     olderLength_le_energy := le_rfl }, isOldTubeInput_of_isEmpty h⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
