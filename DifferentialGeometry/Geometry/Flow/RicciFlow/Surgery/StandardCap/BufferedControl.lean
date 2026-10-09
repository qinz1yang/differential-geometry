import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Curvature.DimensionThree.TensorNorm

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

structure StandardCapModel where
  solution : SmoothRiemannianMetric ThreeModel ThreeSpace
  initial : solution = standardCapMetric
  tip : ThreeSpace

structure CapClass where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initialParameter : ℝ
  initialParameter_pos : 0 < initialParameter
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  volumeConstant : ℝ
  volumeConstant_pos : 0 < volumeConstant
  scaleLower : ℝ
  scaleLower_pos : 0 < scaleLower
  scaleUpper : ℝ
  scale_lt : scaleLower < scaleUpper

structure OldData where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initialParameter : ℝ
  initialParameter_pos : 0 < initialParameter
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  comparisonConstant : ℝ
  comparisonConstant_pos : 0 < comparisonConstant
  volumeConstant : ℝ
  volumeConstant_pos : 0 < volumeConstant
  scaleLower : ℝ
  scaleLower_pos : 0 < scaleLower
  noncollapsing : ℝ
  noncollapsing_pos : 0 < noncollapsing
  olderLength : ℝ
  olderLength_pos : 0 < olderLength
  energyBound : ℝ
  olderLength_le_energy : olderLength ≤ energyBound

structure PreparedCapSeed (H : ObservedHistory.{u}) (L : ℝ) (N : ℕ) (ζ : ℝ) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace (H.stage 0).Carrier ∞
  ball_subset_source : Metric.ball (0 : ThreeSpace) L ⊆ chart.source
  scale : ℝ
  scale_pos : 0 < scale
  order : ℕ
  order_lower : N ≤ order
  accuracy_pos : 0 < ζ

structure BackwardRealization {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (metric : ℝ → SmoothRiemannianMetric ThreeModel M) (t s : ℝ) where
  chart : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace M ∞
  zero_mem_source : (0 : ThreeSpace) ∈ chart.source
  ball_subset_source : Metric.ball (0 : ThreeSpace) (4 * s) ⊆ chart.source
  curvature_bound : ∀ u ∈ Icc (t - 4 * s ^ 2) t,
    ∀ x ∈ Metric.ball (0 : ThreeSpace) (4 * s),
      curvatureNormSq (metric u) (chart x)
        (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
          (M := M) (metric u) (chart x)) ≤ (s ^ 2)⁻¹

inductive TrackedFace where
  | incoming
  | observed

structure TrackedChart (P : OrientedThreeStage.{u}) (G : ℝ → P.Metric)
    (J : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace P.Carrier ∞) (q L K : ℝ) where
  time : ℝ
  time_nonneg : 0 ≤ time
  time_le : time ≤ q
  face : TrackedFace
  flow : ℝ → ThreeSpace → P.Carrier
  flow_zero : Set.EqOn (flow 0) ⇑J (Metric.ball (0 : ThreeSpace) L)
  flow_injective : ∀ s ∈ Icc (0 : ℝ) time, Function.Injective (flow s)
  domain : Set ThreeSpace
  domain_open : IsOpen domain
  wide : ∀ x : ThreeSpace, ‖x‖ ≤ L → x ∈ domain
  normalizedMetric : ℝ → SmoothRiemannianMetric ThreeModel ThreeSpace
  normalized_metric_eq : ∀ s ∈ Icc (0 : ℝ) time,
    ∀ (x : ThreeSpace) (V W : TangentSpace ThreeModel x),
      (normalizedMetric s).inner x V W = (q - s)⁻¹ *
        (G (q - s)).inner (flow s x)
          (mfderiv ThreeModel ThreeModel (flow s) x V)
          (mfderiv ThreeModel ThreeModel (flow s) x W)
  curvature_bound : ∀ s ∈ Icc (0 : ℝ) time, ∀ x : ThreeSpace, ‖x‖ ≤ L →
    curvatureNormSq (normalizedMetric s) x
      (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := ThreeModel)
        (M := ThreeSpace) (normalizedMetric s) x) ≤ K ^ 2

structure AdmissibleDatum (c : CapClass) where
  history : ObservedHistory.{u}
  eventCount_pos : 0 < history.eventCount
  horizon_le : history.horizon ≤ c.horizon
  ambientMetric : ℝ → (history.stage 0).Metric
  precision : ℝ
  precision_pos : 0 < precision
  scale : ℝ
  scale_pos : 0 < scale

def ProtectedSurvives {c : CapClass} (D : AdmissibleDatum.{u} c) (a : ℝ)
    (i : Fin D.history.eventCount) : Prop :=
  Nonempty (BackwardRealization
    (fun u => (D.history.event i).incoming.flow.base.metric u) (D.history.time i.succ) (a / 4))

def IsLossEvent {c : CapClass} (D : AdmissibleDatum.{u} c) (a : ℝ)
    (i : Fin D.history.eventCount) : Prop :=
  ¬ ProtectedSurvives D a i

def IsStoppingFace {c : CapClass} (D : AdmissibleDatum.{u} c) (a θ : ℝ) (T : ℝ) : Prop :=
  T ∈ Icc a (a + θ / D.scale) ∧
    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧ T = D.history.time i.succ ∧
        ∀ j : Fin D.history.eventCount, IsLossEvent D a j → a < D.history.time j.succ →
          T ≤ D.history.time j.succ) ∨
      ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧ a < D.history.time i.succ ∧
          D.history.time i.succ ≤ a + θ / D.scale) ∧
        T = min D.history.horizon (a + θ / D.scale)))

def isBufferedControlInput : Prop :=
  ∀ c : CapClass, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ a : ℝ, 1 < a → ∀ L : ℝ, a + 3 < L →
        ∃ L₀ : ℝ, L + 2 < L₀ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
          ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ D : AdmissibleDatum.{u} c, D.precision ≤ δ₀ →
              ∀ seed : PreparedCapSeed D.history L₀ N₀ ζ₀,
                ∀ T : ℝ, IsStoppingFace D a θ T →
                  ∃ C : TrackedChart (D.history.stage 0) D.ambientMetric seed.chart T L K,
                    ((∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.incoming) ∧
                    ((¬ ∃ i : Fin D.history.eventCount, IsLossEvent D a i ∧
                        T = D.history.time i.succ) → C.face = TrackedFace.observed) ∧
                    Nonempty (BackwardRealization (fun u => D.ambientMetric u) T (L / 4))

structure CapEscapeModel where
  horizon : ℝ
  horizon_pos : 0 < horizon
  radius : ℝ
  radius_pos : 0 < radius
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  action : ℝ → (ℝ → ThreeSpace) → ℝ≥0∞

def isCapEscapeCostBarrier (C : CapEscapeModel) : Prop :=
  ∀ H : ℝ, 0 < H →
    ∃ A : ℝ, A < C.radius ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ v : ℝ, 0 < v → v ≤ θ →
      ∀ ξ : ℝ → ThreeSpace,
        (∀ u ∈ Icc 0 v, dist (ξ u) (0 : ThreeSpace) ≤ C.radius) →
        ENNReal.ofReal H < C.action v ξ

structure CapEscapeTransfer (H : ObservedHistory.{u}) where
  insertionTime : ℝ
  duration : ℝ
  duration_pos : 0 < duration
  depth : ℝ
  depth_pos : 0 < depth
  comparison : CapEscapeModel
  barrier : isCapEscapeCostBarrier comparison

def isOldTubeInput (d : OldData) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    ∃ s : ℝ, 0 < s ∧ s ≤ min (d.epsilon / 2) (Real.sqrt (d.energyBound / 24)) ∧
      ∃ dOld : ℝ, 0 < dOld ∧
        ∀ (H : ObservedHistory.{u}) (P : CutoffParameters) (i : Fin H.eventCount) (t : ℝ)
          (x : (H.stage i.castSucc).Carrier),
          P.delta t ≤ dOld →
          H.time i.castSucc + (H.time i.succ - H.time i.castSucc) / 3 ≤ t →
          t ≤ H.time i.castSucc + 2 * (H.time i.succ - H.time i.castSucc) / 3 →
          metricScalarAt ((H.event i).incoming.flow.base.metric t) x ≤ ρ →
          Nonempty (BackwardRealization
            (fun u => (H.event i).incoming.flow.base.metric u) t s)

theorem nonempty_oldData : Nonempty OldData :=
  ⟨{ horizon := 1, horizon_pos := one_pos
     initialParameter := 1, initialParameter_pos := one_pos
     epsilon := 1, epsilon_pos := one_pos
     comparisonConstant := 1, comparisonConstant_pos := one_pos
     volumeConstant := 1, volumeConstant_pos := one_pos
     scaleLower := 1, scaleLower_pos := one_pos
     noncollapsing := 1, noncollapsing_pos := one_pos
     olderLength := 1, olderLength_pos := one_pos
     energyBound := 1, olderLength_le_energy := le_rfl }⟩

theorem nonempty_capClass : Nonempty CapClass :=
  ⟨{ horizon := 1, horizon_pos := one_pos
     initialParameter := 1, initialParameter_pos := one_pos
     epsilon := 1, epsilon_pos := one_pos
     comparisonConstant := 1, comparisonConstant_pos := one_pos
     volumeConstant := 1, volumeConstant_pos := one_pos
     scaleLower := 1, scaleLower_pos := one_pos
     scaleUpper := 2, scale_lt := one_lt_two }⟩

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
