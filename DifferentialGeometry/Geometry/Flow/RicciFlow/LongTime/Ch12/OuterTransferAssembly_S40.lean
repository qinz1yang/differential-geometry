import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferVolume_S40
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterThinAmbientV2_S35

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- Eventual `δ < 1/4` for the buffer accuracy. -/
theorem accuracy_lt_quarter_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K) :
    ∃ T : ℝ, ∀ t (_ : B.start ≤ t), T ≤ t → B.accuracy t < 1 / 4 := by
  obtain ⟨T, hT⟩ := B.accuracy_decay (1 / 4) (by norm_num)
  exact ⟨T, fun t _ ht => hT t ht⟩

/-- The `hC0` input of `hLow_S41` (frozen in `[FROZEN] CH12-S41`) from the S2 C⁰ comparison:
`h ≤ 2² · ḡ(dφ ·, dφ ·)` on the closed `h`-ball of radius `4` about `y ∈ B(x_i, n)`, for late `t`. -/
theorem hC0_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K) :
    ∃ T₀ : ℝ, ∀ t (ht : B.start ≤ t), T₀ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
      ∀ x ∈ riemannianClosedBallOf (B.model i).metric y 4, ∀ v : TangentSpace (𝓡 3) x,
        (B.model i).metric.inner x v v ≤
          (2 : ℝ) ^ 2 *
            (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
              (postMetric F.observation t)).inner (B.map i t ht x)
              (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x v)
              (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) x v) := by
  obtain ⟨T, hT⟩ := accuracy_lt_quarter_S40 B
  refine ⟨T, fun t ht hTt i y hy x hx v => ?_⟩
  have hδ := hT t ht hTt
  have hn4 : 4 ≤ (B.accuracy t)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (B.accuracy_pos t ht)]
    norm_num
    exact hδ.le
  have hlow := bufferedMap_metric_lower_S40 B i t ht x
    (closedBall_subset_buffer_S40 B i t ht y hy hn4 hx) v
  have hnn := metric_inner_self_nonneg (B.model i).metric x v
  nlinarith

/-- **(G3)** The decomposed transfer hypothesis `hTrans` of `outerThin_ambient_v2_S35` (verbatim),
from S41's curvature conjuncts (`hUp_S41`, `hLow_S41` conclusions, `[FROZEN] CH12-S41`) and the
S40 volume comparison. -/
theorem hTrans_of_curv_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (hUp : ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)))
    (hLow : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
      ∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) c₀,
        SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t →
      ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        (∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) c₀,
          SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) ∧
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)) ∧
        ∀ r : ℝ, 0 < r → r ^ 2 ≤ 8 →
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) (B.map i t ht y) r ≤
          ENNReal.ofReal 2 * ballVolume (B.model i).metric y 4 := by
  obtain ⟨Tu, hTu⟩ := hUp
  obtain ⟨c₀, hc₀, Tl, hTl⟩ := hLow
  obtain ⟨Tv, hTv⟩ := accuracy_lt_quarter_S40 B
  refine ⟨c₀, hc₀, max (max Tl Tu) Tv, fun t ht hT i y hy => ⟨?_, ?_, ?_⟩⟩
  · exact hTl t ht ((le_max_left _ _).trans ((le_max_left _ _).trans hT)) i y hy
  · exact hTu t ht ((le_max_right _ _).trans ((le_max_left _ _).trans hT)) i y hy
  · intro r hr hr8
    exact bufferedMap_ballVolume_le_S40 B i t ht y hy (hTv t ht ((le_max_right _ _).trans hT)).le
      hr hr8

/-- **(G3, consumer)** `outerThin_ambient_v2_S35` fed by `hTrans_of_curv_S40`. -/
theorem outerThin_ambient_of_curv_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i))
    (hUp : ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
        ¬ SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) (-(1 / 8 : ℝ)))
    (hLow : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ T₁ : ℝ, ∀ t (ht : B.start ≤ t), T₁ ≤ t → ∀ i : Fin B.count,
      ∀ y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹,
      ∀ q ∈ riemannianBallOf (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) (B.map i t ht y) c₀,
        SectionalBoundedBelowAt (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
          (postMetric F.observation t)) q (-(c₀ ^ 2)⁻¹)) :
    ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ t (ht : B.start ≤ t), T ≤ t →
      ∀ trunc : (i : Fin B.count) → HyperbolicTruncation (B.model i),
        (∀ i, riemannianClosedBallOf (B.model i).metric (B.model i).basepoint
            ((B.accuracy t)⁻¹ / 2) ⊆ Set.range (trunc i).inclusion) →
        ∀ x : (postStage F.observation t).Carrier,
          x ∉ ⋃ i : Fin B.count, B.map i t ht '' Set.range (trunc i).inclusion →
          volumeCollapsedAtCurvatureScale
            (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
              (postMetric F.observation t)) w x :=
  outerThin_ambient_v2_S35 B base (hTrans_of_curv_S40 B hUp hLow)

end GC.LongTime.Ch12
