import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR51Applications
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR52Applications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypesApplications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CompactClassification

/-!
# Row LFR54: classify the same finite local packet

Lane LFR54-ROW, group G4. Frozen blueprint master207A, LFR54
(`thm:collapse-classified-finite-zero-packet`, A:29526–29565):

"Supply LFR49's finite joint zero packet for the original oriented three-manifolds, with `K ≥ 10`,
and the same-model at-most-one-end conclusion of LC77. Then every indicated smooth radial sublevel
has one of the following smooth types: `D³, S¹ × D², ℝP³ ∖ int D³, D(o(K))` (LFR54.1), or one of the
compact types in LFR53. These identifications apply to the ACTUAL sublevels and include their
boundary."

The row `lfr54_classified_finite_zero_packet` is stated for ONE model's soul data (deviation D7): the
normal-form soul bundle `V` (LFR47's `Ê → Ŝ`), the carrier `e : TotalSpace F V ≃ₘ N` and its actual
disc cores `D_T = {‖(e⁻¹ x).2‖ ≤ T} ⊆ N`, `T > 0` (X84 `discCoreChartedSpace`), and LC77 for `N`.
Each clause gives ONE diffeomorphism (or embedding) of `D_T` onto the fixed chapter-14 model that
also carries the boundary `{‖(e⁻¹ x).2‖ = T}` exactly onto the model boundary (review 43: the
relative identification of the pair):

1. point soul: `D_T ≅ ClosedCell 3` (`D³`), boundary onto the unit sphere;
2. circle soul: `solidTorusCarrier ≅ D_T` (`S¹ × D²`), boundary torus `{cliffordHeight = 0}`;
3. surface soul (LC77 excludes `S² × ℝ`, `T² × ℝ` by LFR52): `D_T` is smoothly embedded in `ℝP³`
   onto the complement of an open oriented ball chart, boundary onto the boundary sphere
   (`ℝP³ ∖ int D³`), or `D_T ≅ {Q ≤ 0} = mobiusBundleSet` (`D(o(K))`), boundary onto `{Q = 0}`;
4. compact model: LFR53's types (`Collapse.IsCompactNonnegativeType`) for the original carrier and
   its `C^n` metric, `n ≥ 2`.

The packet binding (which model, the source sublevels `{η ≤ t} ≅ D_T`, orientation of the sources)
is lane LPA02's (LPA05's sublevel clause). The original metric is never replaced: LFR53's auxiliary
smooth metric lives inside its proof only.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Manifold

universe u uEB uHB uB uF uV uEN uHN uN

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The boundary charts of the closed ball `ClosedCell 3` (`𝓡∂ 3`). -/
local instance ballChartsRow_LFR54ROW : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The closed ball is a smooth manifold with boundary. -/
local instance ballSmoothRow_LFR54ROW : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-- **Row LFR54 (classify the same finite local packet).** On every actual disc core `D_T`,
`T > 0`, of a finite soul carrier `e`, with the boundary going onto the model boundary by the same
map: point soul `D³`; oriented circle soul `S¹ × D²`; oriented surface soul with LC77 `ℝP³ ∖ int D³`
or `D(o(K))`; and a compact model with a `C^n` metric of `K ≥ 0` has one of LFR53's types. -/
theorem lfr54_classified_finite_zero_packet :
    (∀ {EB : Type uEB} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
      {HB : Type uHB} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
      [IsContMDiffRiemannianBundle IB ∞ F V] [Subsingleton B] [Nonempty B]
      {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      {HN : Type uHN} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
      {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
      (hd : finrank ℝ (EB × F) = 2 + 1), finrank ℝ EB = 0 →
      ∀ (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e hd T hT
      ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {x : N // ‖(e.symm x).2‖ ≤ T} (ClosedCell 3) ∞,
        (∀ x, T * ‖(Ψ x).val‖ = ‖(e.symm x.val).2‖) ∧
        ∀ x, ‖(e.symm x.val).2‖ = T ↔ ‖(Ψ x).val‖ = 1) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : AddCircle (1 : ℝ) → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
      [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]
      {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      {HN : Type uHN} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
      {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
      (hF : finrank ℝ F = 2), SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      ∀ (e : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e (finrank_real_prod_eq_three hF) T hT
      ∃ Φ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
          (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
          {x : N // ‖(e.symm x).2‖ ≤ T} ∞,
        ∀ x : GC.GraphManifold.solidTorusCarrier.{u}.Carrier,
          GC.GraphManifold.cliffordHeight (x : GC.GraphManifold.solidTorusSet.{u}).val = 0 ↔
            ‖(e.symm (Φ x).val).2‖ = T) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
      [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V] [CompactSpace B] [ConnectedSpace B] [T2Space B]
      {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
      {HN : Type uHN} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
      {N : Type uN} [MetricSpace N] [ProperSpace N] [ChartedSpace HN N]
      (hd : finrank ℝ (E2 × F) = 2 + 1),
      SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      ∀ {n : ℕ∞ω}, (2 : ℕ∞ω) ≤ n →
      ∀ (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _)),
      (∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) →
      ∀ (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞),
      (∀ K : Set N, IsCompact K → ∀ a b : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) →
      ∀ (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e hd T hT
      (∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : {x : N // ‖(e.symm x).2‖ ≤ T} → projectiveThreeSpaceLift.{u}.Carrier),
        IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
        range f = {y | y ∉ c.chart '' Metric.ball (0 : E3) 1} ∧
        ∀ x, f x ∈ c.chart '' Metric.sphere (0 : E3) 1 ↔ ‖(e.symm x.val).2‖ = T) ∨
      ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {x : N // ‖(e.symm x).2‖ ≤ T} GC.Seifert.mobiusBundleSet.{u} ∞,
        ∀ x, ‖(e.symm x.val).2‖ = T ↔ GC.Seifert.mobiusBundleFunction (Φ x).val = 0) ∧
    (∀ (P : ConnectedClosedOrientedManifold.{u} 3) {n : ℕ∞ω}, (2 : ℕ∞ω) ≤ n →
      ∀ (g : Bundle.ContMDiffRiemannianMetric (𝓡 3) n E3
        (TangentSpace (𝓡 3) : P.Carrier → Type _)),
      (∀ x (v w : TangentSpace (𝓡 3) x), 0 ≤ g.sectionalCurvature x v w) →
      Collapse.IsCompactNonnegativeType P) := by
  obtain ⟨hP, hC, -⟩ := lfr51_discCore_types.{u, uEB, uHB, uB, uF, uV, uEN, uHN, uN}
  refine ⟨?_, fun hF oV e T hT => hC hF oV e T hT, ?_,
    fun P _ hn g hsec => Collapse.isCompactNonnegativeType_of_finite_metric P hn g hsec⟩
  · intro EB _ _ _ HB _ IB _ B _ _ _ F _ _ _ V _ _ _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ hd h0 e T hT
    let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
    obtain ⟨Ψ, hΨ⟩ := hP (IB := IB) (V := V) hd h0 e T hT
    refine ⟨Ψ, hΨ, fun x => ?_⟩
    rw [← hΨ x]
    constructor
    · intro h
      exact mul_left_cancel₀ hT.ne' (h.trans (mul_one T).symm)
    · intro h
      rw [h, mul_one]
  · intro F _ _ _ B _ _ _ V _ _ _ _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ _ hd oN n hn k hK e hLC77 T hT
    exact discCore_surface_soul_types_of_unit_map_dichotomy.{u} e hd
      (lfr52_lc77_surface_soul_twisted hd oN hn k hK e.toHomeomorph hLC77) T hT

end DifferentialGeometry.Geometry.Collapse.ZeroModel
