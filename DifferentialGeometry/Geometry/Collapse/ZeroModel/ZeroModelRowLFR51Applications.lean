import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR51
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypes

/-!
# Consumer of row LFR51: the `D(Ê)` column on every actual disc core

Lane LFR54-ROW, group G2. For a carrier `e : TotalSpace F V ≃ₘ N` (LFR47's normal-flow carrier) and
its actual disc cores `D_T = {‖(e⁻¹ x).2‖ ≤ T} ⊆ N`, `T > 0`, with the transported boundary charts
(X84 `discCoreChartedSpace`), row LFR51 gives the `D(Ê)` column of (LFR51.1) on EVERY `D_T`, each
time through ONE diffeomorphism that also carries the boundary `{‖(e⁻¹ x).2‖ = T}` onto the model
boundary (`lfr51_discCore_types`):

* point soul: `D_T ≅ ClosedCell 3`, `T · ‖Ψ x‖ = ‖(e⁻¹ x).2‖`;
* circle soul: `D_T ≅ solidTorusCarrier`, boundary torus `{cliffordHeight = 0}` onto the boundary;
* surface soul: `D_T ≅ D(S² × ℝ)` or `D(T² × ℝ)` (closed unit disc bundles of the trivial line,
  `T · ‖Ψ x‖ = ‖(e⁻¹ x).2‖`), or a smooth embedding onto `ℝP³ ∖ (open ball)` (boundary onto the
  boundary sphere), or `D_T ≅ {Q ≤ 0} = D(o(K))` (boundary onto the torus `{Q = 0}`).

The unit-radius identification `unitDiscCoreDiffeomorph` scales the fibre norm by `T`
(`norm_discCore_eq_mul_unitDiscCore_symm`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Module
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
open DifferentialGeometry.Topology.Manifold

universe u uEB uHB uB uF uV uEN uHN uN

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The boundary charts of the closed ball `ClosedCell 3` (`𝓡∂ 3`). -/
local instance ballChartsDisc_LFR54ROW : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The closed ball is a smooth manifold with boundary. -/
local instance ballSmoothDisc_LFR54ROW : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

section Scale

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- The unit-radius map of a disc core scales the fibre norm by `T`. -/
theorem norm_discCore_eq_mul_unitDiscCore_symm {m : ℕ}
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞)
    (hd : finrank ℝ (EB × F) = m + 1) {T : ℝ} (hT : 0 < T) (x : {x : N // ‖(e.symm x).2‖ ≤ T}) :
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
    letI := discCoreChartedSpace e hd T hT
    ‖(e.symm x.val).2‖ = T * ‖((unitDiscCoreDiffeomorph e hd T hT).symm x).val.2‖ := by
  let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
  let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
  have h := unitDiscCoreDiffeomorph_apply e hd T hT ((unitDiscCoreDiffeomorph e hd T hT).symm x)
  rw [Diffeomorph.apply_symm_apply] at h
  rw [h, e.symm_apply_apply]
  change ‖T • _‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]

end Scale

/-- **Consumer of LFR51: the `D(Ê)` column on every actual disc core.** For a carrier
`e : TotalSpace F V ≃ₘ N` of a finite soul bundle in normal form, every disc core
`D_T = {‖(e⁻¹ x).2‖ ≤ T} ⊆ N`, `T > 0`, with its transported boundary charts, is
1. (point soul) `≅ ClosedCell 3` with `T · ‖Ψ x‖ = ‖(e⁻¹ x).2‖`;
2. (circle soul, oriented) `≅ solidTorusCarrier`, boundary torus onto `{‖(e⁻¹ x).2‖ = T}`;
3. (surface soul, oriented, `K ≥ 0` base metric) `≅ D(S² × ℝ)` or `≅ D(T² × ℝ)` (trivial line,
   `T · ‖Ψ x‖ = ‖(e⁻¹ x).2‖`), or embedded onto `ℝP³ ∖ (open ball)` with boundary onto the
   boundary sphere, or `≅ {Q ≤ 0}` with boundary onto `{Q = 0}`. -/
theorem lfr51_discCore_types :
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
        ∀ x, T * ‖(Ψ x).val‖ = ‖(e.symm x.val).2‖) ∧
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
      {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
      (hd : finrank ℝ (E2 × F) = 2 + 1),
      SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      ∀ {n : ℕ∞ω}, (2 : ℕ∞ω) ≤ n →
      ∀ (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _)),
      (∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) →
      ∀ (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e hd T hT
      (letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := Trivial S2 E1)
          finrank_euclideanTwo_prod_one 1 one_pos
        ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
            {x : N // ‖(e.symm x).2‖ ≤ T} {z : TotalSpace E1 (Trivial S2 E1) // ‖z.2‖ ≤ 1} ∞,
          ∀ x, T * ‖(Ψ x).val.2‖ = ‖(e.symm x.val).2‖) ∨
      (letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (V := Trivial T2 E1) finrank_real_prod_real_prod_one 1 one_pos
        ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
            {x : N // ‖(e.symm x).2‖ ≤ T} {z : TotalSpace E1 (Trivial T2 E1) // ‖z.2‖ ≤ 1} ∞,
          ∀ x, T * ‖(Ψ x).val.2‖ = ‖(e.symm x.val).2‖) ∨
      (∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : {x : N // ‖(e.symm x).2‖ ≤ T} → projectiveThreeSpaceLift.{u}.Carrier),
        IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
        range f = {y | y ∉ c.chart '' Metric.ball (0 : E3) 1} ∧
        ∀ x, f x ∈ c.chart '' Metric.sphere (0 : E3) 1 ↔ ‖(e.symm x.val).2‖ = T) ∨
      ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {x : N // ‖(e.symm x).2‖ ≤ T} GC.Seifert.mobiusBundleSet.{u} ∞,
        ∀ x, ‖(e.symm x.val).2‖ = T ↔ GC.Seifert.mobiusBundleFunction (Φ x).val = 0) := by
  obtain ⟨hP, hC, hS⟩ := lfr51_oriented_finite_soul_bundle_types.{u, uEB, uHB, uB, uF, uV}
  refine ⟨?_, ?_, ?_⟩
  · intro EB _ _ _ HB _ IB _ B _ _ _ F _ _ _ V _ _ _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ hd h0 e T hT
    let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
    let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
    obtain ⟨-, Ψ, hΨ, -⟩ := hP (IB := IB) (V := V) hd h0
    refine ⟨(unitDiscCoreDiffeomorph e hd T hT).symm.trans Ψ, fun x => ?_⟩
    rw [norm_discCore_eq_mul_unitDiscCore_symm e hd hT x]
    exact congrArg (T * ·) (hΨ _)
  · intro F _ _ _ V _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ hF oV e T hT
    have hd := finrank_real_prod_eq_three hF
    let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos
    let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
    obtain ⟨-, Ψ, hΨ⟩ := hC hF oV
    refine ⟨Ψ.trans (unitDiscCoreDiffeomorph e hd T hT), fun x => ?_⟩
    rw [hΨ x]
    have h := norm_discCore_eq_mul_unitDiscCore_symm e hd hT (unitDiscCoreDiffeomorph e hd T hT (Ψ x))
    rw [Diffeomorph.symm_apply_apply] at h
    change ‖(Ψ x).val.2‖ = 1 ↔ ‖(e.symm ((unitDiscCoreDiffeomorph e hd T hT) (Ψ x)).val).2‖ = T
    rw [h]
    constructor
    · intro h1
      rw [h1, mul_one]
    · intro h1
      exact mul_left_cancel₀ hT.ne' (h1.trans (mul_one T).symm)
  · intro F _ _ _ B _ _ _ V _ _ _ _ _ _ _ _ _ _ EN _ _ HN _ IN N _ _ hd oN n hn k hK e T hT
    let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    let csCore_LFR54ROW := discCoreChartedSpace e hd T hT
    rcases hS hd oN hn k hK with ⟨-, Ψ, hΨ, Ψ', hΨ'⟩ | ⟨-, -, Ψ, hΨ, Ψ', hΨ'⟩ |
        ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc, -⟩ |
        ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc, -⟩
    · left
      let csTriv_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := Trivial S2 E1)
        finrank_euclideanTwo_prod_one 1 one_pos
      refine ⟨(unitDiscCoreDiffeomorph e hd T hT).symm.trans Ψ'.symm, fun x => ?_⟩
      rw [norm_discCore_eq_mul_unitDiscCore_symm e hd hT x]
      congr 1
      have h := hΨ' (Ψ'.symm ((unitDiscCoreDiffeomorph e hd T hT).symm x))
      rw [Diffeomorph.apply_symm_apply] at h
      rw [h, hΨ]
      rfl
    · right; left
      let csTriv_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        (V := Trivial T2 E1) finrank_real_prod_real_prod_one 1 one_pos
      refine ⟨(unitDiscCoreDiffeomorph e hd T hT).symm.trans Ψ'.symm, fun x => ?_⟩
      rw [norm_discCore_eq_mul_unitDiscCore_symm e hd hT x]
      congr 1
      have h := hΨ' (Ψ'.symm ((unitDiscCoreDiffeomorph e hd T hT).symm x))
      rw [Diffeomorph.apply_symm_apply] at h
      rw [h, hΨ]
      rfl
    · right; right; left
      exact exists_puncturedRP3_embedding_discCore_of_antipodal_unit_map.{u} e hd ν hν hνS hνinj
        hνsurj hνneg hνloc T hT
    · right; right; right
      exact exists_mobiusBundleSet_diffeomorph_discCore_of_klein_unit_map.{u} e hd ν hν hνS hνinj
        hνsurj hνneg hνloc T hT

end DifferentialGeometry.Geometry.Collapse.ZeroModel
