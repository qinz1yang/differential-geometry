import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowPoint
import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowSurface
import DifferentialGeometry.Geometry.Collapse.ZeroModel.SolidTorusZeroModel
import DifferentialGeometry.Topology.VectorBundle.CircleBase.OrthonormalFrameApplications

/-!
# Row LFR51: orientation determines the finite soul bundle types

Lane LFR54-ROW, group G2. Frozen blueprint master207A, LFR51
(`lem:collapse-oriented-finite-soul-types`, A:29309–29378), table (LFR51.1):

| `Ŝ` | `Ê` | `D(Ê)` |
|---|---|---|
| `{*}` | `ℝ³` | `D³` |
| `S¹` | `S¹ × ℝ²` | `S¹ × D²` |
| `S²` | `S² × ℝ` | `S² × [-1, 1]` |
| `T²` | `T² × ℝ` | `T² × [-1, 1]` |
| `ℝP²` | `o(ℝP²)` | `D(o(ℝP²))` |
| `K` | `o(K)` | `D(o(K))` |

"These are smooth bundle identifications, including closed disk bundles after matching the fiber
norms." The row `lfr51_oriented_finite_soul_bundle_types` is the conjunction of the three soul
dimensions, each clause quantified over its own bundle (the bundle side of LFR47's `Ê → Ŝ`):

* point soul (`exists_point_soul_bundle_type`): `Ê ≅ ℝ³` and `D(Ê) ≅ ClosedCell 3`, norm to norm;
* circle soul (`exists_circle_soul_bundle_type`): oriented total space ⇒ `Ê ≅ S¹ × ℝ²` over the
  identity, norm-preserving, and `D(Ê) ≅ solidTorusCarrier` (the fixed `S¹ × D²`), the boundary torus
  `{cliffordHeight = 0}` going onto the unit sphere bundle;
* surface soul (`exists_surface_soul_bundle_type`): the four rank-one rows with (LFR51.2).

The metric of the original carrier is not touched: every identification is of the bundle `V`
with its own fibre norm.

Deviations (sheet-LFR54-ROW.md): D1 the base in normal form (point: `[Subsingleton B] [Nonempty B]`,
`finrank EB = 0`; circle: `AddCircle 1`; surface: charted on `E2`); D2 the surface base metric is an
argument; D5 `D(S² × ℝ)`, `D(T² × ℝ)` are the closed disc bundles of the trivial line; D6 `Ŝ = K` is
the double cover `T² → B` with deck `(x, y) ↦ (x + ½, -y)`. The point clause needs no orientation
(dropped).
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

universe u uEB uHB uB uF uV

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)
local notation "RP2" =>
  DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient

/-- The boundary charts of the closed ball `ClosedCell 3` (`𝓡∂ 3`). -/
local instance ballCharts_LFR54ROW : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The closed ball is a smooth manifold with boundary. -/
local instance ballSmooth_LFR54ROW : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

section Point

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

/-- **The point clause of LFR51** (`{*} | ℝ³ | D³`). Over a one-point base (`finrank EB = 0`) the
total space of a smooth Riemannian bundle of total dimension `3` is `ℝ³` (fibre norm = Euclidean
norm) and its closed unit disc bundle, with its native boundary charts, is `ClosedCell 3`, the
fibre norm going to the Euclidean norm (so the boundary goes onto the boundary sphere). -/
theorem exists_point_soul_bundle_type [Subsingleton B] [Nonempty B]
    (hd : finrank ℝ (EB × F) = 2 + 1) (h0 : finrank ℝ EB = 0) :
    (∃ Φ : Diffeomorph (IB.prod 𝓘(ℝ, F)) (𝓡 3) (TotalSpace F V) E3 ∞,
      ∀ z, ‖Φ z‖ = ‖z.2‖) ∧
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {z : TotalSpace F V // ‖z.2‖ ≤ 1} (ClosedCell 3) ∞,
      (∀ z, ‖(Ψ z).val‖ = ‖z.val.2‖) ∧ ∀ z, ‖z.val.2‖ = 1 ↔ ‖(Ψ z).val‖ = 1 := by
  have hk : finrank ℝ F = 3 := by
    rw [finrank_prod, h0, zero_add] at hd
    exact hd
  refine ⟨exists_euclidean_diffeomorph_totalSpace_of_subsingleton (IB := IB) (V := V) hk, ?_⟩
  obtain ⟨Ψ, hΨ, hbd⟩ :=
    exists_closedCell_diffeomorph_normClosedDisc_of_subsingleton (IB := IB) (V := V) hd h0 1 one_pos
  exact ⟨Ψ, fun z => by simpa only [one_mul] using hΨ z, hbd⟩

end Point

section Circle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

/-- **The circle clause of LFR51** (`S¹ | S¹ × ℝ² | S¹ × D²`). For a smooth Riemannian rank-two
bundle over `S¹ = AddCircle 1` with an oriented total space: `Ê ≅ S¹ × ℝ²` over the identity of
`S¹`, preserving fibre norms, and the closed unit disc bundle (native boundary charts) is the fixed
solid torus `solidTorusCarrier`, its boundary torus `{cliffordHeight = 0}` going exactly onto the
unit sphere bundle. -/
theorem exists_circle_soul_bundle_type (hF : finrank ℝ F = 2)
    (oV : SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (TotalSpace F V)) :
    (∃ Φ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
        (AddCircle (1 : ℝ) × E2) (TotalSpace F V) ∞,
      (∀ p, (Φ p).proj = p.1) ∧ ∀ p, ‖(Φ p).2‖ = ‖p.2‖) ∧
    letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V)
      (finrank_real_prod_eq_three hF) 1 one_pos
    ∃ Ψ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
        (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
        {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
      ∀ x : GC.GraphManifold.solidTorusCarrier.{u}.Carrier,
        GC.GraphManifold.cliffordHeight (x : GC.GraphManifold.solidTorusSet.{u}).val = 0 ↔
          ‖(Ψ x).val.2‖ = 1 := by
  obtain ⟨Φ₀, hproj, hnorm⟩ := exists_normPreserving_trivialization_of_orientable_totalSpace_circle hF oV
  refine ⟨⟨(trivialProdDiffeomorph 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) E2).trans Φ₀,
    fun p => hproj _, fun p => hnorm _⟩, ?_⟩
  have hd := finrank_real_prod_eq_three hF
  let csNorm_LFR54ROW := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos
  obtain ⟨Ψ⟩ := nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orientable.{u} hF oV
  refine ⟨Ψ, fun x => ?_⟩
  have h1 := GC.GraphManifold.solidTorus_isBoundaryPoint_iff.{u} x
  have h2 : GC.GraphManifold.solidTorusCarrier.{u}.model.IsBoundaryPoint x ↔
      (morseModelWithCornersHalfSpace 2).IsBoundaryPoint (Ψ x) :=
    (Ψ.isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)
  have h3 := normClosedDiscBundle_boundary_iff (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos (Ψ x)
  exact h1.symm.trans (h2.trans h3)

end Circle

/-- **Row LFR51 (orientation determines the finite soul bundle types).** The table (LFR51.1) on the
bundle side, as smooth bundle identifications including the closed unit disc bundles with their
boundaries, one clause per soul dimension:
1. point soul: `Ê ≅ ℝ³`, `D(Ê) ≅ D³ = ClosedCell 3` (norm to norm);
2. circle soul (oriented total space): `Ê ≅ S¹ × ℝ²` over the identity, norm-preserving,
   `D(Ê) ≅ S¹ × D² = solidTorusCarrier`, boundary torus onto the unit sphere bundle;
3. surface soul (oriented total space, `C^n` base metric of `K ≥ 0`): `S² × ℝ`, flat `T² × ℝ` (with
   `D(Ê)` the closed disc bundle of the trivial line), `o(ℝP²)` (base `≅ ℝP²`) or `o(K)` (base the
   Klein double cover), the twisted ones with (LFR51.2) and the absolute-value fibre norm. -/
theorem lfr51_oriented_finite_soul_bundle_types :
    (∀ {EB : Type uEB} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
      {HB : Type uHB} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
      [IsContMDiffRiemannianBundle IB ∞ F V] [Subsingleton B] [Nonempty B]
      (hd : finrank ℝ (EB × F) = 2 + 1), finrank ℝ EB = 0 →
      (∃ Φ : Diffeomorph (IB.prod 𝓘(ℝ, F)) (𝓡 3) (TotalSpace F V) E3 ∞,
        ∀ z, ‖Φ z‖ = ‖z.2‖) ∧
      letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
      ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {z : TotalSpace F V // ‖z.2‖ ≤ 1} (ClosedCell 3) ∞,
        (∀ z, ‖(Ψ z).val‖ = ‖z.val.2‖) ∧ ∀ z, ‖z.val.2‖ = 1 ↔ ‖(Ψ z).val‖ = 1) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {V : AddCircle (1 : ℝ) → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
      [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]
      (hF : finrank ℝ F = 2), SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      (∃ Φ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
          (AddCircle (1 : ℝ) × E2) (TotalSpace F V) ∞,
        (∀ p, (Φ p).proj = p.1) ∧ ∀ p, ‖(Φ p).2‖ = ‖p.2‖) ∧
      letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V)
        (finrank_real_prod_eq_three hF) 1 one_pos
      ∃ Ψ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
          (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
          {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
        ∀ x : GC.GraphManifold.solidTorusCarrier.{u}.Carrier,
          GC.GraphManifold.cliffordHeight (x : GC.GraphManifold.solidTorusSet.{u}).val = 0 ↔
            ‖(Ψ x).val.2‖ = 1) ∧
    (∀ {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      {B : Type uB} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
      {V : B → Type uV} [TopologicalSpace (TotalSpace F V)]
      [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
      [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
      [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V] [CompactSpace B] [ConnectedSpace B] [T2Space B]
      (hd : finrank ℝ (E2 × F) = 2 + 1),
      SmoothOrientation ((𝓡 2).prod 𝓘(ℝ, F)) (TotalSpace F V) →
      ∀ {n : ℕ∞ω}, (2 : ℕ∞ω) ≤ n →
      ∀ (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : B → Type _)),
      (∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) →
      (¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} ∧
        ∃ Ψ : (S2 × E1) ≃ₘ⟮(𝓡 2).prod (𝓡 1), (𝓡 2).prod 𝓘(ℝ, F)⟯ TotalSpace F V,
          (∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∧
          letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := Trivial S2 E1)
            finrank_euclideanTwo_prod_one 1 one_pos
          letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
          ∃ Ψ' : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
              {z : TotalSpace E1 (Trivial S2 E1) // ‖z.2‖ ≤ 1}
              {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
            ∀ z, (Ψ' z).val = Ψ (z.val.proj, z.val.2)) ∨
      (¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1} ∧
        (∀ (b : B) (v w : TangentSpace (𝓡 2) b), k.sectionalCurvature b v w = 0) ∧
        ∃ Ψ : (T2 × E1) ≃ₘ⟮(𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 1), (𝓡 2).prod 𝓘(ℝ, F)⟯
            TotalSpace F V,
          (∀ z, ‖(Ψ z).2‖ = ‖z.2‖) ∧
          letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
            (V := Trivial T2 E1) finrank_real_prod_real_prod_one 1 one_pos
          letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
          ∃ Ψ' : Diffeomorph (morseModelWithCornersHalfSpace 2) (morseModelWithCornersHalfSpace 2)
              {z : TotalSpace E1 (Trivial T2 E1) // ‖z.2‖ ≤ 1}
              {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
            ∀ z, (Ψ' z).val = Ψ (z.val.proj, z.val.2)) ∨
      (∃ ν : S2 → TotalSpace F V, ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
        (∀ x, ‖(ν x).2‖ = 1) ∧ Injective ν ∧
        (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) ∧
        (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) ∧
        IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj) ∧
        (∃ h : Diffeomorph (𝓡 2) (𝓡 2) B RP2 ∞, ∀ x, h (ν x).proj =
          DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj
            x) ∧
        ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ (rankOneParam ν) ∧
        Surjective (rankOneParam ν) ∧
        (∀ q q' : S2 × ℝ, rankOneParam ν q' = rankOneParam ν q ↔ q' = q ∨ q' = (-q.1, -q.2)) ∧
        ∀ q : S2 × ℝ, ‖(rankOneParam ν q).2‖ = |q.2|) ∨
      (∃ ν : T2 → TotalSpace F V,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
        (∀ p, ‖(ν p).2‖ = 1) ∧ Injective ν ∧
        (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) ∧
        (∀ x y : AddCircle (1 : ℝ),
          ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩) ∧
        IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj) ∧
        Surjective (fun p => (ν p).proj) ∧
        (∀ p p' : T2, (ν p').proj = (ν p).proj ↔
          p' = p ∨ p' = (p.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -p.2)) ∧
        ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞
          (rankOneParam ν) ∧
        Surjective (rankOneParam ν) ∧
        (∀ q q' : T2 × ℝ, rankOneParam ν q' = rankOneParam ν q ↔
          q' = q ∨ q' = ((q.1.1 + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -q.1.2), -q.2)) ∧
        ∀ q : T2 × ℝ, ‖(rankOneParam ν q).2‖ = |q.2|)) :=
  ⟨fun hd h0 => exists_point_soul_bundle_type hd h0,
    fun hF oV => exists_circle_soul_bundle_type.{u} hF oV,
    fun hd oN _ hn k hK => exists_surface_soul_bundle_type hd oN hn k hK⟩

end DifferentialGeometry.Geometry.Collapse.ZeroModel
