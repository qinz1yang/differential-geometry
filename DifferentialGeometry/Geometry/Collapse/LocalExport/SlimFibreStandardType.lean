import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreDiffeomorph
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreSmoothType
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget

/-!
# The original slim zero fibre is the STANDARD smooth `S²` or `T²` (review 70, D70-2)

Lane C14-SLIM-STD, group 1 (external review 70 §3.2, disposition D70-2). The deterministic adapter
between LFR20-CMP's smooth classification of the zero fibre
(`slimSurfaceFactor_zeroFibre_diffeomorph`, round sphere or `AddCircle 1 × AddCircle 1`) and the
standard models of the FC39 certificate (`ClosureSphere = ULift SphereTwo` with model `𝓡 2`;
`Torus = Circle × Circle` with `torusModel = (𝓡 1).prod (𝓡 1)`).

* `sphereClosureSphereDiffeomorph_SSTD`: the round sphere `sphere (0 : ℝ³) 1` and `ClosureSphere`
  (`uliftDiffeomorph`).
* `addTorusDiffeomorph_SSTD`: `AddCircle 1 × AddCircle 1` (model `𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)`) and
  `Torus` (model `torusModel`), the product of two `AddCircle.diffeomorphCircle` (written out:
  Mathlib's `Diffeomorph.prodCongr` asks both second factors to share one model vector space).
* `SlimChart.zero_fibre_standard_type_SSTD` (D70-2): for a slim chart `c`, `K ≥ 5`, `Δ ≥ 1`, ANY
  product model `P : SlimProductModel c K` and ANY surface factor `Q : SlimSurfaceFactor P`, the
  zero fibre `F₀` of C14-FIBRE-PRE (`slabMap_FPRE` over `zeroPoint_FPRE`, with
  `fibreChartedSpace_FPRE`, i.e. the SAME regular-fibre structure of `realSlabMap` that LFR20-CMP
  uses) is smoothly diffeomorphic to `ClosureSphere` or to `Torus`.

The hypothesis is `1 ≤ Δ` (LFR20-CMP's), not `0 < Δ`.

Consumer: `SlimChart.exists_standard_level_embedding_SSTD` — EVERY whole level set
`{x ∈ B(p, L) | η x = a}`, `|a| < 905·10³Δ`, is the exact image of a smooth embedding
(`IsSmoothEmbedding`) of the standard `ClosureSphere`, or every one of the standard `Torus`
(FPRE's `exists_embedding_fibre_FPRE` composed with the inverse standard identification,
`isSmoothEmbedding_comp_diffeomorph_symm_SSTD`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Metric WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold GC.MetricGeometry
open GC.GraphManifold GC.Endpoint

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The model of the slim fibres (`dim M - 1`). -/
local notation "𝓘S" => 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

local instance nezero_finrank_euclideanThree_SSTD : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u

/-- **Model adapter, sphere**: the round sphere `sphere (0 : ℝ³) 1` and the standard
`ClosureSphere = ULift SphereTwo` of the FC39 certificate. -/
def sphereClosureSphereDiffeomorph_SSTD :
    Metric.sphere (0 : E3) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u} :=
  uliftDiffeomorph (𝓡 2) SphereTwo

/-- **Model adapter, torus**: `AddCircle 1 × AddCircle 1` (model `𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)`) and the
standard `Torus = Circle × Circle` (model `torusModel`). -/
def addTorusDiffeomorph_SSTD :
    (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), torusModel⟯ Torus :=
  { toEquiv := AddCircle.diffeomorphCircle.toEquiv.prodCongr AddCircle.diffeomorphCircle.toEquiv
    contMDiff_toFun := (AddCircle.diffeomorphCircle.contMDiff.comp contMDiff_fst).prodMk
      (AddCircle.diffeomorphCircle.contMDiff.comp contMDiff_snd)
    contMDiff_invFun := (AddCircle.diffeomorphCircle.symm.contMDiff.comp contMDiff_fst).prodMk
      (AddCircle.diffeomorphCircle.symm.contMDiff.comp contMDiff_snd) }

/-- An embedding of a standard model through a diffeomorphism: if `ι : F → M` is smooth, a
topological embedding with injective differential, and `d : F ≃ₘ S`, then `ι ∘ d⁻¹ : S → M` is a
smooth embedding (into a boundaryless `N`) with the same image. -/
theorem isSmoothEmbedding_comp_diffeomorph_symm_SSTD {EF HF ES HS EN HN : Type*}
    [NormedAddCommGroup EF] [NormedSpace ℝ EF] [NormedAddCommGroup ES]
    [NormedSpace ℝ ES] [FiniteDimensional ℝ ES] [Nontrivial ES] [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [FiniteDimensional ℝ EN] [TopologicalSpace HF] [TopologicalSpace HS]
    [TopologicalSpace HN] {IF : ModelWithCorners ℝ EF HF} {IS : ModelWithCorners ℝ ES HS}
    {IN : ModelWithCorners ℝ EN HN} [IS.Boundaryless] [IN.Boundaryless]
    {F S N : Type*} [TopologicalSpace F] [ChartedSpace HF F]
    [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S]
    [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
    (ι : F → N) (hι : ContMDiff IF IN ∞ ι) (hemb : Topology.IsEmbedding ι)
    (hinj : ∀ y, Injective (mfderiv IF IN ι y)) (d : F ≃ₘ⟮IF, IS⟯ S) :
    IsSmoothEmbedding IS IN ∞ (ι ∘ d.symm) ∧ range (ι ∘ d.symm) = range ι := by
  refine ⟨isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp)
    (hι.comp d.symm.contMDiff) (hemb.comp d.symm.toHomeomorph.isEmbedding) (fun y => ?_)
    (fun _ => BoundarylessManifold.isInteriorPoint), d.symm.surjective.range_comp ι⟩
  have hιd : MDifferentiableAt IF IN ι (d.symm y) := (hι _).mdifferentiableAt (by simp)
  have hdd : MDifferentiableAt IS IF d.symm y := d.symm.contMDiff.contMDiffAt.mdifferentiableAt
    (by simp)
  rw [mfderiv_comp y hιd hdd]
  exact (hinj (d.symm y)).comp (d.symm.mfderivToContinuousLinearEquiv (by simp) y).injective

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **D70-2: the zero fibre of C14-FIBRE-PRE is the standard smooth `S²` or `T²`.** For a slim
chart `c`, `K ≥ 5`, `Δ ≥ 1`, a product model `P : SlimProductModel c K` and a surface factor
`Q : SlimSurfaceFactor P`, the zero fibre `F₀ = {x // c.slabMap_FPRE (905·10³Δ) x = 0}` with its
regular-fibre smooth structure `c.fibreChartedSpace_FPRE` is diffeomorphic to `ClosureSphere` or to
`Torus` (LFR20-CMP's `slimSurfaceFactor_zeroFibre_diffeomorph` on the same fibre, composed with the
two model adapters). -/
theorem SlimChart.zero_fibre_standard_type_SSTD {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    (c : SlimChart g hEnorm Δ σ α) {K : ℕ} (hK : 5 ≤ K) (hΔ : 1 ≤ Δ)
    (P : SlimProductModel c K) (Q : SlimSurfaceFactor P) :
    letI := c.fibreChartedSpace_FPRE le_rfl
      (SlimChart.zeroPoint_FPRE (lt_of_lt_of_le zero_lt_one hΔ))
    Nonempty ({x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x =
        SlimChart.zeroPoint_FPRE (lt_of_lt_of_le zero_lt_one hΔ)} ≃ₘ⟮𝓘S, 𝓡 2⟯
          ClosureSphere.{u}) ∨
      Nonempty ({x // c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x =
        SlimChart.zeroPoint_FPRE (lt_of_lt_of_le zero_lt_one hΔ)} ≃ₘ⟮𝓘S, torusModel⟯ Torus) := by
  let _ := c.fibreChartedSpace_FPRE le_rfl
    (SlimChart.zeroPoint_FPRE (lt_of_lt_of_le zero_lt_one hΔ))
  obtain ⟨-, h⟩ := slimSurfaceFactor_zeroFibre_diffeomorph hK hΔ P Q
  rcases h with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · exact Or.inl ⟨d.trans sphereClosureSphereDiffeomorph_SSTD⟩
  · exact Or.inr ⟨d.trans addTorusDiffeomorph_SSTD⟩

/-- **Consumer: the standard parametrization of every whole level set.** Under the hypotheses of
`SlimChart.zero_fibre_standard_type_SSTD`, EITHER every whole level set
`{x ∈ B(p, L) | η x = a}`, `|a| < 905·10³Δ`, is the image of a smooth embedding of the standard
`ClosureSphere`, OR every one is the image of a smooth embedding of the standard `Torus` (one type
for all levels; the shape of FC39's `SlimFibre` constructors). -/
theorem SlimChart.exists_standard_level_embedding_SSTD {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    (c : SlimChart g hEnorm Δ σ α) {K : ℕ} (hK : 5 ≤ K) (hΔ : 1 ≤ Δ)
    (P : SlimProductModel c K) (Q : SlimSurfaceFactor P) :
    (∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ e : ClosureSphere.{u} → M,
      IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ e ∧
        range e = {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = a}) ∨
    (∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ e : Torus → M,
      IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ e ∧
        range e = {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = a}) := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  let _ := c.fibreChartedSpace_FPRE le_rfl (SlimChart.zeroPoint_FPRE hΔ0)
  have _ := regularFiberIsManifold (c.slabMap_FPRE (905 * 10 ^ 3 * Δ))
    (SlimChart.zeroPoint_FPRE hΔ0) (c.contMDiff_slabMap_FPRE _)
    (fun x _ => c.surjective_mfderiv_slabMap_FPRE le_rfl x)
  have hemb : ∀ a : ℝ, |a| < 905 * 10 ^ 3 * Δ → ∃ ι : {x //
      c.slabMap_FPRE (905 * 10 ^ 3 * Δ) x = SlimChart.zeroPoint_FPRE hΔ0} → M,
      ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧ Topology.IsEmbedding ι ∧
        (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
        range ι = {x | x ∈ ball p (10 ^ 6 * Δ) ∧ c.coord x = a} := fun a ha =>
    c.exists_embedding_fibre_FPRE hΔ0 ⟨a, mem_lineBallOpens_iff.mpr ha⟩
  rcases c.zero_fibre_standard_type_SSTD hK hΔ P Q with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · refine Or.inl fun a ha => ?_
    obtain ⟨ι, hι, he, hi, hr⟩ := hemb a ha
    obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD ι hι he hi d
    exact ⟨ι ∘ d.symm, h1, h2.trans hr⟩
  · refine Or.inr fun a ha => ?_
    obtain ⟨ι, hι, he, hi, hr⟩ := hemb a ha
    obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD ι hι he hi d
    exact ⟨ι ∘ d.symm, h1, h2.trans hr⟩

end DifferentialGeometry.Geometry.Collapse
