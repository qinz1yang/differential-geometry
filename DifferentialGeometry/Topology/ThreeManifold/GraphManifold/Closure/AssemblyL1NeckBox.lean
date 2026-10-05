import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyBallHandleCycleApplications

/-!
# Chapter-14 assembly, item L1, group G3b: the closed neck box and the relative signs

Shared definitions of the four sub-statements of G3b (`BallHandleCycle.exists_cycleNormalForm`,
lane ASM-L1b; sub-statements frozen in `build-logs/scratch/ASM-L1b/Targets.lean`):

* `closedNeckDomain ε`: the closed neck box `{‖z‖ ≤ 1 + 2ε, |τ| ≤ 2ε}`. The necks of G3b are
  constructed on a neighbourhood of this compact box: a new handle (ball) must equal its neck on the
  OPEN end strip (cap region) and be smooth on the CLOSED cell, so the neck must extend across the
  far side of the strip.
* `restrictNeck`: the restriction of a partial diffeomorphism to an open part of its source (the
  necks of `CycleNormalForm` have source exactly `neckDomain ε`).
* `handleNeckDet`, `ballNeckDet`: the determinant of a neck differential read through the inverse
  differential of an edge handle (resp. of a ball read in `ClosedCell 3`). The orientation of the
  carrier enters G3b only through the signs of these determinants.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1b : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance ballCharts_ASML1b : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The closed neck box at scale `ε`. -/
def closedNeckDomain (ε : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {q | ‖q.1‖ ≤ 1 + 2 * ε ∧ |q.2| ≤ 2 * ε}

theorem isOpen_neckDomain (ε : ℝ) : IsOpen (neckDomain ε) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem isClosed_closedNeckDomain (ε : ℝ) : IsClosed (closedNeckDomain ε) :=
  (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
    (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)

theorem isCompact_closedNeckDomain (ε : ℝ) : IsCompact (closedNeckDomain ε) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 + 2 * ε)).prod
    (isCompact_closedBall (0 : ℝ) (2 * ε)) |>.of_isClosed_subset (isClosed_closedNeckDomain ε)
  rintro q ⟨h1, h2⟩
  exact ⟨mem_closedBall_zero_iff.mpr h1, mem_closedBall_zero_iff.mpr (by simpa using h2)⟩

theorem neckDomain_subset_closedNeckDomain (ε : ℝ) : neckDomain ε ⊆ closedNeckDomain ε :=
  fun _ hq => ⟨hq.1.le, hq.2.le⟩

/-- The restriction of a partial diffeomorphism to `Φ.source ∩ s`, `s` open. -/
def restrictNeck {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
    (Φ : PartialDiffeomorph I I' M M' ∞) (s : Set M) (hs : IsOpen s) :
    PartialDiffeomorph I I' M M' ∞ where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen s hs).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen s hs).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen s hs).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left

section restrictNeck

variable {E E' H H' M M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  (Φ : PartialDiffeomorph I I' M M' ∞) {s : Set M} (hs : IsOpen s)

theorem restrictNeck_apply (x : M) : restrictNeck Φ s hs x = Φ x :=
  rfl

theorem restrictNeck_source : (restrictNeck Φ s hs).source = Φ.source ∩ s :=
  rfl

theorem restrictNeck_source_of_subset (hsub : s ⊆ Φ.source) : (restrictNeck Φ s hs).source = s :=
  inter_eq_right.mpr hsub

theorem restrictNeck_target_subset : (restrictNeck Φ s hs).target ⊆ Φ.target :=
  inter_subset_left

end restrictNeck

/-- `ℝ² × ℝ¹ ≃ ℝ² × ℝ` (the tangent space of the handle model and the neck space). -/
def cylTangentEquiv :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
    ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ))

/-- The determinant of `(dH_q)⁻¹ ∘ L` (read in `ℝ² × ℝ`): the orientation of a neck differential
`L` relative to the handle `H` at `q`. -/
def handleNeckDet {W : CompactCarrier.{u}} (H : EdgeHandle W) (q : ClosedCell 2 × Icc (0 : ℝ) 1)
    (L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  LinearMap.det ((cylTangentEquiv : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ)) ∘ₗ
    ((LinearEquiv.ofBijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model H.map q).toLinearMap
      (H.mfderiv_bijective q)).symm.toLinearMap ∘ₗ L.toLinearMap))

/-- A fixed identification `ℝ³ ≃ ℝ² × ℝ` (only signs of determinants computed with it are used). -/
def neckSpaceEquiv : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  LinearEquiv.ofFinrankEq _ _ (by simp)

/-- The determinant of `de_{e⁻¹x} ∘ (dB_{e⁻¹x})⁻¹ ∘ L ∘ J` (`J = neckSpaceEquiv`): the orientation of
a neck differential `L` relative to the ball `B ∘ e⁻¹` (read in `ClosedCell 3`) at `x`. -/
def ballNeckDet {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (x : ClosedCell 3)
    (L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  LinearMap.det ((mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm x)).toLinearMap ∘ₗ
    (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).toLinearMap
      (B.mfderiv_bijective (e.symm x))).symm.toLinearMap ∘ₗ L.toLinearMap ∘ₗ
    neckSpaceEquiv.toLinearMap)

end GC.GraphManifold.Assembly
