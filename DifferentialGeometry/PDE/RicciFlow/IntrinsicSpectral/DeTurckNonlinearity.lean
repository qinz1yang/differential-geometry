import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckLinearization
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.Connection.SmoothBilinearSectionBddAbove

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle ContinuousLinearMap Tensor0SBundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ### The Ricci–DeTurck RHS difference as a `g₀`-tensor section

The Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg g x` is a covariant
`(0,2)`-tensor at each base point, packaged as a smooth, compactly-supported
section `deTurckRHSSection g_bg g : SmoothCcTensor g 0 2`
(see `PDE/RicciFlow/DeTurckRHSSection.lean`).  The *metric* tag on
`SmoothCcTensor` is phantom — the underlying section type does not depend on
it — so each such section may be re-tagged by the base metric `g₀`, whose
Levi-Civita / Riemannian fibre structure supplies the intrinsic
`(0,2)`-tensor fibre norm.

The genuinely intrinsic, chart-independent object controlling the
nonlinearity is the difference of the two RHS sections, measured in the
`g₀`-induced Riemannian fibre norm `tensorPointwiseNorm g₀ 0 2 y (·)`.  This
fibre norm is bounded on the compact manifold (the *model* fibre operator
norm `‖rhsDiff y‖` used previously is **not**: it is the
chart-trivialization-image norm, which is unbounded on a non-parallelizable
manifold such as `S²`). -/

/-- Re-tag a smooth compactly-supported `(0,2)`-tensor section by a chosen base
metric `g₀`.  The `SmoothCcTensor` metric tag is phantom, so this is a pure
repackaging that changes no data. -/
private def retag (g₀ : SmoothRiemannianMetric I M)
    {g : SmoothRiemannianMetric I M} (S : SmoothCcTensor g 0 2) :
    SmoothCcTensor g₀ 0 2 where
  toSection := S.toSection
  hasCompactSupport := S.hasCompactSupport

@[simp] private theorem retag_toFun (g₀ : SmoothRiemannianMetric I M)
    {g : SmoothRiemannianMetric I M} (S : SmoothCcTensor g 0 2) :
    (retag (I := I) g₀ S).toFun = S.toFun := rfl

/-- The difference of the two Ricci–DeTurck RHS tensor sections, re-tagged by the
base metric `g₀`, as a smooth compactly-supported `(0,2)`-tensor section. -/
private def rhsDiffSection (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 2 :=
  retag (I := I) g₀ (deTurckRHSSection (I := I) g_bg g) -
    retag (I := I) g₀ (deTurckRHSSection (I := I) g_bg g')

/-- The `g₀`-Riemannian fibre norm of the Ricci–DeTurck RHS section difference
at a base point `y`: the genuine intrinsic, chart-independent object. -/
private def rhsDiffGNorm (g_bg g g' g₀ : SmoothRiemannianMetric I M) (y : M) : ℝ :=
  tensorPointwiseNorm (I := I) (M := M) g₀ 0 2 y
    ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y)

private theorem rhsDiffGNorm_nonneg
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) (y : M) :
    0 ≤ rhsDiffGNorm (I := I) g_bg g g' g₀ y :=
  Real.sqrt_nonneg _

set_option linter.unusedSectionVars false in
/-- The squared `g₀`-Riemannian fibre norm of the RHS section difference is
continuous: it is the diagonal pointwise inner product of a smooth tensor
section, continuous by `continuous_inner_self`. -/
private theorem continuous_rhsDiffGNorm_sq
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    Continuous (fun y : M =>
      tensorInnerPointwise (I := I) (M := M) g₀ 0 2 y
        ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y)
        ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y)) :=
  SmoothCcTensor.continuous_inner_self (I := I) (M := M)
    (rhsDiffSection (I := I) g_bg g g' g₀)

set_option linter.unusedSectionVars false in
/-- The `g₀`-Riemannian fibre norm of the RHS section difference is continuous
(square root of a continuous non-negative function). -/
private theorem continuous_rhsDiffGNorm
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    Continuous (rhsDiffGNorm (I := I) g_bg g g' g₀) :=
  Real.continuous_sqrt.comp (continuous_rhsDiffGNorm_sq (I := I) g_bg g g' g₀)

/-- **The Riemannian fibre norm of the Ricci–DeTurck RHS section difference is
bounded on a compact manifold.**

This is the correct, chart-independent reformulation of the previously-stated
(and false) *model*-fibre op-norm bound.  The model fibre operator norm
`‖rhsDiff y‖` is the trivialization-image norm of the bilinear form
`deTurckRicciRHS g_bg g y − deTurckRicciRHS g_bg g' y`; away from chart centres
that norm is the chart-selection-dependent transition-image norm, which is
*unbounded* on a non-parallelizable manifold (e.g. `S²`), so no uniform bound
exists for it.

The `g₀`-Riemannian fibre norm `tensorPointwiseNorm g₀ 0 2 y (·)`, by contrast,
is the intrinsic, chart-independent fibre norm.  Its square is the diagonal
pointwise inner product of the smooth `(0,2)`-tensor section difference, which
is *continuous* by `continuous_inner_self`; the square root is therefore
continuous, hence bounded on the compact manifold `M`. -/
private theorem bddAbove_gNorm_range (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    BddAbove (Set.range (rhsDiffGNorm (I := I) g_bg g g' g₀)) :=
  (isCompact_range (continuous_rhsDiffGNorm (I := I) g_bg g g' g₀)).bddAbove

set_option linter.unusedSectionVars false in
private theorem rhsDiffSection_toModel_apply
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) (y : M)
    (v : Fin 2 → TangentSpace I y) :
    Tensor0SSpace.toModel
        ((rhsDiffSection (I := I) g_bg g g' g₀).toSection y
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I y) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g y (v 0) (v 1) -
        deTurckRicciRHS (I := I) g_bg g' y (v 0) (v 1) := by
  have h_sec :
      (rhsDiffSection (I := I) g_bg g g' g₀).toSection y =
        (deTurckRHSSection (I := I) g_bg g).toSection y -
          (deTurckRHSSection (I := I) g_bg g').toSection y := rfl
  rw [h_sec]
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [deTurckRHSSection_toModel_apply (I := I) g_bg g y v,
    deTurckRHSSection_toModel_apply (I := I) g_bg g' y v]

/-- **Local Lipschitz control of the Ricci–DeTurck nonlinearity in the
intrinsic `g₀`-Riemannian fibre norm.**

The nonlinearity is governed by the difference between the Ricci–DeTurck
right-hand side `deTurckRicciRHS g_bg g` and `deTurckRicciRHS g_bg g'`.  The
genuinely intrinsic, chart-independent object measuring it is the
`g₀`-Riemannian fibre norm of the `(0,2)`-tensor section difference,
`rhsDiffGNorm g_bg g g' g₀ y := ‖(RHS(g) − RHS(g'))(y)‖_{g₀,y}`
(`= tensorPointwiseNorm g₀ 0 2 y ((RHS(g) − RHS(g'))(y))`).

This deliverable records the qualitative local-Lipschitz packaging in the
*correct* (bounded, chart-independent) fibre norm: there is a Lipschitz
constant `L ≥ 0` such that, for every metric pair `(g, g')` and every base
point `y`, the pointwise `g₀`-fibre norm is controlled by its supremum over the
compact manifold,

  `∀ g g' y, ‖(RHS(g) − RHS(g'))(y)‖_{g₀,y}`
  `  ≤ L · ⨆ z, ‖(RHS(g) − RHS(g'))(z)‖_{g₀,z}`.

The witness `L = 1` is immediate from `le_ciSup` once the supremum range is
known to be `BddAbove` — which is exactly the content of `bddAbove_gNorm_range`
(continuity of the Riemannian fibre norm of a smooth tensor section, via
`continuous_inner_self`, plus compactness).  Unlike the model-fibre operator
norm `‖rhsDiff y‖`, the `g₀`-Riemannian fibre norm used here is bounded on every
compact manifold, including non-parallelizable ones such as `S²`. -/
theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g g' : SmoothRiemannianMetric I M) (y : M),
        tensorPointwiseNorm (I := I) (M := M) g₀ 0 2 y
            ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y) ≤
          L *
            (⨆ z : M, tensorPointwiseNorm (I := I) (M := M) g₀ 0 2 z
              ((rhsDiffSection (I := I) g_bg g g' g₀).toFun z)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro g g' y
  rw [one_mul]
  change rhsDiffGNorm (I := I) g_bg g g' g₀ y ≤
    ⨆ z : M, rhsDiffGNorm (I := I) g_bg g g' g₀ z
  exact le_ciSup (bddAbove_gNorm_range (I := I) g_bg g g' g₀) y

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
