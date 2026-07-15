import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldDifferentiatedTowerNormalForm

/-! # The differentiated fixed-coefficient metric-contraction tower and its iterated-gradient grid

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file builds — for a fixed smooth `(r, r)`-operator coefficient field (the
inverse-Gram / metric-contraction symbol baked in) — the recursive differentiated-operator tower,
packaged as a `DiffBilinOp` (the abstract differentiated bilinear-contraction engine of
`MetricContractionLeibnizGrid`), and applies the engine's *proved* binomial covariant-Leibniz grid to
obtain the iterated-covariant-gradient `rfns` (intrinsic squared Riemannian fibre norm) bound — the
Moser-tame estimate the order-`m` jet induction of the Ricci–DeTurck right-hand side consumes for its
metric-built term.

## Why a *unary* tower with a baked-in coefficient (and not the bilinear contraction product)

The bilinear cometric double-trace contraction product `gInvGramProdSection`
(`RicciDeTurckLinearization`) does **not** satisfy the front-slot covariant Leibniz `covGrad_prod` as
literally stated: the gradient of a *contraction* lands in the contracted slots, so the naive bilinear
Leibniz identity is false-as-stated (the gradient is contracted away).  The curvature arm
(`pureRGenuineDiffOp`, `FrozenFramePureRCurvatureTower`) solved the structurally-identical problem by
going *unary*: the contracted coefficient (there the Riemann curvature `R`; here the inverse-Gram
symbol) is BAKED INTO the operator as a fixed smooth operator field `Φ₀ r`, leaving a unary
`SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)` family whose differentiated tower is the exact
covariant-Leibniz remainder — so the gradient passenger rides the FRONT via `op (p + 1)`, never
contracted away.  This file replicates that proven curvature pattern for the metric arm.

## The genuine mathematical input

The single genuine *mathematical input* a working geometer supplies is a fixed smooth `(r, r)`-operator
coefficient field `Φ₀ : ∀ r, SmoothCcTensor g (r + 0) (r + 0)` — exactly as the curvature arm SUPPLIES
its smooth curvature endomorphism field (`exists_pureRGenuineDiffOp_base_appCc`) and the abstract engine
(`normalForm_of_base`) CONSUMES it.  For the inverse-Gram metric arm this `Φ₀ r` is the per-rank smooth
cometric / inverse-Gram fibre endomorphism (its C⁰ ball-uniformity is exactly the uniform fibre-norm
bound of the fixed smooth field).  Stating the tower against the *coefficient field* (rather than
re-deriving a concrete `slotInsertEndoFib` witness here) keeps this prototype decoupled and lets the
downstream consumer instantiate whichever concrete inverse-Gram symbol the linearization needs; the
existence of such a smooth field is the metric analogue of `exists_pureRGenuineDiffOp_base_appCc`.

## The construction (mirror of the curvature tower)

* `fixedCoeffTowerOp Φ₀` — the order-`p` differentiated operator, defined recursively: at `p = 0` the
  operator-field action `appCc (Φ₀ r) W` of the baked-in coefficient; at `p + 1` the exact
  covariant-Leibniz remainder `∇(op p r W) − (rank-cast) op p (r + 1) (∇W)`.
* `fixedCoeffTower_covGrad_op` — the single-step covariant Leibniz, *proved* by `sub_add_cancel`.
* `fixedCoeffDiffOp Φ₀` — the packed `DiffBilinOp` instance: `op`/`covGrad_op` as above, and the
  per-order per-rank `rfns` jet envelope `kappa`/`rfns_op_le` obtained — **with no posit of its own** —
  from the abstract operator-field normal-form engine (`normalForm_of_base`,
  `exists_jet_bound_of_normalForm`) applied to the fixed-coefficient base factorisation.

## Main result

* `fixedCoeffDiffOp_iteratedCovGrad_singleSum_le` — the engine's single-sum collapse applied to
  `fixedCoeffDiffOp Φ₀`: at every gradient order `a`, base rank `r`, section `W`, and point `x`,
  ```
  rfns(∇^a (fixedCoeffDiffOp.op 0 r W))(x) ≤ C r a · ∑_{q ≤ a} rfns(∇^q W)(x),
  ```
  the metric-arm Moser-tame `rfns` grid, with the inverse-Gram coefficient C⁰ envelope absorbed into
  the engine constant `C r a` (exactly as the curvature derivatives ride inside the curvature arm's
  constant).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## The differentiated fixed-coefficient metric-contraction tower -/

/-- **The order-`p` differentiated fixed-coefficient metric-contraction operator.** Acting on a smooth
compactly-supported `(0, r)`-tensor section `W`, the `p`-times covariantly-differentiated metric
contraction with its coefficient field `Φ₀` baked in, defined recursively as the exact covariant-Leibniz
remainder:

* `p = 0`: the operator-field action `appCc (Φ₀ r) W` of the fixed, baked-in coefficient field;
* `p + 1`: `∇(op p r W) − (rank-cast) op p (r + 1) (∇W)` — the differentiated coefficient remainder (the
  input section's derivative `∇W` cancels), rank-cast `(r + 1) + p = r + (p + 1)`.

By construction the single-step covariant Leibniz holds by `sub_add_cancel`.  Because the coefficient is
the fixed smooth field, the differentiated tower differentiates only the coefficient, never a frame jet
— the same sound shape as `pureRGenuineDiffOp`. -/
def fixedCoeffTowerOp (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0)) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W =>
      appCc (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (fixedCoeffTowerOp g Φ₀ p r W) -
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (fixedCoeffTowerOp g Φ₀ p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

/-- **The exact single-step covariant Leibniz of the differentiated fixed-coefficient tower.**  By the
recursive definition, `∇(op p r W)` splits exactly into the higher-order remainder `op (p + 1) r W` and
the rank-cast lower-order term applied to `∇W`.  Proved by `sub_add_cancel` (the passenger gradient
rides the FRONT through `op (p + 1)`, never contracted away — the defect that breaks the bilinear
product). -/
theorem fixedCoeffTower_covGrad_op (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p)
        (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p r W) =
      fixedCoeffTowerOp (I := I) (M := M) g Φ₀ (p + 1) r W +
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p)
      (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p r W) -
      castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
        (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

/-- **The order-`0` base factorisation: the fixed-coefficient tower at order `0` is the
operator-field action of `Φ₀`.**  Definitional. -/
theorem fixedCoeffTower_base_appCc (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (r : ℕ) (W : SmoothCcTensor g 0 r) :
    fixedCoeffTowerOp (I := I) (M := M) g Φ₀ 0 r W =
      appCc (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W :=
  rfl

/-! ## The packed `DiffBilinOp` instance -/

/-- **The differentiated fixed-coefficient metric-contraction tower, packaged as a `DiffBilinOp`.**
The `op`/`covGrad_op` fields are the recursive tower and its `sub_add_cancel` Leibniz; the per-order
per-rank `rfns` jet envelope (`kappa`/`kappa_nonneg`/`rfns_op_le`) is obtained — **with no posit of its
own** — from the abstract operator-field normal-form engine
(`normalForm_of_base`, `exists_jet_bound_of_normalForm`) applied to the fixed-coefficient base
factorisation `fixedCoeffTower_base_appCc`: the normal form propagates the base `appCc Φ₀` up the tower,
and each differentiated coefficient is a fixed smooth operator field with a uniform fibre-norm bound
(`exists_uniform_riemannianFiberNormSq_appCc_le`), so the jet envelope is uniform over the compact `M`.
The inverse-Gram coefficient's C⁰ ball-uniformity is exactly the uniform bound of `Φ₀`, absorbed into
`kappa`. -/
def fixedCoeffDiffOp (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0)) :
    DiffBilinOp (I := I) (M := M) g :=
  let op := fixedCoeffTowerOp (I := I) (M := M) g Φ₀
  let covGrad_op := fixedCoeffTower_covGrad_op (I := I) (M := M) g Φ₀
  let hNF : ∀ (p r : ℕ), NormalForm (I := I) (M := M) g op p r :=
    fun p => normalForm_of_base (I := I) (M := M) g op covGrad_op Φ₀
      (fun r W => fixedCoeffTower_base_appCc (I := I) (M := M) g Φ₀ r W) p
  { op := op
    covGrad_op := covGrad_op
    kappa := fun p r => Classical.choose
      (exists_jet_bound_of_normalForm (I := I) (M := M) g op p r (hNF p r))
    kappa_nonneg := fun p r =>
      (Classical.choose_spec
        (exists_jet_bound_of_normalForm (I := I) (M := M) g op p r (hNF p r))).1
    rfns_op_le := fun p r W x =>
      (Classical.choose_spec
        (exists_jet_bound_of_normalForm (I := I) (M := M) g op p r (hNF p r))).2 W x }

/-! ## The iterated-covariant-gradient `rfns` grid (the metric-arm Moser tame) -/

set_option linter.unusedSectionVars false in
/-- **The metric-arm Moser-tame `rfns` grid.**  Applying the engine's single-sum collapse
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at` to the fixed-coefficient tower
`fixedCoeffDiffOp Φ₀`: at every base point `x`, gradient order `a`, base rank `r`, and section `W`, the
intrinsic squared Riemannian fibre norm of the `a`-th iterated covariant gradient of the order-`0`
metric contraction is bounded by a single nonnegative per-rank, per-order constant
`C r a := 4^a · gridWindowSum (fixedCoeffDiffOp Φ₀).kappa 0 r a` times the order-`≤ a` covariant jet of
`W`:
```
rfns(∇^a (fixedCoeffDiffOp.op 0 r W))(x) ≤ C r a · ∑_{q ≤ a} rfns(∇^q W)(x).
```
The inverse-Gram coefficient's C⁰ envelope rides inside `C r a` (through `kappa`), exactly as the
curvature derivatives ride inside the curvature arm's constant.  This is the shape the order-`m` jet
induction and the intrinsic Moser-tame product of the Ricci–DeTurck right-hand side consume for the
metric-built term. -/
theorem fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (x₀ : M) (r : ℕ) (W : SmoothCcTensor g 0 r) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + a) x₀
        ((iteratedCovGrad g 0 r a
          ((fixedCoeffDiffOp (I := I) (M := M) g Φ₀).op 0 r W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).kappa 0 r a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀) :=
  DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).op
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).covGrad_op
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).kappa
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).kappa_nonneg x₀
    (fun p r W => (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).rfns_op_le p r W x₀) r W a

end Connection
end Integral
end DifferentialGeometry

end
