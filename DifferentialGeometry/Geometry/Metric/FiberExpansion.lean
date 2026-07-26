import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.unusedSectionVars false

/-!
# Fiberwise expansion in a `g`-orthonormal family

Any tangent vector expands in **any** given `g`-orthonormal family of full
cardinality: `v = ∑ i, g.inner x (e i) v • e i`.  This is the pointwise
fiber-linear-algebra input of the Jacobi frame reduction (brick J-a of the
option-1 route in `Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`): the
curvature term `R(·, γ̇)γ̇` is expanded in the parallel frame to produce the
frame-coordinate Jacobi system.

Unlike `tangent_frame_expansion`
(`Analysis/Elliptic/…/RiemannianFiberNormSqRiemannOpVWFactorBound.lean`),
which chooses its own frame, the family here is **supplied** — e.g. the
parallel frame of `exists_intrFrame` evaluated at a point of the geodesic.

The proof installs the honest inner-product structure of `g` on the fiber
(`g.toRiemannianMetric.toCore` + `InnerProductSpace.ofCoreOfTopology`, the
same `letI` chain as `exists_gOrthonormalBasis`), under which the family is
orthonormal of full cardinality, hence an `OrthonormalBasis`; the expansion
is `OrthonormalBasis.sum_repr'`.
-/

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Expansion in a supplied full `g`-orthonormal family.**  If
`e : ι → TangentSpace I x` is `g`-orthonormal and `card ι = finrank`, then
every tangent vector at `x` is `∑ i, g.inner x (e i) v • e i`. -/
theorem gON_expand (g : SmoothRiemannianMetric I M) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (e : ι → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ (TangentSpace I x))
    (v : TangentSpace I x) :
    v = ∑ i, g.inner x (e i) v • e i := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) :=
    g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun w : TangentSpace I x => cd.inner w w) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {w : TangentSpace I x |
      RCLike.re (cd.inner w w) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have hinner_eq : ∀ u w : TangentSpace I x,
      (inner ℝ u w : ℝ) = g.inner x u w := fun _ _ => rfl
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner_eq (e i) (e j)]
    exact hON i j
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    have hb := (basisOfOrthonormalOfCardEqFinrank hon hcard).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at hb
    exact hb.ge
  set ob : OrthonormalBasis ι ℝ (TangentSpace I x) :=
    OrthonormalBasis.mk hon hsp with hob
  have hcoe : ∀ i, ob i = e i := fun i => by
    rw [hob, OrthonormalBasis.coe_mk]
  have hrepr : ∑ i, (inner ℝ (ob i) v : ℝ) • ob i = v :=
    OrthonormalBasis.sum_repr' ob v
  calc v = ∑ i, (inner ℝ (ob i) v : ℝ) • ob i := hrepr.symm
    _ = ∑ i, g.inner x (e i) v • e i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoe i, hinner_eq (e i) v]

end DifferentialGeometry
