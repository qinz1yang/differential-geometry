import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.LiftedMetricSmoothness
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Riemannian structure on the universal cover

Equips the universal cover `UniversalCover M` of a smooth Riemannian
manifold `M` with its own smooth Riemannian metric, pulled back fiberwise
along `proj : UniversalCover M → M` (which is a local diffeomorphism by
the covering structure of `UniversalCover.proj_isCoveringMap`).

The pieces assembled here are:

* `UniversalCover.liftedMetric g` — the lifted `SmoothRiemannianMetric`
  on the universal cover. Fiberwise its inner product at `x'` is the inner
  product of `g` at the base point `proj x'`, under the chart identification
  of `T_{x'} (UniversalCover M)` with `T_{proj x'} M` along the local
  diffeomorphism `proj`.
* `UniversalCover.uc_pseudoEMetricSpace g` — the canonical
  `PseudoEMetricSpace` on the universal cover, built from
  `riemannianEDist` for the lifted bundle via Mathlib's
  `PseudoEMetricSpace.ofRiemannianMetric`. Mirrors Mathlib's pattern
  (`def` with the metric witness `g` and the model-with-corners `I`
  explicit) rather than `instance`, since the model-space parameters
  cannot be recovered from the conclusion type alone.
* `isRiemannianManifold g` — companion `theorem`: the
  `IsRiemannianManifold` predicate holds for the canonical
  `uc_pseudoEMetricSpace g`, by `rfl` on `riemannianEDist`.
* `uc_regularSpace` — the universal cover is a regular topological
  space (Hausdorff + locally compact ⇒ regular), discharging the
  `[RegularSpace (UC M)]` hypothesis of the principled API above.
* `UniversalCover.liftedMetric_inner_eq` — the pointwise statement that the
  lifted inner product at `x'` equals the base inner product `g.inner` at
  `proj x'`, i.e. the chart identification carries the base metric to the
  lifted metric at the level of fibre inner products (holds by `rfl`).
-/

open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

/-- **The lifted smooth Riemannian metric on the universal cover.**

For each `x' : UniversalCover M`, the fibre inner product at `x'` is the
inner product of `g` at the base point `proj x'`, transported via the
identification of `T_{x'} (UniversalCover M)` with `T_{proj x'} M` by the
local diffeomorphism `proj` (here both tangent spaces are the model space
`E`, so the fibre inner product is literally `g.inner (proj x')`).

Symmetry, positivity and `IsVonNBounded` inherit pointwise from `g`.
Smoothness of the assembled section is supplied by
`uc_liftedMetric_contMDiff` (see `LiftedMetricSmoothness.lean`), whose proof
reduces the cover-side `inCoordinates` representation to the base-side one
via `uc_hom_bundle_inCoordinates_pullback`. -/
noncomputable def liftedMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  inner x' := g.inner (proj x')
  symm x' v w := g.symm (proj x') v w
  pos x' v hv := g.pos (proj x') v hv
  isVonNBounded x' := g.isVonNBounded (proj x')
  contMDiff := uc_liftedMetric_contMDiff (I := I) (M := M) g

/-- **Principled pseudo-emetric construction on the universal cover.**

Mirrors Mathlib's `PseudoEMetricSpace.ofRiemannianMetric`: a `def` with
the lifted-metric witness `g` (and `I` via the section variable)
explicit rather than an `instance`, since the model-space parameters
cannot be recovered from the conclusion type alone.

Downstream consumers should invoke this via
`letI : PseudoEMetricSpace (UC M) := uc_pseudoEMetricSpace g` once they
have the lifted metric `g` in hand. By reducibility of Mathlib's
`ofRiemannianMetric`, the resulting `edist` is `riemannianEDist I`.

The body installs the auxiliary instances `RiemannianBundle`
(from `g.toRiemannianMetric`) and `IsContinuousRiemannianBundle` (from
the smooth-implies-continuous projection of `g`) so that Mathlib's
`ofRiemannianMetric` typechecks. -/
@[reducible] noncomputable def uc_pseudoEMetricSpace
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  letI : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  PseudoEMetricSpace.ofRiemannianMetric I _

/-- **`IsRiemannianManifold` for the universal cover.**

For a lifted metric `g` on `UniversalCover M`, under the `letI`-injected
`RiemannianBundle` and the canonical `uc_pseudoEMetricSpace g` structure
the `IsRiemannianManifold I (UniversalCover M)` predicate holds: its
defining equation `edist x y = riemannianEDist I x y` holds by `rfl`,
because `uc_pseudoEMetricSpace` is reducibly
`PseudoEMetricSpace.ofRiemannianMetric`. -/
theorem isRiemannianManifold
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    letI : RiemannianBundle
        (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) g
    IsRiemannianManifold I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  letI : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) g
  exact ⟨fun _ _ => rfl⟩

/-- **The universal cover is a regular topological space.**

`UniversalCover M` is Hausdorff (`instT2Space`, hence `R1Space`) and,
being a finite-dimensional smooth manifold, locally compact: its base
`M` is locally compact (`Manifold.locallyCompact_of_finiteDimensional`)
and local compactness pulls back along the covering projection
(`instLocallyCompactSpace`).  A weakly
locally compact `R1` space is regular
(`WeaklyLocallyCompactSpace` + `R1Space` → `RegularSpace`), so the
cover is regular.

This discharges the `[RegularSpace (UniversalCover M)]` hypothesis of
`uc_pseudoEMetricSpace` / `isRiemannianManifold`, with no extra
ambient assumptions beyond the manifold structure already in scope.

Supplied as a `theorem` (taking `I` explicitly) rather than an
`instance`, because the model-space data `E`, `H`, `I` cannot be
recovered from `UniversalCover M` alone — the same reason
`uc_pseudoEMetricSpace` is a `def`.  Consumers inject it via
`haveI := uc_regularSpace I`. -/
theorem uc_regularSpace (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  infer_instance

/-- **The lifted inner product equals the base inner product pulled back
along `proj`.**

For every `x' : UniversalCover M` and all `v w : E`, the lifted metric's
inner product `(liftedMetric g).inner x'` agrees with `g.inner (proj x')`.
This is the defining equation of `liftedMetric` (whose fibre inner product
is literally `g.inner (proj x')`), so it holds by `rfl`. It records, at the
level of fibre inner products, that the chart identification of the tangent
spaces carries the base metric to the lifted metric. -/
theorem liftedMetric_inner_eq (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ∀ (v w : E),
      g.inner (proj x') v w =
        (liftedMetric (I := I) g).inner x' v w :=
  fun _ _ => rfl

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
