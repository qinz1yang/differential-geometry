import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.PointwiseMixed
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Integral.L2.Hilbert.Inherited
import DifferentialGeometry.Integral.L2.Hilbert.DenseSubset
import DifferentialGeometry.Integral.L2.Hilbert.SimpLemmas
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective

/-!
# The connection Laplacian as a partially-defined operator on `L²`

For a closed Riemannian manifold `(M, g)`, this file defines the
connection (rough) Laplacian `Δ_∇` as an unbounded operator on the metric
`L²` Hilbert space `TensorL2 r s g`, with domain the image of the
smooth compactly-supported `(r, s)`-tensor sections under the canonical
embedding `SmoothCcTensor.toL2`.

## Main definitions

* `smoothCcToL2Submodule g r s` — the canonical `ℝ`-submodule of
  `TensorL2 r s g` cut out by the image of `SmoothCcTensor.toL2`.
* `connLaplacianL2Action g r s` — the underlying `ℝ`-linear map from
  `SmoothCcTensor g r s` to `TensorL2 r s g`, sending `T` to the `L²`
  embedding of `rawTensorConnLapSmooth g r s T`.
* `connLaplacianL2 g r s` — the partially-defined operator
  `TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g`, with domain
  `smoothCcToL2Submodule g r s`.

## Main results

* `connLaplacianL2_domain_eq` — the domain of `connLaplacianL2` agrees
  with the canonical `SmoothCcTensor` image submodule.
* `connLaplacianL2_apply_toL2` — on the embedded image of
  `T : SmoothCcTensor g r s`, the value of the operator is obtained by
  evaluating `connLaplacianL2Action` on a representative whose `L²`
  embedding agrees with that of `T`. The representative is supplied via
  the projective-module structure of the `L²`-image submodule (every
  `ℝ`-vector space is free, hence projective); on smooth representatives
  the value `connLaplacianL2Action g r s _` is the `L²`-embedding of the
  pointwise rough Laplacian.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- The canonical `ℝ`-submodule of `TensorL2 r s g` carved out by the
range of the dense embedding
`SmoothCcTensor.toL2 : SmoothCcTensor g r s →L[ℝ] TensorL2 r s g`. This is
the natural choice of domain for an unbounded operator that is initially
defined only on smooth, compactly-supported sections. -/
def smoothCcToL2Submodule (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Submodule ℝ (TensorL2 r s g) :=
  LinearMap.range
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)

set_option linter.unusedSectionVars false in
/-- The `ℝ`-linear map sending a smooth, compactly-supported
`(r, s)`-tensor section to the `L²`-embedding of its pointwise rough
Laplacian.

Concretely, the value at `T : SmoothCcTensor g r s` is
`SmoothCcTensor.toL2 (rawTensorConnLapSmooth g r s T)`, the canonical
`L²`-embedding of the bundled compactly-supported smooth section
obtained by applying the pointwise rough Laplacian `rawTensorConnLap` to
`T` and packaging the unconditional smoothness witness via
`tensorConnLaplacian_of_contMDiff`. -/
def connLaplacianL2Action (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] TensorL2 r s g where
  toFun T :=
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
      (rawTensorConnLapSmooth (I := I) g r s T)
  map_add' T₁ T₂ := by
    have h_lap_add :
        rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂) =
          rawTensorConnLapSmooth (I := I) g r s T₁ +
            rawTensorConnLapSmooth (I := I) g r s T₂ := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      have hsum :=
        tensorConnLaplacian_of_contMDiff_add (I := I) g r s T₁ T₂
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T₁.toSection z) T₁.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T₂.toSection z) T₂.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => (T₁ + T₂).toSection z)
            (T₁ + T₂).toSection.contMDiff_toFun) x
      have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T₁ + T₂)).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s (T₁ + T₂)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (T₁ + T₂).toSection z)
              (T₁ + T₂).toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T₁
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₁.toSection z)
              T₁.toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T₂
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T₂.toSection z)
              T₂.toSection.contMDiff_toFun)).toSection x := rfl
      have hsum_section :
          (rawTensorConnLapSmooth (I := I) g r s T₁ +
              rawTensorConnLapSmooth (I := I) g r s T₂).toSection x =
            (rawTensorConnLapSmooth (I := I) g r s T₁).toSection x +
              (rawTensorConnLapSmooth (I := I) g r s T₂).toSection x := by
        rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]
        rfl
      rw [hLHS, hsum_section, hRHS₁, hRHS₂]
      exact hsum
    rw [h_lap_add, SmoothCcTensor.toL2_add]
  map_smul' c T := by
    have h_lap_smul :
        rawTensorConnLapSmooth (I := I) g r s (c • T) =
          c • rawTensorConnLapSmooth (I := I) g r s T := by
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      have hsmul :=
        tensorConnLaplacian_of_contMDiff_smul (I := I) g r s c T
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => T.toSection z) T.toSection.contMDiff_toFun)
          (rawTensorConnLap_contMDiff (I := I) g r s
            (fun z : M => (c • T).toSection z)
            (c • T).toSection.contMDiff_toFun) x
      have hLHS : (rawTensorConnLapSmooth (I := I) g r s (c • T)).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s (c • T)
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => (c • T).toSection z)
              (c • T).toSection.contMDiff_toFun)).toSection x := rfl
      have hRHS : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
          (tensorConnLaplacian_of_contMDiff (I := I) g r s T
            (rawTensorConnLap_contMDiff (I := I) g r s
              (fun z : M => T.toSection z)
              T.toSection.contMDiff_toFun)).toSection x := rfl
      have hsmul_section :
          (c • rawTensorConnLapSmooth (I := I) g r s T).toSection x =
            c • (rawTensorConnLapSmooth (I := I) g r s T).toSection x := by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]
        rfl
      rw [hLHS, hsmul_section, hRHS]
      exact hsmul
    rw [h_lap_smul, SmoothCcTensor.toL2_smul]
    rfl

set_option linter.unusedSectionVars false in
@[simp] lemma connLaplacianL2Action_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    connLaplacianL2Action (I := I) g r s T =
      SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (rawTensorConnLapSmooth (I := I) g r s T) := rfl

set_option linter.unusedSectionVars false in
/-- The canonical surjection `SmoothCcTensor g r s →ₗ[ℝ] smoothCcToL2Submodule g r s`
obtained by codomain-restricting `SmoothCcTensor.toL2` to its image submodule. -/
def toL2RangeRestrict (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →ₗ[ℝ] smoothCcToL2Submodule (I := I) g r s :=
  LinearMap.rangeRestrict
    ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)).toLinearMap)

set_option linter.unusedSectionVars false in
/-- Surjectivity of `toL2RangeRestrict`: the codomain-restricted embedding
maps onto the entire image submodule, by construction of
`LinearMap.rangeRestrict`. -/
lemma toL2RangeRestrict_surjective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Surjective (toL2RangeRestrict (I := I) g r s) := by
  intro u
  obtain ⟨T, hT⟩ := u.property
  refine ⟨T, ?_⟩
  apply Subtype.ext
  exact hT

set_option linter.unusedSectionVars false in
/-- A linear right-inverse / section of `toL2RangeRestrict`. Every
`ℝ`-vector space is free (`Module.Free.of_divisionRing`), hence
projective; the projective lifting property applied to the surjection
`toL2RangeRestrict` yields a linear right-inverse. -/
def smoothCcSection (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] SmoothCcTensor g r s :=
  Classical.choose
    ((toL2RangeRestrict (I := I) g r s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (toL2RangeRestrict_surjective (I := I) g r s)))

set_option linter.unusedSectionVars false in
/-- The defining property of `smoothCcSection`: composing
`toL2RangeRestrict` after it gives the identity on
`smoothCcToL2Submodule`. -/
lemma toL2RangeRestrict_smoothCcSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (toL2RangeRestrict (I := I) g r s).comp (smoothCcSection (I := I) g r s) =
      LinearMap.id :=
  Classical.choose_spec
    ((toL2RangeRestrict (I := I) g r s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (toL2RangeRestrict_surjective (I := I) g r s)))

set_option linter.unusedSectionVars false in
/-- Pointwise form: applying the section and then the surjection recovers
the original submodule element. -/
lemma toL2RangeRestrict_smoothCcSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    (toL2RangeRestrict (I := I) g r s) (smoothCcSection (I := I) g r s u) =
      u := by
  have h := toL2RangeRestrict_smoothCcSection (I := I) g r s
  exact congrArg (fun (f : _ →ₗ[ℝ] _) => f u) h

set_option linter.unusedSectionVars false in
/-- Underlying `TensorL2`-equality from the section property: the `L²`
embedding of `smoothCcSection u` equals the `TensorL2` value of `u`. -/
lemma toL2_smoothCcSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (smoothCcSection (I := I) g r s u) = (u : TensorL2 r s g) := by
  have h := toL2RangeRestrict_smoothCcSection_apply (I := I) g r s u
  have hval : ((toL2RangeRestrict (I := I) g r s)
      (smoothCcSection (I := I) g r s u)).val = (u : TensorL2 r s g) := by
    exact congrArg Subtype.val h
  change SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
      (smoothCcSection (I := I) g r s u) = (u : TensorL2 r s g)
  have hrr : ((toL2RangeRestrict (I := I) g r s)
      (smoothCcSection (I := I) g r s u)).val =
      SmoothCcTensor.toL2 (g := g) (r := r) (s := s)
        (smoothCcSection (I := I) g r s u) := rfl
  rw [hrr] at hval
  exact hval

set_option linter.unusedSectionVars false in
/-- The factored action of `connLaplacianL2Action` through the dense
embedding `SmoothCcTensor.toL2`, as a linear map on the image submodule.
Concretely, the value at `u : smoothCcToL2Submodule g r s` is
`connLaplacianL2Action g r s (smoothCcSection g r s u)`, where
`smoothCcSection` is a linear section of the canonical surjection
`SmoothCcTensor ↠ smoothCcToL2Submodule`. -/
def connLaplacianL2OnDomain (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    smoothCcToL2Submodule (I := I) g r s →ₗ[ℝ] TensorL2 r s g :=
  (connLaplacianL2Action (I := I) g r s).comp
    (smoothCcSection (I := I) g r s)

set_option linter.unusedSectionVars false in
@[simp] lemma connLaplacianL2OnDomain_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : smoothCcToL2Submodule (I := I) g r s) :
    connLaplacianL2OnDomain (I := I) g r s u =
      connLaplacianL2Action (I := I) g r s
        (smoothCcSection (I := I) g r s u) := rfl

set_option linter.unusedSectionVars false in
/-- The connection (rough) Laplacian `Δ_∇` as a partially-defined operator
`TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g`, with domain the canonical image
submodule of compactly-supported smooth `(r, s)`-tensor sections, and
underlying action given by the pointwise rough Laplacian on a chosen
representative section.

This `LinearPMap` is the entry point for the Friedrichs / spectral /
heat-semigroup theory developed downstream. -/
def connLaplacianL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g where
  domain := smoothCcToL2Submodule (I := I) g r s
  toFun := connLaplacianL2OnDomain (I := I) g r s

set_option linter.unusedSectionVars false in
/-- The domain of the partially-defined operator `connLaplacianL2 g r s`
is the canonical image submodule of smooth, compactly-supported sections
under `SmoothCcTensor.toL2`. -/
@[simp] theorem connLaplacianL2_domain_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (connLaplacianL2 (I := I) g r s).domain =
      smoothCcToL2Submodule (I := I) g r s := rfl

set_option linter.unusedSectionVars false in
/-- Applied to the `L²`-image of `T : SmoothCcTensor g r s`, the
partially-defined operator returns the value of `connLaplacianL2Action`
on a smooth, compactly-supported representative `T'` whose `L²`-image
agrees with that of `T`. The representative `T'` is the value of the
canonical linear section `smoothCcSection` at the embedded image of `T`;
its existence relies only on the projectivity of the image submodule
(`Module.Free.of_divisionRing`). -/
theorem connLaplacianL2_apply_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    (connLaplacianL2 (I := I) g r s)
        ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩ =
      connLaplacianL2Action (I := I) g r s
        (smoothCcSection (I := I) g r s
          ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩) := rfl

set_option linter.unusedSectionVars false in
/-- The `L²`-image of any smooth compactly-supported `(r, s)`-tensor section
lies in the domain of `connLaplacianL2`. -/
theorem toL2_mem_connLaplacianL2_domain
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain := by
  rw [connLaplacianL2_domain_eq]
  exact LinearMap.mem_range_self _ T

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
