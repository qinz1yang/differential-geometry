import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Pointwise metric data on fibers and the tangent flat map

This file provides the finite-dimensional pointwise metric interface used by
the tensor bundle layer. A `MetricFiberData V` packages a symmetric,
nonnegative flat isomorphism `V ≃ₗ[ℝ] Module.Dual ℝ V`, modelling a genuine
pointwise inner product on a finite-dimensional real vector-space fiber, and
exposes the associated inner product, sharp isomorphism, positive-definiteness,
inner-product core, and metric adjoint.

It then specializes this interface to the tangent bundle: from a smooth
Riemannian metric `g` on `TM` we build the tangent flat map
`tangentFlatLinear`, prove it injective by positive-definiteness, upgrade it to
the linear equivalence `tangentFlatEquiv`, and assemble the pointwise
`TangentMetricData` whose inner product realizes `g.inner`.

The interface deliberately takes explicit metric-extension data tied to a given
Riemannian metric rather than constructing tensor-power metrics by choice; later
files build on this data.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

/-- Metric data on a finite-dimensional real vector-space fiber, packaged by
its flat isomorphism.  Symmetry and nonnegativity are included because this is
intended to model a genuine pointwise inner product, not just an arbitrary
linear equivalence to the dual. -/
structure MetricFiberData (V : Type*) [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] where
  flat : V ≃ₗ[Real] Module.Dual Real V
  symm : forall v w : V, flat v w = flat w v
  nonneg : forall v : V, 0 <= flat v v

namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

private theorem dual_finrank_eq :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V) :=
  Subspace.dual_finrank_eq.symm

/-- Build metric data from an injective flat map into the dual. -/
def ofFlat
    (flat : V →ₗ[Real] Module.Dual Real V)
    (hinj : Function.Injective flat)
    (hsymm : forall v w : V, flat v w = flat w v)
    (hnonneg : forall v : V, 0 <= flat v v) :
    MetricFiberData V where
  flat := LinearMap.linearEquivOfInjective flat hinj dual_finrank_eq
  symm := hsymm
  nonneg := hnonneg

/-- Inner product associated to a metric flat isomorphism. -/
def inner (D : MetricFiberData V) (v w : V) : Real :=
  D.flat v w

/-- Sharp isomorphism associated to `MetricFiberData`. -/
def sharp (D : MetricFiberData V) : Module.Dual Real V ≃ₗ[Real] V :=
  D.flat.symm

@[simp] theorem inner_apply (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.flat v w := by
  rfl

theorem inner_comm (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.inner w v := by
  exact D.symm v w

theorem inner_nonneg (D : MetricFiberData V) (v : V) :
    0 <= D.inner v v := by
  exact D.nonneg v

/-- A metric fiber has no nonzero null vectors. -/
theorem inner_self_eq_zero_iff (D : MetricFiberData V) (v : V) :
    D.inner v v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hvw : forall w : V, D.inner v w = 0 := by
      intro w
      by_contra hne
      let a := D.inner v w
      let b := D.inner w w
      let t := -((b + 1) / (2 * a))
      have ha : a ≠ 0 := hne
      have hquad : 0 <= D.inner (w + t • v) (w + t • v) :=
        D.inner_nonneg (w + t • v)
      have hcalc : D.inner (w + t • v) (w + t • v) = -1 := by
        have hexpand :
            D.inner (w + t • v) (w + t • v) =
              b + 2 * t * a + t * t * D.inner v v := by
          unfold inner a b
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul]
          rw [D.symm w v]
          simp [inner]
          ring_nf
        rw [hexpand, hv]
        unfold t b a
        field_simp [ha]
        ring
      linarith
    have hflat : D.flat v = 0 := by
      ext w
      exact hvw w
    exact D.flat.injective (by simpa using hflat)
  · intro hv
    simp [hv, inner]

/-- Positive-definiteness of a metric fiber. -/
theorem inner_pos_of_ne_zero (D : MetricFiberData V) {v : V} (hv : v ≠ 0) :
    0 < D.inner v v := by
  have hnonneg := D.inner_nonneg v
  have hne : D.inner v v ≠ 0 := by
    intro hzero
    exact hv ((D.inner_self_eq_zero_iff v).1 hzero)
  exact lt_of_le_of_ne' hnonneg hne

/-- The inner-product core induced by metric fiber data.

This is used only as a private bridge to Mathlib finite-dimensional
Hilbert-space trace lemmas; the public tensor metric API remains based on
`MetricFiberData`. -/
@[reducible] def toCore (D : MetricFiberData V) : InnerProductSpace.Core Real V where
  inner := fun v w => D.inner v w
  conj_inner_symm := by
    intro x y
    exact D.symm y x
  re_inner_nonneg := by
    intro x
    simpa using D.inner_nonneg x
  add_left := by
    intro x y z
    simp [MetricFiberData.inner, map_add]
  smul_left := by
    intro x y r
    simp [MetricFiberData.inner, smul_eq_mul]
  definite := by
    intro x hx
    exact (D.inner_self_eq_zero_iff x).1 (by simpa using hx)

theorem toCore_inner (D : MetricFiberData V) (v w : V) :
    letI : InnerProductSpace.Core Real V := D.toCore
    letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
    Inner.inner Real v w = D.inner v w := by
  change D.toCore.inner v w = D.inner v w
  rfl

section MetricEquiv

variable {V' W' : Type*}
  [NormedAddCommGroup V'] [NormedSpace Real V'] [FiniteDimensional Real V']
  [NormedAddCommGroup W'] [NormedSpace Real W'] [FiniteDimensional Real W']

/-- Equal-dimensional metric fibers admit a continuous linear equivalence
preserving their metric inner products. -/
theorem exists_metric_cle
    (DV : MetricFiberData V') (DW : MetricFiberData W')
    (hfin : Module.finrank Real V' = Module.finrank Real W') :
    ∃ e : V' ≃L[Real] W',
      ∀ v w, DW.inner (e v) (e w) = DV.inner v w := by
  classical
  let addV : AddCommGroup V' := inferInstance
  let modV : Module Real V' := inferInstance
  let addW : AddCommGroup W' := inferInstance
  let modW : Module Real W' := inferInstance
  let eData :
      {e : V' ≃ₗ[Real] W' //
        ∀ v w, DW.inner (e v) (e w) = DV.inner v w} := by
    letI : InnerProductSpace.Core Real V' := DV.toCore
    letI : NormedAddCommGroup V' :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real V' _ addV modV DV.toCore
    letI : AddCommGroup V' := addV
    letI : Module Real V' := modV
    letI : InnerProductSpace Real V' :=
      @InnerProductSpace.ofCore Real V' _ _ _ DV.toCore.toCore
    letI : InnerProductSpace.Core Real W' := DW.toCore
    letI : NormedAddCommGroup W' :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real W' _ addW modW DW.toCore
    letI : AddCommGroup W' := addW
    letI : Module Real W' := modW
    letI : InnerProductSpace Real W' :=
      @InnerProductSpace.ofCore Real W' _ _ _ DW.toCore.toCore
    let bV := stdOrthonormalBasis Real V'
    let bW := stdOrthonormalBasis Real W'
    let e : V' ≃ₗᵢ[Real] W' := bV.equiv bW (finCongr hfin)
    refine ⟨e.toLinearEquiv, ?_⟩
    intro v w
    change Inner.inner Real (e v) (e w) = Inner.inner Real v w
    exact e.inner_map_map v w
  let e : V' ≃L[Real] W' := eData.1.toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  intro v w
  change DW.inner (eData.1 v) (eData.1 w) = DV.inner v w
  exact eData.2 v w

end MetricEquiv

variable {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]

/-- Metric adjoint of a linear map between metric fibers. -/
def adjoint (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) : W →ₗ[Real] V :=
  DV.flat.symm.toLinearMap.comp
    (A.dualMap.comp DW.flat.toLinearMap)

/-- The metric adjoint satisfies the expected defining identity. -/
theorem adjoint_inner
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) (y : W) (x : V) :
    DV.inner (adjoint DV DW A y) x = DW.inner y (A x) := by
  unfold inner adjoint
  change
    DV.flat (DV.flat.symm
        ((A.dualMap.comp DW.flat.toLinearMap) y)) x =
      DW.flat y (A x)
  rw [DV.flat.apply_symm_apply]
  rfl

end MetricFiberData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Tensor-folder alias for a smooth Riemannian metric on `TM`. -/
abbrev SmoothMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

/-- The tangent flat map induced by a smooth Riemannian metric. -/
def tangentFlatLinear (g : SmoothMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    simp
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    simp

@[simp] theorem tangentFlatLinear_apply
    (g : SmoothMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatLinear (I := I) g x v w = g.inner x v w := by
  rfl

/-- The tangent flat map is injective by positive-definiteness. -/
theorem tangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (tangentFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [tangentFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)

/-- The tangent flat equivalence induced by a smooth Riemannian metric. -/
def tangentFlatEquiv (g : SmoothMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (tangentFlatLinear (I := I) g x)
    (tangentFlatLinear_injective (I := I) g x)
    MetricFiberData.dual_finrank_eq

@[simp] theorem tangentFlatEquiv_apply
    (g : SmoothMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatEquiv (I := I) g x v w = g.inner x v w := by
  rfl

/-- Explicit pointwise metric data on `T_x M` tied to the Riemannian metric `g`.

This is an interface, not an existence theorem.  The eventual construction
should fill `metric` with the flat map induced by `g.inner`. -/
structure TangentMetricData
    (g : SmoothMetric I M) (x : M) where
  metric : MetricFiberData (TangentSpace I x)
  realizes_inner : forall X Y : TangentSpace I x,
    metric.inner X Y = g.inner x X Y

/-- The tangent metric data constructed from the Riemannian metric. -/
def tangentMetricData (g : SmoothMetric I M) (x : M) :
    TangentMetricData (I := I) g x where
  metric :=
    { flat := tangentFlatEquiv (I := I) g x
      symm := by
        intro X Y
        exact g.symm x X Y
      nonneg := by
        intro X
        by_cases hX : X = 0
        · simp [hX]
        · exact le_of_lt (g.pos x X hX) }
  realizes_inner := by
    intro X Y
    rfl

namespace TangentMetricData

@[simp] theorem inner_eq
    {g : SmoothMetric I M} {x : M} (D : TangentMetricData (I := I) g x)
    (X Y : TangentSpace I x) :
    D.metric.inner X Y = g.inner x X Y :=
  D.realizes_inner X Y

end TangentMetricData

end

end Tensor0SBundle
