import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.Curvature.Basic
import RicciFlower.Operators
import RicciFlower.Tensor.RSTensor.CotangentRiemannian
import RicciFlower.VectorBundle.PartialMfderiv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Metric compatibility in local-frame components

This file contains coordinate/local-frame consequences of metric compatibility
that are independent of Ricci-flow time evolution.  In particular it exposes
the component form of `nabla gInv = 0` for an arbitrary smooth metric and a
metric-compatible connection.
-/

namespace RicciFlower
namespace Coordinates

noncomputable section

open Bundle
open RicciFlower.Realized
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

/-! ## Fixed-chart inverse metric components -/

noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  ((metricFlatEquiv (I := I) g x₀).trans
    (LinearMap.toContinuousLinearMap :
      (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real))).toContinuousLinearEquiv

theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w = g.inner x₀ v w := by
  change ((metricFlatEquiv (I := I) g x₀) v) w = g.inner x₀ v w
  rw [metricFlatEquiv_apply]

/-- The metric flat map represented in the tangent trivialization centered at
`x₀`, viewed over the model chart target. -/
noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  (trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
      ⟨(extChartAt I x₀).symm y, g.inner ((extChartAt I x₀).symm y)⟩).2

theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) := by
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  ext v w
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  change
    (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun p : M => TangentSpace I p →L[Real] Real) x₀ x₀ x₀ x₀
        (g.inner x₀) v) w =
      ((metricFlatContinuousEquiv (I := I) g x₀) v) w
  have hxT :
      x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simp
  have hxDual :
      x₀ ∈ (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  rw [metricFlatContinuousEquiv_apply]
  simp only [hom_trivializationAt, Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply, Function.comp_apply]
  have hxR : x₀ ∈ (trivializationAt Real (fun _ : M => Real) x₀).baseSet := by
    simp
  rw [Trivialization.continuousLinearMapAt_apply]
  rw [(trivializationAt Real (fun _ : M => Real) x₀).coe_linearMapAt_of_mem
    (R := Real) hxR]
  have hL :
      (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := x₀) (mem_chart_source H x₀)]
    ext z
    exact (tangentBundleCore I M).coordChange_self (achart H x₀) x₀
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x₀) z
  have hsymm (z : E) :
      (trivializationAt E (TangentSpace I) x₀).symm x₀ z = z := by
    change (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ z = z
    rw [hL]
    rfl
  have hsymmL (z : E) :
      (trivializationAt E (TangentSpace I) x₀).symmL Real x₀ z = z := by
    rw [hL]
    rfl
  change g.inner x₀ ((trivializationAt E (TangentSpace I) x₀).symm x₀ v)
      ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) = g.inner x₀ v w
  calc
    g.inner x₀ ((trivializationAt E (TangentSpace I) x₀).symm x₀ v)
        ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w)
        = g.inner x₀ v ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) := by
          exact congrArg
            (fun z => g.inner x₀ z ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w))
            (hsymm v)
    _ = g.inner x₀ v w := by
          exact congrArg (fun z => g.inner x₀ v z) (hsymmL w)

theorem flatChart_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w =
      g.inner x
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
  have hx_src : x ∈ (extChartAt I x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hx
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x) = x :=
    (extChartAt I x₀).left_inv hx_src
  simp only [metricFlatModelInChart]
  rw [hom_trivializationAt_apply]
  rw [hcenter]
  have hxT :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hxDual :
      x ∈ (trivializationAt (E →L[Real] Real)
          (fun p : M => TangentSpace I p →L[Real] Real) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hxT, by simp⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxT hxDual]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply]

theorem flatChart_inv
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).IsInvertible := by
  haveI : CompleteSpace (E →L[Real] Real) := inferInstance
  let A : E →ₗ[Real] (E →L[Real] Real) :=
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)).toLinearMap
  have hxT :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  have hker : LinearMap.ker A = ⊥ := by
    ext v
    constructor
    · intro hv
      change A v = 0 at hv
      have hself :
          metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v v = 0 := by
        exact congrArg (fun L : E →L[Real] Real => L v) hv
      have hinner :
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) = 0 := by
        rw [← flatChart_apply (I := I) g x₀ hx v v]
        exact hself
      by_contra hvne
      have hsymm_ne :
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v ≠ 0 := by
        intro hzero
        have hmap := congrArg
          ((trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
            Real x) hzero
        have hcancel :
            (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt
                Real x
              ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) = v :=
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousLinearMapAt_symmL
            (R := Real) hxT v
        rw [hcancel] at hmap
        exact hvne (by simpa using hmap)
      exact False.elim ((ne_of_gt (g.pos x
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
        hsymm_ne)) hinner)
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      simp [A, hv0]
  have hdim :
      Module.finrank Real E = Module.finrank Real (E →L[Real] Real) := by
    calc
      Module.finrank Real E = Module.finrank Real (Module.Dual Real E) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank Real (E →L[Real] Real) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real)).finrank_eq
  let Aequiv : E ≃ₗ[Real] (E →L[Real] Real) :=
    A.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hker) hdim
  let Acle : E ≃L[Real] (E →L[Real] Real) :=
    Aequiv.toContinuousLinearEquiv
  have hA : (Acle : E →L[Real] E →L[Real] Real) =
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) := by
    ext v w
    change Aequiv v w =
      metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x) v w
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  rw [← hA]
  exact ContinuousLinearMap.isInvertible_equiv

theorem coordBasis_model
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := Real) E) :
    coordinateFrameAt_basis (I := I) x₀ hx i =
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x
        ((Module.finBasis Real E) i) := by
  rw [coordinateFrameAt_basis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  simpa [Trivialization.symmL_apply, extChartAt] using
    (congrArg (fun L : E →L[Real] TangentSpace I x => L ((Module.finBasis Real E) i))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src)).symm

theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The fixed-chart metric flat map is smooth on the model chart at the center. -/
theorem metricFlatModelInChart_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hcoord :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2) x₀ :=
    by
      rw [contMDiffAt_totalSpace] at hg
      simpa [e] using hg.2
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => (e ⟨p, g.inner p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt
      (x := extChartAt I x₀ x₀) hsymm
  exact hcomp.contDiffWithinAt

/-- The inverse metric flat map is smooth in the fixed model chart. -/
theorem inverseMetricFlatModelInChart_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact
    (metricFlatModelInChart_center_isInvertible (I := I) g x₀).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt
        (x := extChartAt I x₀ x₀)
        (metricFlatModelInChart_contDiffWithinAt (I := I) g x₀)

noncomputable def inverseMetricFlatModelInChart_component
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  (Module.finBasis Real E).coord k
    ((ContinuousLinearMap.inverse
        (metricFlatModelInChart (I := I) g x₀ y))
      (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))

/-- Fixed-chart inverse metric coefficients are smooth model functions. -/
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (inverseMetricFlatModelInChart_component (I := I) g x₀ k l)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv := inverseMetricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  simpa [inverseMetricFlatModelInChart_component, εk, εl] using
    (contDiffWithinAt_const (c := εk)).clm_apply happ

theorem gInvComp_contMDiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀ := by
  haveI : CompleteSpace E := FiniteDimensional.complete Real E
  let f : E -> Real :=
    inverseMetricFlatModelInChart_component (I := I) g x₀ k l
  have hf :
      ContDiffWithinAt Real ∞ f (Set.range I) (extChartAt I x₀ x₀) :=
    inverseMetricFlatModelInChart_component_contDiffWithinAt (I := I) g x₀ k l
  have hchart :
      ContMDiffWithinAt I 𝓘(Real, E) ∞ (extChartAt I x₀)
        (extChartAt I x₀).source x₀ :=
    (contMDiffAt_extChartAt (I := I) (x := x₀)).contMDiffWithinAt
  have hcomp :
      ContMDiffWithinAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀)
        (extChartAt I x₀).source x₀ := by
    exact hf.comp_contMDiffWithinAt hchart (by
      intro y hy
      exact extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hy))
  have hcompAt :
      ContMDiffAt I 𝓘(Real, Real) ∞ (f ∘ extChartAt I x₀) x₀ :=
    hcomp.contMDiffAt ((isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source (I := I) x₀))
  simpa [f, Function.comp_def] using hcompAt

theorem gInvComp_mdiffAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y)) x₀ := by
  exact (gInvComp_contMDiffAt (I := I) g x₀ k l).mdifferentiableAt (by simp)

theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ x₀) =
      inverseMetricFlatModelInChart_component (I := I) g x₀ j i
        (extChartAt I x₀ x₀) := by
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  simp only [inverseMetricFlatModelInChart_component]
  rw [hInv]
  calc
    (Module.finBasis Real E).coord i (A.symm (ε j))
        = (ε i) (A.symm (ε j)) := rfl
    _ = (A (A.symm (ε i))) (A.symm (ε j)) := by
          rw [A.apply_symm_apply]
    _ = g.inner x₀ (A.symm (ε i)) (A.symm (ε j)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = g.inner x₀ (A.symm (ε j)) (A.symm (ε i)) := by
          exact g.symm x₀ (A.symm (ε i)) (A.symm (ε j))
    _ = (A (A.symm (ε j))) (A.symm (ε i)) := by
          rw [metricFlatContinuousEquiv_apply]
    _ = (ε j) (A.symm (ε i)) := by
          rw [A.apply_symm_apply]
    _ = (Module.finBasis Real E).coord j (A.symm (ε i)) := rfl

/-- Fixed-chart inverse metric coefficients are symmetric at points where the
coordinate frame is defined. -/
theorem gInvChart_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricFlatModelInChart_component (I := I) g x₀ i j
        (extChartAt I x₀ x) =
      inverseMetricFlatModelInChart_component (I := I) g x₀ j i
        (extChartAt I x₀ x) := by
  let A : E →L[Real] (E →L[Real] Real) :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  have hInv : A.IsInvertible := flatChart_inv (I := I) g x₀ hx
  have hA_sym (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            exact flatChart_apply (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            rw [flatChart_apply (I := I) g x₀ hx w v]
  simp only [inverseMetricFlatModelInChart_component]
  calc
    (Module.finBasis Real E).coord i (ContinuousLinearMap.inverse A (ε j))
        = (ε i) (ContinuousLinearMap.inverse A (ε j)) := rfl
    _ = (A (ContinuousLinearMap.inverse A (ε i)))
          (ContinuousLinearMap.inverse A (ε j)) := by
          rw [hInv.self_apply_inverse]
    _ = (A (ContinuousLinearMap.inverse A (ε j)))
          (ContinuousLinearMap.inverse A (ε i)) := by
          exact hA_sym (ContinuousLinearMap.inverse A (ε i))
            (ContinuousLinearMap.inverse A (ε j))
    _ = (ε j) (ContinuousLinearMap.inverse A (ε i)) := by
          rw [hInv.self_apply_inverse]
    _ = (Module.finBasis Real E).coord j (ContinuousLinearMap.inverse A (ε i)) := rfl

theorem gInvBasisAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    MetricInverseInBasis (I := I) g x (coordinateFrameAt_basis (I := I) x₀ hx)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ x)) := by
  classical
  let A : E →L[Real] (E →L[Real] Real) :=
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x)
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => inverseMetricFlatModelInChart_component (I := I) g x₀ k l
      (extChartAt I x₀ x)
  have hInv : A.IsInvertible := flatChart_inv (I := I) g x₀ hx
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.inverse (ε l)) := by
    rfl
  have hA_sym (v w : E) : A v w = A w v := by
    calc
      A v w =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w) := by
            exact flatChart_apply (I := I) g x₀ hx v w
      _ =
          g.inner x
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x w)
            ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x v) := by
            exact g.symm x _ _
      _ = A w v := by
            rw [flatChart_apply (I := I) g x₀ hx w v]
  have hmetric (i j : CoordinateIdx (𝕜 := Real) E) :
      g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
          ((coordinateFrameAt_basis (I := I) x₀ hx) j) =
        A ((Module.finBasis Real E) i) ((Module.finBasis Real E) j) := by
    rw [coordBasis_model (I := I) x₀ hx i]
    rw [coordBasis_model (I := I) x₀ hx j]
    rw [flatChart_apply (I := I) g x₀ hx]
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.inverse (ε l))
          = (ε k) (A.inverse (ε l)) := rfl
      _ = (A (A.inverse (ε k))) (A.inverse (ε l)) := by
            rw [hInv.self_apply_inverse]
      _ = (A (A.inverse (ε l))) (A.inverse (ε k)) := by
            exact hA_sym (A.inverse (ε k)) (A.inverse (ε l))
      _ = (ε l) (A.inverse (ε k)) := by
            rw [hInv.self_apply_inverse]
      _ = (Module.finBasis Real E).coord l (A.inverse (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) i)
            ((coordinateFrameAt_basis (I := I) x₀ hx) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    simp only [hmetric, hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.inverse (ε j)))
          = A ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (A ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.inverse (ε j)))
                ((Module.finBasis Real E) k)
            calc
              A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.inverse (ε j))
                  =
                (Module.finBasis Real E).coord k (A.inverse (ε j)) *
                  A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by ring
              _ =
                (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                  A ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) := by simp
              _ =
                A ((Module.finBasis Real E) i)
                  ((Module.finBasis Real E).coord k (A.inverse (ε j)) •
                    (Module.finBasis Real E) k) := hmap.symm
      _ = A ((Module.finBasis Real E) i) (A.inverse (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.inverse (ε j)) •
                    (Module.finBasis Real E) k) = A.inverse (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.inverse (ε j))
            exact congrArg (fun v => A ((Module.finBasis Real E) i) v) hsum
      _ = (A (A.inverse (ε j))) ((Module.finBasis Real E) i) := by
            exact hA_sym ((Module.finBasis Real E) i) (A.inverse (ε j))
      _ = (ε j) ((Module.finBasis Real E) i) := by
            rw [hInv.self_apply_inverse]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := fun h => hij h.symm
              simp [ε, hij, hji]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) k)
            ((coordinateFrameAt_basis (I := I) x₀ hx) j))
          =
        ∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x ((coordinateFrameAt_basis (I := I) x₀ hx) j)
            ((coordinateFrameAt_basis (I := I) x₀ hx) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x ((coordinateFrameAt_basis (I := I) x₀ hx) k)
              ((coordinateFrameAt_basis (I := I) x₀ hx) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j

theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAt_toBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ x₀)) := by
  classical
  let A : E ≃L[Real] (E →L[Real] Real) := metricFlatContinuousEquiv (I := I) g x₀
  let ε : CoordinateIdx (𝕜 := Real) E -> E →L[Real] Real :=
    fun a => LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord a)
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l => inverseMetricFlatModelInChart_component (I := I) g x₀ k l
      (extChartAt I x₀ x₀)
  have hInv :
      ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)) =
        A.symm := by
    rw [metricFlatModelInChart_center_eq (I := I) g x₀]
    exact ContinuousLinearMap.inverse_equiv A
  have hbasis :
      coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis Real E :=
    coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀
  have hginv (k l : CoordinateIdx (𝕜 := Real) E) :
      gInv k l = (Module.finBasis Real E).coord k (A.symm (ε l)) := by
    dsimp [gInv, inverseMetricFlatModelInChart_component]
    simpa [extChartAt] using
      congrArg (fun L : (E →L[Real] Real) →L[Real] E =>
        (Module.finBasis Real E).coord k (L (ε l))) hInv
  have hsym (k l : CoordinateIdx (𝕜 := Real) E) : gInv k l = gInv l k := by
    simp only [hginv]
    calc
      (Module.finBasis Real E).coord k (A.symm (ε l))
          = (ε k) (A.symm (ε l)) := rfl
      _ = (A (A.symm (ε k))) (A.symm (ε l)) := by
            rw [A.apply_symm_apply]
      _ = g.inner x₀ (A.symm (ε k)) (A.symm (ε l)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = g.inner x₀ (A.symm (ε l)) (A.symm (ε k)) := by
            exact g.symm x₀ (A.symm (ε k)) (A.symm (ε l))
      _ = (A (A.symm (ε l))) (A.symm (ε k)) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = (ε l) (A.symm (ε k)) := by
            rw [A.apply_symm_apply]
      _ = (Module.finBasis Real E).coord l (A.symm (ε k)) := rfl
  have hsecond (i j : CoordinateIdx (𝕜 := Real) E) :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) i)
            ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k j) =
        (if i = j then 1 else 0) := by
    rw [hbasis]
    simp only [hginv]
    calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
            (Module.finBasis Real E).coord k (A.symm (ε j)))
          = g.inner x₀ ((Module.finBasis Real E) i)
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                (Module.finBasis Real E).coord k (A.symm (ε j)) •
                  (Module.finBasis Real E) k) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            have hmap :=
              map_smul (g.inner x₀ ((Module.finBasis Real E) i))
                ((Module.finBasis Real E).coord k (A.symm (ε j)))
                ((Module.finBasis Real E) k)
            calc
              g.inner x₀ ((Module.finBasis Real E) i) ((Module.finBasis Real E) k) *
                  (Module.finBasis Real E).coord k (A.symm (ε j))
                  = (Module.finBasis Real E).coord k (A.symm (ε j)) *
                      g.inner x₀ ((Module.finBasis Real E) i)
                        ((Module.finBasis Real E) k) := by ring
              _ = (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    g.inner x₀ ((Module.finBasis Real E) i)
                      ((Module.finBasis Real E) k) := by simp
              _ = g.inner x₀ ((Module.finBasis Real E) i)
                    ((Module.finBasis Real E).coord k (A.symm (ε j)) •
                      (Module.finBasis Real E) k) := hmap.symm
      _ = g.inner x₀ ((Module.finBasis Real E) i) (A.symm (ε j)) := by
            have hsum :
                (∑ k : CoordinateIdx (𝕜 := Real) E,
                  (Module.finBasis Real E).coord k (A.symm (ε j)) •
                    (Module.finBasis Real E) k) = A.symm (ε j) := by
              exact (Module.finBasis Real E).sum_repr (A.symm (ε j))
            exact congrArg (fun v => g.inner x₀ ((Module.finBasis Real E) i) v) hsum
      _ = g.inner x₀ (A.symm (ε j)) ((Module.finBasis Real E) i) := by
            exact g.symm x₀ ((Module.finBasis Real E) i) (A.symm (ε j))
      _ = (A (A.symm (ε j))) ((Module.finBasis Real E) i) := by
            rw [metricFlatContinuousEquiv_apply]
      _ = ε j ((Module.finBasis Real E) i) := by
            rw [A.apply_symm_apply]
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp [ε]
            · have hji : j ≠ i := by exact fun h => hij h.symm
              simp [ε, hji, hij]
  intro i j
  constructor
  · calc
      (∑ k : CoordinateIdx (𝕜 := Real) E,
          gInv i k * g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
            ((coordinateFrameAt_toBasis (I := I) x₀) j))
          = ∑ k : CoordinateIdx (𝕜 := Real) E,
              g.inner x₀ ((coordinateFrameAt_toBasis (I := I) x₀) j)
                ((coordinateFrameAt_toBasis (I := I) x₀) k) * gInv k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hsym i k, g.symm x₀ ((coordinateFrameAt_toBasis (I := I) x₀) k)
              ((coordinateFrameAt_toBasis (I := I) x₀) j)]
            ring
      _ = (if j = i then 1 else 0) := hsecond j i
      _ = (if i = j then 1 else 0) := by
            by_cases hij : i = j
            · subst hij
              simp
            · have hji : j ≠ i := fun h => hij h.symm
              simp [hij, hji]
  · exact hsecond i j

/-- Metric component of a smooth metric in a fixed local frame. -/
def metricCompForMetricInFrame
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  g.inner x (frame i x) (frame j x)

theorem gInvBasisNhds
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (fun y : M => ∑ k : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x₀ i k
          (extChartAt I x₀ y) *
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) y k j) =ᶠ[𝓝 x₀]
      fun _ : M => if i = j then 1 else 0 := by
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
    (coordinateFrameAt_mem (I := I) x₀)] with y hy
  have h := (gInvBasisAt (I := I) g x₀ hy i j).1
  simpa [metricCompForMetricInFrame, coordinateFrameAt_basis_apply] using h

/-- Inverse-metric components for a fixed metric and local frame. -/
def InverseMetricComponentsForMetricInFrameOn [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
        (if i = j then 1 else 0)

/-- A supplied two-sided inverse of a metric frame Gram matrix is symmetric. -/
theorem gInvForMetric_symm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame) :
    forall x i j, gInv x i j = gInv x j i := by
  intro x i j
  exact Curvature.invComp_symm
    (I := I) (g := g) (gInv := gInv) frame
    (by
      intro y a b
      simpa [metricCompForMetricInFrame] using hinv y a b)
    x i j

/-- Covariant derivative components of the inverse metric in a local frame. -/
def inverseMetricCovDerivForMetricCompInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d k l : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => gInv y k l) x (frame d x) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a k * gInv x a l) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a l * gInv x k a)

def inverseMetricCovDerivForMetricCompAlongInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (k l : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => gInv y k l) x X +
    (∑ a : Idx,
      christoffelAlongInFrame cov frame hframe x X a k * gInv x a l) +
    (∑ a : Idx,
      christoffelAlongInFrame cov frame hframe x X a l * gInv x k a)

private theorem metric_localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

theorem metricComp_mdiffAt
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have hi := metric_localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hj := metric_localFrame_mdiffAt (I := I) frame hframe hu hx j
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (frame i y) (frame j y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hi hj
  rw [mdifferentiableAt_totalSpace] at htotal
  simpa [metricCompForMetricInFrame] using htotal.2

/-- Metric compatibility in a local frame:
the directional derivative of the metric components is the Christoffel
correction in both slots. -/
theorem metricCompForMetricInFrame_extDerivFun_eq_christoffel
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (frame d x) =
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d b p *
          metricCompForMetricInFrame (I := I) g frame x a p) := by
  classical
  have hd := metric_localFrame_mdiffAt (I := I) frame hframe hu hx d
  have ha := metric_localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hb := metric_localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmetric :=
    RicciFlower.Connection.metric_compatible_apply
      (I := I) hmc (frame d) (frame a) (frame b) hd ha hb
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          x (frame d x) =
        g.inner x ((cov (frame a) x) (frame d x)) (frame b x) +
          g.inner x (frame a x) ((cov (frame b) x) (frame d x)) := by
    simpa [extDerivFun, metricCompForMetricInFrame] using hmetric
  rw [hmetric']
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d a]
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d b]
  simp [metricCompForMetricInFrame, map_sum]

/-- Metric-compatibility derivative formula in an arbitrary tangent
direction. -/
theorem metricComp_extDeriv_tangent
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (X : TangentSpace I x) (a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x X =
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x X a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x X b p *
          metricCompForMetricInFrame (I := I) g frame x a p) := by
  classical
  let c : Idx -> Real := fun d => hframe.coeff d x X
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  let Γ : Idx -> Idx -> Idx -> Real := fun d i j =>
    christoffelSymbolInFrame cov frame hframe x d i j
  have hX : X = ∑ d : Idx, c d • frame d x := by
    simpa [c, IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe] using
      ((hframe.toBasisAt hx).sum_repr X).symm
  have hbasis (d : Idx) :
      extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          x (frame d x) =
        (∑ p : Idx, Γ d a p * G p b) +
          (∑ p : Idx, Γ d b p * G a p) := by
    simpa [Γ, G] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffel
        (I := I) g cov hmc frame hframe hu hx d a b
  have hAlongA (p : Idx) :
      christoffelAlongInFrame cov frame hframe x X a p =
        ∑ d : Idx, c d * Γ d a p := by
    simpa [c, Γ] using
      christoffelAlongInFrame_eq_sum_coeff
        (I := I) cov frame hframe hx X a p
  have hAlongB (p : Idx) :
      christoffelAlongInFrame cov frame hframe x X b p =
        ∑ d : Idx, c d * Γ d b p := by
    simpa [c, Γ] using
      christoffelAlongInFrame_eq_sum_coeff
        (I := I) cov frame hframe hx X b p
  have htermA :
      (∑ d : Idx, c d * (∑ p : Idx, Γ d a p * G p b)) =
        ∑ p : Idx, (∑ d : Idx, c d * Γ d a p) * G p b := by
    calc
      (∑ d : Idx, c d * (∑ p : Idx, Γ d a p * G p b))
          = ∑ d : Idx, ∑ p : Idx, c d * (Γ d a p * G p b) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ p : Idx, ∑ d : Idx, c d * (Γ d a p * G p b) := by
              rw [Finset.sum_comm]
      _ = ∑ p : Idx, (∑ d : Idx, c d * Γ d a p) * G p b := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
  have htermB :
      (∑ d : Idx, c d * (∑ p : Idx, Γ d b p * G a p)) =
        ∑ p : Idx, (∑ d : Idx, c d * Γ d b p) * G a p := by
    calc
      (∑ d : Idx, c d * (∑ p : Idx, Γ d b p * G a p))
          = ∑ d : Idx, ∑ p : Idx, c d * (Γ d b p * G a p) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ p : Idx, ∑ d : Idx, c d * (Γ d b p * G a p) := by
              rw [Finset.sum_comm]
      _ = ∑ p : Idx, (∑ d : Idx, c d * Γ d b p) * G a p := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
  calc
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x X
        =
      extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (∑ d : Idx, c d • frame d x) := by
          rw [hX]
    _ = ∑ d : Idx,
          c d *
            extDerivFun (I := I)
              (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
              x (frame d x) := by
          simp [map_sum, map_smul]
    _ = ∑ d : Idx,
          c d * ((∑ p : Idx, Γ d a p * G p b) +
            (∑ p : Idx, Γ d b p * G a p)) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hbasis d]
    _ = (∑ p : Idx, (∑ d : Idx, c d * Γ d a p) * G p b) +
        (∑ p : Idx, (∑ d : Idx, c d * Γ d b p) * G a p) := by
          rw [← htermA, ← htermB]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
    _ = (∑ p : Idx,
          christoffelAlongInFrame cov frame hframe x X a p *
            metricCompForMetricInFrame (I := I) g frame x p b) +
        (∑ p : Idx,
          christoffelAlongInFrame cov frame hframe x X b p *
            metricCompForMetricInFrame (I := I) g frame x a p) := by
          congr 1
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [hAlongA p]
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [hAlongB p]

theorem metricCompForMetricInFrame_extDerivFun_eq_christoffelAlong
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (X x) =
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) b p *
          metricCompForMetricInFrame (I := I) g frame x a p) := by
  classical
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have ha := metric_localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hb := metric_localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmetric :=
    RicciFlower.Connection.metric_compatible_apply
      (I := I) hmc (fun y : M => X y) (frame a) (frame b) hX ha hb
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          x (X x) =
        g.inner x ((cov (frame a) x) (X x)) (frame b x) +
          g.inner x (frame a x) ((cov (frame b) x) (X x)) := by
    simpa [extDerivFun, metricCompForMetricInFrame] using hmetric
  rw [hmetric']
  have hcov_a :
      (cov (frame a) x) (X x) =
        ∑ p : Idx, christoffelAlongInFrame cov frame hframe x (X x) a p • frame p x :=
    hframe.coeff_sum_eq (fun y => (cov (frame a) y) (X y)) hx
  have hcov_b :
      (cov (frame b) x) (X x) =
        ∑ p : Idx, christoffelAlongInFrame cov frame hframe x (X x) b p • frame p x :=
    hframe.coeff_sum_eq (fun y => (cov (frame b) y) (X y)) hx
  rw [hcov_a, hcov_b]
  simp [metricCompForMetricInFrame, map_sum]

/-- Differentiability of a finite sum of scalar functions. -/
theorem mdiffAt_finset_sum_real
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

/-- Directional derivative of a finite sum of scalar functions. -/
theorem extDerivFun_finset_sum_real
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
        exact mdiffAt_finset_sum_real (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

/-- Directional derivative of a product of scalar functions. -/
theorem extDerivFun_mul_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

theorem deriv_congr_nhds
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

private theorem inverseMetric_derivative_solve
    [DecidableEq Idx]
    (metric ric gInv gInvDt : Idx -> Idx -> Real)
    (i : Idx)
    (hrow : forall j : Idx,
      (∑ a : Idx,
        (gInvDt i a * metric a j + gInv i a * ((-2 : Real) * ric a j))) = 0)
    (hleft : forall a b : Idx,
      (∑ k : Idx, gInv a k * metric k b) = (if a = b then 1 else 0))
    (hright : forall a b : Idx,
      (∑ k : Idx, metric a k * gInv k b) = (if a = b then 1 else 0))
    (hmetric_symm : forall a b : Idx, metric a b = metric b a)
    (j : Idx) :
    gInvDt i j =
      2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
  classical
  have hsymm : forall a b : Idx, gInv a b = gInv b a := by
    intro a b
    let A : Matrix Idx Idx Real := fun i j => gInv i j
    let G : Matrix Idx Idx Real := fun i j => metric i j
    have hAG : A * G = 1 := by
      ext p q
      simpa [A, G, Matrix.mul_apply] using hleft p q
    have hGA : G * A = 1 := by
      ext p q
      simpa [A, G, Matrix.mul_apply] using hright p q
    have hGt : Matrix.transpose G = G := by
      ext p q
      simpa [G] using hmetric_symm q p
    have hAtG : Matrix.transpose A * G = 1 := by
      calc
        Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
        _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
        _ = 1 := by rw [hGA]; simp
    have hAt : Matrix.transpose A = A := by
      calc
        Matrix.transpose A = Matrix.transpose A * 1 := by simp
        _ = Matrix.transpose A * (G * A) := by rw [hGA]
        _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
        _ = 1 * A := by rw [hAtG]
        _ = A := by simp
    have hentry := congrArg (fun B : Matrix Idx Idx Real => B b a) hAt
    simpa [A] using hentry
  have hrow' : forall m : Idx,
      (∑ a : Idx, gInvDt i a * metric a m) =
        2 * (∑ a : Idx, gInv i a * ric a m) := by
    intro m
    have hm := hrow m
    rw [Finset.sum_add_distrib] at hm
    have hm' :
        (∑ a : Idx, gInvDt i a * metric a m) +
            (-2 : Real) * (∑ a : Idx, gInv i a * ric a m) = 0 := by
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hm
    linarith
  calc
    gInvDt i j
        = ∑ a : Idx, gInvDt i a * (if a = j then 1 else 0) := by
            simp
    _ = ∑ a : Idx, gInvDt i a *
          (∑ k : Idx, metric a k * gInv k j) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            rw [hright a j]
    _ = ∑ k : Idx, (∑ a : Idx, gInvDt i a * metric a k) * gInv k j := by
            calc
              (∑ a : Idx, gInvDt i a *
                  (∑ k : Idx, metric a k * gInv k j))
                  =
                ∑ a : Idx, ∑ k : Idx,
                  gInvDt i a * (metric a k * gInv k j) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ k : Idx, ∑ a : Idx,
                  gInvDt i a * (metric a k * gInv k j) := by
                    rw [Finset.sum_comm]
              _ = ∑ k : Idx, (∑ a : Idx, gInvDt i a * metric a k) * gInv k j := by
                    refine Finset.sum_congr rfl fun k _hk => ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    ring
    _ = ∑ k : Idx, (2 * (∑ a : Idx, gInv i a * ric a k)) * gInv k j := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [hrow' k]
    _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
            calc
              (∑ k : Idx, (2 * (∑ a : Idx, gInv i a * ric a k)) * gInv k j)
                  =
                2 * (∑ k : Idx, (∑ a : Idx, gInv i a * ric a k) * gInv k j) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _hk => ?_
                  ring
              _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
                  congr 1
                  calc
                    (∑ k : Idx, (∑ a : Idx, gInv i a * ric a k) * gInv k j)
                        =
                      ∑ k : Idx, ∑ a : Idx,
                        (gInv i a * ric a k) * gInv k j := by
                          refine Finset.sum_congr rfl fun k _hk => ?_
                          rw [Finset.sum_mul]
                    _ = ∑ a : Idx, ∑ b : Idx,
                        (gInv i a * ric a b) * gInv b j := by
                          rw [Finset.sum_comm]
                    _ = ∑ a : Idx, ∑ b : Idx,
                        gInv i a * gInv j b * ric a b := by
                          refine Finset.sum_congr rfl fun a _ha => ?_
                          refine Finset.sum_congr rfl fun b _hb => ?_
                          rw [hsymm b j]
                          ring

/-- Metric compatibility in coordinates for the inverse metric:
`nabla_d g^{kl} = 0`. -/
theorem inverseMetricCovDerivForMetricCompInFrame_eq_zero
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (d k l : Idx) :
    inverseMetricCovDerivForMetricCompInFrame (I := I) gInv cov frame hframe x d k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompForMetricInFrame (I := I) g frame x a b
  let U : Idx -> Idx -> Real := fun a b => gInv x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (frame d x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv y a b) x (frame d x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelSymbolInFrame cov frame hframe x d a b
  have hsymm : forall x i j, gInv x i j = gInv x j i :=
    gInvForMetric_symm (I := I) g gInv frame hinv
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffel
        (I := I) g cov hmc frame hframe hu hx d a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
      simpa using extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (frame d x) =
          gInv x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        extDerivFun_mul_real (I := I) (x := x) (frame d x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) =
        (fun _ : M => if k = m then 1 else 0) := by
      funext y
      exact (hinv y k m).1
    have hderiv :=
      congrArg (fun F : M -> Real => extDerivFun (I := I) F x (frame d x)) hconst
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
          x (frame d x) = 0 := by
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv x k a * DG a m + DU k a * G a m) := by
              simp [U, add_comm]
      _ = ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              rw [hprod a]
      _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) := hsum.symm
      _ = 0 := hzero
  have hsolve := inverseMetric_derivative_solve
    (metric := G)
    (ric := fun a b : Idx => (-1 / 2 : Real) * DG a b)
    (gInv := U)
    (gInvDt := DU)
    k
    (by
      intro m
      calc
        (∑ a : Idx,
            (DU k a * G a m +
              U k a * ((-2 : Real) * ((-1 / 2 : Real) * DG a m)))) =
            ∑ a : Idx, (DU k a * G a m + U k a * DG a m) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              ring
        _ = 0 := hrow m)
    (by
      intro a b
      simpa [G, U] using (hinv x a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv x a b).2)
    (by
      intro a b
      simpa [G, metricCompForMetricInFrame] using g.symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv x k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv x l b * G p b = G p b * gInv x b l
              rw [hsymm x l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv x p l).2
  have hterm1 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b)) =
        ∑ a : Idx, Γ a l * U k a := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b))
          =
        ∑ a : Idx, ∑ p : Idx, U k a * Γ a p *
          (∑ b : Idx, U l b * G p b) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            calc
              (∑ b : Idx, U k a * U l b *
                (∑ p : Idx, Γ a p * G p b))
                  =
                ∑ b : Idx, ∑ p : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ b : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    rw [Finset.sum_comm]
              _ = ∑ p : Idx, U k a * Γ a p *
                  (∑ b : Idx, U l b * G p b) := by
                    refine Finset.sum_congr rfl fun p _hp => ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
      _ = ∑ a : Idx, ∑ p : Idx,
          U k a * Γ a p * (if p = l then 1 else 0) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_right_sym p]
      _ = ∑ a : Idx, U k a * Γ a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a l * U k a := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            ring
  have hterm2 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p)) =
        ∑ a : Idx, Γ a k * U a l := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p))
          =
        ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
          (∑ a : Idx, U k a * G a p) := by
            calc
              (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * (∑ p : Idx, Γ b p * G a p))
                  =
                ∑ b : Idx, ∑ a : Idx,
                  U k a * U l b * (∑ p : Idx, Γ b p * G a p) := by
                    rw [Finset.sum_comm]
              _ = ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
                  (∑ a : Idx, U k a * G a p) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    calc
                      (∑ a : Idx, U k a * U l b *
                        (∑ p : Idx, Γ b p * G a p))
                          =
                        ∑ a : Idx, ∑ p : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            rw [Finset.mul_sum]
                      _ = ∑ p : Idx, ∑ a : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            rw [Finset.sum_comm]
                      _ = ∑ p : Idx, U l b * Γ b p *
                          (∑ a : Idx, U k a * G a p) := by
                            refine Finset.sum_congr rfl fun p _hp => ?_
                            rw [Finset.mul_sum]
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            ring
      _ = ∑ b : Idx, ∑ p : Idx,
          U l b * Γ b p * (if k = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_left p]
      _ = ∑ b : Idx, U l b * Γ b k := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            simp
      _ = ∑ a : Idx, Γ a k * U a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            change gInv x l a * Γ a k = Γ a k * gInv x a l
            rw [hsymm x l a]
            ring
  have htrace :
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) =
        (∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l) := by
    calc
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b)
          =
        ∑ a : Idx, ∑ b : Idx,
          U k a * U l b *
            ((∑ p : Idx, Γ a p * G p b) +
              (∑ p : Idx, Γ b p * G a p)) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun b _hb => ?_
            rw [hDG a b]
      _ =
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ a p * G p b)) +
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ b p * G a p)) := by
            simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l) := by
            rw [hterm1, hterm2]
  have hDU :
      DU k l =
        - ((∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l)) := by
    calc
      DU k l =
          2 * (∑ a : Idx, ∑ b : Idx,
            U k a * U l b * ((-1 / 2 : Real) * DG a b)) := hsolve
      _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
            calc
              2 * (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * ((-1 / 2 : Real) * DG a b))
                  =
                ∑ a : Idx, ∑ b : Idx,
                  2 * (U k a * U l b * ((-1 / 2 : Real) * DG a b)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ a : Idx, ∑ b : Idx,
                  -(U k a * U l b * DG a b) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
              _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [← Finset.sum_neg_distrib]
      _ = - ((∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l)) := by
            rw [htrace]
  unfold inverseMetricCovDerivForMetricCompInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring

theorem inverseMetricCovDerivForMetricCompAlongInFrame_eq_zero
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (k l : Idx) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I) gInv cov frame hframe x (X x) k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompForMetricInFrame (I := I) g frame x a b
  let U : Idx -> Idx -> Real := fun a b => gInv x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (X x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv y a b) x (X x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelAlongInFrame cov frame hframe x (X x) a b
  have hsymm : forall x i j, gInv x i j = gInv x j i :=
    gInvForMetric_symm (I := I) g gInv frame hinv
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffelAlong
        (I := I) g cov hmc X frame hframe hu hx a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (X x) := by
      simpa using extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (X x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (X x) =
          gInv x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        extDerivFun_mul_real (I := I) (x := x) (X x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) =
        (fun _ : M => if k = m then 1 else 0) := by
      funext y
      exact (hinv y k m).1
    have hderiv :=
      congrArg (fun F : M -> Real => extDerivFun (I := I) F x (X x)) hconst
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
          x (X x) = 0 := by
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv x k a * DG a m + DU k a * G a m) := by
              simp [U, add_comm]
      _ = ∑ a : Idx, extDerivFun (I := I) (F a) x (X x) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              rw [hprod a]
      _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) := hsum.symm
      _ = 0 := hzero
  have hsolve := inverseMetric_derivative_solve
    (metric := G)
    (ric := fun a b : Idx => (-1 / 2 : Real) * DG a b)
    (gInv := U)
    (gInvDt := DU)
    k
    (by
      intro m
      calc
        (∑ a : Idx,
            (DU k a * G a m +
              U k a * ((-2 : Real) * ((-1 / 2 : Real) * DG a m)))) =
            ∑ a : Idx, (DU k a * G a m + U k a * DG a m) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              ring
        _ = 0 := hrow m)
    (by
      intro a b
      simpa [G, U] using (hinv x a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv x a b).2)
    (by
      intro a b
      simpa [G, metricCompForMetricInFrame] using g.symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv x k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv x l b * G p b = G p b * gInv x b l
              rw [hsymm x l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv x p l).2
  have hterm1 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b)) =
        ∑ a : Idx, Γ a l * U k a := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b))
          =
        ∑ a : Idx, ∑ p : Idx, U k a * Γ a p *
          (∑ b : Idx, U l b * G p b) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            calc
              (∑ b : Idx, U k a * U l b *
                (∑ p : Idx, Γ a p * G p b))
                  =
                ∑ b : Idx, ∑ p : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ b : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    rw [Finset.sum_comm]
              _ = ∑ p : Idx, U k a * Γ a p *
                  (∑ b : Idx, U l b * G p b) := by
                    refine Finset.sum_congr rfl fun p _hp => ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
      _ = ∑ a : Idx, ∑ p : Idx,
          U k a * Γ a p * (if p = l then 1 else 0) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_right_sym p]
      _ = ∑ a : Idx, U k a * Γ a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a l * U k a := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            ring
  have hterm2 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p)) =
        ∑ a : Idx, Γ a k * U a l := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p))
          =
        ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
          (∑ a : Idx, U k a * G a p) := by
            calc
              (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * (∑ p : Idx, Γ b p * G a p))
                  =
                ∑ b : Idx, ∑ a : Idx,
                  U k a * U l b * (∑ p : Idx, Γ b p * G a p) := by
                    rw [Finset.sum_comm]
              _ = ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
                  (∑ a : Idx, U k a * G a p) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    calc
                      (∑ a : Idx, U k a * U l b *
                        (∑ p : Idx, Γ b p * G a p))
                          =
                        ∑ a : Idx, ∑ p : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            rw [Finset.mul_sum]
                      _ = ∑ p : Idx, ∑ a : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            rw [Finset.sum_comm]
                      _ = ∑ p : Idx, U l b * Γ b p *
                          (∑ a : Idx, U k a * G a p) := by
                            refine Finset.sum_congr rfl fun p _hp => ?_
                            rw [Finset.mul_sum]
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            ring
      _ = ∑ b : Idx, ∑ p : Idx,
          U l b * Γ b p * (if k = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_left p]
      _ = ∑ b : Idx, U l b * Γ b k := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            simp
      _ = ∑ a : Idx, Γ a k * U a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            change gInv x l a * Γ a k = Γ a k * gInv x a l
            rw [hsymm x l a]
            ring
  have htrace :
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) =
        (∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l) := by
    calc
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b)
          =
        ∑ a : Idx, ∑ b : Idx,
          U k a * U l b *
            ((∑ p : Idx, Γ a p * G p b) +
              (∑ p : Idx, Γ b p * G a p)) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun b _hb => ?_
            rw [hDG a b]
      _ =
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ a p * G p b)) +
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ b p * G a p)) := by
            simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l) := by
            rw [hterm1, hterm2]
  have hDU :
      DU k l =
        - ((∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l)) := by
    calc
      DU k l =
          2 * (∑ a : Idx, ∑ b : Idx,
            U k a * U l b * ((-1 / 2 : Real) * DG a b)) := hsolve
      _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
            calc
              2 * (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * ((-1 / 2 : Real) * DG a b))
                  =
                ∑ a : Idx, ∑ b : Idx,
                  2 * (U k a * U l b * ((-1 / 2 : Real) * DG a b)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ a : Idx, ∑ b : Idx,
                  -(U k a * U l b * DG a b) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
              _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [← Finset.sum_neg_distrib]
      _ = - ((∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l)) := by
            rw [htrace]
  unfold inverseMetricCovDerivForMetricCompAlongInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring

theorem invCovZeroLocal
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M}
    (hinvX : ∀ i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
          (if i = j then 1 else 0))
    (hinvN : ∀ i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (hu : IsOpen u) (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (k l : Idx) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I) gInv cov frame hframe x (X x) k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompForMetricInFrame (I := I) g frame x a b
  let U : Idx -> Idx -> Real := fun a b => gInv x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (X x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv y a b) x (X x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelAlongInFrame cov frame hframe x (X x) a b
  have hsymmX : forall i j : Idx, gInv x i j = gInv x j i := by
    intro i j
    let A : Matrix Idx Idx Real := fun i j => gInv x i j
    let G : Matrix Idx Idx Real := fun i j =>
      metricCompForMetricInFrame (I := I) g frame x i j
    have hAG : A * G = 1 := by
      ext a b
      simpa [A, G, Matrix.mul_apply] using (hinvX a b).1
    have hGA : G * A = 1 := by
      ext a b
      simpa [A, G, Matrix.mul_apply] using (hinvX a b).2
    have hGt : Matrix.transpose G = G := by
      ext a b
      simpa [G, metricCompForMetricInFrame] using
        g.symm x (frame b x) (frame a x)
    have hAtG : Matrix.transpose A * G = 1 := by
      calc
        Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
        _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
        _ = 1 := by rw [hGA]; simp
    have hAt : Matrix.transpose A = A := by
      calc
        Matrix.transpose A = Matrix.transpose A * 1 := by simp
        _ = Matrix.transpose A * (G * A) := by rw [hGA]
        _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
        _ = 1 * A := by rw [hAtG]
        _ = A := by simp
    have hentry := congrArg (fun B : Matrix Idx Idx Real => B j i) hAt
    simpa [A] using hentry
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffelAlong
        (I := I) g cov hmc X frame hframe hu hx a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (X x) := by
      simpa using extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (X x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (X x) =
          gInv x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        extDerivFun_mul_real (I := I) (x := x) (X x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
          x (X x) = 0 := by
      calc
        extDerivFun (I := I)
            (fun y : M => ∑ a : Idx,
              gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
            x (X x)
            =
          extDerivFun (I := I) (fun _ : M => if k = m then 1 else 0) x (X x) :=
            deriv_congr_nhds (I := I) (X x) (hinvN k m)
        _ = 0 := by
            simp [extDerivFun]
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv x k a * DG a m + DU k a * G a m) := by
              simp [U, add_comm]
      _ = ∑ a : Idx, extDerivFun (I := I) (F a) x (X x) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              rw [hprod a]
      _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) := hsum.symm
      _ = 0 := hzero
  have hsolve := inverseMetric_derivative_solve
    (metric := G)
    (ric := fun a b : Idx => (-1 / 2 : Real) * DG a b)
    (gInv := U)
    (gInvDt := DU)
    k
    (by
      intro m
      calc
        (∑ a : Idx,
            (DU k a * G a m +
              U k a * ((-2 : Real) * ((-1 / 2 : Real) * DG a m)))) =
            ∑ a : Idx, (DU k a * G a m + U k a * DG a m) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              ring
        _ = 0 := hrow m)
    (by
      intro a b
      simpa [G, U] using (hinvX a b).1)
    (by
      intro a b
      simpa [G, U] using (hinvX a b).2)
    (by
      intro a b
      simpa [G, metricCompForMetricInFrame] using g.symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinvX k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv x l b * G p b = G p b * gInv x b l
              rw [hsymmX l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinvX p l).2
  have hterm1 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b)) =
        ∑ a : Idx, Γ a l * U k a := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b))
          =
        ∑ a : Idx, ∑ p : Idx, U k a * Γ a p *
          (∑ b : Idx, U l b * G p b) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            calc
              (∑ b : Idx, U k a * U l b *
                (∑ p : Idx, Γ a p * G p b))
                  =
                ∑ b : Idx, ∑ p : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ b : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    rw [Finset.sum_comm]
              _ = ∑ p : Idx, U k a * Γ a p *
                  (∑ b : Idx, U l b * G p b) := by
                    refine Finset.sum_congr rfl fun p _hp => ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
      _ = ∑ a : Idx, ∑ p : Idx,
          U k a * Γ a p * (if p = l then 1 else 0) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_right_sym p]
      _ = ∑ a : Idx, U k a * Γ a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a l * U k a := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            ring
  have hterm2 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p)) =
        ∑ a : Idx, Γ a k * U a l := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p))
          =
        ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
          (∑ a : Idx, U k a * G a p) := by
            calc
              (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * (∑ p : Idx, Γ b p * G a p))
                  =
                ∑ b : Idx, ∑ a : Idx,
                  U k a * U l b * (∑ p : Idx, Γ b p * G a p) := by
                    rw [Finset.sum_comm]
              _ = ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
                  (∑ a : Idx, U k a * G a p) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    calc
                      (∑ a : Idx, U k a * U l b *
                        (∑ p : Idx, Γ b p * G a p))
                          =
                        ∑ a : Idx, ∑ p : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            rw [Finset.mul_sum]
                      _ = ∑ p : Idx, ∑ a : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            rw [Finset.sum_comm]
                      _ = ∑ p : Idx, U l b * Γ b p *
                          (∑ a : Idx, U k a * G a p) := by
                            refine Finset.sum_congr rfl fun p _hp => ?_
                            rw [Finset.mul_sum]
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            ring
      _ = ∑ b : Idx, ∑ p : Idx,
          U l b * Γ b p * (if k = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_left p]
      _ = ∑ b : Idx, U l b * Γ b k := by
            refine Finset.sum_congr rfl fun b _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a k * U a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            change gInv x l a * Γ a k = Γ a k * gInv x a l
            rw [hsymmX l a]
            ring
  have htrace :
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) =
        (∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l) := by
    calc
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b)
          =
        ∑ a : Idx, ∑ b : Idx,
          U k a * U l b *
            ((∑ p : Idx, Γ a p * G p b) +
              (∑ p : Idx, Γ b p * G a p)) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun b _hb => ?_
            rw [hDG a b]
      _ =
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ a p * G p b)) +
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ b p * G a p)) := by
            simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l) := by
            rw [hterm1, hterm2]
  have hDU :
      DU k l =
        - ((∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l)) := by
    calc
      DU k l =
          2 * (∑ a : Idx, ∑ b : Idx,
            U k a * U l b * ((-1 / 2 : Real) * DG a b)) := hsolve
      _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
            calc
              2 * (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * ((-1 / 2 : Real) * DG a b))
                  =
                ∑ a : Idx, ∑ b : Idx,
                  2 * (U k a * U l b * ((-1 / 2 : Real) * DG a b)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ a : Idx, ∑ b : Idx,
                  -(U k a * U l b * DG a b) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
              _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [← Finset.sum_neg_distrib]
      _ = - ((∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l)) := by
            rw [htrace]
  unfold inverseMetricCovDerivForMetricCompAlongInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring

theorem gInvCovZeroAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (x₀ : M) (k l : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x₀ a b
            (extChartAt I x₀ y))
        cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) k l = 0 := by
  classical
  let gInv : M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun y a b => inverseMetricFlatModelInChart_component (I := I) g x₀ a b
      (extChartAt I x₀ y)
  have hinvX : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ r : CoordinateIdx (𝕜 := Real) E,
        gInv x₀ i r *
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) x₀ r j) =
          (if i = j then 1 else 0) ∧
        (∑ r : CoordinateIdx (𝕜 := Real) E,
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) x₀ i r * gInv x₀ r j) =
          (if i = j then 1 else 0) := by
    intro i j
    have h := gInvBasisAt (I := I) g x₀ (coordinateFrameAt_mem (I := I) x₀) i j
    simpa [gInv, metricCompForMetricInFrame, coordinateFrameAt_basis_apply] using h
  have hinvN : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (fun y : M => ∑ r : CoordinateIdx (𝕜 := Real) E,
          gInv y i r *
            metricCompForMetricInFrame (I := I) g
              (coordinateFrameAt (I := I) x₀) y r j) =ᶠ[𝓝 x₀]
        fun _ : M => if i = j then 1 else 0 := by
    intro i j
    simpa [gInv] using gInvBasisNhds (I := I) g x₀ i j
  have hginv_mdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x₀ := by
    intro a b
    simpa [gInv] using gInvComp_mdiffAt (I := I) g x₀ a b
  have hmetric_mdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) y a b) x₀ := by
    intro a b
    exact metricComp_mdiffAt (I := I) g
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) a b
  simpa [gInv] using
    invCovZeroLocal (I := I) g gInv cov X
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      hinvX hinvN hmc
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀)
      hginv_mdiff hmetric_mdiff k l

end Components

end
end Coordinates
end RicciFlower
