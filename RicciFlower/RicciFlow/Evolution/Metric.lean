import Mathlib.Analysis.Calculus.ContDiff.Operations
import RicciFlower.RicciFlow.Basic
import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Coordinates.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Ricci-Flow Metric Evolution in a Fixed Frame

This file translates the first Section 6.2 metric calculation into the realized
interval API.  The core geometric input is the Ricci-flow equation
`partial_t g = -2 Ric`; the inverse-metric result is obtained by differentiating
the frame identity `g^{-1} g = I`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open RicciFlower.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

/-- Metric component in a fixed local frame. -/
def metricCompInFrame
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (S.family.metric t).inner x (frame i x) (frame j x)

@[simp] theorem metricCompInFrame_apply
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    metricCompInFrame (I := I) S frame t x i j =
      (S.family.metric t).inner x (frame i x) (frame j x) := by
  rfl

/-- Fixed-frame metric evolution, directly extracted from `IsSolutionOn`. -/
theorem metricCompInFrame_hasDerivWithinAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrame (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [metricCompInFrame, ricciCompInFrame] using
    metric_derivWithin_eq_neg_two_ricci (I := I) S hS t x
      (frame i x) (frame j x)

/-- The inverse components invert the frame Gram matrix at all times. -/
def InverseMetricComponentsInFrameOn [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrame (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)

/-- Symmetry of the inverse metric components in the chosen frame. -/
def SymmetricInverseMetricComponentsInFrameOn
    (gInv : Real -> Realized.InverseMetricComponents M Idx) : Prop :=
  forall t x i j, gInv t x i j = gInv t x j i

/-- A supplied two-sided inverse of the frame Gram matrix is automatically
symmetric. -/
theorem gInv_symm [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    SymmetricInverseMetricComponentsInFrameOn gInv := by
  intro t x i j
  exact Curvature.invComp_symm
    (I := I) (g := S.family.metric t)
    (gInv := fun x i j => gInv t x i j) frame
    (by
      intro y a b
      simpa [metricCompInFrame] using hinv t y a b)
    x i j

/-- Componentwise regularity of a supplied inverse-metric component family. -/
def InverseMetricDerivativeComponentsOn
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : Realized.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (gInvDt (t : Real) x i j)
      D.carrier
      (t : Real)

/-- Metric-side regularity in a fixed local frame.

This package is deliberately metric-side: it records smooth time dependence of
the frame Gram matrix, nondegeneracy through a chosen two-sided inverse frame
matrix, time differentiability of that inverse matrix, and uniqueness of time
derivatives on the interval.  The inverse evolution formula itself is still
proved by differentiating the inverse identity in
`inverseMetricEvolutionEquationInFrame_of_inverse_components`; it is not assumed
here. -/
structure MetricFrameTimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop where
  metricSmooth :
    forall x : M, x ∈ u -> forall i j : Idx,
      ContDiffOn Real ⊤
        (fun t : Real => metricCompInFrame (I := I) S frame t x i j)
        D.carrier
  /-- Nondegeneracy is represented by an explicit two-sided inverse of the
  frame Gram matrix. -/
  nondegenerateGram :
    InverseMetricComponentsInFrameOn (I := I) S gInv frame
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)

/-- Spacetime metric regularity in a fixed local frame.

The extra mixed-derivative field is the fixed-base statement
`∂s d_x(g_s) = d_x(∂s g_s)` specialized to the Ricci-flow metric variation
`∂s g_s = -2 Ric_s`.  This is weaker than, and does not assert, commutation of
`∂t` with the evolving covariant derivative. -/
structure MetricFrameSpacetimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop extends
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u where
  frameMetricSpacetimeSmooth :
    forall i j : Idx,
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
        (fun p : Real × M => metricCompInFrame (I := I) S frame p.1 p.2 i j)
        (D.carrier ×ˢ u)
  frameMetricExtDerivTimeDerivative :
    forall (t : Realized.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall d a b : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x))
          ((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x))
          D.carrier
          (t : Real)

private noncomputable def frameEntryCLM
    [DecidableEq Idx] (i j : Idx) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.single Real (fun _ : Idx => Real) i).comp
      (LinearMap.proj (R := Real) (φ := fun _ : Idx => Real) j))

@[simp] private theorem frameEntryCLM_apply
    [DecidableEq Idx] (i j a : Idx) (v : Idx -> Real) :
    frameEntryCLM (Idx := Idx) i j v a =
      if a = i then v j else 0 := by
  classical
  by_cases h : a = i
  · subst a
    simp [frameEntryCLM]
  · simp [frameEntryCLM, h]

private noncomputable def frameGramCLM
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  ∑ i : Idx, ∑ j : Idx,
    metricCompInFrame (I := I) S frame p.1 p.2 i j •
      frameEntryCLM (Idx := Idx) i j

private noncomputable def frameGInvCLM
    [DecidableEq Idx]
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (p : Real × M) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  ∑ i : Idx, ∑ j : Idx,
    gInv p.1 p.2 i j • frameEntryCLM (Idx := Idx) i j

@[simp] private theorem frameGramCLM_apply
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M) (v : Idx -> Real) (i : Idx) :
    frameGramCLM (I := I) S frame p v i =
      ∑ j : Idx, metricCompInFrame (I := I) S frame p.1 p.2 i j * v j := by
  classical
  simp [frameGramCLM, Finset.sum_apply, mul_comm]

@[simp] private theorem frameGInvCLM_apply
    [DecidableEq Idx]
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (p : Real × M) (v : Idx -> Real) (i : Idx) :
    frameGInvCLM (Idx := Idx) gInv p v i =
      ∑ j : Idx, gInv p.1 p.2 i j * v j := by
  classical
  simp [frameGInvCLM, Finset.sum_apply]

private theorem contMDiffOn_finset_sum
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {D : Realized.RealTimeInterval} {u : Set M}
    {s : Finset ι} {f : ι -> Real × M -> V}
    (hf : forall a, a ∈ s ->
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, V) ⊤ (f a)
        (D.carrier ×ˢ u)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, V) ⊤
      (fun p => s.sum (fun a => f a p)) (D.carrier ×ˢ u) := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro hf
    simpa using
      (contMDiffOn_const
        (I := 𝓘(Real, Real).prod I) (I' := 𝓘(Real, V))
        (n := ⊤) (s := D.carrier ×ˢ u) (c := 0))
  · intro a s ha ih hf
    have hfa : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, V) ⊤
        (f a) (D.carrier ×ˢ u) := by
      exact hf a (Finset.mem_insert_self a s)
    have hsum : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, V) ⊤
        (fun p => s.sum (fun x => f x p)) (D.carrier ×ˢ u) := by
      exact ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    simpa [Finset.sum_insert ha] using hfa.add hsum

private theorem frameGramCLM_spacetimeSmooth
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u) :
    ContMDiffOn (𝓘(Real, Real).prod I)
      𝓘(Real, (Idx -> Real) →L[Real] (Idx -> Real)) ⊤
      (fun p : Real × M => frameGramCLM (I := I) S frame p)
      (D.carrier ×ˢ u) := by
  classical
  unfold frameGramCLM
  apply contMDiffOn_finset_sum
  intro i _hi
  apply contMDiffOn_finset_sum
  intro j _hj
  exact (hreg.frameMetricSpacetimeSmooth i j).smul contMDiffOn_const

private theorem metric_mul_inverse_apply
    [DecidableEq Idx]
    (metric gInv : Idx -> Idx -> Real)
    (hright : forall a b : Idx,
      (∑ k : Idx, metric a k * gInv k b) = (if a = b then 1 else 0))
    (v : Idx -> Real) (i : Idx) :
    (∑ j : Idx, metric i j * (∑ k : Idx, gInv j k * v k)) = v i := by
  classical
  calc
    (∑ j : Idx, metric i j * (∑ k : Idx, gInv j k * v k))
        = ∑ j : Idx, ∑ k : Idx, metric i j * (gInv j k * v k) := by
            simp [Finset.mul_sum]
    _ = ∑ k : Idx, ∑ j : Idx, metric i j * (gInv j k * v k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Idx, (∑ j : Idx, metric i j * gInv j k) * v k := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _hj => ?_
            ring
    _ = ∑ k : Idx, (if i = k then 1 else 0) * v k := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [hright i k]
    _ = v i := by
            simp

private theorem inverse_mul_metric_apply
    [DecidableEq Idx]
    (metric gInv : Idx -> Idx -> Real)
    (hleft : forall a b : Idx,
      (∑ k : Idx, gInv a k * metric k b) = (if a = b then 1 else 0))
    (v : Idx -> Real) (i : Idx) :
    (∑ j : Idx, gInv i j * (∑ k : Idx, metric j k * v k)) = v i := by
  classical
  calc
    (∑ j : Idx, gInv i j * (∑ k : Idx, metric j k * v k))
        = ∑ j : Idx, ∑ k : Idx, gInv i j * (metric j k * v k) := by
            simp [Finset.mul_sum]
    _ = ∑ k : Idx, ∑ j : Idx, gInv i j * (metric j k * v k) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Idx, (∑ j : Idx, gInv i j * metric j k) * v k := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _hj => ?_
            ring
    _ = ∑ k : Idx, (if i = k then 1 else 0) * v k := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [hleft i k]
    _ = v i := by
            simp

private theorem sum_mul_pi_single
    [DecidableEq Idx] (f : Idx -> Real) (j : Idx) :
    (∑ k : Idx, f k * Pi.single (M := fun _ : Idx => Real) j (1 : Real) k) = f j := by
  classical
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _hb hbj
    simp [Pi.single_eq_of_ne hbj]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

private theorem frameGramCLM_comp_frameGInvCLM
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (p : Real × M) :
    frameGramCLM (I := I) S frame p ∘L frameGInvCLM (Idx := Idx) gInv p =
      ContinuousLinearMap.id Real (Idx -> Real) := by
  classical
  ext v i
  simpa [ContinuousLinearMap.comp_apply] using
    metric_mul_inverse_apply
      (metric := fun a b => metricCompInFrame (I := I) S frame p.1 p.2 a b)
      (gInv := fun a b => gInv p.1 p.2 a b)
      (fun a b => (hinv p.1 p.2 a b).2)
      v i

private theorem frameGInvCLM_comp_frameGramCLM
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (p : Real × M) :
    frameGInvCLM (Idx := Idx) gInv p ∘L frameGramCLM (I := I) S frame p =
      ContinuousLinearMap.id Real (Idx -> Real) := by
  classical
  ext v i
  simpa [ContinuousLinearMap.comp_apply] using
    inverse_mul_metric_apply
      (metric := fun a b => metricCompInFrame (I := I) S frame p.1 p.2 a b)
      (gInv := fun a b => gInv p.1 p.2 a b)
      (fun a b => (hinv p.1 p.2 a b).1)
      v i

private theorem frameGramCLM_isInvertible
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (p : Real × M) :
    (frameGramCLM (I := I) S frame p).IsInvertible := by
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (frameGramCLM_comp_frameGInvCLM (I := I) S gInv frame hinv p)
    (frameGInvCLM_comp_frameGramCLM (I := I) S gInv frame hinv p)

private theorem frameGInvCLM_eq_inverse
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (p : Real × M) :
    ContinuousLinearMap.inverse (frameGramCLM (I := I) S frame p) =
      frameGInvCLM (Idx := Idx) gInv p := by
  exact ContinuousLinearMap.inverse_eq
    (frameGramCLM_comp_frameGInvCLM (I := I) S gInv frame hinv p)
    (frameGInvCLM_comp_frameGramCLM (I := I) S gInv frame hinv p)

private theorem frameGInvCLM_spacetimeSmooth
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u) :
    ContMDiffOn (𝓘(Real, Real).prod I)
      𝓘(Real, (Idx -> Real) →L[Real] (Idx -> Real)) ⊤
      (fun p : Real × M => frameGInvCLM (Idx := Idx) gInv p)
      (D.carrier ×ˢ u) := by
  classical
  intro p hp
  have hgram :=
    frameGramCLM_spacetimeSmooth (I := I) S gInv gInvDt frame hreg p hp
  have hinvAt :
      ContDiffAt Real ⊤ ContinuousLinearMap.inverse
        (frameGramCLM (I := I) S frame p) :=
    (frameGramCLM_isInvertible (I := I) S gInv frame
      hreg.nondegenerateGram p).contDiffAt_map_inverse
  have hcomp :
      ContMDiffWithinAt (𝓘(Real, Real).prod I)
        𝓘(Real, (Idx -> Real) →L[Real] (Idx -> Real)) ⊤
        (fun q : Real × M =>
          ContinuousLinearMap.inverse (frameGramCLM (I := I) S frame q))
        (D.carrier ×ˢ u) p :=
    by
      simpa [Function.comp_def] using hinvAt.comp_contMDiffWithinAt hgram
  refine hcomp.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards with q
  exact (frameGInvCLM_eq_inverse (I := I) S gInv frame hreg.nondegenerateGram q).symm

/-- Spacetime smoothness of the supplied inverse-metric components.

Dependencies:
* `frameMetricSpacetimeSmooth` supplies smooth frame Gram entries.
* `nondegenerateGram` identifies `gInv` as the two-sided inverse matrix.
* `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse` supplies smoothness
  of inversion on finite-dimensional continuous linear maps.
* `gInvDt` is threaded only because the existing regularity structure carries it;
  this theorem does not use the time derivative field directly. -/
theorem gInv_spacetimeSmooth
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (i j : Idx) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
      (fun p : Real × M => gInv p.1 p.2 i j)
      (D.carrier ×ˢ u) := by
  classical
  have hsmooth :=
    frameGInvCLM_spacetimeSmooth (I := I) S gInv gInvDt frame hreg
  have happ :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Idx -> Real) ⊤
        (fun p : Real × M =>
          frameGInvCLM (Idx := Idx) gInv p (Pi.single j 1))
        (D.carrier ×ˢ u) := by
    exact hsmooth.clm_apply contMDiffOn_const
  have hcoord :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
        (fun p : Real × M =>
          frameGInvCLM (Idx := Idx) gInv p (Pi.single j 1) i)
        (D.carrier ×ˢ u) := by
    exact (contMDiffOn_const
      (I := 𝓘(Real, Real).prod I)
      (I' := 𝓘(Real, (Idx -> Real) →L[Real] Real))
      (n := ⊤) (s := D.carrier ×ˢ u)
      (c := LinearMap.toContinuousLinearMap
        (LinearMap.proj (R := Real) (φ := fun _ : Idx => Real) i))).clm_apply happ
  refine hcoord.congr ?_
  intro p hp
  simpa using
    (sum_mul_pi_single (Idx := Idx) (fun k => gInv p.1 p.2 i k) j).symm

/-- Fixed-time spatial differentiability of inverse metric components, extracted
from the spacetime metric regularity package. -/
theorem MetricFrameSpacetimeRegularityInFrameOnLocal.gInv_mdiffAt
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (t : Realized.RealTimeInterval.RegularTime D)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => gInv (t : Real) y i j) x := by
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hslice :
      ContMDiffOn I (𝓘(Real, Real).prod I) ⊤
        (fun y : M => ((t : Real), y)) u := by
    exact (contMDiffOn_const (c := (t : Real))).prodMk contMDiffOn_id
  have hsmooth :=
    gInv_spacetimeSmooth (I := I) S gInv gInvDt frame hreg i j
  have hcomp :
      ContMDiffOn I 𝓘(Real, Real) ⊤
        ((fun p : Real × M => gInv p.1 p.2 i j) ∘
          fun y : M => ((t : Real), y)) u := by
    exact hsmooth.comp hslice (by
      intro y hy
      exact ⟨ht, hy⟩)
  exact (hcomp.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt (by simp)

/-- Fixed-time spatial differentiability of metric frame components, extracted
from the spacetime metric regularity package. -/
theorem MetricFrameSpacetimeRegularityInFrameOnLocal.metricComp_mdiffAt
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (t : Realized.RealTimeInterval.RegularTime D)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => metricCompInFrame (I := I) S frame (t : Real) y i j) x := by
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hslice :
      ContMDiffOn I (𝓘(Real, Real).prod I) ⊤
        (fun y : M => ((t : Real), y)) u := by
    exact (contMDiffOn_const (c := (t : Real))).prodMk contMDiffOn_id
  have hsmooth := hreg.frameMetricSpacetimeSmooth i j
  have hcomp :
      ContMDiffOn I 𝓘(Real, Real) ⊤
        ((fun p : Real × M =>
            metricCompInFrame (I := I) S frame p.1 p.2 i j) ∘
          fun y : M => ((t : Real), y)) u := by
    exact hsmooth.comp hslice (by
      intro y hy
      exact ⟨ht, hy⟩)
  exact (hcomp.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt (by simp)

/-- Covariant derivative components of the inverse metric in a local frame.

For a metric-compatible connection these components vanish:
`nabla_d g^{kl} = 0`.  The signs are the contravariant-slot convention. -/
def inverseMetricCovDerivCompInFrame
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Real) (x : M) (d k l : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a k * gInv t x a l) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a l * gInv t x k a)

private theorem metric_localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

theorem metricCompInFrame_extDerivFun_eq_christoffel
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Real)
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (hg : g = S.family.metric t)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompInFrame (I := I) S frame t y a b)
        x (frame d x) =
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d a p *
          metricCompInFrame (I := I) S frame t x p b) +
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d b p *
          metricCompInFrame (I := I) S frame t x a p) := by
  classical
  subst hg
  have hd := metric_localFrame_mdiffAt (I := I) frame hframe hu hx d
  have ha := metric_localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hb := metric_localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmetric :=
    RicciFlower.Connection.metric_compatible_apply
      (I := I) hmc (frame d) (frame a) (frame b) hd ha hb
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M => metricCompInFrame (I := I) S frame t y a b)
          x (frame d x) =
        (S.family.metric t).inner x
          ((cov (frame a) x) (frame d x)) (frame b x) +
        (S.family.metric t).inner x (frame a x)
          ((cov (frame b) x) (frame d x)) := by
    simpa [extDerivFun, metricCompInFrame] using hmetric
  rw [hmetric']
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d a]
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d b]
  simp [metricCompInFrame, map_sum]

theorem metric_mdiffAt_finset_sum
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

theorem metric_extDerivFun_finset_sum
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
        exact metric_mdiffAt_finset_sum (I := I) t f hft
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

theorem metric_extDerivFun_mul
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

private theorem inverseMetric_derivative_row_eq
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    (∑ a : Idx,
        (gInvDt (t : Real) x i a *
          metricCompInFrame (I := I) S frame (t : Real) x a j +
        gInv (t : Real) x i a *
          ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j))) =
      0 := by
  let lhs : Real -> Real :=
    fun s => ∑ a : Idx,
      gInv s x i a * metricCompInFrame (I := I) S frame s x a j
  have hlhs :
      HasDerivWithinAt lhs
        (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j)))
        D.carrier
        (t : Real) := by
    dsimp [lhs]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          gInv s x i a * metricCompInFrame (I := I) S frame s x a j)
        (A' := fun a =>
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j)))
        (s := D.carrier) (x := (t : Real))
        (fun a _ha =>
          by
            exact (hdt t x i a).mul
              (metricCompInFrame_hasDerivWithinAt (I := I) S hS frame t x a j)))
  have hconst :
      HasDerivWithinAt lhs 0 D.carrier (t : Real) := by
    dsimp [lhs]
    exact
      (hasDerivWithinAt_const
        (x := (t : Real)) (s := D.carrier)
        (c := (if i = j then 1 else 0 : Real))).congr
        (fun s _hs => by
          exact (hinv s x i j).1)
        (by
          exact (hinv (t : Real) x i j).1)
  have h1 := hlhs.derivWithin (hunique t)
  have h0 := hconst.derivWithin (hunique t)
  exact h1.symm.trans h0

theorem inverseMetric_derivative_solve
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
`nabla_d g^{kl} = 0`.

The differentiability hypotheses are deliberately explicit.  In Ricci-flow
applications they should be supplied by `gInv_spacetimeSmooth` and the
regularity package for the first Ricci covariant derivative. -/
theorem inverseMetricCovDerivCompInFrame_eq_zero
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (t : Real)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I)
      cov (S.family.metric t))
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompInFrame (I := I) S frame t y a b) x)
    (d k l : Idx) :
    inverseMetricCovDerivCompInFrame (I := I) gInv cov frame hframe t x d k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompInFrame (I := I) S frame t x a b
  let U : Idx -> Idx -> Real := fun a b => gInv t x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompInFrame (I := I) S frame t y a b)
      x (frame d x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv t y a b) x (frame d x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelSymbolInFrame cov frame hframe x d a b
  have hsymm : SymmetricInverseMetricComponentsInFrameOn gInv :=
    gInv_symm (I := I) S gInv frame hinv
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompInFrame_extDerivFun_eq_christoffel
        (I := I) S cov t (S.family.metric t) hmc rfl frame hframe hu hx d a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv t y k a * metricCompInFrame (I := I) S frame t y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
      simpa using metric_extDerivFun_finset_sum
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (frame d x) =
          gInv t x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        metric_extDerivFun_mul (I := I) (x := x) (frame d x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv t y k a * metricCompInFrame (I := I) S frame t y a m) =
        (fun _ : M => if k = m then 1 else 0) := by
      funext y
      exact (hinv t y k m).1
    have hderiv :=
      congrArg (fun F : M -> Real => extDerivFun (I := I) F x (frame d x)) hconst
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv t y k a * metricCompInFrame (I := I) S frame t y a m)
          x (frame d x) = 0 := by
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv t y k a * metricCompInFrame (I := I) S frame t y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv t x k a * DG a m + DU k a * G a m) := by
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
      simpa [G, U] using (hinv t x a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv t x a b).2)
    (by
      intro a b
      simpa [G, metricCompInFrame] using
        (S.family.metric t).symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv t x k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv t x l b * G p b = G p b * gInv t x b l
              rw [hsymm t x l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv t x p l).2
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
            change gInv t x l a * Γ a k = Γ a k * gInv t x a l
            rw [hsymm t x l a]
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
  unfold inverseMetricCovDerivCompInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring

/-- Inverse-metric evolution from the differentiated identity `g^{-1}g = I`.

The proof uses the Ricci-flow metric derivative, the product rule on the
left-inverse identity, uniqueness of the interval derivative, and the two-sided
inverse identity to solve for the component derivative.  Inverse-metric
symmetry is derived from the two-sided inverse identities. -/
theorem inverseMetricEvolutionEquationInFrame_of_inverse_components
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame := by
  intro t x i j
  have hrow : forall m : Idx,
      (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a m +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a m))) =
        0 := by
    intro m
    exact inverseMetric_derivative_row_eq
      (I := I) S hS gInv gInvDt frame hdt hinv hunique t x i m
  have hsolve :
      gInvDt (t : Real) x i j =
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j := by
    unfold inverseMetricEvolutionRHSInFrame raisedRicciCompInFrame
    exact inverseMetric_derivative_solve
      (metric := fun a b => metricCompInFrame (I := I) S frame (t : Real) x a b)
      (ric := fun a b => ricciCompInFrame (I := I) S frame (t : Real) x a b)
      (gInv := fun a b => gInv (t : Real) x a b)
      (gInvDt := fun a b => gInvDt (t : Real) x a b)
      i
      hrow
      (fun a b => (hinv (t : Real) x a b).1)
      (fun a b => (hinv (t : Real) x a b).2)
      (fun a b => by
        simpa [metricCompInFrame] using
          (S.family.metric (t : Real)).symm x (frame a x) (frame b x))
      j
  exact (hdt t x i j).congr_deriv hsolve

/-- Metric-frame regularity produces the inverse-metric evolution equation.

The computation is the existing inverse-identity differentiation theorem; this
wrapper keeps the future matrix-inverse smoothness work attached to the metric
regularity package rather than to the Christoffel evolution layer. -/
theorem inverseMetricEvolution_of_metricFrameTimeRegularity
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame :=
  inverseMetricEvolutionEquationInFrame_of_inverse_components
    (I := I) S hS gInv gInvDt frame
    hreg.inverseMetricDerivative
    hreg.nondegenerateGram
    hreg.uniqueTimeDerivatives

/-- LaTeX Lemma 6.1 in fixed-frame component form:
`partial_t g^{ij} = 2 Ric^{ij}`. -/
theorem evol_inverse_metric_inFrame
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (2 * raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have hEq : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame :=
    inverseMetricEvolution_of_metricFrameTimeRegularity
      (I := I) S hS gInv gInvDt frame hreg
  have h :=
    inverseMetricEvolutionEquationInFrame_apply
      (I := I) (S := S) (gInv := gInv) (frame := frame) hEq t x i j
  simpa [inverseMetricEvolutionRHSInFrame] using h

end Components

end RicciFlow
end RicciFlower
