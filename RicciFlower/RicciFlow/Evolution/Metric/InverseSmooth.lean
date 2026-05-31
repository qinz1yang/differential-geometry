import RicciFlower.RicciFlow.Evolution.Metric.Basic

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
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}

noncomputable def frameEntryCLM
    [DecidableEq Idx] (i j : Idx) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.single Real (fun _ : Idx => Real) i).comp
      (LinearMap.proj (R := Real) (φ := fun _ : Idx => Real) j))

@[simp] theorem frameEntryCLM_apply
    [DecidableEq Idx] (i j a : Idx) (v : Idx -> Real) :
    frameEntryCLM (Idx := Idx) i j v a =
      if a = i then v j else 0 := by
  classical
  by_cases h : a = i
  · subst a
    simp [frameEntryCLM]
  · simp [frameEntryCLM, h]

noncomputable def frameGramCLM
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  ∑ i : Idx, ∑ j : Idx,
    metricCompInFrame (I := I) S frame p.1 p.2 i j •
      frameEntryCLM (Idx := Idx) i j

noncomputable def frameGInvCLM
    [DecidableEq Idx]
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (p : Real × M) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  ∑ i : Idx, ∑ j : Idx,
    gInv p.1 p.2 i j • frameEntryCLM (Idx := Idx) i j

@[simp] theorem frameGramCLM_apply
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M) (v : Idx -> Real) (i : Idx) :
    frameGramCLM (I := I) S frame p v i =
      ∑ j : Idx, metricCompInFrame (I := I) S frame p.1 p.2 i j * v j := by
  classical
  simp [frameGramCLM, Finset.sum_apply, mul_comm]

@[simp] theorem frameGInvCLM_apply
    [DecidableEq Idx]
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (p : Real × M) (v : Idx -> Real) (i : Idx) :
    frameGInvCLM (Idx := Idx) gInv p v i =
      ∑ j : Idx, gInv p.1 p.2 i j * v j := by
  classical
  simp [frameGInvCLM, Finset.sum_apply]

noncomputable def matrixCLM
    [DecidableEq Idx] (A : Idx -> Idx -> Real) :
    (Idx -> Real) →L[Real] (Idx -> Real) :=
  ∑ i : Idx, ∑ j : Idx, A i j • frameEntryCLM (Idx := Idx) i j

@[simp] theorem matrixCLM_apply
    [DecidableEq Idx] (A : Idx -> Idx -> Real)
    (v : Idx -> Real) (i : Idx) :
    matrixCLM (Idx := Idx) A v i = ∑ j : Idx, A i j * v j := by
  classical
  simp [matrixCLM, Finset.sum_apply]

theorem contMDiffOn_finset_sum
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

theorem frameGramCLM_spacetimeSmooth
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

theorem metric_mul_inverse_apply
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

theorem inverse_mul_metric_apply
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

theorem sum_mul_pi_single
    [DecidableEq Idx] (f : Idx -> Real) (j : Idx) :
    (∑ k : Idx, f k * Pi.single (M := fun _ : Idx => Real) j (1 : Real) k) = f j := by
  classical
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _hb hbj
    simp [Pi.single_eq_of_ne hbj]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

theorem matrixInvDerivEntry
    [DecidableEq Idx]
    (gInv ric : Idx -> Idx -> Real)
    (hsymm : forall a b : Idx, gInv a b = gInv b a)
    (i j : Idx) :
    ((-(matrixCLM (Idx := Idx) gInv *
          matrixCLM (Idx := Idx) (fun a b => (-2 : Real) * ric a b) *
          matrixCLM (Idx := Idx) gInv))
        (Pi.single (M := fun _ : Idx => Real) j (1 : Real))) i =
      2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
  classical
  calc
    ((-(matrixCLM (Idx := Idx) gInv *
          matrixCLM (Idx := Idx) (fun a b => (-2 : Real) * ric a b) *
          matrixCLM (Idx := Idx) gInv))
        (Pi.single (M := fun _ : Idx => Real) j (1 : Real))) i
        =
        2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv b j * ric a b) := by
          simp [ContinuousLinearMap.mul_apply, Finset.mul_sum,
            mul_assoc, mul_left_comm, mul_comm, sum_mul_pi_single]
    _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
          congr 1
          refine Finset.sum_congr rfl fun a _ha => ?_
          refine Finset.sum_congr rfl fun b _hb => ?_
          rw [hsymm b j]

theorem frameGramCLM_comp_frameGInvCLM
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

theorem frameGInvCLM_comp_frameGramCLM
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

theorem frameGramCLM_isInvertible
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

theorem frameGInvCLM_eq_inverse
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

theorem frameGramCLM_comp_frameGInvCLM_at
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M)
    (_hleft : forall a b : Idx,
      (∑ k : Idx,
        gInv p.1 p.2 a k * metricCompInFrame (I := I) S frame p.1 p.2 k b) =
        (if a = b then 1 else 0))
    (hright : forall a b : Idx,
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame p.1 p.2 a k * gInv p.1 p.2 k b) =
        (if a = b then 1 else 0)) :
    frameGramCLM (I := I) S frame p ∘L frameGInvCLM (Idx := Idx) gInv p =
      ContinuousLinearMap.id Real (Idx -> Real) := by
  classical
  ext v i
  simpa [ContinuousLinearMap.comp_apply] using
    metric_mul_inverse_apply
      (metric := fun a b => metricCompInFrame (I := I) S frame p.1 p.2 a b)
      (gInv := fun a b => gInv p.1 p.2 a b)
      hright v i

theorem frameGInvCLM_comp_frameGramCLM_at
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M)
    (hleft : forall a b : Idx,
      (∑ k : Idx,
        gInv p.1 p.2 a k * metricCompInFrame (I := I) S frame p.1 p.2 k b) =
        (if a = b then 1 else 0))
    (_hright : forall a b : Idx,
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame p.1 p.2 a k * gInv p.1 p.2 k b) =
        (if a = b then 1 else 0)) :
    frameGInvCLM (Idx := Idx) gInv p ∘L frameGramCLM (I := I) S frame p =
      ContinuousLinearMap.id Real (Idx -> Real) := by
  classical
  ext v i
  simpa [ContinuousLinearMap.comp_apply] using
    inverse_mul_metric_apply
      (metric := fun a b => metricCompInFrame (I := I) S frame p.1 p.2 a b)
      (gInv := fun a b => gInv p.1 p.2 a b)
      hleft v i

theorem frameGramCLM_isInvertible_at
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M)
    (hleft : forall a b : Idx,
      (∑ k : Idx,
        gInv p.1 p.2 a k * metricCompInFrame (I := I) S frame p.1 p.2 k b) =
        (if a = b then 1 else 0))
    (hright : forall a b : Idx,
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame p.1 p.2 a k * gInv p.1 p.2 k b) =
        (if a = b then 1 else 0)) :
    (frameGramCLM (I := I) S frame p).IsInvertible := by
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (frameGramCLM_comp_frameGInvCLM_at (I := I) S gInv frame p hleft hright)
    (frameGInvCLM_comp_frameGramCLM_at (I := I) S gInv frame p hleft hright)

theorem frameGInvCLM_eq_inverse_at
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (p : Real × M)
    (hleft : forall a b : Idx,
      (∑ k : Idx,
        gInv p.1 p.2 a k * metricCompInFrame (I := I) S frame p.1 p.2 k b) =
        (if a = b then 1 else 0))
    (hright : forall a b : Idx,
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame p.1 p.2 a k * gInv p.1 p.2 k b) =
        (if a = b then 1 else 0)) :
    ContinuousLinearMap.inverse (frameGramCLM (I := I) S frame p) =
      frameGInvCLM (Idx := Idx) gInv p := by
  exact ContinuousLinearMap.inverse_eq
    (frameGramCLM_comp_frameGInvCLM_at (I := I) S gInv frame p hleft hright)
    (frameGInvCLM_comp_frameGramCLM_at (I := I) S gInv frame p hleft hright)

theorem frameGramCLM_hasDerivWithinAt
    [DecidableEq Idx]
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Realized.RealTimeInterval.RegularTime D)
    (x : M) :
    HasDerivWithinAt
      (fun s : Real => frameGramCLM (I := I) S frame (s, x))
      (matrixCLM (Idx := Idx)
        (fun a b => (-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a b))
      D.carrier
      (t : Real) := by
  classical
  unfold frameGramCLM matrixCLM
  simpa using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun a s =>
        ∑ b : Idx,
          metricCompInFrame (I := I) S frame s x a b •
            frameEntryCLM (Idx := Idx) a b)
      (A' := fun a =>
        ∑ b : Idx,
          ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a b) •
            frameEntryCLM (Idx := Idx) a b)
      (s := D.carrier) (x := (t : Real))
      (fun a _ha =>
        by
          simpa using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s =>
                metricCompInFrame (I := I) S frame s x a b •
                  frameEntryCLM (Idx := Idx) a b)
              (A' := fun b =>
                ((-2 : Real) *
                    ricciCompInFrame (I := I) S frame (t : Real) x a b) •
                  frameEntryCLM (Idx := Idx) a b)
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                (metricCompInFrame_hasDerivWithinAt
                  (I := I) S hS frame t x a b).smul_const
                    (frameEntryCLM (Idx := Idx) a b)))))

theorem hasFDerivAt_clmInv
    (A : (Idx -> Real) →L[Real] (Idx -> Real))
    (hA : A.IsInvertible) :
    HasFDerivAt ContinuousLinearMap.inverse
      (-(ContinuousLinearMap.mulLeftRight Real
          ((Idx -> Real) →L[Real] (Idx -> Real)) A.inverse A.inverse))
      A := by
  rcases hA with ⟨e, rfl⟩
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  simpa [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.toUnit] using
    (hasFDerivAt_ringInverse (ContinuousLinearEquiv.toUnit e))

theorem coordInvCLM_eq
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) {x : M}
    (hx : x ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (s : Real) :
    ContinuousLinearMap.inverse
        (frameGramCLM (I := I) S (Coordinates.coordinateFrameAt (I := I) x0)
          (s, x)) =
      frameGInvCLM (Idx := Coordinates.CoordinateIdx E)
        (coordInv (I := I) S x0) (s, x) := by
  classical
  have hbasis :=
    Coordinates.gInvBasisAt (I := I) (S.family.metric s) x0 hx
  exact
    frameGInvCLM_eq_inverse_at
      (I := I) S (coordInv (I := I) S x0)
      (Coordinates.coordinateFrameAt (I := I) x0) (s, x)
      (by
        intro a b
        simpa [coordInv, metricCompInFrame,
          Coordinates.coordinateFrameAt_basis_apply] using (hbasis a b).1)
        (by
          intro a b
          simpa [coordInv, metricCompInFrame,
            Coordinates.coordinateFrameAt_basis_apply] using (hbasis a b).2)

theorem coordFrameGramCLM_spacetimeSmooth
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) :
    ContMDiffOn (𝓘(Real, Real).prod I)
      𝓘(Real,
        (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) →L[Real]
          (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)) ⊤
      (fun p : Real × M =>
        frameGramCLM (I := I) S (Coordinates.coordinateFrameAt (I := I) x0) p)
      (D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0) := by
  classical
  unfold frameGramCLM
  apply contMDiffOn_finset_sum
  intro i _hi
  apply contMDiffOn_finset_sum
  intro j _hj
  exact (coordMetricSmooth (I := I) S hS x0 i j).smul contMDiffOn_const

theorem coordFrameGInvCLM_spacetimeSmooth
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) :
    ContMDiffOn (𝓘(Real, Real).prod I)
      𝓘(Real,
        (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) →L[Real]
          (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)) ⊤
      (fun p : Real × M =>
        frameGInvCLM (Idx := Coordinates.CoordinateIdx (𝕜 := Real) E)
          (coordInv (I := I) S x0) p)
      (D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0) := by
  classical
  intro p hp
  have hgram := coordFrameGramCLM_spacetimeSmooth (I := I) S hS x0 p hp
  have hbasis :=
    Coordinates.gInvBasisAt (I := I) (S.family.metric p.1) x0 hp.2
  have hleft : ∀ a b : Coordinates.CoordinateIdx (𝕜 := Real) E,
      (∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        coordInv (I := I) S x0 p.1 p.2 a k *
          metricCompInFrame (I := I) S
            (Coordinates.coordinateFrameAt (I := I) x0) p.1 p.2 k b) =
        (if a = b then 1 else 0) := by
    intro a b
    simpa [coordInv, metricCompInFrame,
      Coordinates.coordinateFrameAt_basis_apply] using (hbasis a b).1
  have hright : ∀ a b : Coordinates.CoordinateIdx (𝕜 := Real) E,
      (∑ k : Coordinates.CoordinateIdx (𝕜 := Real) E,
        metricCompInFrame (I := I) S
            (Coordinates.coordinateFrameAt (I := I) x0) p.1 p.2 a k *
          coordInv (I := I) S x0 p.1 p.2 k b) =
        (if a = b then 1 else 0) := by
    intro a b
    simpa [coordInv, metricCompInFrame,
      Coordinates.coordinateFrameAt_basis_apply] using (hbasis a b).2
  have hinvAt :
      ContDiffAt Real ⊤ ContinuousLinearMap.inverse
        (frameGramCLM (I := I) S
          (Coordinates.coordinateFrameAt (I := I) x0) p) :=
    (frameGramCLM_isInvertible_at
      (I := I) S (coordInv (I := I) S x0)
      (Coordinates.coordinateFrameAt (I := I) x0) p
      hleft hright).contDiffAt_map_inverse
  have hcomp :
      ContMDiffWithinAt (𝓘(Real, Real).prod I)
        𝓘(Real,
          (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) →L[Real]
            (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)) ⊤
        (fun q : Real × M =>
          ContinuousLinearMap.inverse
            (frameGramCLM (I := I) S
              (Coordinates.coordinateFrameAt (I := I) x0) q))
        (D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0) p := by
    simpa [Function.comp_def] using hinvAt.comp_contMDiffWithinAt hgram
  refine hcomp.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact
    (coordInvCLM_eq (I := I) S x0 (x := q.2) hq.2 q.1).symm

/-- Canonical coordinate inverse metric components are jointly smooth on the
coordinate-frame spacetime domain. -/
theorem coordInvSmooth
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (i j : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
      (fun p : Real × M => coordInv (I := I) S x0 p.1 p.2 i j)
      (D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0) := by
  classical
  have hsmooth :=
    coordFrameGInvCLM_spacetimeSmooth (I := I) S hS x0
  have happ :
      ContMDiffOn (𝓘(Real, Real).prod I)
        𝓘(Real, Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) ⊤
        (fun p : Real × M =>
          frameGInvCLM (Idx := Coordinates.CoordinateIdx (𝕜 := Real) E)
            (coordInv (I := I) S x0) p
            (Pi.single j 1))
        (D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0) := by
    exact hsmooth.clm_apply contMDiffOn_const
  have hcoord :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
        (fun p : Real × M =>
          frameGInvCLM (Idx := Coordinates.CoordinateIdx (𝕜 := Real) E)
            (coordInv (I := I) S x0) p
            (Pi.single j 1) i)
        (D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0) := by
    exact (contMDiffOn_const
      (I := 𝓘(Real, Real).prod I)
      (I' := 𝓘(Real, (Coordinates.CoordinateIdx (𝕜 := Real) E -> Real) →L[Real] Real))
      (n := ⊤) (s := D.carrier ×ˢ Coordinates.coordinateFrameSet (I := I) x0)
      (c := LinearMap.toContinuousLinearMap
        (LinearMap.proj (R := Real)
          (φ := fun _ : Coordinates.CoordinateIdx (𝕜 := Real) E => Real) i))).clm_apply happ
  refine hcoord.congr ?_
  intro p hp
  simpa using
    (sum_mul_pi_single (Idx := Coordinates.CoordinateIdx (𝕜 := Real) E)
      (fun k => coordInv (I := I) S x0 p.1 p.2 i k) j).symm

/-- Pointwise spacetime smoothness of canonical coordinate inverse metric
components at regular times and coordinate-frame points. -/
theorem coordInvSmoothAt
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (t : Realized.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ Coordinates.coordinateFrameSet (I := I) x0)
    (i j : Coordinates.CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ⊤
      (fun p : Real × M => coordInv (I := I) S x0 p.1 p.2 i j)
      ((t : Real), x) := by
  exact
    (coordInvSmooth (I := I) S hS x0 i j).contMDiffAt
      (prod_mem_nhds (D.regular_mem_nhds t.2)
        ((Coordinates.coordinateFrameSet_open (I := I) x0).mem_nhds hx))

theorem frameGInvCLM_spacetimeSmooth
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
  have hleft : forall a b : Idx,
      (∑ k : Idx,
        gInv p.1 p.2 a k *
          metricCompInFrame (I := I) S frame p.1 p.2 k b) =
        (if a = b then 1 else 0) := by
    intro a b
    exact (hreg.nondegenerateGram p.1 p.2 hp.2 a b).1
  have hright : forall a b : Idx,
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame p.1 p.2 a k *
          gInv p.1 p.2 k b) =
        (if a = b then 1 else 0) := by
    intro a b
    exact (hreg.nondegenerateGram p.1 p.2 hp.2 a b).2
  have hinvAt :
      ContDiffAt Real ⊤ ContinuousLinearMap.inverse
        (frameGramCLM (I := I) S frame p) :=
    (frameGramCLM_isInvertible_at (I := I) S gInv frame p
      hleft hright).contDiffAt_map_inverse
  have hcomp :
      ContMDiffWithinAt (𝓘(Real, Real).prod I)
        𝓘(Real, (Idx -> Real) →L[Real] (Idx -> Real)) ⊤
        (fun q : Real × M =>
          ContinuousLinearMap.inverse (frameGramCLM (I := I) S frame q))
        (D.carrier ×ˢ u) p :=
    by
      simpa [Function.comp_def] using hinvAt.comp_contMDiffWithinAt hgram
  refine hcomp.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hleftq : forall a b : Idx,
      (∑ k : Idx,
        gInv q.1 q.2 a k *
          metricCompInFrame (I := I) S frame q.1 q.2 k b) =
        (if a = b then 1 else 0) := by
    intro a b
    exact (hreg.nondegenerateGram q.1 q.2 hq.2 a b).1
  have hrightq : forall a b : Idx,
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame q.1 q.2 a k *
          gInv q.1 q.2 k b) =
        (if a = b then 1 else 0) := by
    intro a b
    exact (hreg.nondegenerateGram q.1 q.2 hq.2 a b).2
  exact (frameGInvCLM_eq_inverse_at (I := I) S gInv frame q
    hleftq hrightq).symm

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


end Components

end RicciFlow
end RicciFlower
