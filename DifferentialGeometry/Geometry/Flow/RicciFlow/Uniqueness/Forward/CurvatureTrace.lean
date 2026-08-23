import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureBounds
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Tensor.RSTensor.NormSqProduct

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section TraceSlots

def rm04TraceSlots : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide
  right_inv := by decide

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem traceInput_domDomCongr {x : M}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y : TangentSpace I x) (tail : Fin 2 -> TangentSpace I x) :
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04)
        (metricTraceInput (I := I) X Y tail) =
      Rm04 (vec4 (I := I) X (tail 0) (tail 1) Y) := by
  have h :
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04)
          (metricTraceInput (I := I) X Y tail) =
        Rm04 (fun m => metricTraceInput (I := I) X Y tail (rm04TraceSlots m)) := rfl
  rw [h]
  congr 1
  funext m
  fin_cases m <;> rfl

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem domDomCongr_sub {x : M} {s s' : Nat} (e : Fin s ≃ Fin s')
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    ContinuousMultilinearMap.domDomCongr e (A - B) =
      ContinuousMultilinearMap.domDomCongr e A -
        ContinuousMultilinearMap.domDomCongr e B := by
  refine tensor0SSpace_ext (𝕜 := Real) s' x fun v => ?_
  have hD := Tensor0SSpace.sub_apply (I := I) s' x
    (ContinuousMultilinearMap.domDomCongr e A)
    (ContinuousMultilinearMap.domDomCongr e B) v
  have hE := Tensor0SSpace.sub_apply (I := I) s x A B (fun i => v (e i))
  calc (ContinuousMultilinearMap.domDomCongr e (A - B)) v
      = (A - B) (fun i => v (e i)) := rfl
    _ = A (fun i => v (e i)) - B (fun i => v (e i)) := hE
    _ = (ContinuousMultilinearMap.domDomCongr e A) v -
        (ContinuousMultilinearMap.domDomCongr e B) v := rfl
    _ = (ContinuousMultilinearMap.domDomCongr e A -
        ContinuousMultilinearMap.domDomCongr e B) v := hD.symm

end TraceSlots

section RicciTrace

omit [SigmaCompactSpace M] [T2Space M] in
theorem ricci_eq_trace_rm04 (g : SmoothRiemannianMetric I M) {x : M}
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x Rm13 Rm04) :
    ricciFromRm13At (I := I) (M := M) Rm13 =
      metricTraceFirstTwo0STensor (I := I) g
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04) := by
  classical
  set basis := Module.finBasis Real (TangentSpace I x) with hbasisdef
  set gInv := basisInvMetric (I := I) g x basis with hgInvdef
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    basisInvMetric_real (I := I) g x basis
  refine tensor0SSpace_ext (𝕜 := Real) 2 x fun u => ?_
  set L : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    ricciFromRm13At (I := I) (M := M) Rm13 with hLdef
  set R : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    metricTraceFirstTwo0STensor (I := I) g
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04) with hRdef
  suffices h : L.toMultilinearMap = R.toMultilinearMap by
    exact congrArg
      (fun T : MultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 2 => basis) ?_
  intro v
  change L (fun i => basis (v i)) = R (fun i => basis (v i))
  have hL : L (fun i => basis (v i)) =
      ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) (v 0) (v 1) := by
    rw [ricciCompAt_apply, hLdef]
    congr 1
    funext a
    fin_cases a <;> rfl
  have hR : R (fun i => basis (v i)) =
      ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
        ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
          gInv a k * rm04CompAt (I := I) basis Rm04 a (v 0) (v 1) k := by
    rw [hRdef]
    change metricTraceFirstTwo0STensor (I := I) g
      (ContinuousMultilinearMap.domDomCongr rm04TraceSlots Rm04)
        (fun i => basis (v i)) = _
    rw [metricTraceFirstTwo0STensor_apply,
      ← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [rm04CompAt_apply]
    exact traceInput_domDomCongr (I := I) Rm04 (basis a) (basis k) (fun i => basis (v i))
  rw [hL, hR,
    ricciFromRm13_comp_eq_rm04_trace (I := I) g basis gInv hinv Rm13 Rm04 hLower]

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricRicci_eq_trace (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g x =
      metricTraceFirstTwo0STensor (I := I) g
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (metricRm04At (I := I) g x)) :=
  ricci_eq_trace_rm04 (I := I) g (metricRm13At (I := I) g x) (metricRm04At (I := I) g x)
    (fun X Y Z W =>
      CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
        (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) X Y Z W)

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricRicci_eq_trace_cross (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g₂ x =
      metricTraceFirstTwo0STensor (I := I) g₁
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (CovariantDerivative.riemannCurvature04At (I := I) g₁
            (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x)) :=
  ricci_eq_trace_rm04 (I := I) g₁ (metricRm13At (I := I) g₂ x) _
    (fun X Y Z W =>
      CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) X Y Z W)

omit [SigmaCompactSpace M] [T2Space M] in
private theorem trace_sub (g : SmoothRiemannianMetric I M) {x : M} {s : Nat}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    metricTraceFirstTwo0STensor (I := I) g A -
        metricTraceFirstTwo0STensor (I := I) g B =
      metricTraceFirstTwo0STensor (I := I) g (A - B) := by
  classical
  set basis := Module.finBasis Real (TangentSpace I x) with hbasisdef
  set gInv := basisInvMetric (I := I) g x basis with hgInvdef
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    basisInvMetric_real (I := I) g x basis
  refine tensor0SSpace_ext (𝕜 := Real) s x fun tail => ?_
  have key : ∀ T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x,
      metricTraceFirstTwo0SAt (I := I) g T tail =
        ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
            gInv a k * T (metricTraceInput (I := I) (basis a) (basis k) tail) := by
    intro T
    rw [← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv]
    rfl
  have hsub := Tensor0SSpace.sub_apply (I := I) s x
    (metricTraceFirstTwo0STensor (I := I) g A)
    (metricTraceFirstTwo0STensor (I := I) g B) tail
  calc (metricTraceFirstTwo0STensor (I := I) g A -
          metricTraceFirstTwo0STensor (I := I) g B) tail
      = metricTraceFirstTwo0STensor (I := I) g A tail -
        metricTraceFirstTwo0STensor (I := I) g B tail := hsub
    _ = (∑ a : Fin (Module.finrank Real (TangentSpace I x)),
            ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
              gInv a k * A (metricTraceInput (I := I) (basis a) (basis k) tail)) -
          ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
            ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
              gInv a k * B (metricTraceInput (I := I) (basis a) (basis k) tail) := by
        rw [metricTraceFirstTwo0STensor_apply, metricTraceFirstTwo0STensor_apply,
          key A, key B]
    _ = ∑ a : Fin (Module.finrank Real (TangentSpace I x)),
          ∑ k : Fin (Module.finrank Real (TangentSpace I x)),
            gInv a k * (A - B) (metricTraceInput (I := I) (basis a) (basis k) tail) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hAB := Tensor0SSpace.sub_apply (I := I) (s + 2) x A B
          (metricTraceInput (I := I) (basis a) (basis k) tail)
        calc gInv a k * A (metricTraceInput (I := I) (basis a) (basis k) tail) -
              gInv a k * B (metricTraceInput (I := I) (basis a) (basis k) tail)
            = gInv a k * (A (metricTraceInput (I := I) (basis a) (basis k) tail) -
                B (metricTraceInput (I := I) (basis a) (basis k) tail)) := by ring
          _ = gInv a k * (A - B) (metricTraceInput (I := I) (basis a) (basis k) tail) :=
              congrArg (fun r : Real => gInv a k * r) hAB.symm
    _ = metricTraceFirstTwo0STensor (I := I) g (A - B) tail := by
        rw [metricTraceFirstTwo0STensor_apply, key (A - B)]

omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciDiff_eq_trace (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x =
      metricTraceFirstTwo0STensor (I := I) g₁
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (rmDiffLowAt (I := I) g₁ g₂ x)) := by
  have h₁ := metricRicci_eq_trace (I := I) g₁ x
  have h₂ := metricRicci_eq_trace_cross (I := I) g₁ g₂ x
  have h₃ := domDomCongr_sub (I := I) (x := x) rm04TraceSlots
    (metricRm04At (I := I) g₁ x)
    (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x)
  have h₄ := trace_sub (I := I) (s := 2) g₁
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots (metricRm04At (I := I) g₁ x))
    (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
      (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
        (metricCov_smooth (I := I) g₂) x))
  calc metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x
      = metricTraceFirstTwo0STensor (I := I) g₁
            (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (metricRm04At (I := I) g₁ x)) -
          metricTraceFirstTwo0STensor (I := I) g₁
            (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (CovariantDerivative.riemannCurvature04At (I := I) g₁
                (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x)) := by
        rw [h₁, h₂]
    _ = metricTraceFirstTwo0STensor (I := I) g₁
          (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (metricRm04At (I := I) g₁ x) -
            ContinuousMultilinearMap.domDomCongr rm04TraceSlots
              (CovariantDerivative.riemannCurvature04At (I := I) g₁
                (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x)) := h₄
    _ = metricTraceFirstTwo0STensor (I := I) g₁
          (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
            (rmDiffLowAt (I := I) g₁ g₂ x)) :=
        congrArg (metricTraceFirstTwo0STensor (I := I) g₁) h₃.symm

end RicciTrace

section TraceNorm

omit [SigmaCompactSpace M] [T2Space M] in
private theorem exists_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricData_gen.inner_eq_gen
    (tangentMetricData_gen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

omit [SigmaCompactSpace M] [T2Space M] in
theorem normSq_ricciTraceRep (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g₁ x 4
        (ContinuousMultilinearMap.domDomCongr rm04TraceSlots
          (rmDiffLowAt (I := I) g₁ g₂ x)) =
      rmDiffSq (I := I) g₁ g₂ x := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  rw [rmDiffSq_def]
  exact normSq0S_domDomCongr (I := I) g₁ x basis (onFrame_inv (I := I) g₁ basis hON)
    rm04TraceSlots (rmDiffLowAt (I := I) g₁ g₂ x)

end TraceNorm

end DifferentialGeometry.PDE.RicciFlow

end
