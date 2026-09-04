import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.DifferenceFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Connection.Difference

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section Lowering

variable {x : M}

def bilin12At
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => connectionDifferenceOutput (I := I) A α
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        change Tensor0SSpace.eval (connectionDifferenceOutput (I := I) A (α + β)) v =
          Tensor0SSpace.eval
            (connectionDifferenceOutput (I := I) A α + connectionDifferenceOutput (I := I) A β) v
        rw [connectionDifferenceOutput_apply]
        change Tensor0SSpace.eval (α + β) (fun _ : Fin 1 => (A (v 1)) (v 0)) = _
        rw [Tensor0SSpace.eval_add]
        rw [Tensor0SSpace.eval_add, connectionDifferenceOutput_apply,
          connectionDifferenceOutput_apply]
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        change Tensor0SSpace.eval (connectionDifferenceOutput (I := I) A (c • α)) v =
          Tensor0SSpace.eval (c • connectionDifferenceOutput (I := I) A α) v
        rw [connectionDifferenceOutput_apply]
        change Tensor0SSpace.eval (c • α) (fun _ : Fin 1 => (A (v 1)) (v 0)) = _
        rw [Tensor0SSpace.eval_smul]
        rw [Tensor0SSpace.eval_smul, connectionDifferenceOutput_apply] }

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem bilin12At_apply
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    Tensor0SSpace.eval (bilin12At (I := I) A α) v =
      Tensor0SSpace.eval α (fun _ : Fin 1 => (A (v 1)) (v 0)) := by
  change Tensor0SSpace.eval (connectionDifferenceOutput (I := I) A α) v = _
  rw [connectionDifferenceOutput_apply]

private def lowerBilinOut (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).symm
    (ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 2)
      (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
      (LinearMap.toContinuousLinearMap
        { toFun := fun W =>
            tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
              (bilin12At (I := I) A
                ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 1 x).symm
                  (ContinuousMultilinearMap.curryLeft
                    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x q) W)))
          map_add' := by
            intro W₁ W₂
            rw [map_add, map_add, map_add, map_add]
          map_smul' := by
            intro c W
            rw [map_smul, map_smul, map_smul, map_smul, RingHom.id_apply] }))

omit [SigmaCompactSpace M] [T2Space M] in
private theorem lowerBilinOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (w : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerBilinOut (I := I) q A) w =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then w 0 else (A (w 2)) (w 1)) := by
  have h : Tensor0SSpace.eval (lowerBilinOut (I := I) q A) w =
      Tensor0SSpace.eval
        (bilin12At (I := I) A
          ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 1 x).symm
            (ContinuousMultilinearMap.curryLeft
              (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x q) (w 0))))
        (Fin.tail w) := by
    unfold lowerBilinOut Tensor0SSpace.eval
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.uncurryLeft_apply]
    rw [LinearMap.coe_toContinuousLinearMap']
    rfl
  rw [h, bilin12At_apply, Tensor0SSpace.eval_fiber_equiv_symm,
    ContinuousMultilinearMap.curryLeft_apply]
  change Tensor0SSpace.eval q
      (Fin.cons (w 0) (fun x_1 => (A (Fin.tail w 1)) (Fin.tail w 0))) = _
  congr 1
  funext a
  fin_cases a <;> simp [Fin.tail]

private def lowerStdPerm : Equiv.Perm (Fin 3) where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  invFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

def lowerBilin (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  Tensor0SSpace.domDomCongr
    (lowerBilinOut (I := I)
      (Tensor0SSpace.domDomCongr q (Equiv.swap (0 : Fin 2) 1)) A)
    lowerStdPerm

omit [SigmaCompactSpace M] [T2Space M] in
theorem lowerBilin_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (v : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerBilin (I := I) q A) v =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then (A (v 1)) (v 0) else v 2) := by
  have h : Tensor0SSpace.eval (lowerBilin (I := I) q A) v =
      Tensor0SSpace.eval
        (lowerBilinOut (I := I)
          (Tensor0SSpace.domDomCongr q (Equiv.swap (0 : Fin 2) 1)) A)
        (fun i : Fin 3 => v (lowerStdPerm i)) := rfl
  rw [h, lowerBilinOut_apply]
  rw [Tensor0SSpace.eval_domDomCongr]
  congr 1
  funext a
  fin_cases a <;> simp [lowerStdPerm]

end Lowering

section Expansion

variable {x : M}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor02_expand {ι : Type*} [Fintype ι]
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (b : Module.Basis ι Real (TangentSpace I x)) (W Z : TangentSpace I x) :
    q (fun a : Fin 2 => if a = 0 then W else Z) =
      ∑ k, b.repr W k * q (fun a : Fin 2 => if a = 0 then b k else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then W else Z with hm
  have hupd : ∀ W' : TangentSpace I x,
      Function.update m 0 W' = (fun a : Fin 2 => if a = 0 then W' else Z) := by
    intro W'
    funext a
    fin_cases a <;> simp [hm]
  have hW : (∑ k, b.repr W k • b k) = W := b.sum_repr W
  calc q (fun a : Fin 2 => if a = 0 then W else Z)
      = q (Function.update m 0 (∑ k, b.repr W k • b k)) := by rw [hupd, hW]
    _ = ∑ k, q (Function.update m 0 (b.repr W k • b k)) :=
        q.toMultilinearMap.map_update_sum Finset.univ 0 (fun k => b.repr W k • b k) m
    _ = ∑ k, b.repr W k * q (fun a : Fin 2 => if a = 0 then b k else Z) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [q.map_update_smul, hupd, smul_eq_mul]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem bilin_expand {ι : Type*} [Fintype ι]
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (b : Module.Basis ι Real (TangentSpace I x)) (X Y : TangentSpace I x) :
    (A Y) X = ∑ j, ∑ i, (b.repr Y j * b.repr X i) • (A (b j)) (b i) := by
  classical
  have hY : (∑ j, b.repr Y j • b j) = Y := b.sum_repr Y
  have hX : (∑ i, b.repr X i • b i) = X := b.sum_repr X
  have step1 : (A Y) X = ∑ j, b.repr Y j • ((A (b j)) X) := by
    conv_lhs => rw [← hY]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply]
  have step2 : ∀ j : ι, (A (b j)) X = ∑ i, b.repr X i • (A (b j)) (b i) := by
    intro j
    conv_lhs => rw [← hX]
    simp only [map_sum, map_smul]
  rw [step1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [step2 j, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

end Expansion

section Speed

def connectionDifferenceDot (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (t : Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  (-2 : Real) •
      lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
        (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
          (metricCov (I := I) (g₂ t)) x) +
    lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceDot_apply (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    (t : Real) (x : M) (v : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceDot (I := I) g₁ g₂ Adot t x) v =
      (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then
            CovariantDerivative.difference (metricCov (I := I) (g₁ t))
              (metricCov (I := I) (g₂ t)) x (v 1) (v 0) else v 2) +
        (g₁ t).inner x ((Adot x (v 1)) (v 0)) (v 2) := by
  have hadd :
      Tensor0SSpace.eval (connectionDifferenceDot (I := I) g₁ g₂ Adot t x) v =
        Tensor0SSpace.eval (((-2 : Real) •
            lowerBilin (I := I) (metricRicciAt (I := I) (g₁ t) x)
              (CovariantDerivative.difference (metricCov (I := I) (g₁ t))
                (metricCov (I := I) (g₂ t)) x)) +
          lowerBilin (I := I) (metricTensorField (I := I) (g₁ t) x) (Adot x)) v := rfl
  rw [hadd, Tensor0SSpace.eval_add, Tensor0SSpace.eval_smul,
    lowerBilin_apply, lowerBilin_apply, Tensor0SSpace.eval_eq,
    Tensor0SSpace.eval_eq, smul_eq_mul,
    metricTensorField_apply]
  simp

end Speed

section

variable {x : M}

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceLow_hasDerivAt
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : (x : M) →
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x)
    {t : Real}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x Y X)
        ((Adot x Y) X) t)
    (v : Fin 3 -> TangentSpace I x) :
    HasDerivAt
      (fun r : Real =>
        Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x) v)
      (Tensor0SSpace.eval (connectionDifferenceDot (I := I) g₁ g₂ Adot t x) v) t := by
  classical
  set b : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x) with hb
  set F : Real → TangentSpace I x := fun r =>
    CovariantDerivative.difference (metricCov (I := I) (g₁ r))
      (metricCov (I := I) (g₂ r)) x (v 1) (v 0) with hF
  set Fdot : TangentSpace I x := (Adot x (v 1)) (v 0) with hFdot
  have hFderiv : HasDerivAt F Fdot t := hA (v 0) (v 1)
  have hcomp : ∀ k, HasDerivAt (fun r : Real => b.repr (F r) k) (b.repr Fdot k) t := by
    intro k
    have hL : HasDerivAt (fun r : Real =>
        (LinearMap.toContinuousLinearMap (b.coord k)) (F r))
        ((LinearMap.toContinuousLinearMap (b.coord k)) Fdot) t :=
      (LinearMap.toContinuousLinearMap (b.coord k)).hasFDerivAt.comp_hasDerivAt t hFderiv
    simpa using hL
  have hmet : ∀ k, HasDerivAt
      (fun r : Real => (g₁ r).inner x (b k) (v 2))
      ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
        (fun a : Fin 2 => if a = 0 then b k else v 2)) t := fun k => hPDE₁ (b k) (v 2)
  have hsum : ∀ r : Real,
      Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x) v =
        ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 2) := by
    intro r
    rw [connectionDifferenceLowAt_apply]
    have h1 : (g₁ r).inner x (F r) (v 2) =
        metricTensorField (I := I) (g₁ r) x
          (fun a : Fin 2 => if a = 0 then F r else v 2) := by
      rw [metricTensorField_apply]; simp
    have h2 : ∀ k : Fin (Module.finrank Real (TangentSpace I x)),
        metricTensorField (I := I) (g₁ r) x
            (fun a : Fin 2 => if a = 0 then b k else v 2) =
          (g₁ r).inner x (b k) (v 2) := by
      intro k; rw [metricTensorField_apply]; simp
    rw [show
        (g₁ r).inner x
            (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
              (metricCov (I := I) (g₂ r)) x (v 1) (v 0)) (v 2) =
          (g₁ r).inner x (F r) (v 2) from rfl,
      h1, tensor02_expand (I := I) (metricTensorField (I := I) (g₁ r) x) b (F r) (v 2)]
    exact Finset.sum_congr rfl fun k _ => by rw [h2 k]
  have hderiv : HasDerivAt (fun r : Real => ∑ k, b.repr (F r) k * (g₁ r).inner x (b k) (v 2))
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 2) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 2)))) t :=
    HasDerivAt.fun_sum fun k _ => (hcomp k).mul (hmet k)
  have hval :
      (∑ k, (b.repr Fdot k * (g₁ t).inner x (b k) (v 2) +
        b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 2)))) =
        Tensor0SSpace.eval (connectionDifferenceDot (I := I) g₁ g₂ Adot t x) v := by
    rw [Finset.sum_add_distrib, connectionDifferenceDot_apply]
    have hg : (∑ k, b.repr Fdot k * (g₁ t).inner x (b k) (v 2)) =
        (g₁ t).inner x Fdot (v 2) := by
      have h1 : ∀ k : Fin (Module.finrank Real (TangentSpace I x)),
          (g₁ t).inner x (b k) (v 2) =
            metricTensorField (I := I) (g₁ t) x
              (fun a : Fin 2 => if a = 0 then b k else v 2) := by
        intro k; rw [metricTensorField_apply]; simp
      have h2 : (g₁ t).inner x Fdot (v 2) =
          metricTensorField (I := I) (g₁ t) x
            (fun a : Fin 2 => if a = 0 then Fdot else v 2) := by
        rw [metricTensorField_apply]; simp
      rw [h2, tensor02_expand (I := I) (metricTensorField (I := I) (g₁ t) x) b Fdot (v 2)]
      exact Finset.sum_congr rfl fun k _ => by rw [h1 k]
    have hr : (∑ k, b.repr (F t) k * ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then b k else v 2))) =
        (-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then F t else v 2) := by
      rw [tensor02_expand (I := I) (metricRicciAt (I := I) (g₁ t) x) b (F t) (v 2),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hg, hr]
    ring
  have := hderiv.congr_deriv hval
  simpa only [hsum] using this

end

section Frame

variable {Idx : Type*} [Fintype Idx] {u : Set M} {x : M}

omit [Fintype Idx] [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceVec_hasDerivAt [Finite Idx]
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (hframe.coeff k x ((Adot x (frame j x)) (frame i x))) t)
    (X Y : TangentSpace I x) :
    HasDerivAt
      (fun r : Real =>
        CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x Y X)
      ((Adot x Y) X) t := by
  classical
  let _ : Fintype Idx := Fintype.ofFinite Idx
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ i : Idx, b i = frame i x := fun i =>
    IsLocalFrameOn.toBasisAt_coe hframe hx i
  have hcoeff : ∀ (k : Idx) (w : TangentSpace I x),
      hframe.coeff k x w = b.repr w k := by
    intro k w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  have hfr : ∀ j : Idx, MDifferentiableAt I I.tangent (T% (frame j)) x := fun j =>
    (hframe.contMDiffAt hu hx j).mdifferentiableAt (by simp)
  have hbasis : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i)) k)
        (b.repr ((Adot x (b j)) (b i)) k) t := by
    intro i j k
    have hdiff : ∀ r : Real,
        CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i) =
          (metricCov (I := I) (g₁ r) (frame j) x) (frame i x) -
            (metricCov (I := I) (g₂ r) (frame j) x) (frame i x) := by
      intro r
      have h := IsCovariantDerivativeOn.difference_apply
        (metricCov (I := I) (g₁ r)).isCovariantDerivativeOnUniv
        (metricCov (I := I) (g₂ r)).isCovariantDerivativeOnUniv
        (x := x) (Set.mem_univ x) (σ := fun y => frame j y) (hfr j)
      have h' : CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (frame j x) =
            metricCov (I := I) (g₁ r) (frame j) x -
              metricCov (I := I) (g₂ r) (frame j) x := by
        simpa [CovariantDerivative.difference] using h
      rw [hbcoe j, hbcoe i, h']
      rfl
    have hfun : (fun r : Real =>
        b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x (b j) (b i)) k) =
        fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k := by
      funext r
      rw [hdiff r, ← hcoeff k]
      simp only [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval]
      exact map_sub (hframe.coeff k x) _ _
    have hval : b.repr ((Adot x (b j)) (b i)) k =
        hframe.coeff k x ((Adot x (frame j x)) (frame i x)) := by
      rw [hcoeff k, hbcoe i, hbcoe j]
    rw [hfun, hval]
    exact hΓ i j k
  have hvec : ∀ i j : Idx,
      HasDerivAt
        (fun r : Real =>
          CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i))
        ((Adot x (b j)) (b i)) t := by
    intro i j
    have hsum : ∀ r : Real,
        CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i) =
          ∑ k, b.repr (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j) (b i)) k • b k := fun r =>
      (b.sum_repr _).symm
    have htgt : ((Adot x (b j)) (b i)) =
        ∑ k, b.repr ((Adot x (b j)) (b i)) k • b k := (b.sum_repr _).symm
    rw [htgt]
    have := HasDerivAt.fun_sum (u := (Finset.univ : Finset Idx))
      (fun k (_ : k ∈ (Finset.univ : Finset Idx)) => (hbasis i j k).smul_const (b k))
    simpa only [← hsum] using this
  have hexp : ∀ r : Real,
      CovariantDerivative.difference (metricCov (I := I) (g₁ r))
          (metricCov (I := I) (g₂ r)) x Y X =
        ∑ j, ∑ i, (b.repr Y j * b.repr X i) •
          (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j)) (b i) := fun r =>
    bilin_expand (I := I) _ b X Y
  have htgt : ((Adot x Y) X) =
      ∑ j, ∑ i, (b.repr Y j * b.repr X i) • (Adot x (b j)) (b i) :=
    bilin_expand (I := I) (Adot x) b X Y
  rw [htgt]
  have hstep : HasDerivAt
      (fun r : Real =>
        ∑ j, ∑ i, (b.repr Y j * b.repr X i) •
          (CovariantDerivative.difference (metricCov (I := I) (g₁ r))
            (metricCov (I := I) (g₂ r)) x (b j)) (b i))
      (∑ j, ∑ i, (b.repr Y j * b.repr X i) • (Adot x (b j)) (b i)) t :=
    HasDerivAt.fun_sum fun j _ =>
      HasDerivAt.fun_sum fun i _ => (hvec i j).const_smul _
  simpa only [← hexp] using hstep

omit [Fintype Idx] [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceLow_hasDerivAt_frame [Finite Idx]
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u) (hx : x ∈ u) {t : Real}
    (Adot : (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hΓ : ∀ i j k : Idx,
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) frame hframe x i j k)
        (hframe.coeff k x ((Adot x (frame j x)) (frame i x))) t)
    (v : Fin 3 -> TangentSpace I x) :
    HasDerivAt (fun r : Real => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v)
      (connectionDifferenceDot (I := I) g₁ g₂ Adot t x v) t := by
  classical
  let _ : Fintype Idx := Fintype.ofFinite Idx
  exact connectionDifferenceLow_hasDerivAt (I := I) g₁ g₂ Adot hPDE₁
    (fun X Y => connectionDifferenceVec_hasDerivAt (I := I) g₁ g₂ frame hframe hu hx Adot hΓ X Y) v

def bilinOfComp (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Real) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (b.constr Real fun j =>
      LinearMap.toContinuousLinearMap (b.constr Real fun i => ∑ k, c i j k • b k))

omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem bilinOfComp_basis (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx -> Idx -> Idx -> Real) (i j : Idx) :
    (bilinOfComp (I := I) b c (b j)) (b i) = ∑ k, c i j k • b k := by
  have h : bilinOfComp (I := I) b c (b j) =
      LinearMap.toContinuousLinearMap (b.constr Real fun i => ∑ k, c i j k • b k) := by
    change (b.constr Real fun j' =>
      LinearMap.toContinuousLinearMap (b.constr Real fun i => ∑ k, c i j' k • b k)) (b j) = _
    rw [Module.Basis.constr_basis]
  rw [h]
  change (b.constr Real fun i' => ∑ k, c i' j k • b k) (b i) = _
  rw [Module.Basis.constr_basis]

omit [SigmaCompactSpace M] [T2Space M] in
theorem coeff_bilinOfComp (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u) (hx : x ∈ u)
    (c : Idx -> Idx -> Idx -> Real) (i j k : Idx) :
    hframe.coeff k x
        ((bilinOfComp (I := I) (hframe.toBasisAt hx) c (frame j x)) (frame i x)) =
      c i j k := by
  classical
  set b : Module.Basis Idx Real (TangentSpace I x) := hframe.toBasisAt hx with hbdef
  have hbcoe : ∀ l : Idx, b l = frame l x := fun l =>
    IsLocalFrameOn.toBasisAt_coe hframe hx l
  have hcoeff : ∀ (l : Idx) (w : TangentSpace I x),
      hframe.coeff l x w = b.repr w l := by
    intro l w
    simp [IsLocalFrameOn.coeff, hx, hbdef, Module.Basis.coord_apply]
  rw [← hbcoe i, ← hbcoe j, hcoeff k, bilinOfComp_basis]
  simp [Finsupp.single_apply]

end Frame

section SolutionBridge

variable {Idx : Type*} {u : Set M}

omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffel_symbol_in_frame_eq_solution_metric_connection
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (s : Real) (x : M) (i j k : Idx) :
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection s) frame hframe x i j k =
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (metricCov (I := I) (S.base.metric s)) frame hframe x i j k := rfl

end SolutionBridge

end DifferentialGeometry.PDE.RicciFlow

end
