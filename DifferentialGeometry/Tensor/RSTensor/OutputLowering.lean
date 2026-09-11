import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

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

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Lowering

variable {x : M}

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02_add_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (u₁ u₂ Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z) =
      Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
        Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then u₁ else Z with hm
  have hupd : ∀ u : TangentSpace I x,
      Function.update m 0 u = (fun a : Fin 2 => if a = 0 then u else Z) := by
    intro u
    funext a
    fin_cases a <;> simp [hm]
  rw [Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq]
  calc q (fun a : Fin 2 => if a = 0 then u₁ + u₂ else Z)
      = q (Function.update m 0 (u₁ + u₂)) := by rw [hupd]
    _ = q (Function.update m 0 u₁) + q (Function.update m 0 u₂) := q.map_update_add m 0 u₁ u₂
    _ = q (fun a : Fin 2 => if a = 0 then u₁ else Z) +
          q (fun a : Fin 2 => if a = 0 then u₂ else Z) := by rw [hupd, hupd]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02_smul_left
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real) (u Z : TangentSpace I x) :
    Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then c • u else Z) =
      c * Tensor0SSpace.eval q (fun a : Fin 2 => if a = 0 then u else Z) := by
  classical
  set m : Fin 2 -> TangentSpace I x := fun a => if a = 0 then u else Z with hm
  have hupd : ∀ u' : TangentSpace I x,
      Function.update m 0 u' = (fun a : Fin 2 => if a = 0 then u' else Z) := by
    intro u'
    funext a
    fin_cases a <;> simp [hm]
  rw [Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq]
  calc q (fun a : Fin 2 => if a = 0 then c • u else Z)
      = q (Function.update m 0 (c • u)) := by rw [hupd]
    _ = c • q (Function.update m 0 u) := q.map_update_smul m 0 c u
    _ = c * q (fun a : Fin 2 => if a = 0 then u else Z) := by rw [hupd, smul_eq_mul]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem lowerBilin_add
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A B : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (A + B) =
      lowerBilin (I := I) q A + lowerBilin (I := I) q B := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (lowerBilin (I := I) q (A + B)) v =
    Tensor0SSpace.eval (lowerBilin (I := I) q A + lowerBilin (I := I) q B) v
  rw [Tensor0SSpace.eval_add, lowerBilin_apply, lowerBilin_apply, lowerBilin_apply]
  have hAB : ((A + B) (v 1)) (v 0) = (A (v 1)) (v 0) + (B (v 1)) (v 0) := rfl
  rw [hAB, tensor02_add_left]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem lowerBilin_smul
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (c : Real)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x) :
    lowerBilin (I := I) q (c • A) = c • lowerBilin (I := I) q A := by
  apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 3 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval (lowerBilin (I := I) q (c • A)) v =
    Tensor0SSpace.eval (c • lowerBilin (I := I) q A) v
  rw [Tensor0SSpace.eval_smul, lowerBilin_apply, lowerBilin_apply]
  have hA : ((c • A) (v 1)) (v 0) = c • ((A (v 1)) (v 0)) := rfl
  rw [hA, tensor02_smul_left, smul_eq_mul]

private def lowerTriOut
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousLinearMap.uncurryLeft (𝕜 := Real) (n := 3)
    (Ei := fun _ : Fin 4 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          (lowerBilin (I := I) q (A X) :
            ContinuousMultilinearMap Real (fun _ : Fin 3 => TangentSpace I x) Real)
        map_add' := by
          intro X₁ X₂
          rw [map_add]
          exact lowerBilin_add (I := I) q (A X₁) (A X₂)
        map_smul' := by
          intro c X
          rw [map_smul]
          exact lowerBilin_smul (I := I) q c (A X) })

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem lowerTriOut_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (w : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerTriOut (I := I) q A) w =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then ((A (w 0)) (w 2)) (w 1) else w 3) := by
  have h : Tensor0SSpace.eval (lowerTriOut (I := I) q A) w =
      Tensor0SSpace.eval (lowerBilin (I := I) q (A (w 0))) (Fin.tail w) := by
    rfl
  rw [h, lowerBilin_apply]
  congr 1

def lowerTri
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 4) 2)
    (lowerTriOut (I := I) q A)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lowerTri_apply
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (v : Fin 4 -> TangentSpace I x) :
    Tensor0SSpace.eval (lowerTri (I := I) q A) v =
      Tensor0SSpace.eval q
        (fun a : Fin 2 => if a = 0 then ((A (v 0)) (v 1)) (v 2) else v 3) := by
  have h : Tensor0SSpace.eval (lowerTri (I := I) q A) v =
      Tensor0SSpace.eval (lowerTriOut (I := I) q A)
        (fun i : Fin 4 => v (Equiv.swap (1 : Fin 4) 2 i)) := rfl
  rw [h, lowerTriOut_apply]
  congr 1

end Lowering

end DifferentialGeometry.PDE.RicciFlow

end
