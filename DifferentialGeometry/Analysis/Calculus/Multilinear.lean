import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod

open scoped BigOperators

namespace ContinuousMultilinearMap

theorem differentiableWithinAt_of_basis_eval
    {𝕜 P F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {d n : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    {f : P → ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜}
    {s : Set P} {x : P}
    (hf : ∀ m : Fin n → Fin d, DifferentiableWithinAt 𝕜
      (fun y => f y (fun q => b (m q))) s x) : DifferentiableWithinAt 𝕜 f s x := by
  let _ : FiniteDimensional 𝕜 F := b.finiteDimensional_of_finite
  let _ : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜) :=
    DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional n
  let e := (DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis b n).equivFun
    |>.toContinuousLinearEquiv
  apply (e.comp_differentiableWithinAt_iff).mp
  apply differentiableWithinAt_pi.mpr
  intro m
  change DifferentiableWithinAt 𝕜
    (fun y => (DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis b n).repr
      (f y) m) s x
  simpa only [DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr] using hf m

theorem differentiableAt_of_basis_eval
    {𝕜 P F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {d n : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    {f : P → ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜} {x : P}
    (hf : ∀ m : Fin n → Fin d, DifferentiableAt 𝕜
      (fun y => f y (fun q => b (m q))) x) : DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ]
  exact differentiableWithinAt_of_basis_eval b (fun m => (hf m).differentiableWithinAt)

theorem hasDerivWithinAt_of_basis_eval
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {d n : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    {f : 𝕜 → ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜}
    {f' : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜}
    {s : Set 𝕜} {x : 𝕜}
    (hf : ∀ m : Fin n → Fin d, HasDerivWithinAt
      (fun y => f y (fun q => b (m q))) (f' (fun q => b (m q))) s x) :
    HasDerivWithinAt f f' s x := by
  let _ : FiniteDimensional 𝕜 F := b.finiteDimensional_of_finite
  let _ : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜) :=
    DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional n
  let e := (DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis b n).equivFun
    |>.toContinuousLinearEquiv
  have he : HasDerivWithinAt (fun y => e (f y)) (e f') s x := by
    apply hasDerivWithinAt_pi.mpr
    intro m
    change HasDerivWithinAt
      (fun y => (DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis b n).repr
        (f y) m)
      ((DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapBasis b n).repr f' m) s x
    simpa only [DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_basis_repr]
      using hf m
  have h := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt x he
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using h

theorem hasDerivAt_of_basis_eval
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {d n : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    {f : 𝕜 → ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜}
    {f' : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜} {x : 𝕜}
    (hf : ∀ m : Fin n → Fin d, HasDerivAt
      (fun y => f y (fun q => b (m q))) (f' (fun q => b (m q))) x) :
    HasDerivAt f f' x := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_of_basis_eval b (fun m => (hf m).hasDerivWithinAt)


end ContinuousMultilinearMap

theorem HasDerivWithinAt.continuousMultilinearMap_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → ContinuousMultilinearMap 𝕜 E F}
    {f' : ContinuousMultilinearMap 𝕜 E F}
    {g : ∀ i, 𝕜 → E i} {g' : ∀ i, E i} {s : Set 𝕜} {x : 𝕜}
    (hf : HasDerivWithinAt f f' s x)
    (hg : ∀ i, HasDerivWithinAt (g i) (g' i) s x) :
    HasDerivWithinAt (fun y => f y (fun i => g i y))
      (f' (fun i => g i x) + ∑ i, f x (Function.update (fun j => g j x) i (g' i))) s x := by
  have h := hf.hasFDerivWithinAt.continuousMultilinearMap_apply
    (fun i => (hg i).hasFDerivWithinAt)
  simpa using h.hasDerivWithinAt

theorem HasDerivAt.continuousMultilinearMap_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : 𝕜 → ContinuousMultilinearMap 𝕜 E F}
    {f' : ContinuousMultilinearMap 𝕜 E F}
    {g : ∀ i, 𝕜 → E i} {g' : ∀ i, E i} {x : 𝕜}
    (hf : HasDerivAt f f' x)
    (hg : ∀ i, HasDerivAt (g i) (g' i) x) :
    HasDerivAt (fun y => f y (fun i => g i y))
      (f' (fun i => g i x) + ∑ i, f x (Function.update (fun j => g j x) i (g' i))) x := by
  rw [← hasDerivWithinAt_univ]
  exact hf.hasDerivWithinAt.continuousMultilinearMap_apply (fun i => (hg i).hasDerivWithinAt)
