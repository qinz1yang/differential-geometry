import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {𝕜 D E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem contDiffOn_clm_of_basis
    {ι : Type*} [Finite ι] (b : Module.Basis ι 𝕜 E)
    {s : Set D} {f : D → E →L[𝕜] F} {m : ℕ∞ω}
    (hf : ∀ i, ContDiffOn 𝕜 m (fun x => f x (b i)) s) : ContDiffOn 𝕜 m f s := by
  classical
  let := Fintype.ofFinite ι
  let e : (E →L[𝕜] F) ≃L[𝕜] (ι → F) :=
    (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans (ContinuousLinearEquiv.piRing ι)
  have he (A : E →L[𝕜] F) (i : ι) : e A i = A (b i) := by
    change A (b.equivFunL.symm (Pi.single i 1)) = A (b i)
    congr 1
    change b.equivFun.symm (Pi.single i 1) = b i
    simp
  have hc : ContDiffOn 𝕜 m (fun x => e (f x)) s :=
    contDiffOn_pi.mpr fun i => by simpa only [he] using hf i
  have hfinal : ContDiffOn 𝕜 m (fun x => e.symm (e (f x))) s :=
    e.symm.contDiff.comp_contDiffOn hc
  simpa only [e.symm_apply_apply] using hfinal

theorem contDiffOn_continuousMultilinearMap_of_basis
    {ι : Type*} [Finite ι] (b : Module.Basis ι 𝕜 E)
    {s : Set D} {n : ℕ} {m : ℕ∞ω} {f : D → E [×n]→L[𝕜] F}
    (hf : ∀ v : Fin n → ι, ContDiffOn 𝕜 m (fun x => f x (fun i => b (v i))) s) :
    ContDiffOn 𝕜 m f s := by
  induction n with
  | zero =>
      let e := continuousMultilinearCurryFin0 𝕜 E F
      have hc : ContDiffOn 𝕜 m (fun x => e (f x)) s := by
        simpa only [e, continuousMultilinearCurryFin0_apply,
          Subsingleton.elim (0 : Fin 0 → E) (fun i => b (Fin.elim0 i))] using
          hf (fun i => Fin.elim0 i)
      have hfinal : ContDiffOn 𝕜 m (fun x => e.symm (e (f x))) s :=
        e.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hc
      simpa only [e.symm_apply_apply] using hfinal
  | succ n ih =>
      let e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F
      have hc : ContDiffOn 𝕜 m (fun x => e (f x)) s := by
        apply contDiffOn_clm_of_basis b
        intro i
        apply ih
        intro v
        simpa only [e, continuousMultilinearCurryLeftEquiv_apply,
          ContinuousMultilinearMap.curryLeft_apply, ← Function.comp_def, Fin.comp_cons] using
          hf (Fin.cons i v)
      have hfinal : ContDiffOn 𝕜 m (fun x => e.symm (e (f x))) s := by
        set_option backward.isDefEq.respectTransparency false in
          exact e.symm.contDiff.comp_contDiffOn hc
      simpa only [e.symm_apply_apply] using hfinal

omit [CompleteSpace 𝕜] in
theorem contDiffOn_succ_of_contDiffOn_iteratedFDeriv
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F} {n : ℕ}
    (hu : ContDiffOn 𝕜 n u Ω) (hD : ContDiffOn 𝕜 1 (iteratedFDeriv 𝕜 n u) Ω) :
    ContDiffOn 𝕜 (n + 1 : ℕ) u Ω := by
  have hbase := (contDiffOn_nat_iff_continuousOn_differentiableOn hΩ.uniqueDiffOn).mp hu
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn hΩ.uniqueDiffOn).mpr
  constructor
  · intro k hk
    by_cases hkn : k ≤ n
    · exact hbase.1 k hkn
    · have heq : k = n + 1 := by omega
      subst k
      have hc : ContinuousOn (iteratedFDeriv 𝕜 (n + 1) u) Ω := by
        rw [iteratedFDeriv_succ_eq_comp_left]
        let e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F
        apply e.symm.continuous.comp_continuousOn
        exact hD.continuousOn_fderiv_of_isOpen hΩ le_rfl
      exact hc.congr (iteratedFDerivWithin_of_isOpen (𝕜 := 𝕜) (n + 1) hΩ)
  · intro k hk
    by_cases hkn : k < n
    · exact hbase.2 k hkn
    · have heq : k = n := by omega
      subst k
      exact (hD.differentiableOn one_ne_zero).congr
        (iteratedFDerivWithin_of_isOpen (𝕜 := 𝕜) n hΩ)

omit [CompleteSpace 𝕜] in
theorem contDiffOn_add_two_of_contDiffOn_iteratedFDeriv
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F} {n : ℕ}
    (hu : ContDiffOn 𝕜 n u Ω) (hD : ContDiffOn 𝕜 2 (iteratedFDeriv 𝕜 n u) Ω) :
    ContDiffOn 𝕜 (n + 2 : ℕ) u Ω := by
  have hu1 := contDiffOn_succ_of_contDiffOn_iteratedFDeriv hΩ hu (hD.of_le (by norm_num))
  have hD1 : ContDiffOn 𝕜 1 (iteratedFDeriv 𝕜 (n + 1) u) Ω := by
    rw [iteratedFDeriv_succ_eq_comp_left]
    let e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F
    exact e.symm.contDiff.comp_contDiffOn (hD.fderiv_of_isOpen (m := 1) hΩ (by norm_num))
  exact contDiffOn_succ_of_contDiffOn_iteratedFDeriv hΩ hu1 hD1

end DifferentialGeometry.Analysis

end

noncomputable section
open Set
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_two_iteratedFDeriv_apply
    {f : E → F} {x : E} (n : ℕ) (a b : E) (v : Fin n → E) :
    iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n f) x ![a, b] v =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b v)) := by
  let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm
  have heq : fderiv ℝ (iteratedFDeriv ℝ (n + 1) f) x =
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) x) := by
    change fderiv ℝ (e ∘ fderiv ℝ (iteratedFDeriv ℝ n f)) x = _
    exact LinearIsometryEquiv.comp_fderiv
      (𝕜 := ℝ) (E := E →L[ℝ] E [×n]→L[ℝ] F) (F := E [×(n + 1)]→L[ℝ] F)
      (G := E) e (f := fderiv ℝ (iteratedFDeriv ℝ n f)) (x := x)
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_succ_apply_left, heq]
  rfl

theorem iteratedFDeriv_two_apply_const
    {f : E → F} {x : E} {n : ℕ} (hf : ContDiffAt ℝ (n + 2) f x)
    (a b : E) (v : Fin n → E) :
    iteratedFDeriv ℝ 2 (fun y => iteratedFDeriv ℝ n f y v) x ![a, b] =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b v)) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F v
  have hT : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by norm_cast; omega)
  have h := congrArg (fun A => A ![a, b]) (L.iteratedFDeriv_comp_left hT le_rfl)
  exact h.trans (iteratedFDeriv_two_iteratedFDeriv_apply n a b v)

end DifferentialGeometry.Analysis

end
