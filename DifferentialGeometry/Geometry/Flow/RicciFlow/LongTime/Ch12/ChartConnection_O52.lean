import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# CH12-O52 G1b: the Euclidean chart connection identity

For a coefficient field `P : F → (F →L F →L ℝ)` and a `C²` map `Ψ : E → F`, the pulled-back
coefficient field is `G̃ x = pullbackForm (P (Ψ x), DΨ x)`, `G̃ x a b = P (Ψ x) (DΨ x a) (DΨ x b)`.

* `fderiv_pullbackForm_comp_O52`: `DG̃(e)(a,b) = DP(Me)(Ma,Mb) + P(D²Ψ(e,a), Mb) + P(Ma, D²Ψ(e,b))`.
* `koszul_pullback_O52` (first kind): `Kos(DG̃)(a,b,c) = Kos(DP)(Ma,Mb,Mc) + 2 P(D²Ψ(a,b), Mc)`,
  where `Kos T a b c = T a b c + T b a c - T c a b` (`koszul_O52`).
* `secondDeriv_eq_O52` (solved form, `E = F` finite dimensional, `G̃ y` invertible):
  `D²Ψ(a,b) = M (G̃ y)⁻¹ (½ (Kos(DG̃) a b - M^*(Kos(DP)(Ma,Mb))))`.

This is step b2 of the single-model core `L1` (`[FROZEN] CH12-O26`, `[FROZEN] CH12-O52 G1`).
-/

set_option autoImplicit false

open Set
open scoped ContDiff
open DifferentialGeometry.CheegerGromovCompactness

namespace GC.LongTime.Ch12

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Koszul combination of a trilinear form: `koszul_O52 T a b c = T a b c + T b a c - T c a b`. -/
noncomputable def koszul_O52 (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  T + T.flip -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp T.flip

theorem koszul_O52_apply (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (a b c : E) :
    koszul_O52 T a b c = T a b c + T b a c - T c a b := by
  simp [koszul_O52]

/-- Derivative of the pulled-back coefficient field. -/
theorem fderiv_pullbackForm_comp_O52 {P : F → F →L[ℝ] F →L[ℝ] ℝ} {Ψ : E → F} {y : E}
    (hP : DifferentiableAt ℝ P (Ψ y)) (hΨ : ContDiffAt ℝ 2 Ψ y) (e a b : E) :
    fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y e a b =
      fderiv ℝ P (Ψ y) (fderiv ℝ Ψ y e) (fderiv ℝ Ψ y a) (fderiv ℝ Ψ y b) +
      P (Ψ y) (fderiv ℝ (fderiv ℝ Ψ) y e a) (fderiv ℝ Ψ y b) +
      P (Ψ y) (fderiv ℝ Ψ y a) (fderiv ℝ (fderiv ℝ Ψ) y e b) := by
  have hΨd : DifferentiableAt ℝ Ψ y := hΨ.differentiableAt (by norm_num)
  have hMd : DifferentiableAt ℝ (fderiv ℝ Ψ) y :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc : HasFDerivAt (fun x => P (Ψ x)) ((fderiv ℝ P (Ψ y)).comp (fderiv ℝ Ψ y)) y :=
    hP.hasFDerivAt.comp y hΨd.hasFDerivAt
  have hGd : DifferentiableAt ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y :=
    ((pullbackForm.contDiff (E := E) (F := F)).differentiable (by simp) _).comp y
      (hc.differentiableAt.prodMk hMd)
  -- evaluation at `(a, b)` commutes with `fderiv`
  have h1 : HasFDerivAt (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) a)
      ((fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y).flip a) y := by
    have := hGd.hasFDerivAt.clm_apply (hasFDerivAt_const a y)
    convert this using 1
    ext e' c
    simp
  have h2 : HasFDerivAt (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x) a b)
      (((fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y).flip a).flip b) y := by
    have := h1.clm_apply (hasFDerivAt_const b y)
    convert this using 1
    ext e'
    simp
  -- direct product rule
  have hMa : HasFDerivAt (fun x => fderiv ℝ Ψ x a) ((fderiv ℝ (fderiv ℝ Ψ) y).flip a) y := by
    have := hMd.hasFDerivAt.clm_apply (hasFDerivAt_const a y)
    convert this using 1
    ext e'
    simp
  have hMb : HasFDerivAt (fun x => fderiv ℝ Ψ x b) ((fderiv ℝ (fderiv ℝ Ψ) y).flip b) y := by
    have := hMd.hasFDerivAt.clm_apply (hasFDerivAt_const b y)
    convert this using 1
    ext e'
    simp
  have h3 := (hc.clm_apply hMa).clm_apply hMb
  have h4 := congrArg (fun L => L e) (h2.unique h3)
  simp only [ContinuousLinearMap.flip_apply, _root_.add_apply,
    ContinuousLinearMap.comp_apply] at h4
  rw [h4]
  ring

/-- **Chart connection identity (first kind).** -/
theorem koszul_pullback_O52 {P : F → F →L[ℝ] F →L[ℝ] ℝ} {Ψ : E → F} {y : E}
    (hP : DifferentiableAt ℝ P (Ψ y)) (hΨ : ContDiffAt ℝ 2 Ψ y)
    (hsym : ∀ v w, P (Ψ y) v w = P (Ψ y) w v) (a b c : E) :
    koszul_O52 (fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y) a b c =
      koszul_O52 (fderiv ℝ P (Ψ y)) (fderiv ℝ Ψ y a) (fderiv ℝ Ψ y b) (fderiv ℝ Ψ y c) +
        2 * P (Ψ y) (fderiv ℝ (fderiv ℝ Ψ) y a b) (fderiv ℝ Ψ y c) := by
  have hsymm : IsSymmSndFDerivAt ℝ Ψ y := hΨ.isSymmSndFDerivAt (by simp)
  rw [koszul_O52_apply, koszul_O52_apply, fderiv_pullbackForm_comp_O52 hP hΨ,
    fderiv_pullbackForm_comp_O52 hP hΨ, fderiv_pullbackForm_comp_O52 hP hΨ,
    hsymm b a, hsymm c a, hsymm c b,
    hsym (fderiv ℝ (fderiv ℝ Ψ) y a c) (fderiv ℝ Ψ y b)]
  ring

/-- **Solved form**: the second derivative of `Ψ` is determined by `(G̃, DG̃, DP ∘ Ψ, DΨ)`. -/
theorem secondDeriv_eq_O52 [FiniteDimensional ℝ E] {P : E → E →L[ℝ] E →L[ℝ] ℝ} {Ψ : E → E}
    {y : E} (hP : DifferentiableAt ℝ P (Ψ y)) (hΨ : ContDiffAt ℝ 2 Ψ y)
    (hsym : ∀ v w, P (Ψ y) v w = P (Ψ y) w v)
    (hA : (pullbackForm (P (Ψ y), fderiv ℝ Ψ y)).IsInvertible) (a b : E) :
    fderiv ℝ (fderiv ℝ Ψ) y a b = fderiv ℝ Ψ y ((pullbackForm (P (Ψ y), fderiv ℝ Ψ y)).inverse
      ((1 / 2 : ℝ) • (koszul_O52 (fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y) a b -
        (koszul_O52 (fderiv ℝ P (Ψ y)) (fderiv ℝ Ψ y a) (fderiv ℝ Ψ y b)).comp
          (fderiv ℝ Ψ y)))) := by
  have hAinj : Function.Injective (pullbackForm (P (Ψ y), fderiv ℝ Ψ y)) := hA.injective
  have hMinj : Function.Injective (fderiv ℝ Ψ y) := by
    intro v w hvw
    apply hAinj
    ext c
    simp [pullbackForm_apply, hvw]
  have hMsurj : Function.Surjective (fderiv ℝ Ψ y) :=
    (LinearMap.injective_iff_surjective (f := ((fderiv ℝ Ψ y : E →L[ℝ] E) : E →ₗ[ℝ] E))).1 hMinj
  have hPinj : ∀ v : E, (∀ c : E, P (Ψ y) v (fderiv ℝ Ψ y c) = 0) → v = 0 := by
    intro v hv
    obtain ⟨v', rfl⟩ := hMsurj v
    have h0 : pullbackForm (P (Ψ y), fderiv ℝ Ψ y) v' = 0 := by
      ext c
      simpa [pullbackForm_apply] using hv c
    have : v' = 0 := hAinj (by rw [h0, map_zero])
    simp [this]
  set R : E →L[ℝ] ℝ := (1 / 2 : ℝ) •
    (koszul_O52 (fderiv ℝ (fun x => pullbackForm (P (Ψ x), fderiv ℝ Ψ x)) y) a b -
      (koszul_O52 (fderiv ℝ P (Ψ y)) (fderiv ℝ Ψ y a) (fderiv ℝ Ψ y b)).comp (fderiv ℝ Ψ y))
    with hR
  have hx := hA.self_apply_inverse R
  have key : ∀ c, P (Ψ y) (fderiv ℝ Ψ y ((pullbackForm (P (Ψ y), fderiv ℝ Ψ y)).inverse R))
      (fderiv ℝ Ψ y c) = P (Ψ y) (fderiv ℝ (fderiv ℝ Ψ) y a b) (fderiv ℝ Ψ y c) := by
    intro c
    have h1 : P (Ψ y) (fderiv ℝ Ψ y ((pullbackForm (P (Ψ y), fderiv ℝ Ψ y)).inverse R))
        (fderiv ℝ Ψ y c) = R c := congrArg (fun L => L c) hx
    have h2 := koszul_pullback_O52 hP hΨ hsym a b c
    have hRc : R c = 1 / 2 * (koszul_O52 (fderiv ℝ (fun x => pullbackForm (P (Ψ x),
        fderiv ℝ Ψ x)) y) a b c - koszul_O52 (fderiv ℝ P (Ψ y)) (fderiv ℝ Ψ y a)
          (fderiv ℝ Ψ y b) (fderiv ℝ Ψ y c)) := by
      rw [hR]
      simp
    rw [h1, hRc, h2]
    ring
  have h := hPinj (fderiv ℝ Ψ y ((pullbackForm (P (Ψ y), fderiv ℝ Ψ y)).inverse R) -
    fderiv ℝ (fderiv ℝ Ψ) y a b) (fun c => by simp [key c])
  exact (sub_eq_zero.1 h).symm

end GC.LongTime.Ch12
