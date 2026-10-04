import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Regularity bootstrap for second-order identities of connection type (LFR11, kernel K1)

Let `f : E → F` be `C²` on an open set `U` and satisfy
`D²f z (v, w) = Df z (A z v w) - B (f z) (Df z v, Df z w)` on `U`, with `A` of class `C^m` on `U`
and `B` of class `C^m` on a set containing `f '' U`. Then `f` is `C^{m+2}` on `U`
(`contDiffOn_of_fderiv_fderiv_eq`, and `contDiffOn_of_fderiv_fderiv_eq_enat` for `m : ℕ∞`).

Two instances are used for blueprint LFR11 (A:25566–25672):
* `B = 0`, `F = ℝ`: a function whose chart Hessian is `Df ∘ Γ` (a parallel differential) is
  `C^{K+1}` when `Γ` is `C^{K-1}` (the 1-form form of the parallel bootstrap);
* the Levi-Civita transformation formula for a `C²` isometry between `C^K` metrics
  (Matveev–Troyanov (2.4)), which then becomes `C^{K+1}`.

The induction raises `Df` one order at a time: if `f ∈ C^{k+2}` and `k + 1 ≤ m`, the right-hand
side is `C^{k+1}`, hence `D(Df) ∈ C^{k+1}`, `Df ∈ C^{k+2}` and `f ∈ C^{k+3}`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The bilinear map `(v, w) ↦ L (A v w) - B (L v) (L w)`. -/
def connectionRHS (L : E →L[ℝ] F) (A : E →L[ℝ] E →L[ℝ] E) (B : F →L[ℝ] F →L[ℝ] F) :
    E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E E F L).comp A -
    ((ContinuousLinearMap.compL ℝ E F F).flip L).comp (B.comp L)

@[simp] theorem connectionRHS_apply (L : E →L[ℝ] F) (A : E →L[ℝ] E →L[ℝ] E)
    (B : F →L[ℝ] F →L[ℝ] F) (v w : E) :
    connectionRHS L A B v w = L (A v w) - B (L v) (L w) := by
  simp [connectionRHS]

theorem contDiffOn_connectionRHS {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {s : Set X} {L : X → E →L[ℝ] F} {A : X → E →L[ℝ] E →L[ℝ] E}
    {B : X → F →L[ℝ] F →L[ℝ] F} (hL : ContDiffOn ℝ n L s) (hA : ContDiffOn ℝ n A s)
    (hB : ContDiffOn ℝ n B s) :
    ContDiffOn ℝ n (fun z => connectionRHS (L z) (A z) (B z)) s := by
  unfold connectionRHS
  refine ContDiffOn.sub ?_ ?_
  · exact ((ContinuousLinearMap.compL ℝ E E F).contDiff.comp_contDiffOn hL).clm_comp hA
  · exact (((ContinuousLinearMap.compL ℝ E F F).flip).contDiff.comp_contDiffOn hL).clm_comp
      (hB.clm_comp hL)

/-- **Kernel K1 (connection bootstrap).** A `C²` solution of
`D²f z (v, w) = Df z (A z v w) - B (f z) (Df z v) (Df z w)` with `C^m` coefficients is `C^{m+2}`. -/
theorem contDiffOn_of_fderiv_fderiv_eq {U : Set E} (hU : IsOpen U) {V : Set F} {f : E → F}
    {m : ℕ} {A : E → E →L[ℝ] E →L[ℝ] E} {B : F → F →L[ℝ] F →L[ℝ] F}
    (hf : ContDiffOn ℝ 2 f U) (hfV : MapsTo f U V) (hA : ContDiffOn ℝ m A U)
    (hB : ContDiffOn ℝ m B V)
    (heq : ∀ z ∈ U, ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w =
      fderiv ℝ f z (A z v w) - B (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)) :
    ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) f U := by
  have hD2 : ∀ z ∈ U, fderiv ℝ (fderiv ℝ f) z =
      connectionRHS (fderiv ℝ f z) (A z) (B (f z)) := by
    intro z hz
    ext v w
    rw [connectionRHS_apply]
    exact heq z hz v w
  have key : ∀ k : ℕ, k ≤ m → ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) f U := by
    intro k
    induction k with
    | zero => intro _; simpa using hf
    | succ k ih =>
      intro hk
      have hfk := ih (by omega)
      have hk1 : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hk
      have hk2 : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ((k + 2 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast (show k + 1 ≤ k + 2 by omega)
      have hDf : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) U :=
        hfk.fderiv_of_isOpen hU (by push_cast; exact le_of_eq (by ring))
      have hBf : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun z => B (f z)) U :=
        (hB.of_le hk1).comp (hfk.of_le hk2) hfV
      have hRHS : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          (fun z => connectionRHS (fderiv ℝ f z) (A z) (B (f z))) U :=
        contDiffOn_connectionRHS hDf (hA.of_le hk1) hBf
      have hD2f : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ f)) U :=
        hRHS.congr (fun z hz => hD2 z hz)
      have hDf' : ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) U := by
        rw [show ((k + 2 : ℕ) : WithTop ℕ∞) = ((k + 1 : ℕ) : WithTop ℕ∞) + 1 by push_cast; ring,
          contDiffOn_succ_iff_fderiv_of_isOpen hU]
        refine ⟨hDf.differentiableOn (by simp), fun h => ?_, hD2f⟩
        exact absurd h (by simp)
      rw [show ((k + 1 + 2 : ℕ) : WithTop ℕ∞) = ((k + 2 : ℕ) : WithTop ℕ∞) + 1 by push_cast; ring,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨hfk.differentiableOn (by simp), fun h => ?_, hDf'⟩
      exact absurd h (by simp)
  exact key m le_rfl

/-- **Kernel K1, `ℕ∞` form.** With coefficients of class `C^m`, `m : ℕ∞`, the solution is
`C^{m+2}` (smooth for `m = ∞`). -/
theorem contDiffOn_of_fderiv_fderiv_eq_enat {U : Set E} (hU : IsOpen U) {V : Set F} {f : E → F}
    {m : ℕ∞} {A : E → E →L[ℝ] E →L[ℝ] E} {B : F → F →L[ℝ] F →L[ℝ] F}
    (hf : ContDiffOn ℝ 2 f U) (hfV : MapsTo f U V) (hA : ContDiffOn ℝ m A U)
    (hB : ContDiffOn ℝ m B V)
    (heq : ∀ z ∈ U, ∀ v w : E, fderiv ℝ (fderiv ℝ f) z v w =
      fderiv ℝ f z (A z v w) - B (f z) (fderiv ℝ f z v) (fderiv ℝ f z w)) :
    ContDiffOn ℝ ((m : WithTop ℕ∞) + 2) f U := by
  induction m using ENat.recTopCoe with
  | top =>
    have h : ((⊤ : ℕ∞) : WithTop ℕ∞) + 2 = ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      change (((⊤ : ℕ∞) + 2 : ℕ∞) : WithTop ℕ∞) = _
      rfl
    rw [h, contDiffOn_infty]
    intro n
    have hA' : ContDiffOn ℝ (n : ℕ) A U := hA.of_le (by exact_mod_cast le_top)
    have hB' : ContDiffOn ℝ (n : ℕ) B V := hB.of_le (by exact_mod_cast le_top)
    exact (contDiffOn_of_fderiv_fderiv_eq hU hf hfV hA' hB' heq).of_le
      (by exact_mod_cast (show n ≤ n + 2 by omega))
  | coe m =>
    have h := contDiffOn_of_fderiv_fderiv_eq hU hf hfV (m := m) (by exact_mod_cast hA)
      (by exact_mod_cast hB) heq
    have he : (((m : ℕ∞) : WithTop ℕ∞) + 2) = ((m + 2 : ℕ) : WithTop ℕ∞) := by push_cast; rfl
    rw [he]
    exact h

end DifferentialGeometry.Analysis
