import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import DifferentialGeometry.Analysis.Calculus.ParametricIntervalIntegral

namespace DifferentialGeometry
namespace Analysis

open Filter Function MeasureTheory Set
open scoped Interval Topology

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasDerivAt_second (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (fderiv ℝ g (t • x)) x)
      (((fderiv ℝ (fderiv ℝ g) (t • x)) x) x) t := by
  have hsmul : HasFDerivAt (fun t : ℝ => t • x) ((1 : ℝ →L[ℝ] ℝ).smulRight x) t := by
    exact (hasStrictFDerivAt_id (x := t)).hasFDerivAt.smul_const x
  have hfd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (t • x)) (t • x) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hd : DifferentiableAt ℝ (fderiv ℝ g) (t • x) :=
      ((h1 _ (Set.mem_univ _)).differentiableWithinAt
        (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
    exact hd.hasFDerivAt
  have hc : HasFDerivAt (fun t : ℝ => fderiv ℝ g (t • x))
      ((fderiv ℝ (fderiv ℝ g) (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)) t :=
    HasFDerivAt.comp (hg := hfd) (hf := hsmul)
  have hu : HasFDerivAt (fun t : ℝ => x) 0 t :=
    hasFDerivAt_const (𝕜 := ℝ) (c := x) (x := t)
  have hcapp : HasFDerivAt (fun t : ℝ => (fderiv ℝ g (t • x)) x)
      (((fderiv ℝ (fderiv ℝ g) (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)).flip x) t := by
    simpa using hc.clm_apply hu
  have hdeq : (((fderiv ℝ (fderiv ℝ g) (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)).flip x) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (((fderiv ℝ (fderiv ℝ g) (t • x)) x) x) := by
    apply ContinuousLinearMap.ext
    intro s
    rw [ContinuousLinearMap.flip_apply]
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [map_smul]
    simp
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa [hdeq] using hcapp

private theorem hasDerivAt_first (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => g (t • x)) ((fderiv ℝ g (t • x)) x) t := by
  have hsmul : HasFDerivAt (fun t : ℝ => t • x) ((1 : ℝ →L[ℝ] ℝ).smulRight x) t := by
    exact (hasStrictFDerivAt_id (x := t)).hasFDerivAt.smul_const x
  have hg' : HasFDerivAt g (fderiv ℝ g (t • x)) (t • x) := by
    have hda : DifferentiableAt ℝ g (t • x) :=
      (hg.contDiffAt (x := t • x)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)
    exact hda.hasFDerivAt
  have hcomp : HasFDerivAt (fun t : ℝ => g (t • x))
      ((fderiv ℝ g (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)) t :=
    HasFDerivAt.comp (hg := hg') (hf := hsmul)
  have hdeq : ((fderiv ℝ g (t • x)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight x)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight ((fderiv ℝ g (t • x)) x) := by
    apply ContinuousLinearMap.ext
    intro s
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [map_smul]
    rfl
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa [hdeq] using hcomp

theorem second_order_taylor_integral (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    g x - g 0 = (fderiv ℝ g 0) x + ∫ t in (0 : ℝ)..1,
      (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x := by
  let h : ℝ → ℝ := fun t => g (t • x)
  let h' : ℝ → ℝ := fun t => (fderiv ℝ g (t • x)) x
  let h'' : ℝ → ℝ := fun t => ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x
  have hh' : ∀ t : ℝ, HasDerivAt h (h' t) t := by
    intro t
    simpa [h, h'] using hasDerivAt_first g hg x t
  have hh'' : ∀ t : ℝ, HasDerivAt h' (h'' t) t := by
    intro t
    simpa [h', h''] using hasDerivAt_second g hg x t
  have hcont' : ContinuousOn h' (Set.Icc (0 : ℝ) 1) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    have hcont : ContinuousOn (fderiv ℝ g) Set.univ := h1.continuousOn
    have hsmul : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hmain : ContinuousOn (fun t : ℝ => (fderiv ℝ g (t • x)) x) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hcAt : ContinuousAt (fderiv ℝ g) (t • x) :=
        (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
      have hcomp : ContinuousAt (fun t : ℝ => fderiv ℝ g (t • x)) t :=
        ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt
      exact (hcomp.clm_apply (continuousAt_const (x := t) (y := x))).continuousWithinAt
    simpa [h'] using hmain
  have hcont'' : ContinuousOn h'' (Set.Icc (0 : ℝ) 1) := by
    have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ g)) Set.univ := by
      have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
        hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
      exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ g)) Set.univ := h0.continuousOn
    have hsmul : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hmain : ContinuousOn (fun t : ℝ => ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x)
        (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (t • x) :=
        (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
      have hcomp : ContinuousAt (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x)) t :=
        ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt
      exact ((hcomp.clm_apply (continuousAt_const (x := t) (y := x))).clm_apply
        (continuousAt_const (x := t) (y := x))).continuousWithinAt
    simpa [h''] using hmain
  have hcontH : ContDiffOn ℝ 1 h (Set.Icc (0 : ℝ) 1) := by
    have hsmul : ContDiff ℝ 2 (fun t : ℝ => t • x) := by
      exact ContDiff.smul
        (ContDiff.of_le (contDiff_id : ContDiff ℝ ⊤ (id : ℝ → ℝ))
          (by decide : (2 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞)))
        (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => x))
    have hcomp : ContDiff ℝ 2 (fun t : ℝ => g (t • x)) := hg.comp hsmul
    exact (hcomp.contDiffOn.of_le (by decide : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))).mono (by
      intro t ht
      exact Set.mem_univ t)
  have hFTC : ∫ t in (0 : ℝ)..1, h' t = h 1 - h 0 := by
    have hFTC' : ∫ t in (0 : ℝ)..1, deriv h t = h 1 - h 0 :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hcontH (by norm_num : (0 : ℝ) ≤ 1)
    rw [← hFTC']
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hh' t).deriv.symm
  have hIBP : ∫ t in (0 : ℝ)..1, (1 - t) * h'' t = - h' 0 + ∫ t in (0 : ℝ)..1, h' t := by
    have hu : ∀ x : ℝ, x ∈ [[(0 : ℝ), 1]] → HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      intro x hx
      simpa using ((hasDerivAt_const (c := (1 : ℝ)) (x := x)).sub (hasDerivAt_id x))
    have hv : ∀ x : ℝ, x ∈ [[(0 : ℝ), 1]] → HasDerivAt h' (h'' x) x := by
      intro x hx
      exact hh'' x
    have hu' : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hv' : IntervalIntegrable h'' volume (0 : ℝ) 1 :=
      ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont''
    have hIBP' := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    simpa [h''] using hIBP'
  calc
    g x - g 0 = h 1 - h 0 := by
      simp [h]
    _ = ∫ t in (0 : ℝ)..1, h' t := hFTC.symm
    _ = h' 0 + ∫ t in (0 : ℝ)..1, (1 - t) * h'' t := by
      rw [hIBP]
      ring
    _ = (fderiv ℝ g 0) x + ∫ t in (0 : ℝ)..1, (1 - t) * h'' t := by
      simp [h', h'']

theorem second_order_taylor_integral_of_fderiv_eq_zero (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E)
    (hx₀ : fderiv ℝ g 0 = 0) :
    g x - g 0 = ∫ t in (0 : ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x := by
  rw [second_order_taylor_integral g hg x, hx₀]
  simp

theorem fderiv_translate {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (c y : E) (hg : DifferentiableAt ℝ g (y + c)) :
    fderiv ℝ (fun z : E => g (z + c)) y = fderiv ℝ g (y + c) := by
  have hc : HasFDerivAt (fun z : E => z + c) (1 : E →L[ℝ] E) y := by
    have h := (hasFDerivAt_id (x := y) (𝕜 := ℝ)).add
      (hasFDerivAt_const (x := y) (c := c) (𝕜 := ℝ))
    convert h using 1
    · ext z
      simp
  have hcomp : HasFDerivAt (fun z : E => g (z + c))
      (ContinuousLinearMap.comp (fderiv ℝ g (y + c)) (1 : E →L[ℝ] E)) y := by
    exact HasFDerivAt.comp (x := y) (g := g) (g' := fderiv ℝ g (y + c))
      (f := fun z : E => z + c) (f' := (1 : E →L[ℝ] E)) (hg := hg.hasFDerivAt) (hf := hc)
  have hcomp' : HasFDerivAt (fun z : E => g (z + c)) (fderiv ℝ g (y + c)) y := by
    simpa using hcomp
  exact hcomp'.fderiv

theorem fderiv_fderiv_translate (g : E → ℝ) (hg : ContDiff ℝ 2 g) (c y : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) y = fderiv ℝ (fderiv ℝ g) (y + c) := by
  have hfun : fderiv ℝ (fun z : E => g (z + c)) = fun z : E => fderiv ℝ g (z + c) := by
    funext z
    exact fderiv_translate g c z (by
      exact ((hg.contDiffAt (x := z + c)).differentiableAt (by decide : (2 : WithTop ℕ∞) ≠ 0)))
  have hd : DifferentiableAt ℝ (fderiv ℝ g) (y + c) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact ((h1 (y + c) (Set.mem_univ _)).differentiableWithinAt
      (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt Filter.univ_mem
  calc
    fderiv ℝ (fderiv ℝ (fun z : E => g (z + c))) y
        = fderiv ℝ (fun z : E => fderiv ℝ g (z + c)) y := by rw [hfun]
    _ = fderiv ℝ (fderiv ℝ g) (y + c) := fderiv_translate (fderiv ℝ g) c y hd

namespace Calculus

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def hadamardFactor (f : ℝ → F) (a : ℝ) (x : ℝ) : F :=
  ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a))

theorem hadamardFactor_contDiff (f : ℝ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hadamardFactor f a) := by
  have hderiv : ContDiff ℝ (⊤ : ℕ∞) (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2
  have hH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => deriv f (a + p.2 * (p.1 - a))) Set.univ := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => a + p.2 * (p.1 - a)) := by
      fun_prop
    exact hderiv.comp_contDiffOn hinner.contDiffOn
  have hmain := contDiffOn_paramIntervalIntegral
    (f := fun x : ℝ => fun t : ℝ => deriv f (a + t * (x - a))) hH
  exact contDiffOn_univ.mp (by simpa [hadamardFactor] using hmain)

theorem hadamard_factorization (f : ℝ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a x : ℝ) :
    f x - f a = (x - a) • hadamardFactor f a x := by
  let w : ℝ := x - a
  let φ : ℝ → F := fun t => f (a + t * w)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    dsimp [φ]
    have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => a + t * w) := by
      fun_prop
    exact hf.comp hinner
  have hφ₁ : ContDiffOn ℝ 1 φ (Set.Icc (0 : ℝ) 1) :=
    (hφ.contDiffOn.of_le (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mono
      (Set.subset_univ _)
  have hFTC : (∫ t in (0 : ℝ)..1, deriv φ t) = φ 1 - φ 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ₁ (by norm_num)
  have hderivφ : ∀ t : ℝ, deriv φ t = w • deriv f (a + t * w) := by
    intro t
    dsimp [φ]
    have hrewrite : (fun t : ℝ => f (a + t * w)) =
        fun t : ℝ => (fun u : ℝ => f (a + u)) (w * t) := by
      funext t
      rw [mul_comm t w]
    rw [hrewrite]
    rw [deriv_comp_mul_left (c := w) (f := fun u : ℝ => f (a + u)) (x := t)]
    rw [deriv_comp_const_add]
    rw [mul_comm w t]
  calc
    f x - f a = φ 1 - φ 0 := by
      dsimp [φ, w]
      have h1 : a + 1 * (x - a) = x := by ring
      have h0 : a + 0 * (x - a) = a := by ring
      rw [h1, h0]
    _ = ∫ t in (0 : ℝ)..1, deriv φ t := hFTC.symm
    _ = ∫ t in (0 : ℝ)..1, w • deriv f (a + t * w) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hderivφ t
    _ = w • ∫ t in (0 : ℝ)..1, deriv f (a + t * w) := by
      rw [intervalIntegral.integral_smul]
    _ = (x - a) • hadamardFactor f a x := by
      simp [hadamardFactor, w]

theorem exists_contDiff_hadamardFactor (f : ℝ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ∃ g : ℝ → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ x : ℝ, f x - f a = (x - a) • g x :=
  ⟨hadamardFactor f a, hadamardFactor_contDiff f hf a, hadamard_factorization f hf a⟩

end Calculus

end

end Analysis
end DifferentialGeometry
