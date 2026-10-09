import DifferentialGeometry.Topology.Morse.Strip.Defs
import DifferentialGeometry.Topology.Double.Rounded.RoundedDouble
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Monoid

namespace DifferentialGeometry.Topology.RoundedDouble

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

theorem contMDiff_height {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => g p.1 + p.2 ^ 2) := by
  exact (hg.comp contMDiff_fst).add
    ((show ContDiff ℝ ∞ (fun t : ℝ => t ^ 2) by fun_prop).contMDiff.comp contMDiff_snd)

theorem isCriticalPointAt_iff_mvfderiv_eq_zero {g : M → ℝ} (x : M) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x ↔ mvfderiv I g x = 0 := by
  change mfderiv I 𝓘(ℝ, ℝ) g x = 0 ↔ _
  constructor
  · intro h
    simp only [mvfderiv, h, ContinuousLinearMap.comp_zero]
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (g x)).injective
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) h

theorem mvfderiv_height {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (p : M × ℝ) :
    mvfderiv (I.prod 𝓘(ℝ, ℝ)) (fun p : M × ℝ => g p.1 + p.2 ^ 2) p =
      (mvfderiv I g p.1).comp (mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst p) +
        (2 * p.2) • mvfderiv (I.prod 𝓘(ℝ, ℝ)) Prod.snd p := by
  have hg' := hg.mdifferentiable (by simp) p.1
  have hf : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (g ∘ Prod.fst) p :=
    hg'.comp p mdifferentiableAt_fst
  have ht : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (@Prod.snd M ℝ) p :=
    mdifferentiableAt_snd
  have hfun : (fun p : M × ℝ => g p.1 + p.2 ^ 2) =
      (g ∘ Prod.fst) + (@Prod.snd M ℝ) * Prod.snd := by
    ext q
    simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, pow_two]
  rw [hfun, mvfderiv_add hf (ht.mul ht), mvfderiv_comp p hg' mdifferentiableAt_fst,
    mvfderiv_mul ht ht, ← add_smul]
  congr 2
  ring

theorem isCriticalPointAt_height_iff {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (p : M × ℝ) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt (I.prod 𝓘(ℝ, ℝ)) (fun p : M × ℝ => g p.1 + p.2 ^ 2) p ↔
      DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g p.1 ∧ p.2 = 0 := by
  rw [isCriticalPointAt_iff_mvfderiv_eq_zero, isCriticalPointAt_iff_mvfderiv_eq_zero]
  have hh := (contMDiff_height I hg).mdifferentiable (by simp) p
  constructor
  · intro hp
    have hiL : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ)) (fun x : M => (x, p.2)) p.1 :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hiR : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (fun t : ℝ => (p.1, t)) p.2 :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hleft : mvfderiv I (fun x : M => g x + p.2 ^ 2) p.1 = 0 := by
      calc
        _ = (mvfderiv (I.prod 𝓘(ℝ, ℝ))
            (fun q : M × ℝ => g q.1 + q.2 ^ 2) p).comp
            (mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun x : M => (x, p.2)) p.1) :=
          mvfderiv_comp (I := I.prod 𝓘(ℝ, ℝ)) (I' := I)
            (f := fun x : M => (x, p.2))
            (g := fun q : M × ℝ => g q.1 + q.2 ^ 2) p.1 hh hiL
        _ = 0 := by rw [hp, ContinuousLinearMap.zero_comp]
    rw [mvfderiv_fun_add (hg.mdifferentiable (by simp) p.1) mdifferentiableAt_const,
      mvfderiv_const, add_zero] at hleft
    have hright : mvfderiv 𝓘(ℝ, ℝ) (fun t : ℝ => g p.1 + t ^ 2) p.2 = 0 := by
      calc
        _ = (mvfderiv (I.prod 𝓘(ℝ, ℝ))
            (fun q : M × ℝ => g q.1 + q.2 ^ 2) p).comp
            (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun t : ℝ => (p.1, t)) p.2) :=
          mvfderiv_comp (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
            (f := fun t : ℝ => (p.1, t))
            (g := fun q : M × ℝ => g q.1 + q.2 ^ 2) p.2 hh hiR
        _ = 0 := by rw [hp, ContinuousLinearMap.zero_comp]
    have hr : fderiv ℝ (fun t : ℝ => g p.1 + t ^ 2) p.2 = 0 := by
      have hc : (mvfderiv 𝓘(ℝ, ℝ) (fun t : ℝ => g p.1 + t ^ 2) p.2).comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) p.2).symm.toContinuousLinearMap =
          fderiv ℝ (fun t : ℝ => g p.1 + t ^ 2) p.2 := by
        rw [mvfderiv_eq_fderiv]
        rfl
      rw [← hc, hright, ContinuousLinearMap.zero_comp]
    have hd : HasDerivAt (fun t : ℝ => g p.1 + t ^ 2) (2 * p.2) p.2 := by
      convert! HasDerivAt.add (hasDerivAt_const p.2 (g p.1))
        ((hasDerivAt_id p.2).pow 2) using 1
      simp
    have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
      ((HasDerivAt.hasFDerivAt hd).fderiv.symm.trans hr)
    simp at hv
    exact ⟨hleft, by linarith⟩
  · rintro ⟨hg0, ht⟩
    rw [mvfderiv_height I hg, hg0, ht, mul_zero, zero_smul, add_zero]
    exact ContinuousLinearMap.zero_comp _

theorem regular_height_zero {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, g x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt I g x) :
    ∀ p : M × ℝ, g p.1 + p.2 ^ 2 = 0 →
      ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (I.prod 𝓘(ℝ, ℝ)) (fun p : M × ℝ => g p.1 + p.2 ^ 2) p := by
  intro p hp hcrit
  obtain ⟨hx, ht⟩ := (isCriticalPointAt_height_iff I hg p).mp hcrit
  exact hreg p.1 (by simpa [ht] using hp) hx

end DifferentialGeometry.Topology.RoundedDouble
