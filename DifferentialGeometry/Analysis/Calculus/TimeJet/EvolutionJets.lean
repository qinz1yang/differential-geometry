import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {ι P Z : Type*} {X : ι → Type*} [TopologicalSpace P]
  [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem continuousOn_iteratedDerivWithin_of_smooth_lifts
    (next : ι → ι) (π : ∀ i, X (next i) →L[ℝ] X i)
    (R : ∀ i, X (next i) → X i) (Ω : ∀ i, Set (X i))
    (hΩ : ∀ i, IsOpen (Ω i))
    (hπ : ∀ i, MapsTo (π i) (Ω (next i)) (Ω i))
    (hR : ∀ i, ContDiffOn ℝ ∞ (R i) (Ω (next i)))
    {S : Set P} {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (u : ∀ i, P → ℝ → X i)
    (hu : ∀ i, ContinuousOn (fun p : P × ℝ => u i p.1 p.2) (S ×ˢ J))
    (huΩ : ∀ i p, p ∈ S → ∀ t ∈ J, u i p t ∈ Ω i)
    (hcompat : ∀ i p, p ∈ S → ∀ t ∈ J, π i (u (next i) p t) = u i p t)
    (hdu : ∀ i p, p ∈ S → ∀ t ∈ J,
      HasDerivWithinAt (u i p) (R i (u (next i) p t)) J t)
    (k : ℕ) (i : ι) (F : X i → Z) (hF : ContDiffOn ℝ ∞ F (Ω i)) :
    ContinuousOn
      (fun p : P × ℝ => iteratedDerivWithin k (fun t => F (u i p.1 t)) J p.2)
      (S ×ˢ J) := by
  induction k generalizing i with
  | zero =>
    exact hF.continuousOn.comp (hu i) (fun p hp => huΩ i p.1 hp.1 p.2 hp.2)
  | succ k ih =>
    let Φ : X (next i) → Z := fun x => fderiv ℝ F (π i x) (R i x)
    have hΦ : ContDiffOn ℝ ∞ Φ (Ω (next i)) := by
      exact ((hF.fderiv_of_isOpen (hΩ i) (by simp)).comp
        (π i).contDiff.contDiffOn (hπ i)).clm_apply (hR i)
    have heq (p : P) (hp : p ∈ S) :
        EqOn (derivWithin (fun t => F (u i p t)) J)
          (fun t => Φ (u (next i) p t)) J := by
      intro t ht
      have hFt : DifferentiableAt ℝ F (u i p t) :=
        ((hF _ (huΩ i p hp t ht)).contDiffAt
          ((hΩ i).mem_nhds (huΩ i p hp t ht))).differentiableAt (by simp)
      have hd := hFt.hasFDerivAt.comp_hasDerivWithinAt t (hdu i p hp t ht)
      have hvalue := hd.derivWithin (hJ t ht)
      simpa only [Φ, hcompat i p hp t ht, Function.comp_def] using hvalue
    have hcont := ih (next i) Φ hΦ
    apply hcont.congr
    intro p hp
    change iteratedDerivWithin (k + 1) (fun t => F (u i p.1 t)) J p.2 = _
    rw [iteratedDerivWithin_succ']
    exact iteratedDerivWithin_congr (heq p.1 hp.1) hp.2

end DifferentialGeometry.Analysis
