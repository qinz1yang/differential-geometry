import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.Analysis.Integration.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [OpensMeasurableSpace Z]
variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
    {μ : Measure Z} {Ω : Set E} {U V : Z × E → ℝ}
    (hU : LocallyIntegrable U (μ.prod (volume.restrict Ω)))
    (hV : LocallyIntegrable V (μ.prod (volume.restrict Ω)))
    (i : Fin d)
    (hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => V (t, x)) (fun x => U (t, x)) Ω)
    (φ : Z × E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (univ : Set Z) ×ˢ Ω) :
    (∫ p, U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1) ∂μ.prod (volume.restrict Ω)) =
      -∫ p, V p * φ p ∂μ.prod (volume.restrict Ω) := by
  have hdφ : Continuous (fun p => fderiv ℝ φ p (0, EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft : Integrable (fun p => U p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
      (μ.prod (volume.restrict Ω)) :=
    hU.integrable_smul_right_of_hasCompactSupport hdφ
      (hφc.fderiv_apply (𝕜 := ℝ) (0, EuclideanSpace.single i 1))
  have hright : Integrable (fun p => V p * φ p) (μ.prod (volume.restrict Ω)) :=
    hV.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  rw [hleft.integral_prod, hright.integral_prod, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hweak] with t ht
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => φ (t, x)) :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have hsupp : tsupport (fun x : E => φ (t, x)) ⊆ Prod.snd '' tsupport φ := by
    intro x hx
    exact ⟨(t, x), tsupport_comp_subset_preimage (f := fun y : E => (t, y)) φ (by fun_prop) hx, rfl⟩
  have hslice_c : HasCompactSupport (fun x : E => φ (t, x)) :=
    IsCompact.of_isClosed_subset (hφc.image continuous_snd) (isClosed_tsupport _) hsupp
  have hslice_s : tsupport (fun x : E => φ (t, x)) ⊆ Ω := by
    intro x hx
    exact (hφs (tsupport_comp_subset_preimage (f := fun y : E => (t, y)) φ (by fun_prop) hx)).2
  have hd (x : E) : fderiv ℝ (fun y : E => φ (t, y)) x (EuclideanSpace.single i 1) =
      fderiv ℝ φ (t, x) (0, EuclideanSpace.single i 1) := by
    have h := (hφ.differentiable (by simp) (t, x)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    exact congrArg (fun L => L (EuclideanSpace.single i 1)) h.fderiv
  simpa only [hd] using ht (fun x => φ (t, x)) hslice hslice_c hslice_s

theorem integral_fderiv_prod_left_eq_neg_of_finite_weak_partial_trees
    {μ : Measure Z} {W : Set Z} {Ω : Set E} (K : ℕ) (v : Z)
    (U R : ∀ n : ℕ, (Fin n → Fin d) → Z × E → ℝ)
    (hU : ∀ n ≤ K, ∀ α, LocallyIntegrable (U n α) (μ.prod (volume.restrict Ω)))
    (hR : ∀ n ≤ K, ∀ α, LocallyIntegrable (R n α) (μ.prod (volume.restrict Ω)))
    (hUweak : ∀ n < K, ∀ α i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => U (n + 1) (Fin.cons i α) (t, x)) (fun x => U n α (t, x)) Ω)
    (hRweak : ∀ n < K, ∀ α i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
      (fun x => R (n + 1) (Fin.cons i α) (t, x)) (fun x => R n α (t, x)) Ω)
    (hroot : ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W ×ˢ Ω →
      (∫ q, U 0 (fun i => Fin.elim0 i) q * fderiv ℝ φ q (v, 0)
        ∂μ.prod (volume.restrict Ω)) =
        -∫ q, R 0 (fun i => Fin.elim0 i) q * φ q ∂μ.prod (volume.restrict Ω)) :
    ∀ n ≤ K, ∀ α (φ : Z × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W ×ˢ Ω →
      (∫ q, U n α q * fderiv ℝ φ q (v, 0) ∂μ.prod (volume.restrict Ω)) =
        -∫ q, R n α q * φ q ∂μ.prod (volume.restrict Ω) := by
  intro n
  induction n with
  | zero =>
      intro _ α
      have hα : α = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
      subst α
      exact hroot
  | succ n ih =>
      intro hn α φ hφ hφc hφs
      obtain ⟨i, β, rfl⟩ : ∃ (i : Fin d) (β : Fin n → Fin d), α = Fin.cons i β :=
        ⟨α 0, Fin.tail α, (Fin.cons_self_tail α).symm⟩
      have hsp : ∀ ψ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ W ×ˢ Ω →
          (∫ q, U n β q * fderiv ℝ ψ q (0, EuclideanSpace.single i 1)
            ∂μ.prod (volume.restrict Ω)) =
            -∫ q, U (n + 1) (Fin.cons i β) q * ψ q ∂μ.prod (volume.restrict Ω) := by
        intro ψ hψ hψc hψs
        exact integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
          (hU n (by omega) β) (hU (n + 1) hn (Fin.cons i β)) i
          (hUweak n (by omega) β i) ψ hψ hψc
          (hψs.trans (prod_mono (subset_univ _) Subset.rfl))
      exact (integral_weak_deriv_fderiv_comm (0, EuclideanSpace.single i 1) (v, 0)
        hsp (ih (by omega) β) hφ hφc hφs).trans
          (integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
            (hR n (by omega) β) (hR (n + 1) hn (Fin.cons i β)) i
            (hRweak n (by omega) β i) φ hφ hφc
            (hφs.trans (prod_mono (subset_univ _) Subset.rfl)))

end DifferentialGeometry.Analysis.Sobolev.Euclidean
