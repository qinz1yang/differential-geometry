import DifferentialGeometry.Geometry.Collapse.RadialNormalization
import DifferentialGeometry.Geometry.Comparison.AdaptedCoordinateTransfer

/-!
# LC67 feeding LC68: the radial specialization of the stability lemma (consumer)

Blueprint `master207A.tex`, LC68 (lines 23988–24071), its last sentence: "In LC67's setting it
suffices to supply, for this same splitting, such a `φ` with `Lip(u_q - φ) ≤ t`,
`γ + t + ε ≤ ζ`." This consumer composes the LC67 normalization kernel
(`centered_radial_normalization`) with the LC68 clause transfers
(`lipschitz_clause_of_perturbation`, `image_clauses_of_perturbation`): on any set `B` inside the
`λ d`-unit ball about `q`, a reference `φ` with `φ(q) = 0`, `(1 + γ)`-Lipschitz for `λ d`, with
image error `γ`, and `u_q - φ` `t`-Lipschitz for `λ d`, makes the prescribed `ψ_q` satisfy the
Lipschitz and image clauses at quality `ζ` (the Lipschitz clause is the computation of
`lipschitz_clause_of_perturbation` for the distance `λ d`). The derivative clause is the pointwise
`derivative_clause_of_perturbation`; its Riemannian input (the derivative of an ambient-Lipschitz
smooth function along a unit vector) is not part of this consumer. Existence of `φ` is not
asserted (that is LC71/LC79).
-/

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Comparison

/-- **LC67 → LC68, radial specialization (Lipschitz and image clauses).** -/
theorem radial_lipschitz_image_clauses {X : Type*} [PseudoMetricSpace X] {p q : X}
    {η φ : X → ℝ} {ε t γ ζ lam : ℝ} {B : Set X}
    (hlip : ∀ x y, |(η x - dist x p) - (η y - dist y p)| ≤ ε * dist x y)
    (hlam : 0 < lam) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hζ : γ + (t + ε) ≤ ζ)
    (hB : ∀ x ∈ B, lam * dist q x < 1) (hφq : φ q = 0)
    (hφ : ∀ x ∈ B, ∀ y ∈ B, |φ x - φ y| ≤ (1 + γ) * (lam * dist x y))
    (hφ1 : ∀ x ∈ B, Metric.infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ)
    (hφ2 : ∀ s ∈ Ioo (-1 : ℝ) 1, Metric.infDist s (φ '' B) ≤ γ)
    (hcomp : ∀ x y, |((lam * dist p x - lam * dist p q) - φ x) -
      ((lam * dist p y - lam * dist p q) - φ y)| ≤ t * (lam * dist x y)) :
    (∀ x ∈ B, ∀ y ∈ B, |lam * (η x - η q) - lam * (η y - η q)| ≤ (1 + ζ) * (lam * dist x y)) ∧
      (∀ x ∈ B, Metric.infDist (lam * (η x - η q)) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
      ∀ s ∈ Ioo (-1 : ℝ) 1, Metric.infDist s ((fun x => lam * (η x - η q)) '' B) ≤ ζ := by
  obtain ⟨-, -, hnorm, -, -⟩ := centered_radial_normalization hlip q hlam
  set ψ : X → ℝ := fun x => lam * (η x - η q) with hψ
  set u : X → ℝ := fun x => lam * dist p x - lam * dist p q with hu
  have hdiff : ∀ x y, |(ψ x - φ x) - (ψ y - φ y)| ≤ (t + ε) * (lam * dist x y) := by
    intro x y
    have e : (ψ x - φ x) - (ψ y - φ y) =
        ((ψ x - u x) - (ψ y - u y)) + ((u x - φ x) - (u y - φ y)) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε * (lam * dist x y) + t * (lam * dist x y) := add_le_add (hnorm x y) (hcomp x y)
      _ = (t + ε) * (lam * dist x y) := by ring
  have hq0 : ψ q - φ q = 0 := by simp [hψ, hφq]
  have hval : ∀ x ∈ B, |ψ x - φ x| ≤ t + ε := by
    intro x hx
    have h := hdiff x q
    rw [hq0, sub_zero, dist_comm x q] at h
    have hd := hB x hx
    nlinarith [mul_nonneg hlam.le (dist_nonneg (x := q) (y := x))]
  refine ⟨?_, image_clauses_of_perturbation hζ (by positivity) hval hφ1 hφ2⟩
  intro x hx y hy
  change |ψ x - ψ y| ≤ (1 + ζ) * (lam * dist x y)
  have e : ψ x - ψ y = (φ x - φ y) + ((ψ x - φ x) - (ψ y - φ y)) := by ring
  rw [e]
  have hd : 0 ≤ lam * dist x y := mul_nonneg hlam.le dist_nonneg
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (1 + γ) * (lam * dist x y) + (t + ε) * (lam * dist x y) :=
      add_le_add (hφ x hx y hy) (hdiff x y)
    _ ≤ (1 + ζ) * (lam * dist x y) := by nlinarith

end DifferentialGeometry.Geometry.Collapse
