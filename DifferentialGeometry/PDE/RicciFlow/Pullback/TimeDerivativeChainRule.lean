import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! # Substantive transport of the time derivative across the pullback evaluation formula

For a family of smooth diffeomorphisms `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` and a family
of smooth Riemannian metrics `g_fam : ℝ → SmoothRiemannianMetric I M`, the scalar
function

  `s ↦ (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w`

is *definitionally* equal, for every `s`, to

  `s ↦ (g_fam s).inner (Φ_fam s x) (mfderiv I I (Φ_fam s) x v) (mfderiv I I (Φ_fam s) x w)`.

This is the pointwise pullback evaluation formula
(`Diffeomorph.pullbackInner` unfolds to a `comp`/`precomp` pair on the inner
product `g_fam s . inner (Φ_fam s x)`). The present file packages this equality
into a transport principle for `HasDerivWithinAt` / `HasDerivAt`: any derivative
information available for the right-hand "expanded" form transfers verbatim to
the left-hand "bundled" form (and conversely). This is the core primitive used
by downstream chain-rule arguments — it lets the consumer apply the standard
Mathlib product/chain rule on the right-hand side (whose ingredients are the
ordinary metric family derivative and the pushforward variations) and then
read off the same derivative for the bundled `pullbackMetric` form without
re-unfolding `pullbackInner` at the derivative level.

Both `HasDerivWithinAt` and `HasDerivAt` directions are provided. -/

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Scalar evaluation identity for the time-parametrised pullback metric.**
For every `s : ℝ`, the bundled `pullbackMetric` inner product at `(x, v, w)`
equals the metric-family inner product evaluated at `Φ_fam s x` on the
slot-wise manifold derivatives. -/
theorem pullbackMetric_inner_eq_inner_mfderiv
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w
      = (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w) := by
  change Diffeomorph.pullbackInner (g_fam s) (Φ_fam s) x v w
      = (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

/-- **Function-level scalar identification.**
The scalar function `s ↦ (pullbackMetric (g_fam s) (Φ_fam s)).inner x v w` is
literally equal to its evaluation-formula expansion. -/
theorem pullbackMetric_inner_funext
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      = (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
  funext s
  exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w s

/-- **Transport `HasDerivWithinAt` from the evaluation-formula form to the
bundled pullback form.**

If the scalar function
`s ↦ (g_fam s).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`
has within-set derivative `G'` at `t` along `Set.Ici 0` (or any other set),
then the bundled
`s ↦ (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w`
has the same within-set derivative at `t`.

This is the substantive primitive that connects ordinary calculus on the
inner-product evaluation (where Mathlib's product/chain rule applies directly
to `g_fam` paired with the pushforward variations) to derivative information
for the bundled `pullbackMetric` section. No flow or generator hypotheses
appear: the identity is the evaluation-formula expansion in `s`. -/
theorem pullbackMetric_inner_hasDerivWithinAt_of_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_eval : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t := by
  refine h_eval.congr ?_ ?_
  · intro u _
    exact (pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w u).symm
  · exact (pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w t).symm

/-- **Transport `HasDerivWithinAt` from the bundled pullback form to the
evaluation-formula form.**

The converse direction of `pullbackMetric_inner_hasDerivWithinAt_of_eval`. If
the bundled `pullbackMetric` scalar has within-set derivative `G'` at `t`,
then so does the evaluation-formula expansion. -/
theorem pullbackMetric_inner_hasDerivWithinAt_to_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_pullback : HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t) :
    HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t := by
  refine h_pullback.congr ?_ ?_
  · intro u _
    exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w u
  · exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w t

/-- **Biconditional form of the transport.**

The two scalar functions — the bundled `pullbackMetric` inner product and its
evaluation-formula expansion — have the same `HasDerivWithinAt`s. This is the
formal restatement that the identification at the function level lifts to
derivative-witness equivalence. -/
theorem pullbackMetric_inner_hasDerivWithinAt_iff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t
    ↔ HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t :=
  ⟨pullbackMetric_inner_hasDerivWithinAt_to_eval g_fam Φ_fam x v w,
    pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w⟩

/-- **Transport `HasDerivAt` from the evaluation-formula form to the bundled
pullback form.** Strict (unrestricted) variant of
`pullbackMetric_inner_hasDerivWithinAt_of_eval`. -/
theorem pullbackMetric_inner_hasDerivAt_of_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_eval : HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t) :
    HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t := by
  rw [← hasDerivWithinAt_univ] at h_eval ⊢
  exact pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_eval

/-- **Transport `HasDerivAt` from the bundled pullback form to the
evaluation-formula form.** Converse of `pullbackMetric_inner_hasDerivAt_of_eval`. -/
theorem pullbackMetric_inner_hasDerivAt_to_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_pullback : HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t) :
    HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t := by
  rw [← hasDerivWithinAt_univ] at h_pullback ⊢
  exact pullbackMetric_inner_hasDerivWithinAt_to_eval g_fam Φ_fam x v w h_pullback

/-- **Biconditional form of `HasDerivAt` transport.** -/
theorem pullbackMetric_inner_hasDerivAt_iff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t
    ↔ HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t :=
  ⟨pullbackMetric_inner_hasDerivAt_to_eval g_fam Φ_fam x v w,
    pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w⟩

/-- **Three-piece product-rule transport (within-set).**

Given the three component-derivative witnesses on the evaluation-form scalar
function (intrinsic metric-time piece, first-slot pushforward piece,
second-slot pushforward piece) and their assembly into a total
`HasDerivWithinAt` for the *sum* `G' + A' + B'`, conclude the same derivative
for the bundled pullback form. -/
theorem pullbackMetric_inner_hasDerivWithinAt_product_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' A' B' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_total : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      (G' + A' + B') s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      (G' + A' + B') s t :=
  pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_total

/-- **Two-piece sum transport (within-set).**

A two-piece variant of `pullbackMetric_inner_hasDerivWithinAt_product_rule`,
useful when the consumer has already grouped the second- and third-slot
variations into a single Lie-derivative term `L'`, so the total reads
`G' + L'`. -/
theorem pullbackMetric_inner_hasDerivWithinAt_sum
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' L' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_total : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      (G' + L') s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      (G' + L') s t :=
  pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_total

end DifferentialGeometry.PDE.RicciFlow.Pullback
