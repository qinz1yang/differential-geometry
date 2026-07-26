import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Time-jet propagation through a smooth map

The reusable core of the Ricci-flow jet-compatibility argument (the time-jet recursion). If a smooth
map `Φ` is post-composed with two curves `uL`, `uR : ℝ → J` whose one-sided/iterated derivatives
agree to order `n` at `0`, then the iterated derivatives of `Φ ∘ uL` and `Φ ∘ uR` also agree to
order `n` at `0`.

The proof is a single application of Mathlib's Faà-di-Bruno formula
(`iteratedDeriv_vcomp_eq_sum_orderedFinpartition`): both composites expand to the SAME sum over
`OrderedFinpartition i`, and termwise the two factors of each summand agree — the outer factor
`iteratedFDeriv c.length Φ (· 0)` because `uL 0 = uR 0` (the order-`0` jet), and the inner tuple
`fun j ↦ iteratedDeriv (c.partSize j) · 0` because every part size is `≤ i ≤ n`
(`OrderedFinpartition.partSize_le`). No explicit universal Faà-di-Bruno coefficients are formalized.

This is the engine for the Ricci `hglue` jet match: instantiated pointwise in the spatial chart
variable at the coordinate Ricci-flow operator `Φ = -2·chartRicci(·)` (smooth on the
positive-definite metric 2-jet locus, `Lemma 3`), with the curves the time-families of the metric
2-jet, it yields equality of all normal time-jets at the seam from equal boundary metric data.
See `Analysis/Calculus/SmoothExtension/JetGlueParam.md` (Lemma 2 / time-jet recursion).
-/

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

/-- A continuous linear map commutes with `iteratedDerivWithin`:
`iteratedDerivWithin n (L ∘ f) s x = L (iteratedDerivWithin n f s x)`. Used to decompose the
iterated derivative of a product-valued curve over its components (the 2-jet slots). -/
theorem iteratedDerivWithin_clm_comp {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) {f : ℝ → A} {s : Set ℝ} {x : ℝ} {n : ℕ}
    (hf : ContDiffWithinAt ℝ n f s x) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n (fun t => L (f t)) s x = L (iteratedDerivWithin n f s x) := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
    show (fun t => L (f t)) = ⇑L ∘ f from rfl, L.iteratedFDerivWithin_comp_left hf hs hx le_rfl]
  rfl

/-- `iteratedDerivWithin` of a pair-valued curve is the pair of the component derivatives. -/
theorem iteratedDerivWithin_prodMk {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f : ℝ → A} {g : ℝ → B} {s : Set ℝ} {x : ℝ} {n : ℕ}
    (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n (fun t => (f t, g t)) s x
      = (iteratedDerivWithin n f s x, iteratedDerivWithin n g s x) :=
  Prod.ext
    (iteratedDerivWithin_clm_comp (ContinuousLinearMap.fst ℝ A B) (hf.prodMk hg) hs hx).symm
    (iteratedDerivWithin_clm_comp (ContinuousLinearMap.snd ℝ A B) (hf.prodMk hg) hs hx).symm

variable {J F' : Type*}
    [NormedAddCommGroup J] [NormedSpace ℝ J] [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **Time-jet propagation through a smooth map.** If `Φ` is `C^n` at `uL 0`, the curves `uL`, `uR`
are `C^n` at `0`, and their iterated derivatives agree to order `n` at `0`
(`iteratedDeriv a uL 0 = iteratedDeriv a uR 0` for `a ≤ n`), then `iteratedDeriv i (Φ ∘ uL) 0 =
iteratedDeriv i (Φ ∘ uR) 0` for every `i ≤ n`. -/
theorem iteratedDeriv_comp_jet_eq {Φ : J → F'} {uL uR : ℝ → J} {n : ℕ}
    (hΦ : ContDiffAt ℝ n Φ (uL 0)) (huL : ContDiffAt ℝ n uL 0) (huR : ContDiffAt ℝ n uR 0)
    (hjet : ∀ a, a ≤ n → iteratedDeriv a uL 0 = iteratedDeriv a uR 0)
    {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv i (Φ ∘ uL) 0 = iteratedDeriv i (Φ ∘ uR) 0 := by
  have hp : uL 0 = uR 0 := by
    have h := hjet 0 (Nat.zero_le n)
    rwa [iteratedDeriv_zero, iteratedDeriv_zero] at h
  have hΦR : ContDiffAt ℝ n Φ (uR 0) := hp ▸ hΦ
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hΦ huL (by exact_mod_cast hi),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hΦR huR (by exact_mod_cast hi)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have htuple : (fun j => iteratedDeriv (c.partSize j) uL 0)
      = (fun j => iteratedDeriv (c.partSize j) uR 0) :=
    funext fun j => hjet (c.partSize j) (le_trans (c.partSize_le j) hi)
  rw [hp, htuple]

/-- **One-sided / cross-set time-jet propagation through a smooth map.** The `iteratedDerivWithin`
analogue of `iteratedDeriv_comp_jet_eq`, allowing the two curves to use DIFFERENT sets `sL`, `sR`
(e.g. the closed half-lines `Iic 0` and `Ici 0` at a seam). If `Φ` is `C^n` at the common seam point
`uL 0 = uR 0`, the curves are `C^n`-within their sets at `0`, and their within-iterated derivatives
agree to order `n` at `0`, then the within-iterated derivatives of the composites agree to order `n`.

The proof uses the Faà-di-Bruno formula with `Φ`'s target set taken to be `Set.univ`: this makes the
`MapsTo` side-condition trivial and the outer factor `iteratedFDerivWithin c.length Φ univ (· 0)` a
plain `iteratedFDeriv` at the COMMON point `uL 0 = uR 0`, so the cross-set asymmetry is confined to
the inner jet tuple, which matches by `hjet` and `OrderedFinpartition.partSize_le`. -/
theorem iteratedDerivWithin_comp_jet_eq {Φ : J → F'} {uL uR : ℝ → J} {sL sR : Set ℝ} {n : ℕ}
    (hΦ : ContDiffAt ℝ n Φ (uL 0))
    (huL : ContDiffWithinAt ℝ n uL sL 0) (huR : ContDiffWithinAt ℝ n uR sR 0)
    (hsL : UniqueDiffOn ℝ sL) (hsR : UniqueDiffOn ℝ sR)
    (h0L : (0 : ℝ) ∈ sL) (h0R : (0 : ℝ) ∈ sR)
    (hjet : ∀ a, a ≤ n → iteratedDerivWithin a uL sL 0 = iteratedDerivWithin a uR sR 0)
    {i : ℕ} (hi : i ≤ n) :
    iteratedDerivWithin i (Φ ∘ uL) sL 0 = iteratedDerivWithin i (Φ ∘ uR) sR 0 := by
  have hp : uL 0 = uR 0 := by
    have h := hjet 0 (Nat.zero_le n)
    rwa [iteratedDerivWithin_zero, iteratedDerivWithin_zero] at h
  have hΦL : ContDiffWithinAt ℝ n Φ Set.univ (uL 0) := hΦ.contDiffWithinAt
  have hΦR : ContDiffWithinAt ℝ n Φ Set.univ (uR 0) := (hp ▸ hΦ).contDiffWithinAt
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hΦL huL uniqueDiffOn_univ hsL h0L
        (Set.mapsTo_univ _ _) (by exact_mod_cast hi),
    iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hΦR huR uniqueDiffOn_univ hsR h0R
        (Set.mapsTo_univ _ _) (by exact_mod_cast hi)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have htuple : (fun j => iteratedDerivWithin (c.partSize j) uL sL 0)
      = (fun j => iteratedDerivWithin (c.partSize j) uR sR 0) :=
    funext fun j => hjet (c.partSize j) (le_trans (c.partSize_le j) hi)
  rw [hp, htuple]

end Analysis
end DifferentialGeometry

end
