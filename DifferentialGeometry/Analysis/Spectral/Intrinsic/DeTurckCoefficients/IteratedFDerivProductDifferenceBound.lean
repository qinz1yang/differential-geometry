import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Order.Compact

/-!
# All-order Leibniz bound for a single-difference scalar product

The analytic engine of the all-order (Faà-di-Bruno) chart-jet Lipschitz estimate for
the Ricci–DeTurck right-hand side.  The chart-coordinate Ricci and Lie–DeTurck
components are polynomial/rational expressions in the chart-Gram entries, the inverse
chart-Gram, and their partial derivatives.  Their difference between two metrics
telescopes, term by term, into a finite sum of products in which **exactly one factor
is a difference** of constituent scalar fields and every other factor is a smooth scalar
field uniformly bounded in every derivative order on a compact set.

This file proves the order-`N` norm bound for one such single-difference product:
if `δ : E → ℝ` is the difference factor and `h : E → ℝ` is the product of the bounded
factors, with `h` uniformly `Cᴺ`-bounded by `B` on a compact `K` inside an open set
`s`, then
```
‖iteratedFDerivWithin ℝ N (fun y => δ y * h y) s y‖ ≤
    2 ^ N * B * ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ l δ s y‖
```
for every `y ∈ K`.  This is a direct consequence of the higher-order Leibniz rule
`norm_iteratedFDerivWithin_mul_le`, the binomial identity `∑ choose = 2ⁿ`, and the fact
that every term of the right-hand side of Leibniz is a single summand of the difference
seminorm.

The bound is the reusable analytic kernel: the concrete chart estimates package the
relevant difference factor as `δ` and the relevant bounded product as `h`, supply the
uniform `Cᴺ` bound from continuity of the iterated derivatives on a compact set, and sum
the resulting per-term bounds.

## Main results

* `iteratedFDerivSeminorm` — the order-`N` seminorm `∑_{l ≤ N} ‖iteratedFDerivWithin ℝ l f s y‖`.
* `exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn` — a `ContDiffOn` scalar field
  is uniformly `Cᴺ`-bounded on a compact subset of the domain.
* `norm_iteratedFDerivWithin_mul_le_uniformBound` — the order-`N` Leibniz bound for a
  single-difference product against a uniformly `Cᴺ`-bounded factor.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The order-`N` iterated-derivative seminorm of a scalar field `f` on a set `s`,
evaluated at `y`: the sum over orders `l ≤ N` of the operator norms of the iterated
Fréchet derivatives within `s`. -/
def iteratedFDerivSeminorm (N : ℕ) (f : E → ℝ) (s : Set E) (y : E) : ℝ :=
  ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ l f s y‖

lemma iteratedFDerivSeminorm_nonneg (N : ℕ) (f : E → ℝ) (s : Set E) (y : E) :
    0 ≤ iteratedFDerivSeminorm N f s y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The order-`N` seminorm is monotone in `N`. -/
lemma iteratedFDerivSeminorm_mono
    {N N' : ℕ} (hN : N ≤ N') (f : E → ℝ) (s : Set E) (y : E) :
    iteratedFDerivSeminorm N f s y ≤ iteratedFDerivSeminorm N' f s y := by
  unfold iteratedFDerivSeminorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  exact Finset.range_mono (Nat.succ_le_succ hN)

/-- Each iterated derivative of order `l ≤ N` is bounded by the order-`N` seminorm. -/
lemma norm_iteratedFDerivWithin_le_seminorm
    {N l : ℕ} (hl : l ≤ N) (f : E → ℝ) (s : Set E) (y : E) :
    ‖iteratedFDerivWithin ℝ l f s y‖ ≤ iteratedFDerivSeminorm N f s y :=
  Finset.single_le_sum (f := fun l => ‖iteratedFDerivWithin ℝ l f s y‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

/-- The order-`N` seminorm of a difference is symmetric under swapping the two terms:
`iteratedFDerivSeminorm N (f − g) s y = iteratedFDerivSeminorm N (g − f) s y` on a set with
unique differentials.  (Each iterated derivative of `g − f` is the negation of that of
`f − g`, and negation preserves the norm.) -/
lemma iteratedFDerivSeminorm_sub_comm
    {f g : E → ℝ} {s : Set E} (hs : UniqueDiffOn ℝ s) {y : E} (hy : y ∈ s) (N : ℕ) :
    iteratedFDerivSeminorm N (fun z => f z - g z) s y =
      iteratedFDerivSeminorm N (fun z => g z - f z) s y := by
  classical
  unfold iteratedFDerivSeminorm
  refine Finset.sum_congr rfl fun l _ => ?_
  have hvec : iteratedFDerivWithin ℝ l (fun z => g z - f z) s y =
      -iteratedFDerivWithin ℝ l (fun z => f z - g z) s y :=
    calc iteratedFDerivWithin ℝ l (fun z => g z - f z) s y
        = iteratedFDerivWithin ℝ l (fun z => -((fun w => f w - g w) z)) s y :=
          iteratedFDerivWithin_congr (f₁ := fun z => g z - f z)
            (f := fun z => -((fun w => f w - g w) z)) (by intro z _; ring) hy l
      _ = -iteratedFDerivWithin ℝ l (fun w => f w - g w) s y :=
          iteratedFDerivWithin_neg_apply hs hy
  rw [hvec, norm_neg]

/-- A `ContDiffOn ℝ ∞` scalar field is uniformly `Cᴺ`-bounded on a compact subset of its
(open) domain: there is a single bound `B` with
`‖iteratedFDerivWithin ℝ m f s y‖ ≤ B` for every order `m ≤ N` and every `y ∈ K`. -/
theorem exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
    {f : E → ℝ} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ s) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ∀ m : ℕ, m ≤ N →
      ‖iteratedFDerivWithin ℝ m f s y‖ ≤ B := by
  classical
  have hper : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ m f s y‖ ≤ B := by
    intro m
    have hcont : ContinuousOn
        (fun y => iteratedFDerivWithin ℝ m f s y) s :=
      hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs.uniqueDiffOn
    have hcontK : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ m f s y‖) K :=
      (hcont.mono hKsub).norm
    by_cases hKe : K = ∅
    · exact ⟨0, le_refl 0, fun y hy => absurd (hKe ▸ hy) (Set.notMem_empty _)⟩
    obtain ⟨C, hC⟩ := hK.bddAbove_image hcontK
    refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
    exact (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  choose Bm hBm_nn hBm using hper
  refine ⟨∑ m ∈ Finset.range (N + 1), Bm m, Finset.sum_nonneg fun m _ => hBm_nn m, ?_⟩
  intro y hy m hmN
  refine (hBm m y hy).trans ?_
  exact Finset.single_le_sum (f := fun m => Bm m) (fun i _ => hBm_nn i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hmN))

/-- **Order-`N` Leibniz bound for a single-difference scalar product.**

Let `s` be an open set, `δ h : E → ℝ` both `ContDiffOn ℝ ∞` on `s`, and suppose `h` is
uniformly `Cᴺ`-bounded by `B` on a compact `K ⊆ s`.  Then the order-`N` iterated
derivative of the product `δ · h` is bounded, on `K`, by `2ᴺ · B` times the order-`N`
seminorm of the difference factor `δ`:
```
‖iteratedFDerivWithin ℝ N (fun y => δ y * h y) s y‖ ≤
    2 ^ N * B * iteratedFDerivSeminorm N δ s y .
```
This is the higher-order Leibniz rule with every bounded-factor derivative replaced by
its uniform bound and the difference-factor derivative of each Leibniz term majorised by
the full seminorm. -/
theorem norm_iteratedFDerivWithin_mul_le_uniformBound
    {δ h : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hδ : ContDiffOn ℝ ∞ δ s) (hh : ContDiffOn ℝ ∞ h s)
    {K : Set E} (hKsub : K ⊆ s) {B : ℝ} (_hB_nn : 0 ≤ B) (N : ℕ)
    (hHbound : ∀ y ∈ K, ∀ m : ℕ, m ≤ N → ‖iteratedFDerivWithin ℝ m h s y‖ ≤ B)
    {y : E} (hy : y ∈ K) :
    ‖iteratedFDerivWithin ℝ N (fun z => δ z * h z) s y‖ ≤
      2 ^ N * B * iteratedFDerivSeminorm N δ s y := by
  classical
  have hyS : y ∈ s := hKsub hy
  have hLeibniz :
      ‖iteratedFDerivWithin ℝ N (fun z => δ z * h z) s y‖ ≤
        ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i δ s y‖ * ‖iteratedFDerivWithin ℝ (N - i) h s y‖ :=
    norm_iteratedFDerivWithin_mul_le hδ hh hs.uniqueDiffOn hyS (by exact_mod_cast le_top)
  refine hLeibniz.trans ?_
  have hseminorm_nn : 0 ≤ iteratedFDerivSeminorm N δ s y :=
    iteratedFDerivSeminorm_nonneg N δ s y
  have hterm : ∀ i ∈ Finset.range (N + 1),
      (N.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i δ s y‖ *
          ‖iteratedFDerivWithin ℝ (N - i) h s y‖ ≤
        (N.choose i : ℝ) * (B * iteratedFDerivSeminorm N δ s y) := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hδ_le : ‖iteratedFDerivWithin ℝ i δ s y‖ ≤ iteratedFDerivSeminorm N δ s y :=
      norm_iteratedFDerivWithin_le_seminorm hiN δ s y
    have hh_le : ‖iteratedFDerivWithin ℝ (N - i) h s y‖ ≤ B :=
      hHbound y hy (N - i) (Nat.sub_le N i)
    have hchoose_nn : (0 : ℝ) ≤ (N.choose i : ℝ) := by positivity
    calc (N.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i δ s y‖ *
            ‖iteratedFDerivWithin ℝ (N - i) h s y‖
        ≤ (N.choose i : ℝ) * iteratedFDerivSeminorm N δ s y * B := by
          refine mul_le_mul ?_ hh_le (norm_nonneg _)
            (mul_nonneg hchoose_nn hseminorm_nn)
          exact mul_le_mul_of_nonneg_left hδ_le hchoose_nn
      _ = (N.choose i : ℝ) * (B * iteratedFDerivSeminorm N δ s y) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum_choose : (∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ)) = 2 ^ N := by
    have := Nat.sum_range_choose N
    calc (∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ))
        = ((∑ i ∈ Finset.range (N + 1), N.choose i : ℕ) : ℝ) := by
          push_cast; rfl
      _ = ((2 ^ N : ℕ) : ℝ) := by rw [this]
      _ = 2 ^ N := by push_cast; ring
  rw [hsum_choose]
  exact le_of_eq (by ring)

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
