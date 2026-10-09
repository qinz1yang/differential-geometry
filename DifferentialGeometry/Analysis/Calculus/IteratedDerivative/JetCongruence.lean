import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Finite jets of a composite agree when the positive-order inner jets and
all outer jets agree. The outer jets are evaluated at the actual images,
which need not be equal. -/
theorem iteratedFDeriv_comp_eq_of_eq_jets
    {n : ℕ} {f₁ f₂ : E → F} {g₁ g₂ : F → G} {x : E}
    (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x)
    (hg₁ : ContDiffAt 𝕜 n g₁ (f₁ x)) (hg₂ : ContDiffAt 𝕜 n g₂ (f₂ x))
    (hinner : ∀ j, 0 < j → j ≤ n →
      iteratedFDeriv 𝕜 j f₁ x = iteratedFDeriv 𝕜 j f₂ x)
    (houter : ∀ j ≤ n,
      iteratedFDeriv 𝕜 j g₁ (f₁ x) = iteratedFDeriv 𝕜 j g₂ (f₂ x))
    (k : ℕ) (hk : k ≤ n) :
    iteratedFDeriv 𝕜 k (g₁ ∘ f₁) x = iteratedFDeriv 𝕜 k (g₂ ∘ f₂) x := by
  rw [iteratedFDeriv_comp hg₁ hf₁ (i := k) (by exact_mod_cast hk),
    iteratedFDeriv_comp hg₂ hf₂ (i := k) (by exact_mod_cast hk)]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  change c.compAlongOrderedFinpartition (iteratedFDeriv 𝕜 c.length g₁ (f₁ x))
      (fun i => iteratedFDeriv 𝕜 (c.partSize i) f₁ x) =
    c.compAlongOrderedFinpartition (iteratedFDeriv 𝕜 c.length g₂ (f₂ x))
      (fun i => iteratedFDeriv 𝕜 (c.partSize i) f₂ x)
  rw [houter c.length (c.length_le.trans hk)]
  apply congrArg (c.compAlongOrderedFinpartition (iteratedFDeriv 𝕜 c.length g₂ (f₂ x)))
  funext i
  exact hinner (c.partSize i) (c.partSize_pos i) ((c.partSize_le i).trans hk)

/-- Postcomposition with the same finite-regularity map preserves equality of
finite jets. The common image point is recovered from the zero jet. -/
theorem iteratedFDeriv_comp_right_eq_of_eq_jets
    {n : ℕ} {f h : E → F} {B : F → G} {x : E}
    (hf : ContDiffAt 𝕜 n f x) (hh : ContDiffAt 𝕜 n h x)
    (hB : ContDiffAt 𝕜 n B (f x))
    (hjets : ∀ j ≤ n, iteratedFDeriv 𝕜 j f x = iteratedFDeriv 𝕜 j h x)
    (k : ℕ) (hk : k ≤ n) :
    iteratedFDeriv 𝕜 k (B ∘ f) x = iteratedFDeriv 𝕜 k (B ∘ h) x := by
  have hx : f x = h x := by
    simpa only [iteratedFDeriv_zero_apply] using
      congrArg (fun A => A (fun i : Fin 0 => Fin.elim0 i)) (hjets 0 (Nat.zero_le n))
  exact iteratedFDeriv_comp_eq_of_eq_jets hf hh hB (hx ▸ hB)
    (fun j _ hj => hjets j hj) (fun _ _ => congrArg _ hx) k hk

/-- A finite-regularity expression in a point, a map value, and its first
derivative has equal jets through order `n` for maps with equal jets through
order `n + 1`. All regularity is local at the stated point. -/
theorem iteratedFDeriv_comp_value_fderiv_eq_of_eq_jets
    {n : ℕ} {f h : E → F} {x : E} {Φ : E × F × (E →L[𝕜] F) → G}
    (hf : ContDiffAt 𝕜 (n + 1) f x) (hh : ContDiffAt 𝕜 (n + 1) h x)
    (hΦ : ContDiffAt 𝕜 n Φ (x, f x, fderiv 𝕜 f x))
    (hjets : ∀ j ≤ n + 1, iteratedFDeriv 𝕜 j f x = iteratedFDeriv 𝕜 j h x)
    (k : ℕ) (hk : k ≤ n) :
    iteratedFDeriv 𝕜 k (fun y => Φ (y, f y, fderiv 𝕜 f y)) x =
      iteratedFDeriv 𝕜 k (fun y => Φ (y, h y, fderiv 𝕜 h y)) x := by
  have hfn : ContDiffAt 𝕜 n f x :=
    hf.of_le (by exact_mod_cast Nat.le_succ n)
  have hhn : ContDiffAt 𝕜 n h x :=
    hh.of_le (by exact_mod_cast Nat.le_succ n)
  have hDf : ContDiffAt 𝕜 n (fderiv 𝕜 f) x := hf.fderiv_right (by simp)
  have hDh : ContDiffAt 𝕜 n (fderiv 𝕜 h) x := hh.fderiv_right (by simp)
  have hDjets : ∀ j ≤ n,
      iteratedFDeriv 𝕜 j (fderiv 𝕜 f) x = iteratedFDeriv 𝕜 j (fderiv 𝕜 h) x := by
    intro j hj
    apply (continuousMultilinearCurryRightEquiv' 𝕜 j E F).symm.injective
    simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply] using
      hjets (j + 1) (Nat.add_le_add_right hj 1)
  have hpjets : ∀ j ≤ n,
      iteratedFDeriv 𝕜 j (fun y => (f y, fderiv 𝕜 f y)) x =
        iteratedFDeriv 𝕜 j (fun y => (h y, fderiv 𝕜 h y)) x := by
    intro j hj
    rw [iteratedFDeriv_prodMk hfn hDf (i := j) (by exact_mod_cast hj),
      iteratedFDeriv_prodMk hhn hDh (i := j) (by exact_mod_cast hj),
      hjets j (hj.trans (Nat.le_succ n)), hDjets j hj]
  have hfulljets : ∀ j ≤ n,
      iteratedFDeriv 𝕜 j (fun y => (y, f y, fderiv 𝕜 f y)) x =
        iteratedFDeriv 𝕜 j (fun y => (y, h y, fderiv 𝕜 h y)) x := by
    intro j hj
    change iteratedFDeriv 𝕜 j (fun y => (id y, f y, fderiv 𝕜 f y)) x =
      iteratedFDeriv 𝕜 j (fun y => (id y, h y, fderiv 𝕜 h y)) x
    rw [iteratedFDeriv_prodMk contDiffAt_id (hfn.prodMk hDf)
        (i := j) (by exact_mod_cast hj),
      iteratedFDeriv_prodMk contDiffAt_id (hhn.prodMk hDh)
        (i := j) (by exact_mod_cast hj), hpjets j hj]
  exact iteratedFDeriv_comp_right_eq_of_eq_jets
    (contDiffAt_id.prodMk (hfn.prodMk hDf)) (contDiffAt_id.prodMk (hhn.prodMk hDh))
    hΦ hfulljets k hk

end DifferentialGeometry.Analysis
