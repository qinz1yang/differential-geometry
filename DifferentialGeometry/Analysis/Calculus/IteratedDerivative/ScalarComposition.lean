import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

section Algebra

variable {𝕜 F : Type*} [CommSemiring 𝕜] [AddCommMonoid F] [Module 𝕜 F]

def scalarJetComposition (n : ℕ) :
    ((Fin (n + 1) → 𝕜) × (Fin (n + 1) → F)) → F :=
  fun q => ∑ c : OrderedFinpartition n,
    (∏ j : Fin c.length,
      q.1 ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩) •
      q.2 ⟨c.length, Nat.lt_succ_of_le c.length_le⟩

@[simp]
theorem scalarJetComposition_zero (a : Fin 1 → 𝕜) (b : Fin 1 → F) :
    scalarJetComposition 0 (a, b) = b 0 := by
  classical
  simp [scalarJetComposition, OrderedFinpartition.atomic]

end Algebra

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiff_scalarJetComposition (n : ℕ) {m : ℕ∞ω} :
    ContDiff 𝕜 m (scalarJetComposition (𝕜 := 𝕜) (F := F) n) := by
  classical
  unfold scalarJetComposition
  apply ContDiff.sum
  intro c _
  apply ContDiff.smul
  · apply contDiff_prod
    intro j _
    exact (contDiff_apply 𝕜 𝕜
      (⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩ : Fin (n + 1))).comp
      contDiff_fst
  · exact (contDiff_apply 𝕜 F
      (⟨c.length, Nat.lt_succ_of_le c.length_le⟩ : Fin (n + 1))).comp
      contDiff_snd

theorem iteratedDeriv_eq_scalarJetComposition {n : ℕ}
    {f : 𝕜 → 𝕜} {g : 𝕜 → F} {x : 𝕜}
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g (f x)) :
    iteratedDeriv n (g ∘ f) x = scalarJetComposition n
      (fun i => iteratedDeriv i.val f x, fun i => iteratedDeriv i.val g (f x)) := by
  exact iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf le_rfl

theorem continuousOn_iteratedDeriv_scalar_family_comp
    {P : Type*} [TopologicalSpace P] {S : Set P}
    {f : P → 𝕜 → 𝕜} {g : P → 𝕜 → F} {x : P → 𝕜} (n : ℕ)
    (hf : ∀ p ∈ S, ContDiffAt 𝕜 n (f p) (x p))
    (hg : ∀ p ∈ S, ContDiffAt 𝕜 n (g p) (f p (x p)))
    (hinner : ∀ j ≤ n,
      ContinuousOn (fun p => iteratedDeriv j (f p) (x p)) S)
    (houter : ∀ j ≤ n,
      ContinuousOn (fun p => iteratedDeriv j (g p) (f p (x p))) S) :
    ContinuousOn (fun p => iteratedDeriv n (g p ∘ f p) (x p)) S := by
  have hi : ContinuousOn
      (fun p => fun i : Fin (n + 1) => iteratedDeriv i.val (f p) (x p)) S :=
    continuousOn_pi.mpr fun i => hinner i.val (Nat.le_of_lt_succ i.isLt)
  have ho : ContinuousOn
      (fun p => fun i : Fin (n + 1) => iteratedDeriv i.val (g p) (f p (x p))) S :=
    continuousOn_pi.mpr fun i => houter i.val (Nat.le_of_lt_succ i.isLt)
  exact ((contDiff_scalarJetComposition (𝕜 := 𝕜) (F := F) n (m := ∞)).continuous.comp_continuousOn
    (hi.prodMk ho)).congr fun p hp =>
      iteratedDeriv_eq_scalarJetComposition (hf p hp) (hg p hp)

end DifferentialGeometry.Analysis
