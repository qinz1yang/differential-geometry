import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open scoped Manifold ContDiff

namespace Diffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {f g h : E → F}

def graphShear (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) n where
  toEquiv := (Equiv.refl E).prodShear (fun x => Equiv.addRight (g x - f x))
  contMDiff_toFun :=
    (contDiff_fst.prodMk
      (contDiff_snd.add ((hg.sub hf).comp contDiff_fst))).contMDiff
  contMDiff_invFun :=
    (contDiff_fst.prodMk
      (contDiff_snd.add (((hg.sub hf).comp contDiff_fst).neg))).contMDiff

@[simp] theorem graphShear_apply (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (p : E × F) : graphShear hf hg p = (p.1, p.2 + g p.1 - f p.1) := by
  apply Prod.ext
  · rfl
  · change p.2 + (g p.1 - f p.1) = p.2 + g p.1 - f p.1
    abel

theorem graphShear_symm_apply (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (p : E × F) : (graphShear hf hg).symm p = (p.1, p.2 + f p.1 - g p.1) := by
  apply Prod.ext
  · rfl
  · change p.2 + -(g p.1 - f p.1) = p.2 + f p.1 - g p.1
    abel

@[simp] theorem graphShear_symm (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    (graphShear hf hg).symm = graphShear hg hf := by
  apply Diffeomorph.ext
  intro p
  rw [graphShear_symm_apply, graphShear_apply]

@[simp] theorem graphShear_refl (hf : ContDiff ℝ n f) :
    graphShear hf hf = Diffeomorph.refl 𝓘(ℝ, E × F) (E × F) n := by
  apply Diffeomorph.ext
  intro p
  rw [graphShear_apply]
  simp

@[simp] theorem graphShear_trans (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hh : ContDiff ℝ n h) :
    (graphShear hf hg).trans (graphShear hg hh) = graphShear hf hh := by
  apply Diffeomorph.ext
  intro p
  change graphShear hg hh (graphShear hf hg p) = graphShear hf hh p
  simp only [graphShear_apply]
  apply Prod.ext
  · rfl
  · dsimp
    abel

theorem graphShear_apply_eq_self_iff (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (p : E × F) : graphShear hf hg p = p ↔ f p.1 = g p.1 := by
  constructor
  · intro hp
    have hs := congrArg Prod.snd hp
    rw [graphShear_apply] at hs
    change p.2 + g p.1 - f p.1 = p.2 at hs
    have heq : p.2 + g p.1 = p.2 + f p.1 := by
      simpa only [sub_add_cancel] using congrArg (fun y : F => y + f p.1) hs
    exact (add_left_cancel heq).symm
  · intro hp
    rw [graphShear_apply]
    apply Prod.ext
    · rfl
    · change p.2 + g p.1 - f p.1 = p.2
      rw [hp]
      simp

theorem graphShear_image_graphOn (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (s : Set E) : graphShear hf hg '' Set.graphOn f s = Set.graphOn g s := by
  simp only [Set.graphOn, Set.image_image]
  congr 1
  funext x
  simp only [graphShear_apply]
  apply Prod.ext
  · rfl
  · dsimp
    abel

section Epigraph

variable {f g : E → ℝ}

theorem graphShear_image_epigraph (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (s : Set E) :
    graphShear hf hg '' {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} =
      {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [graphShear_apply]
    exact ⟨hq.1, by dsimp; linarith [hq.2]⟩
  · intro hp
    refine ⟨(p.1, p.2 + f p.1 - g p.1), ⟨hp.1, ?_⟩, ?_⟩
    · dsimp
      linarith [hp.2]
    · rw [graphShear_apply]
      apply Prod.ext
      · rfl
      · dsimp
        abel

theorem graphShear_image_strict_epigraph (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (s : Set E) :
    graphShear hf hg '' {p : E × ℝ | p.1 ∈ s ∧ f p.1 < p.2} =
      {p : E × ℝ | p.1 ∈ s ∧ g p.1 < p.2} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [graphShear_apply]
    exact ⟨hq.1, by dsimp; linarith [hq.2]⟩
  · intro hp
    refine ⟨(p.1, p.2 + f p.1 - g p.1), ⟨hp.1, ?_⟩, ?_⟩
    · dsimp
      linarith [hp.2]
    · rw [graphShear_apply]
      apply Prod.ext
      · rfl
      · dsimp
        abel

end Epigraph

end Diffeomorph
