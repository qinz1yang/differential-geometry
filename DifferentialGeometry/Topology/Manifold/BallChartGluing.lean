import DifferentialGeometry.Topology.Manifold.BallDiffeomorphExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactGluing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_diffeomorph_eqOn_of_partialDiffeomorphs_closedBall {ι : Type*}
    (φ : ι → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r : ℝ} (hr : 0 < r) {U : ι → Set E} (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, U i ⊆ (φ i).source) (hcover : closedBall 0 r ⊆ ⋃ i, U i)
    (heq : ∀ i j, EqOn (φ i) (φ j) (U i ∩ U j))
    (himage : ∀ i j, φ i '' (closedBall 0 r ∩ U i) ∩ φ j '' (closedBall 0 r ∩ U j) ⊆
      φ i '' (closedBall 0 r ∩ U i ∩ U j)) :
    ∃ D : E ≃ₘ[ℝ] E, ∀ i, EqOn D (φ i) (closedBall 0 r ∩ U i) := by
  obtain ⟨ψ, hsrc, hψ⟩ := PartialDiffeomorph.exists_gluing_of_isCompact φ
    (isCompact_closedBall _ _) ⟨0, mem_closedBall_self hr.le⟩ hU hs hcover heq himage
  obtain ⟨D, hD⟩ := exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall ψ hr hsrc
  exact ⟨D, fun i x hx => (hD hx.1).trans (hψ i ⟨hsrc hx.1, hx.2⟩)⟩


theorem exists_diffeomorph_eqOn_of_partialDiffeomorphs_closedBall_of_fiber_preserving {ι : Type*}
    (φ : ι → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {P : Type*} (f g : E → P) {r : ℝ} (hr : 0 < r) {Ω : Set E} {S : ι → Set P}
    (hU : ∀ i, IsOpen (Ω ∩ f ⁻¹' S i)) (hs : ∀ i, Ω ∩ f ⁻¹' S i ⊆ (φ i).source)
    (hΩ : closedBall 0 r ⊆ Ω) (hcover : f '' closedBall 0 r ⊆ ⋃ i, S i)
    (heq : ∀ i j, EqOn (φ i) (φ j) (Ω ∩ f ⁻¹' (S i ∩ S j)))
    (hf : ∀ i x, x ∈ Ω ∩ f ⁻¹' S i → g (φ i x) = f x) :
    ∃ D : E ≃ₘ[ℝ] E, ∀ i, EqOn D (φ i) (closedBall 0 r ∩ (Ω ∩ f ⁻¹' S i)) := by
  apply exists_diffeomorph_eqOn_of_partialDiffeomorphs_closedBall φ hr hU hs
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
    exact mem_iUnion.mpr ⟨i, hΩ hx, hxi⟩
  · intro i j x hx
    exact heq i j ⟨hx.1.1, hx.1.2, hx.2.2⟩
  · intro i j
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
    have hxy : f x = f y := (hf i x hx.2).symm.trans
      ((congrArg g hyx).symm.trans (hf j y hy.2))
    have hxj : x ∈ f ⁻¹' S j := by
      change f x ∈ S j
      rw [hxy]
      exact hy.2.2
    exact ⟨x, ⟨hx, hΩ hx.1, hxj⟩, rfl⟩

theorem exists_diffeomorph_eqOn_of_partialDiffeomorphs_closedBall_of_height_intervals
    (φ : Fin 3 → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (f g : E → ℝ) {a b τ r : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (hab : a + τ ≤ b - τ) {U : Fin 3 → Set E}
    (hU : ∀ i, IsOpen (U i)) (hs : ∀ i, U i ⊆ (φ i).source)
    (hband : ∀ i, ∀ x ∈ closedBall (0 : E) r,
      x ∈ U i ↔ f x ∈ ![Iio (a + τ), Ioo a b, Ioi (b - τ)] i)
    (heq : ∀ i j, EqOn (φ i) (φ j) (U i ∩ U j))
    (h₀ : ∀ x ∈ U 0, g (φ 0 x) = f x)
    (h₁ : ∀ x ∈ U 1, g (φ 1 x) = f x)
    (h₂ : ∀ x ∈ U 2, b ≤ g (φ 2 x) ↔ b ≤ f x) :
    ∃ D : E ≃ₘ[ℝ] E, ∀ i, EqOn D (φ i) (closedBall 0 r ∩ U i) := by
  have hb (i : Fin 3) {x : E} (hx : x ∈ closedBall 0 r ∩ U i) (hi : i ≠ 2) :
      g (φ i x) < b := by
    have h := (hband i x hx.1).mp hx.2
    fin_cases i
    · change g (φ 0 x) < b
      rw [h₀ x hx.2]
      change f x < a + τ at h
      linarith
    · change g (φ 1 x) < b
      rw [h₁ x hx.2]
      exact h.2
    · exact (hi rfl).elim
  have hheight (i : Fin 3) {x : E} (hx : x ∈ closedBall 0 r ∩ U i)
      (hlt : g (φ i x) < b) : g (φ i x) = f x := by
    fin_cases i
    · exact h₀ x hx.2
    · exact h₁ x hx.2
    · have hxb : f x < b := lt_of_not_ge (fun h => (not_le_of_gt hlt) ((h₂ x hx.2).mpr h))
      have hxa : b - τ < f x := (hband 2 x hx.1).mp hx.2
      have hx₁ : x ∈ U 1 := (hband 1 x hx.1).mpr ⟨by linarith, hxb⟩
      change g (φ 2 x) = f x
      rw [heq 2 1 ⟨hx.2, hx₁⟩]
      exact h₁ x hx₁
  apply exists_diffeomorph_eqOn_of_partialDiffeomorphs_closedBall φ hr hU hs
  · intro x hx
    by_cases hlo : f x < a + τ
    · exact mem_iUnion.mpr ⟨0, (hband 0 x hx).mpr hlo⟩
    · by_cases hhi : b - τ < f x
      · exact mem_iUnion.mpr ⟨2, (hband 2 x hx).mpr hhi⟩
      · exact mem_iUnion.mpr ⟨1, (hband 1 x hx).mpr ⟨by linarith, by linarith⟩⟩
  · exact heq
  · intro i j
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
    by_cases hij : i = j
    · subst j
      exact ⟨x, ⟨hx, hx.2⟩, rfl⟩
    · have hlt : g (φ i x) < b := by
        by_cases hi : i = 2
        · have hj : j ≠ 2 := fun hj => hij (hi.trans hj.symm)
          rw [← hyx]
          exact hb j hy hj
        · exact hb i hx hi
      have hxy : f x = f y := (hheight i hx hlt).symm.trans
        ((congrArg g hyx).symm.trans (hheight j hy (by rw [hyx]; exact hlt)))
      have hxj : x ∈ U j := (hband j x hx.1).mpr (by
        rw [hxy]
        exact (hband j y hy.1).mp hy.2)
      exact ⟨x, ⟨hx, hxj⟩, rfl⟩

end DifferentialGeometry.Topology.Manifold
