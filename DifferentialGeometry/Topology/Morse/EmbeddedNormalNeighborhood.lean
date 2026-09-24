import DifferentialGeometry.Topology.Morse.EmbeddedNormalFormGlobal
import DifferentialGeometry.Topology.Embedding.GraphNeighborhood
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Set Manifold Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.Morse

variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel n) H}
  [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_global_height_preserving_morse_normal_neighborhood
    {e : M → EuclideanSpace ℝ (Fin n) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) ∞ e)
    {p : M} (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = k) :
    let q := fun y => morseNormalForm hk (e p).2 (EuclideanSpace.equiv (Fin n) ℝ y)
    ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (EuclideanSpace ℝ (Fin n)) M ∞,
        ∃ Φ : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ),
          closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, (Φ z).2 = z.2) ∧
          (∀ y ∈ closedBall 0 r, Φ (y, q y) = e (χ y)) ∧
          (∀ y ∈ closedBall 0 r, q y ∈ ball (e p).2 t) ∧
          (closedBall 0 r ×ˢ closedBall (e p).2 t) ∩ range (Φ.symm ∘ e) =
            (fun y => (y, q y)) '' closedBall 0 r := by
  dsimp only
  let L := EuclideanSpace.equiv (Fin n) ℝ
  let q := fun y => morseNormalForm hk (e p).2 (L y)
  have hq0 : q 0 = (e p).2 := by simp [q, morseNormalForm]
  obtain ⟨R, hR, χ, Φ, hRs, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_morse_normal_form he.contMDiff
      ((he.isImmersion.isImmersionAt p).injective_mfderiv (by simp)) k hk hnd hindex
  have hgraph : ∀ y ∈ ball 0 R, (Φ.symm ∘ e) (χ.toOpenPartialHomeomorph y) = (y, q y) := by
    intro y hy
    change Φ.symm (e (χ y)) = (y, q y)
    rw [← hnormal y (ball_subset_closedBall hy), Φ.symm_apply_apply]
  have hq : Continuous q := by
    dsimp [q, morseNormalForm]
    fun_prop
  have he' := (Φ.symm.toHomeomorph.isEmbedding.comp he.isEmbedding).isInducing
  obtain ⟨r, hr, t, ht, hrs, hqt, hset⟩ :=
    he'.exists_prod_closedBall_inter_range_eq_graph χ.toOpenPartialHomeomorph
        isOpen_ball (ball_subset_closedBall.trans hRs) hgraph (mem_ball_self hR) hq.continuousAt
  refine ⟨r, hr, t, ht, χ, Φ, hrs.trans (ball_subset_closedBall.trans hRs), hχ0,
    hheight, fun y hy => hnormal y (ball_subset_closedBall (hrs hy)), ?_, ?_⟩
  · simpa only [hq0] using hqt
  · simpa only [hq0, Diffeomorph.coe_toHomeomorph] using hset

end DifferentialGeometry.Topology.Morse
