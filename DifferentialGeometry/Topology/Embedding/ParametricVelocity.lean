import DifferentialGeometry.Bundle.PartialMfderiv
import DifferentialGeometry.Topology.Embedding.SmoothParametricGraph
import DifferentialGeometry.Topology.Embedding.Extension

open scoped ContDiff Manifold

namespace Manifold

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

theorem exists_contDiff_compact_velocity_extension
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O : Set (ℝ × V)} (hO : IsOpen O) (hKO : (fun q => (q.1, e q)) '' K ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K := by
  have hgraph := isSmoothEmbedding_parametric_graph he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) :=
    he.deriv_fst
  exact hgraph.exists_contDiff_compact_extension hv hK hO hKO

theorem exists_contDiff_compact_velocity_extension_Icc
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set (ℝ × V)} (hO : IsOpen O)
    (hOe : (fun q => (q.1, e q)) '' (Icc a b ×ˢ univ) ⊆ O) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      ∀ t ∈ Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t := by
  obtain ⟨X, hX, hXc, hXO, hXe⟩ := exists_contDiff_compact_velocity_extension he hf
    (isCompact_Icc.prod isCompact_univ) hO hOe
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, mem_univ x⟩⟩

end Manifold
