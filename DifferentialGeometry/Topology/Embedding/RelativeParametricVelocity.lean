import DifferentialGeometry.Topology.Embedding.ParametricVelocity
import DifferentialGeometry.Topology.Embedding.RelativeExtension

open Set Filter
open scoped ContDiff Manifold Topology

namespace Manifold

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

theorem exists_contDiff_compact_velocity_extension_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      (K ∩ tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ q ∈ K, (q.1, e q) ∈ U → W (q.1, e q) = deriv (fun s => e (s, q.2)) q.1) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K ∧
      X =ᶠ[𝓝ˢ C] W := by
  have hgraph := isSmoothEmbedding_parametric_graph he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) :=
    fun p => DifferentialGeometry.timeDeriv_smoothAt (he p) (by simp)
  exact hgraph.exists_contDiff_compact_extension_eq_nhds hv hK hO hKO hU hC hCU hW hWe

theorem exists_contDiff_compact_velocity_extension_Icc_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      ((Icc a b ×ˢ univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      W (t, e (t, x)) = deriv (fun s => e (s, x)) t) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ t ∈ Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t) ∧
      X =ᶠ[𝓝ˢ C] W := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW⟩ :=
    exists_contDiff_compact_velocity_extension_eq_nhds he hf
      (isCompact_Icc.prod isCompact_univ) hO hKO hU hC hCU hW
      (fun q hq => hWe q.1 hq.1 q.2)
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, mem_univ x⟩, hXW⟩

end

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
  [CompactSpace M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {e : ℝ × M → V}

theorem exists_contDiff_compact_velocity_extension_halfspace_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {K : Set (ℝ × M)} (hK : IsCompact K)
    {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      (K ∩ tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ q ∈ K, (q.1, e q) ∈ U → W (q.1, e q) = deriv (fun s => e (s, q.2)) q.1) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      EqOn (fun q => X (q.1, e q)) (fun q => deriv (fun s => e (s, q.2)) q.1) K ∧
      X =ᶠ[𝓝ˢ C] W := by
  have hgraph := isSmoothEmbedding_parametric_graph_halfspace he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞
      (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1) :=
    fun p => DifferentialGeometry.timeDeriv_smoothAt (he p) (by simp)
  exact hgraph.exists_contDiff_compact_extension_prod_halfspace_eq_nhds
    hv hK hO hKO hU hC hCU hW hWe

theorem exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds
    (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O U C : Set (ℝ × V)} (hO : IsOpen O)
    (hKO : (fun q : ℝ × M => (q.1, e q)) ''
      ((Icc a b ×ˢ univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U ∩ O)
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      W (t, e (t, x)) = deriv (fun s => e (s, x)) t) :
    ∃ X : ℝ × V → V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧ tsupport X ⊆ O ∧
      (∀ t ∈ Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t) ∧
      X =ᶠ[𝓝ˢ C] W := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW⟩ :=
    exists_contDiff_compact_velocity_extension_halfspace_eq_nhds he hf
      (isCompact_Icc.prod isCompact_univ) hO hKO hU hC hCU hW
      (fun q hq => hWe q.1 hq.1 q.2)
  exact ⟨X, hX, hXc, hXO, fun t ht x => hXe (x := (t, x)) ⟨ht, mem_univ x⟩, hXW⟩

end Manifold
