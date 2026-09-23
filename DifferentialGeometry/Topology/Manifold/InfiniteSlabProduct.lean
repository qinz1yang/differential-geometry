import DifferentialGeometry.Topology.Manifold.CylinderCollar.InfiniteSlabs
import DifferentialGeometry.Topology.Manifold.ProductChartProper

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactlyCoherentSpace M]

theorem exists_proper_smooth_product_of_slabs
    (P : ℕ → PartialDiffeomorph IC I (S2 × ℝ) M ∞)
    (η : ℕ → S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n z, P (n + 1) (z, 0) = P n (η n z, 1))
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hescape : ∀ K : Set M, IsCompact K → ∀ᶠ n in atTop,
      Disjoint (P n '' (univ ×ˢ Icc (0 : ℝ) 1)) K) :
    ∃ Θ : S2 × ℝ → M,
      ContMDiffOn IC I ∞ Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      InjOn Θ (univ ×ˢ Ici (0 : ℝ)) ∧
      IsProperMap (fun z : S2 × ℝ≥0 => Θ (z.1, z.2.val)) ∧
      (let U : TopologicalSpace.Opens (S2 × ℝ) :=
        ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
       IsSmoothEmbedding IC I ∞ (fun z : U => Θ z)) ∧
      Θ '' (univ ×ˢ Ici (0 : ℝ)) = ⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z, Θ (z, 0) = P 0 (z, 0)) ∧
      ∀ n : ℕ, Θ '' (univ ×ˢ Icc (n : ℝ) ((n : ℝ) + 1)) =
        P n '' (univ ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨Q, hQ0, hQs, hQi, hQu, hQseam⟩ :=
    exists_compatible_slab_parametrizations P η hsource hseam hadjacent
  have hQface (n) : Q n '' (univ ×ˢ ({1} : Set ℝ)) =
      P n '' (univ ×ˢ ({1} : Set ℝ)) := by
    obtain ⟨μ, hμ⟩ := hQu n
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩
      have : t = 1 := ht
      subst t
      exact ⟨(μ z, 1), ⟨mem_univ _, rfl⟩, (hμ z).symm.trans hzx⟩
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩
      have : t = 1 := ht
      subst t
      refine ⟨(μ.symm z, 1), ⟨mem_univ _, rfl⟩, (hμ _).trans ?_⟩
      exact (congrArg (fun q => P n (q, 1))
        (show μ (μ.symm z) = z from μ.apply_symm_apply z)).trans hzx
  have hQa (n) : Q n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      Q (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = Q n '' (univ ×ˢ ({1} : Set ℝ)) := by
    rw [hQi, hQi, hQface]
    exact hadjacent n
  have hQsep (m n : ℕ) (hmn : m + 1 < n) :
      Disjoint (Q m '' (univ ×ˢ Icc (0 : ℝ) 1)) (Q n '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    rw [hQi, hQi]
    exact hseparated m n hmn
  have hQesc (K : Set M) (hK : IsCompact K) : ∀ᶠ n in atTop,
      Disjoint (Q n '' (univ ×ˢ Icc (0 : ℝ) 1)) K := by
    simpa only [hQi] using hescape K hK
  obtain ⟨hproper, _, hrange, hbase, hstrip⟩ :=
    isProperMap_product_of_compatible_slabs Q hQs hQseam hQa hQsep hQesc
  let Θ := productChartMap (fun n => Q n)
  refine ⟨Θ, contMDiffOn_productChartMap_nonnegative Q hQs hQseam,
    productChartMap_injOn Q hQs hQa hQsep, hproper,
    isSmoothEmbedding_productChartMap_interior Q hQs hQseam hQa hQsep, ?_, ?_, ?_⟩
  · have heq : Θ '' (univ ×ˢ Ici (0 : ℝ)) = range (halfCylinderProductMap (fun n => Q n)) := by
      ext x
      constructor
      · rintro ⟨⟨z, t⟩, ht, htx⟩
        exact ⟨(z, ⟨t, ht.2⟩), htx⟩
      · rintro ⟨⟨z, t⟩, htx⟩
        exact ⟨(z, t.val), ⟨mem_univ _, t.property⟩, htx⟩
    rw [heq, hrange]
    simp only [hQi]
  · intro z
    have h := hbase z
    rw [hQ0] at h
    exact h
  · intro n
    rw [← hQi n]
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ht, htx⟩
      have htt : t - (n : ℝ) ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
      have he := hstrip n z (t - n) htt
      have ht0 : 0 ≤ t := (Nat.cast_nonneg n).trans ht.2.1
      change Θ (z, (n : ℝ) + (t - n)) = Q n (z, t - n) at he
      rw [add_sub_cancel] at he
      exact ⟨(z, t - n), ⟨mem_univ _, htt⟩, he.symm.trans htx⟩
    · rintro ⟨⟨z, t⟩, ht, htx⟩
      exact ⟨(z, (n : ℝ) + t), ⟨mem_univ _, by linarith [ht.2.1], by linarith [ht.2.2]⟩,
        (hstrip n z t ht.2).trans htx⟩

end DifferentialGeometry.Topology.Manifold
