import DifferentialGeometry.Topology.Manifold.HalfClosedIntervalExtension
import DifferentialGeometry.Topology.Manifold.ProductBoundaryExtension
import DifferentialGeometry.Topology.Manifold.SmoothExtension

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {F HS S E HM M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HS] {J : ModelWithCorners ℝ F HS} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace HS S] [IsManifold J ∞ S]
  [T2Space S] [CompactSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

theorem exists_contMDiffOn_extension_prod_Ico {r w : ℝ}
    (hr : 0 ≤ r) (hrw : r < w) (c : S × Ico (0 : ℝ) w → M)
    (hc : letI := Manifold.halfClosedIntervalChartedSpace (hr.trans_lt hrw)
      ContMDiff (J.prod (𝓡∂ 1)) I ∞ c) :
    ∃ Φ : C(S × ℝ, M), ∃ N : Set (S × ℝ), IsOpen N ∧
      (univ ×ˢ Icc (0 : ℝ) r) ⊆ N ∧ ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ Φ N ∧
      ∀ (s : S) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) r),
        Φ (s, t) = c (s, ⟨t, ht.1, ht.2.trans_lt hrw⟩) := by
  let a := (r + w) / 2
  have hra : r < a := by dsimp only [a]; linarith
  have ha : 0 < a := hr.trans_lt hra
  have haw : a < w := by dsimp only [a]; linarith
  obtain ⟨g, hg, hgc⟩ := Manifold.exists_contMDiffOn_extension_prod_Icc ha.le haw c hc
  let K : Set (S × ℝ) := univ ×ˢ Icc (0 : ℝ) r
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hloc : ∀ x ∈ K, ∃ U : S × ℝ → M, ∃ V : Set (S × ℝ),
      IsOpen V ∧ x ∈ V ∧ ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ U V ∧ EqOn U g (K ∩ V) := by
    intro x hx
    by_cases ht : x.2 = 0
    · let A : Set (S × ℝ) := univ ×ˢ Iio a
      have hA : IsOpen A := isOpen_univ.prod isOpen_Iio
      have hxA : (x.1, (0 : ℝ)) ∈ A := ⟨mem_univ _, ha⟩
      have hgA : ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ g
          (A ∩ (univ ×ˢ Ici (0 : ℝ))) :=
        hg.mono (fun y hy => ⟨mem_univ _, hy.2.2, hy.1.2.le⟩)
      obtain ⟨V, hV, hxV, _, U, hU, heq⟩ :=
        exists_contMDiffOn_extension_across_product_boundary hA hxA hgA
      refine ⟨U, V, hV, ?_, hU, ?_⟩
      · exact (show x = (x.1, (0 : ℝ)) from Prod.ext rfl ht).symm ▸ hxV
      · intro y hy
        exact heq ⟨hy.2, mem_univ _, hy.1.2.1⟩
    · have htpos : 0 < x.2 := lt_of_le_of_ne hx.2.1 (Ne.symm ht)
      let V : Set (S × ℝ) := univ ×ˢ Ioo (0 : ℝ) a
      refine ⟨g, V, isOpen_univ.prod isOpen_Ioo,
        ⟨mem_univ _, htpos, hx.2.2.trans_lt hra⟩,
        hg.mono (fun y hy => ⟨mem_univ _, hy.2.1.le, hy.2.2.le⟩), ?_⟩
      exact fun _ _ => rfl
  obtain ⟨Φ, hΦ, hΦg, N, hN, hKN, hΦN⟩ :=
    exists_contMDiffOn_eqOn_of_locally_extendable (J := J.prod 𝓘(ℝ)) (I := I)
      (n := ⊤) g.continuous hK hloc
  refine ⟨⟨Φ, hΦ⟩, N, hN, hKN, hΦN, ?_⟩
  intro s t ht
  exact (hΦg ⟨mem_univ _, ht⟩).trans (hgc s t ⟨ht.1, ht.2.trans hra.le⟩)

end DifferentialGeometry.Topology
