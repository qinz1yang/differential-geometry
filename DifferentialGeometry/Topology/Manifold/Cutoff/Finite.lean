import DifferentialGeometry.Topology.Manifold.CompactSectionExtension

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : ℕ∞} [IsManifold I n M] [T2Space M]

private theorem bump_contMDiff {c : M} (f : SmoothBumpFunction I c) :
    ContMDiff I 𝓘(ℝ, ℝ) n f := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have hs : x ∈ (chartAt H c).source := f.tsupport_subset_chartAt_source hx
  apply ContMDiffAt.congr_of_eventuallyEq ?_ (f.eqOn_source.eventuallyEq_of_mem
    ((chartAt H c).open_source.mem_nhds hs))
  exact f.contDiffAt.contMDiffAt.comp _ (contMDiffAt_extChartAt' hs)

theorem exists_contMDiff_cutoff {K O : Set M} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ β : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) n β ∧ HasCompactSupport β ∧
      tsupport β ⊆ O ∧ (∀ x, β x ∈ Icc (0 : ℝ) 1) ∧ β =ᶠ[𝓝ˢ K] 1 := by
  classical
  obtain ⟨t, b, hb⟩ :=
    DifferentialGeometry.Topology.exists_finite_smoothBumpCovering_of_isCompact (I := I)
      hK (fun _ => O) (fun x hx => hO.mem_nhds (hKO hx))
  let β : M → ℝ := fun x => 1 - ∏ i : t, (1 - b i x)
  have hβ : ContMDiff I 𝓘(ℝ, ℝ) n β := by
    apply contMDiff_const.sub
    exact contMDiff_finsetProd fun i _ => contMDiff_const.sub (bump_contMDiff (b i))
  have hc : IsCompact (⋃ i : t, tsupport (b i)) :=
    isCompact_iUnion fun i => (b i).hasCompactSupport
  have hs : tsupport β ⊆ ⋃ i : t, tsupport (b i) := by
    apply closure_minimal ?_ hc.isClosed
    intro x hx
    by_contra hn
    have hz (i : t) : b i x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))
    exact hx (by simp [β, hz])
  refine ⟨β, hβ, hc.of_isClosed_subset (isClosed_tsupport β) hs, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    exact (hb i).2 hi
  · intro x
    have hnonneg : 0 ≤ ∏ i : t, (1 - b i x) :=
      Finset.prod_nonneg (fun i _ => sub_nonneg.mpr ((b i).le_one))
    have hle : ∏ i : t, (1 - b i x) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr ((b i).le_one))
        (fun i _ => sub_le_self _ ((b i).nonneg))
    exact ⟨sub_nonneg.mpr hle, sub_le_self _ hnonneg⟩
  · apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    filter_upwards [b.eventuallyEq_one x hx] with y hy
    have hz : ∏ i : t, (1 - b i y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (b.ind x hx)) (by rw [hy]; simp)
    simp only [β, hz, sub_zero, Pi.one_apply]

end DifferentialGeometry.Topology
