import DifferentialGeometry.Topology.Manifold.ChartPatch.Sequence

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_fixed_cutoff_eventually_chart_patch_preserving_germs
    {E F H G X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace X] [ChartedSpace H X] [T2Space X]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {p : ℕ∞} [IsManifold I p X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace G (Y i)]
    {A W T P : Set X}
    (hA : IsOpen A) (hW : IsOpen W) (hT : IsOpen T)
    (hcompact : IsCompact (closure W)) (hcover : closure W ⊆ A ∪ T)
    (hP : IsCompact P) (hPA : P ⊆ A) (hPW : P ⊆ W)
    (f : ∀ i, X → Y i) (b : ∀ i, Y i) (q : X → F)
    (hf : ∀ᶠ i in atTop, ContMDiffOn I J p (f i) A)
    (hq : ContMDiffOn I 𝓘(ℝ, F) p q (W ∩ T))
    (e : ∀ i, OpenPartialHomeomorph F (Y i))
    (he : ∀ i, ContMDiffOn 𝓘(ℝ, F) J p (e i) (e i).source)
    (heinv : ∀ i, ContMDiffOn J 𝓘(ℝ, F) p (e i).symm (e i).target)
    {D : Set F} (hD : Convex ℝ D) (hDe : ∀ i, D ⊆ (e i).source)
    (hqD : MapsTo q (W ∩ T) D)
    (hfD : ∀ᶠ i in atTop, ∀ x ∈ W ∩ T ∩ A,
      f i x ∈ (e i).target ∧ (e i).symm (f i x) ∈ D) :
    ∃ χ : X → ℝ, ∃ g : ∀ i, X → Y i,
      ContMDiff I 𝓘(ℝ, ℝ) p χ ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ A ∧
      W ∩ tsupport (fun x => 1 - χ x) ⊆ T ∧
      χ =ᶠ[𝓝ˢ P] 1 ∧ (∀ i, ContMDiffOn I J p (g i) W) ∧
      ∀ᶠ i in atTop,
        EqOn (g i) (f i) (W \ T) ∧
        (∀ x ∈ P, g i =ᶠ[𝓝 x] f i) ∧
        EqOn (g i) (f i) (W ∩ {x | χ x = 1}) ∧
        EqOn (g i) (e i ∘ q) (W ∩ {x | χ x = 0}) ∧
        MapsTo (g i) (W ∩ T) (e i).target ∧
        (∀ x ∈ W ∩ T,
          g i x = e i (q x + χ x • ((e i).symm (f i x) - q x))) ∧
        (∀ x ∈ W ∩ T,
          (e i).symm (g i x) = q x + χ x • ((e i).symm (f i x) - q x)) := by
  classical
  obtain ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, hg, htail⟩ :=
    exists_fixed_cutoff_eventually_chart_patch hA hW hT hcompact hcover hP hPA
      f b q hf hq e he heinv hD hDe hqD hfD
  refine ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, hg, ?_⟩
  filter_upwards [htail] with i hi
  refine ⟨?_, ?_, hi⟩
  · intro x hx
    have hχx : χ x = 1 := by
      by_contra hne
      have hsupport : x ∈ Function.support (fun y => 1 - χ y) := by
        change 1 - χ x ≠ 0
        exact sub_ne_zero.mpr (Ne.symm hne)
      exact hx.2 (hχT ⟨hx.1, subset_tsupport _ hsupport⟩)
    exact hi.1 ⟨hx.1, hχx⟩
  · intro x hx
    have hnear : χ =ᶠ[𝓝 x] 1 := hχP.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hnear, hW.mem_nhds (hPW hx)] with y hχy hy
    exact hi.1 ⟨hy, hχy⟩

end DifferentialGeometry.Topology.Manifold
