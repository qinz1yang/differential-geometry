import DifferentialGeometry.Topology.Manifold.Cutoff.TwoDomain
import DifferentialGeometry.Topology.Manifold.ChartPatch.Interpolation

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_fixed_cutoff_eventually_chart_patch
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
    (hP : IsCompact P) (hPA : P ⊆ A)
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
        EqOn (g i) (f i) (W ∩ {x | χ x = 1}) ∧
        EqOn (g i) (e i ∘ q) (W ∩ {x | χ x = 0}) ∧
        MapsTo (g i) (W ∩ T) (e i).target ∧
        (∀ x ∈ W ∩ T,
          g i x = e i (q x + χ x • ((e i).symm (f i x) - q x))) ∧
        (∀ x ∈ W ∩ T,
          (e i).symm (g i x) = q x + χ x • ((e i).symm (f i x) - q x)) := by
  classical
  obtain ⟨χ, hχ, hχcompact, hχrange, hχA, hχT, hχP⟩ :=
    two_domain_weight_preserving_compact_core (I := I) (n := p)
        hA hT hcompact hcover hP hPA
  let Valid (i : ℕ) : Prop := ContMDiffOn I J p (f i) A ∧
    ∀ x ∈ W ∩ T ∩ A, f i x ∈ (e i).target ∧ (e i).symm (f i x) ∈ D
  let Patch (i : ℕ) (g : X → Y i) : Prop :=
    ContMDiffOn I J p g W ∧
    EqOn g (f i) (W ∩ {x | χ x = 1}) ∧
    EqOn g (e i ∘ q) (W ∩ {x | χ x = 0}) ∧
    MapsTo g (W ∩ T) (e i).target ∧
    (∀ x ∈ W ∩ T, g x = e i (q x + χ x • ((e i).symm (f i x) - q x))) ∧
    (∀ x ∈ W ∩ T, (e i).symm (g x) = q x + χ x • ((e i).symm (f i x) - q x))
  have hpatch (i : ℕ) (hi : Valid i) : ∃ g : X → Y i, Patch i g := by
    exact exists_contMDiffOn_supported_chart_interpolation hA hW hT hi.1 hq
      hχ.contMDiffOn (fun x _ => hχrange x) (fun _ hx => hχA hx.2) hχT
      (e i) (he i) (heinv i) hD (hDe i) hqD
      (fun x hx => hi.2 x ⟨hx.1, hχA hx.2⟩)
  let g (i : ℕ) : X → Y i :=
    if hi : Valid i then Classical.choose (hpatch i hi) else fun _ => b i
  have hgood (i : ℕ) (hi : Valid i) : Patch i (g i) := by
    dsimp only [g]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hpatch i hi)
  refine ⟨χ, g, hχ, hχcompact, hχrange, hχA, hχT, hχP, ?_, ?_⟩
  · intro i
    by_cases hi : Valid i
    · exact (hgood i hi).1
    · simpa only [g, dite_eq_right hi] using
        (contMDiffOn_const : ContMDiffOn I J p (fun _ : X => b i) W)
  · filter_upwards [hf, hfD] with i hi hiD
    exact (hgood i ⟨hi, hiD⟩).2

end DifferentialGeometry.Topology.Manifold
