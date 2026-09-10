import DifferentialGeometry.Topology.Covering.EmbeddedLift

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology

theorem exists_smooth_boundary_lifts
    {A S W M N E F H H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace S] [ChartedSpace H S] [TopologicalSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} [IsManifold J ∞ N]
    {p : N → M} (hp : IsLocalDiffeomorph J J ∞ p)
    {ι : W → M} (hemb : IsEmbedding ι) (g : C(W, N)) (hpg : ∀ w, p (g w) = ι w)
    (e : A → S → M) (he : ∀ i, IsSmoothEmbedding I J ∞ (e i))
    {B : Set W} (hB : ι '' B = ⋃ i, range (e i)) :
    ∃ f : A → S → N, (∀ i, IsSmoothEmbedding I J ∞ (f i)) ∧
      (∀ i x, p (f i x) = e i x) ∧ g '' B = ⋃ i, range (f i) ∧
      ∀ i j, Disjoint (range (e i)) (range (e j)) → Disjoint (range (f i)) (range (f j)) := by
  have hsub (i : A) : range (e i) ⊆ range ι := by
    intro x hx
    exact image_subset_range _ _ (hB ▸ mem_iUnion.mpr ⟨i, hx⟩)
  have hfac (i : A) : ∃ η : C(S, W), ∀ x, ι (η x) = e i x :=
    exists_continuousMap_factor_of_range_subset hemb ⟨e i, (he i).contMDiff.continuous⟩ (hsub i)
  choose η hη using hfac
  let f : A → S → N := fun i ↦ g ∘ η i
  have hpf (i : A) (x : S) : p (f i x) = e i x := (hpg _).trans (hη i x)
  refine ⟨f, ?_, hpf, ?_, ?_⟩
  · intro i
    exact isSmoothEmbedding_of_lift_through_localDiffeomorph hp (he i)
      (g.continuous.comp (η i).continuous) (hpf i)
  · have hBW : B = ⋃ i, range (η i) := by
      apply hemb.injective.image_injective
      rw [image_iUnion]
      simp_rw [← range_comp, show ∀ i, ι ∘ η i = e i from fun i ↦ funext (hη i)]
      exact hB
    rw [hBW, image_iUnion]
    simp_rw [← range_comp]
    rfl
  · intro i j hd
    rw [Set.disjoint_left]
    rintro y ⟨a, ha⟩ ⟨b, hb⟩
    have hei : e i a = e j b := (hpf i a).symm.trans
      ((congrArg p (ha.trans hb.symm)).trans (hpf j b))
    exact hd.le_bot ⟨mem_range_self a, ⟨b, hei.symm⟩⟩

private theorem bool_iUnion {X : Type*} (f : Bool → Set X) : (⋃ b, f b) = f false ∪ f true := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨false, hx⟩
    · exact mem_iUnion.mpr ⟨true, hx⟩

theorem exists_two_smooth_boundary_lifts
    {S W M N E F H H' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace S] [ChartedSpace H S] [TopologicalSpace W]
    [TopologicalSpace M] [ChartedSpace H' M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} [IsManifold J ∞ N]
    {p : N → M} (hp : IsLocalDiffeomorph J J ∞ p)
    {ι : W → M} (hemb : IsEmbedding ι) (g : C(W, N)) (hpg : ∀ w, p (g w) = ι w)
    (e₀ e₁ : S → M) (he₀ : IsSmoothEmbedding I J ∞ e₀) (he₁ : IsSmoothEmbedding I J ∞ e₁)
    {B : Set W} (hB : ι '' B = range e₀ ∪ range e₁) (hd : Disjoint (range e₀) (range e₁)) :
    ∃ f₀ f₁ : S → N, IsSmoothEmbedding I J ∞ f₀ ∧ IsSmoothEmbedding I J ∞ f₁ ∧
      (∀ x, p (f₀ x) = e₀ x) ∧ (∀ x, p (f₁ x) = e₁ x) ∧
      g '' B = range f₀ ∪ range f₁ ∧ Disjoint (range f₀) (range f₁) := by
  let e : Bool → S → M := Bool.rec e₀ e₁
  have he : ∀ b, IsSmoothEmbedding I J ∞ (e b) := by
    intro b
    cases b
    · exact he₀
    · exact he₁
  have hB' : ι '' B = ⋃ b, range (e b) := by
    rw [bool_iUnion]
    exact hB
  obtain ⟨f, hf, hpf, hfB, hfd⟩ := exists_smooth_boundary_lifts hp hemb g hpg e he hB'
  exact ⟨f false, f true, hf false, hf true, hpf false, hpf true,
    hfB.trans (bool_iUnion _), hfd false true hd⟩

end Poincare.Topology
