import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Cauchy

namespace DifferentialGeometry.Topology

open Set Metric Filter _root_.Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_shrinking_limit (K : ℕ → Set X) (h : ℕ → X ≃ₜ X)
    (hcompact : ∀ i, IsCompact (K i))
    (hfixed : ∀ i j, i ≤ j → ∀ x, x ∉ K i → h j x = h i x)
    (hdiam : Tendsto (fun i => diam (h i '' K i)) atTop (𝓝 0)) :
    ∃ f : C(X, X), Function.Surjective f ∧
      TendstoUniformly (fun i => (h i : X → X)) f atTop ∧
      (∀ i x, x ∉ K i → f x = h i x) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ i, K i) ∧ y ∈ ⋂ i, K i) := by
  classical
  have hinside : ∀ i j, i ≤ j → MapsTo (h j) (K i) (h i '' K i) := by
    intro i j hij x hx
    refine ⟨(h i).symm (h j x), ?_, (h i).apply_symm_apply _⟩
    by_contra hy
    have heq : h j ((h i).symm (h j x)) = h j x :=
      (hfixed i j hij _ hy).trans ((h i).apply_symm_apply _)
    apply hy
    rw [(h j).injective heq]
    exact hx
  let H : ℕ → C(X, X) := fun i => ⟨h i, (h i).continuous⟩
  let b : ℕ → ℝ := fun i => diam (h i '' K i)
  have hb : ∀ i, 0 ≤ b i := fun i => diam_nonneg
  have hbound : ∀ i j k, i ≤ j → i ≤ k → ∀ x,
      dist (h j x) (h k x) ≤ b i := by
    intro i j k hij hik x
    by_cases hx : x ∈ K i
    · exact dist_le_diam_of_mem ((hcompact i).image (h i).continuous).isBounded
        (hinside i j hij hx) (hinside i k hik hx)
    · rw [hfixed i j hij x hx, hfixed i k hik x hx, dist_self]
      exact hb i
  have hcauchy : CauchySeq H := by
    apply cauchySeq_iff_le_tendsto_0.mpr
    refine ⟨b, hb, ?_, hdiam⟩
    intro j k i hij hik
    exact (ContinuousMap.dist_le (hb i)).mpr (hbound i j k hij hik)
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpoint : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (f x)) := fun x =>
    (continuous_eval_const x).tendsto f |>.comp hf
  have herror : ∀ i x, dist (f x) (h i x) ≤ b i := by
    intro i x
    apply le_of_tendsto ((hpoint x).dist tendsto_const_nhds)
    exact eventually_atTop.mpr ⟨i, fun j hij => hbound i j i hij le_rfl x⟩
  have hlimit_fixed : ∀ i x, x ∉ K i → f x = h i x := by
    intro i x hx
    apply tendsto_nhds_unique (hpoint x)
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr
      ⟨i, fun j hij => (hfixed i j hij x hx).symm⟩)
  have hlimit_inside : ∀ i x, x ∈ K i → f x ∈ h i '' K i := by
    intro i x hx
    apply ((hcompact i).image (h i).continuous).isClosed.mem_of_tendsto (hpoint x)
    exact eventually_atTop.mpr ⟨i, fun j hij => hinside i j hij hx⟩
  have houtside_injective : ∀ x, x ∉ ⋂ i, K i → ∀ y, f x = f y → x = y := by
    intro x hx y hxy
    obtain ⟨i, hi⟩ : ∃ i, x ∉ K i := by simpa only [mem_iInter, not_forall] using hx
    by_cases hy : y ∈ K i
    · have hximage : h i x ∈ h i '' K i := by
        rw [← hlimit_fixed i x hi, hxy]
        exact hlimit_inside i y hy
      obtain ⟨z, hz, hzx⟩ := hximage
      exact False.elim (hi ((h i).injective hzx ▸ hz))
    · apply (h i).injective
      rwa [← hlimit_fixed i x hi, ← hlimit_fixed i y hy]
  have hcollapsed : ∀ x ∈ ⋂ i, K i, ∀ y ∈ ⋂ i, K i, f x = f y := by
    intro x hx y hy
    have hdist : ∀ i, dist (f x) (f y) ≤ b i := fun i =>
      dist_le_diam_of_mem ((hcompact i).image (h i).continuous).isBounded
        (hlimit_inside i x (mem_iInter.mp hx i))
        (hlimit_inside i y (mem_iInter.mp hy i))
    exact dist_le_zero.mp (ge_of_tendsto hdiam (Eventually.of_forall hdist))
  refine ⟨f, ?_, ContinuousMap.tendsto_iff_tendstoUniformly.mp hf, hlimit_fixed, ?_⟩
  · intro y
    have hy : Tendsto (fun i => f ((h i).symm y)) atTop (𝓝 y) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun i => dist_nonneg) _ hdiam
      intro i
      simpa using herror i ((h i).symm y)
    exact (isCompact_range f.continuous).isClosed.mem_of_tendsto hy
      (Eventually.of_forall fun i => mem_range_self ((h i).symm y))
  · intro x y
    constructor
    · intro hxy
      by_cases hx : x ∈ ⋂ i, K i
      · by_cases hy : y ∈ ⋂ i, K i
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inl (houtside_injective y hy x hxy.symm).symm
      · exact Or.inl (houtside_injective x hx y hxy)
    · rintro (rfl | ⟨hx, hy⟩)
      · rfl
      · exact hcollapsed x hx y hy

theorem exists_shrinking_quotient (K : ℕ → Set X) (h : ℕ → X ≃ₜ X)
    (hcompact : ∀ i, IsCompact (K i)) (hnonempty : ∀ i, (K i).Nonempty)
    (hnested : ∀ i, K (i + 1) ⊆ K i)
    (hfixed : ∀ i j, i ≤ j → ∀ x, x ∉ K i → h j x = h i x)
    (hdiam : Tendsto (fun i => diam (h i '' K i)) atTop (𝓝 0)) :
    ∃ f : C(X, X), Function.Surjective f ∧
      TendstoUniformly (fun i => (h i : X → X)) f atTop ∧
      (∃ p, f ⁻¹' {p} = ⋂ i, K i) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ i, K i) ∧ y ∈ ⋂ i, K i) := by
  obtain ⟨f, hsurj, hunif, -, hfiber⟩ :=
    exists_shrinking_limit K h hcompact hfixed hdiam
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hnested hnonempty (hcompact 0) (fun i => (hcompact i).isClosed)
  refine ⟨f, hsurj, hunif, ⟨f x, ?_⟩, hfiber⟩
  ext y
  simp only [mem_preimage, mem_singleton_iff, hfiber y x]
  exact ⟨fun h => h.elim (fun hy => hy ▸ hx) And.left,
    fun hy => Or.inr ⟨hy, hx⟩⟩

theorem exists_shrinking_quotient_of_step (K : ℕ → Set X) (h : ℕ → X ≃ₜ X)
    (hcompact : ∀ i, IsCompact (K i)) (hnonempty : ∀ i, (K i).Nonempty)
    (hnested : ∀ i, K (i + 1) ⊆ K i)
    (hstep : ∀ i x, x ∉ K i → h (i + 1) x = h i x)
    (hdiam : Tendsto (fun i => diam (h i '' K i)) atTop (𝓝 0)) :
    ∃ f : C(X, X), Function.Surjective f ∧
      TendstoUniformly (fun i => (h i : X → X)) f atTop ∧
      (∃ p, f ⁻¹' {p} = ⋂ i, K i) ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ i, K i) ∧ y ∈ ⋂ i, K i) := by
  apply exists_shrinking_quotient K h hcompact hnonempty hnested _ hdiam
  have hmono : Antitone K := antitone_nat_of_succ_le hnested
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ j hij ih =>
    intro x hx
    rw [hstep j x (fun hxj => hx (hmono hij hxj))]
    exact ih x hx

end DifferentialGeometry.Topology
