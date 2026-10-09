import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# A bundle with compact fibre over an arc is trivial (lane S-BCF03; annulus kernel of BCF03 G7)

Kernel of `annulus_param` of `EmbeddedFacePartition_BCF`: if a map `π : Wt → Z` has, over a
neighbourhood (in `[0, 1]`) of every point of an injective arc `a : [0, 1] → Z`, a continuous
injective whole-fibre parametrization `τ : Q × U → Wt` of `P ∩ π⁻¹(a U)` with
`π (τ (z, s)) = a s`, and `Q` is compact and `Wt` Hausdorff, then there is ONE such
parametrization `E : Q × [0, 1] → Wt` of `P ∩ π⁻¹(a [0, 1])`.

Route: a Lebesgue subdivision `0 = s₀ < ⋯ < s_M = 1` of `[0, 1]` into windows inside single local
trivializations; the pieces are glued one window at a time at a single point `s_k`, adjusting the
next trivialization by the fibre homeomorphism `ρ = τ(·, s_k)⁻¹ ∘ E(·, s_k)` of `Q` (a bundle over
an interval needs no path in the structure group).

* `image_slice_BCF`, `image_restrict_BCF`: slices and sub-windows of a whole-fibre parametrization;
* `glue_step_BCF`: one gluing step;
* **`exists_bundle_trivialization_over_arc_BCF`**: the kernel.
-/

set_option autoImplicit false

open Set Function Topology Metric

namespace DifferentialGeometry.Topology

section Arc

variable {Q Wt Z : Type*} {π : Wt → Z} {a : ℝ → Z} {P : Set Wt}

/-- The slice `{b}` of a whole-fibre parametrization over `A`: the whole fibre over `a b`. -/
theorem image_slice_BCF {A : Set ℝ} {F : Q × ℝ → Wt} (ha : InjOn a (Icc 0 1)) (hA : A ⊆ Icc 0 1)
    (hFπ : ∀ z, ∀ s ∈ A, π (F (z, s)) = a s)
    (hFim : F '' (univ ×ˢ A) = P ∩ π ⁻¹' (a '' A)) {b : ℝ} (hb : b ∈ A) :
    F '' (univ ×ˢ {b}) = P ∩ π ⁻¹' {a b} := by
  ext p
  constructor
  · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
    have hsb : s = b := hs
    subst hsb
    have hmem : F (z, s) ∈ F '' (univ ×ˢ A) := ⟨(z, s), ⟨mem_univ _, hb⟩, rfl⟩
    rw [hFim] at hmem
    exact ⟨hmem.1, hFπ z s hb⟩
  · rintro ⟨hpP, hpπ⟩
    have hp : p ∈ F '' (univ ×ˢ A) := by
      rw [hFim]
      exact ⟨hpP, b, hb, hpπ.symm⟩
    obtain ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩ := hp
    have hsb : a s = a b := by
      have h1 : π (F (z, s)) = a s := hFπ z s hs
      have h2 : π (F (z, s)) = a b := hpπ
      rw [← h1, h2]
    have : s = b := ha (hA hs) (hA hb) hsb
    exact ⟨(z, s), ⟨mem_univ _, this⟩, rfl⟩

/-- A sub-window `S ⊆ A` of a whole-fibre parametrization over `A` parametrizes the fibres over
`a S`. -/
theorem image_restrict_BCF {A S : Set ℝ} {F : Q × ℝ → Wt} (ha : InjOn a (Icc 0 1))
    (hA : A ⊆ Icc 0 1) (hS : S ⊆ A) (hFπ : ∀ z, ∀ s ∈ A, π (F (z, s)) = a s)
    (hFim : F '' (univ ×ˢ A) = P ∩ π ⁻¹' (a '' A)) :
    F '' (univ ×ˢ S) = P ∩ π ⁻¹' (a '' S) := by
  ext p
  constructor
  · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
    have hmem : F (z, s) ∈ F '' (univ ×ˢ A) := ⟨(z, s), ⟨mem_univ _, hS hs⟩, rfl⟩
    rw [hFim] at hmem
    exact ⟨hmem.1, s, hs, (hFπ z s (hS hs)).symm⟩
  · rintro ⟨hpP, s', hs', hpπ⟩
    have hp : p ∈ F '' (univ ×ˢ A) := by
      rw [hFim]
      exact ⟨hpP, s', hS hs', hpπ⟩
    obtain ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩ := hp
    have hsb : a s = a s' := by
      have h1 : π (F (z, s)) = a s := hFπ z s hs
      have h2 : π (F (z, s)) = a s' := hpπ.symm
      rw [← h1, h2]
    have : s = s' := ha (hA hs) (hA (hS hs')) hsb
    exact ⟨(z, s), ⟨mem_univ _, this ▸ hs'⟩, rfl⟩

variable [TopologicalSpace Q] [TopologicalSpace Wt] [CompactSpace Q] [Nonempty Q] [T2Space Wt]

/-- **One gluing step.** A whole-fibre parametrization `E` over `[0, b]` and a local one `τ` over a
window `U ⊇ [b, c]` give a whole-fibre parametrization over `[0, c]`. -/
theorem glue_step_BCF (ha : InjOn a (Icc 0 1)) {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1)
    {E : Q × ℝ → Wt} (hEc : ContinuousOn E (univ ×ˢ Icc 0 b)) (hEi : InjOn E (univ ×ˢ Icc 0 b))
    (hEπ : ∀ z, ∀ s ∈ Icc (0 : ℝ) b, π (E (z, s)) = a s)
    (hEim : E '' (univ ×ˢ Icc 0 b) = P ∩ π ⁻¹' (a '' Icc 0 b))
    {U : Set ℝ} {τ : Q × ℝ → Wt} (hIU : Icc b c ⊆ U)
    (hτc : ContinuousOn τ (univ ×ˢ (U ∩ Icc 0 1))) (hτi : InjOn τ (univ ×ˢ (U ∩ Icc 0 1)))
    (hτπ : ∀ z, ∀ s ∈ U ∩ Icc (0 : ℝ) 1, π (τ (z, s)) = a s)
    (hτim : τ '' (univ ×ˢ (U ∩ Icc 0 1)) = P ∩ π ⁻¹' (a '' (U ∩ Icc 0 1))) :
    ∃ E' : Q × ℝ → Wt, ContinuousOn E' (univ ×ˢ Icc 0 c) ∧ InjOn E' (univ ×ˢ Icc 0 c) ∧
      (∀ z, ∀ s ∈ Icc (0 : ℝ) c, π (E' (z, s)) = a s) ∧
      E' '' (univ ×ˢ Icc 0 c) = P ∩ π ⁻¹' (a '' Icc 0 c) := by
  classical
  have hbI : b ∈ U ∩ Icc (0 : ℝ) 1 := ⟨hIU ⟨le_rfl, hbc⟩, hb, hbc.trans hc⟩
  have hIcc : Icc b c ⊆ U ∩ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨hIU hs, hb.trans hs.1, hs.2.trans hc⟩
  -- the two slices over `a b`
  have hEb : E '' (univ ×ˢ {b}) = P ∩ π ⁻¹' {a b} :=
    image_slice_BCF ha (fun s hs => ⟨hs.1, hs.2.trans (hbc.trans hc)⟩) hEπ hEim ⟨hb, le_rfl⟩
  have hτb : τ '' (univ ×ˢ {b}) = P ∩ π ⁻¹' {a b} :=
    image_slice_BCF ha inter_subset_right hτπ hτim hbI
  set g : Q → Wt := fun z => E (z, b) with hg
  set h : Q → Wt := fun z => τ (z, b) with hh
  have hgc : Continuous g :=
    (hEc.comp_continuous (continuous_id.prodMk continuous_const)
      (fun z => ⟨mem_univ _, hb, le_rfl⟩) : Continuous fun z => E (z, b))
  have hhc : Continuous h :=
    (hτc.comp_continuous (continuous_id.prodMk continuous_const)
      (fun z => ⟨mem_univ _, hbI⟩) : Continuous fun z => τ (z, b))
  have hgi : Injective g := fun z z' hz =>
    (Prod.mk.inj (hEi (x₁ := (z, b)) (x₂ := (z', b)) ⟨mem_univ _, hb, le_rfl⟩
      ⟨mem_univ _, hb, le_rfl⟩ hz)).1
  have hhi : Injective h := fun z z' hz =>
    (Prod.mk.inj (hτi (x₁ := (z, b)) (x₂ := (z', b)) ⟨mem_univ _, hbI⟩
      ⟨mem_univ _, hbI⟩ hz)).1
  have hrg : range g = P ∩ π ⁻¹' {a b} := by
    rw [← hEb]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(z, b), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
      have hsb : s = b := hs
      subst hsb
      exact ⟨z, rfl⟩
  have hrh : range h = P ∩ π ⁻¹' {a b} := by
    rw [← hτb]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(z, b), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
      have hsb : s = b := hs
      subst hsb
      exact ⟨z, rfl⟩
  have hhemb : IsEmbedding h := (hhc.isClosedEmbedding hhi).isEmbedding
  -- the fibre homeomorphism `ρ = h⁻¹ ∘ g`
  have hgr : ∀ z, g z ∈ range h := fun z => by rw [hrh, ← hrg]; exact mem_range_self z
  set ρ : Q → Q := fun z => Function.invFun h (g z) with hρ
  have hρh : ∀ z, h (ρ z) = g z := fun z => Function.invFun_eq (hgr z)
  have hρc : Continuous ρ := by
    rw [hhemb.isInducing.continuous_iff]
    have : (h ∘ ρ) = g := funext hρh
    rw [this]
    exact hgc
  have hρi : Injective ρ := fun z z' hz => hgi (by rw [← hρh z, ← hρh z', hz])
  have hρs : Surjective ρ := fun z' => by
    have : h z' ∈ range g := by rw [hrg, ← hrh]; exact mem_range_self z'
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hhi (by rw [hρh z, hz])⟩
  -- the glued map
  let E' : Q × ℝ → Wt := fun q => if q.2 ≤ b then E q else τ (ρ q.1, q.2)
  have hsplit : (univ : Set Q) ×ˢ Icc (0 : ℝ) c =
      (univ ×ˢ Icc 0 b) ∪ (univ ×ˢ Icc b c) := by
    ext ⟨z, s⟩
    simp only [mem_prod, mem_univ, true_and, mem_union, mem_Icc]
    constructor
    · rintro ⟨h0, h1⟩
      by_cases hs : s ≤ b
      · exact Or.inl ⟨h0, hs⟩
      · exact Or.inr ⟨(not_le.mp hs).le, h1⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · exact ⟨h0, h1.trans hbc⟩
      · exact ⟨hb.trans h0, h1⟩
  have hcl1 : IsClosed ((univ : Set Q) ×ˢ Icc (0 : ℝ) b) := isClosed_univ.prod isClosed_Icc
  have hcl2 : IsClosed ((univ : Set Q) ×ˢ Icc b c) := isClosed_univ.prod isClosed_Icc
  have hE'1 : ContinuousOn E' (univ ×ˢ Icc 0 b) := by
    refine hEc.congr fun q hq => ?_
    have : q.2 ≤ b := hq.2.2
    simp [E', this]
  have hτρ : ContinuousOn (fun q : Q × ℝ => τ (ρ q.1, q.2)) (univ ×ˢ Icc b c) := by
    refine hτc.comp ((hρc.comp continuous_fst).prodMk continuous_snd).continuousOn ?_
    rintro ⟨z, s⟩ ⟨-, hs⟩
    exact ⟨mem_univ _, hIcc hs⟩
  have hE'2 : ContinuousOn E' (univ ×ˢ Icc b c) := by
    refine hτρ.congr fun q hq => ?_
    by_cases hs : q.2 ≤ b
    · have hsb : q.2 = b := le_antisymm hs hq.2.1
      have hq2 : q = (q.1, b) := Prod.ext rfl hsb
      simp only [E', hs, ↓reduceIte]
      rw [hq2]
      simp only
      exact (hρh q.1).symm
    · simp [E', hs]
  refine ⟨E', ?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    exact hE'1.union_of_isClosed hE'2 hcl1 hcl2
  · rintro ⟨z, s⟩ ⟨-, hs0, hsc⟩ ⟨z', s'⟩ ⟨-, hs0', hsc'⟩ heq
    by_cases hs : s ≤ b <;> by_cases hs' : s' ≤ b
    · simp only [E', hs, hs', ↓reduceIte] at heq
      exact hEi ⟨mem_univ _, hs0, hs⟩ ⟨mem_univ _, hs0', hs'⟩ heq
    · simp only [E', hs, hs', ↓reduceIte] at heq
      have h1 := hEπ z s ⟨hs0, hs⟩
      have h2 := hτπ (ρ z') s' (hIcc ⟨(not_le.mp hs').le, hsc'⟩)
      have h3 : a s = a s' := by rw [← h1, ← h2, heq]
      have h4 : s = s' := ha ⟨hs0, hsc.trans hc⟩ ⟨hs0', hsc'.trans hc⟩ h3
      exact absurd (h4 ▸ hs) hs'
    · simp only [E', hs, hs', ↓reduceIte] at heq
      have h1 := hτπ (ρ z) s (hIcc ⟨(not_le.mp hs).le, hsc⟩)
      have h2 := hEπ z' s' ⟨hs0', hs'⟩
      have h3 : a s = a s' := by rw [← h1, heq, h2]
      have h4 : s = s' := ha ⟨hs0, hsc.trans hc⟩ ⟨hs0', hsc'.trans hc⟩ h3
      exact absurd (h4 ▸ hs') hs
    · simp only [E', hs, hs', ↓reduceIte] at heq
      have h5 := hτi (x₁ := (ρ z, s)) (x₂ := (ρ z', s'))
        ⟨mem_univ _, hIcc ⟨(not_le.mp hs).le, hsc⟩⟩
        ⟨mem_univ _, hIcc ⟨(not_le.mp hs').le, hsc'⟩⟩ heq
      obtain ⟨h1, h2⟩ := Prod.mk.inj h5
      exact Prod.ext (hρi h1) h2
  · rintro z s ⟨hs0, hsc⟩
    by_cases hs : s ≤ b
    · simp only [E', hs, ↓reduceIte]
      exact hEπ z s ⟨hs0, hs⟩
    · simp only [E', hs, ↓reduceIte]
      exact hτπ (ρ z) s (hIcc ⟨(not_le.mp hs).le, hsc⟩)
  · ext p
    constructor
    · rintro ⟨⟨z, s⟩, ⟨-, hs0, hsc⟩, rfl⟩
      by_cases hs : s ≤ b
      · simp only [E', hs, ↓reduceIte]
        have hmem : E (z, s) ∈ E '' (univ ×ˢ Icc 0 b) := ⟨(z, s), ⟨mem_univ _, hs0, hs⟩, rfl⟩
        rw [hEim] at hmem
        exact ⟨hmem.1, s, ⟨hs0, hsc⟩, (hEπ z s ⟨hs0, hs⟩).symm⟩
      · simp only [E', hs, ↓reduceIte]
        have hsI := hIcc ⟨(not_le.mp hs).le, hsc⟩
        have hmem : τ (ρ z, s) ∈ τ '' (univ ×ˢ (U ∩ Icc 0 1)) := ⟨(ρ z, s), ⟨mem_univ _, hsI⟩, rfl⟩
        rw [hτim] at hmem
        exact ⟨hmem.1, s, ⟨hs0, hsc⟩, (hτπ (ρ z) s hsI).symm⟩
    · rintro ⟨hpP, s', ⟨hs0', hsc'⟩, hpπ⟩
      by_cases hs : s' ≤ b
      · have hp : p ∈ E '' (univ ×ˢ Icc 0 b) := by
          rw [hEim]
          exact ⟨hpP, s', ⟨hs0', hs⟩, hpπ⟩
        obtain ⟨⟨z, s⟩, ⟨-, hs0, hsb⟩, rfl⟩ := hp
        exact ⟨(z, s), ⟨mem_univ _, hs0, hsb.trans hbc⟩, by simp [E', hsb]⟩
      · have hsI := hIcc ⟨(not_le.mp hs).le, hsc'⟩
        have hp : p ∈ τ '' (univ ×ˢ (U ∩ Icc 0 1)) := by
          rw [hτim]
          exact ⟨hpP, s', hsI, hpπ⟩
        obtain ⟨⟨z', s⟩, ⟨-, hsU⟩, rfl⟩ := hp
        have hsa : a s = a s' := by rw [← hτπ z' s hsU, hpπ]
        have hss : s = s' := ha hsU.2 ⟨hs0', hsc'.trans hc⟩ hsa
        subst hss
        obtain ⟨z, rfl⟩ := hρs z'
        exact ⟨(z, s), ⟨mem_univ _, hs0', hsc'⟩, by simp [E', hs]⟩

/-- **A bundle with compact fibre over an injective arc is trivial** (the kernel of
`annulus_param`): see the module docstring. -/
theorem exists_bundle_trivialization_over_arc_BCF (ha : InjOn a (Icc 0 1))
    (hloc : ∀ t ∈ Icc (0 : ℝ) 1, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ ∃ τ : Q × ℝ → Wt,
      ContinuousOn τ (univ ×ˢ (U ∩ Icc 0 1)) ∧ InjOn τ (univ ×ˢ (U ∩ Icc 0 1)) ∧
      (∀ z, ∀ s ∈ U ∩ Icc (0 : ℝ) 1, π (τ (z, s)) = a s) ∧
      τ '' (univ ×ˢ (U ∩ Icc 0 1)) = P ∩ π ⁻¹' (a '' (U ∩ Icc 0 1))) :
    ∃ E : Q × ℝ → Wt, ContinuousOn E (univ ×ˢ Icc 0 1) ∧ InjOn E (univ ×ˢ Icc 0 1) ∧
      (∀ z, ∀ s ∈ Icc (0 : ℝ) 1, π (E (z, s)) = a s) ∧
      E '' (univ ×ˢ Icc 0 1) = P ∩ π ⁻¹' (a '' Icc 0 1) := by
  have hloc' : ∀ t : Icc (0 : ℝ) 1, ∃ U : Set ℝ, IsOpen U ∧ (t : ℝ) ∈ U ∧ ∃ τ : Q × ℝ → Wt,
      ContinuousOn τ (univ ×ˢ (U ∩ Icc 0 1)) ∧ InjOn τ (univ ×ˢ (U ∩ Icc 0 1)) ∧
      (∀ z, ∀ s ∈ U ∩ Icc (0 : ℝ) 1, π (τ (z, s)) = a s) ∧
      τ '' (univ ×ˢ (U ∩ Icc 0 1)) = P ∩ π ⁻¹' (a '' (U ∩ Icc 0 1)) := fun t => hloc t.1 t.2
  choose U hUo htU τ hτc hτi hτπ hτim using hloc'
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) (c := fun t : Icc (0 : ℝ) 1 => U t) hUo
    (fun s hs => mem_iUnion.mpr ⟨⟨s, hs⟩, htU ⟨s, hs⟩⟩)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  have hMpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have key : ∀ k : ℕ, k ≤ N + 1 → ∃ E : Q × ℝ → Wt,
      ContinuousOn E (univ ×ˢ Icc 0 ((k : ℝ) / (N + 1))) ∧
      InjOn E (univ ×ˢ Icc 0 ((k : ℝ) / (N + 1))) ∧
      (∀ z, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) / (N + 1)), π (E (z, s)) = a s) ∧
      E '' (univ ×ˢ Icc 0 ((k : ℝ) / (N + 1))) =
        P ∩ π ⁻¹' (a '' Icc 0 ((k : ℝ) / (N + 1))) := by
    intro k
    induction k with
    | zero =>
      intro _
      let t₀ : Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.2 zero_le_one⟩
      have hI : Icc (0 : ℝ) (((0 : ℕ) : ℝ) / (N + 1)) ⊆ U t₀ ∩ Icc 0 1 := by
        intro s hs
        have hs0 : s = 0 := by
          have h2 := hs.2
          simp only [Nat.cast_zero, zero_div] at h2
          exact le_antisymm h2 hs.1
        subst hs0
        exact ⟨htU t₀, le_rfl, zero_le_one⟩
      refine ⟨τ t₀, ?_, ?_, ?_, ?_⟩
      · exact (hτc t₀).mono (prod_mono subset_rfl hI)
      · exact (hτi t₀).mono (prod_mono subset_rfl hI)
      · exact fun z s hs => hτπ t₀ z s (hI hs)
      · exact image_restrict_BCF ha inter_subset_right hI (hτπ t₀) (hτim t₀)
    | succ k ih =>
      intro hk
      obtain ⟨E, hEc, hEi, hEπ, hEim⟩ := ih (by omega)
      set b : ℝ := (k : ℝ) / (N + 1) with hb
      set c : ℝ := ((k + 1 : ℕ) : ℝ) / (N + 1) with hc
      have hb0 : 0 ≤ b := by positivity
      have hbc : b ≤ c := by
        rw [hb, hc]
        exact div_le_div_of_nonneg_right (by push_cast; linarith) hMpos.le
      have hc1 : c ≤ 1 := by
        rw [hc, div_le_one hMpos]
        have : ((k + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hk
        push_cast at this ⊢
        linarith
      have hcb : c - b = 1 / ((N : ℝ) + 1) := by
        rw [hb, hc]
        push_cast
        field_simp
        ring
      obtain ⟨t, ht⟩ := hball b ⟨hb0, hbc.trans hc1⟩
      have hIU : Icc b c ⊆ U t := fun s hs => ht (by
        rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
        have : s - b ≤ c - b := by linarith [hs.2]
        rw [hcb] at this
        linarith)
      exact glue_step_BCF ha hb0 hbc hc1 hEc hEi hEπ hEim hIU (hτc t) (hτi t) (hτπ t) (hτim t)
  obtain ⟨E, h1, h2, h3, h4⟩ := key (N + 1) le_rfl
  have hone : (((N + 1 : ℕ) : ℝ)) / ((N : ℝ) + 1) = 1 := by
    push_cast
    exact div_self hMpos.ne'
  rw [hone] at h1 h2 h3 h4
  exact ⟨E, h1, h2, h3, h4⟩

end Arc

end DifferentialGeometry.Topology
