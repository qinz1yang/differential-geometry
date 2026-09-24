import DifferentialGeometry.Topology.Morse.RegularLevel.Components

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem image_superlevel_component_level_of_no_critical_values
    {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace X]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {e : M → X × ℝ} (he : _root_.Topology.IsEmbedding e)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).2))
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact ((fun x => (e x).2) ⁻¹' Icc a b))
    (hregular : ∀ x, (e x).2 ∈ Icc a b → ¬ IsCriticalPointAt I (fun y => (e y).2) x)
    {p : M} (hp : b ≤ (e p).2) (Φ : ℝ → X → X)
    (hΦ : ∀ x, (e x).2 = a → ContinuousOn (fun t => Φ t (e x).1) (Icc a b))
    (hΦa : EqOn (Φ a) id ((fun x => (e x).1) '' {x | (e x).2 = a}))
    (hlevels : ∀ t ∈ Icc a b,
      Φ t '' ((fun x => (e x).1) '' {x | (e x).2 = a}) =
        (fun x => (e x).1) '' {x | (e x).2 = t}) :
    ∀ t ∈ Icc a b,
      Φ t '' ((fun x => (e x).1) ''
        (connectedComponentIn {x | a ≤ (e x).2} p ∩ {x | (e x).2 = a})) =
      (fun x => (e x).1) ''
        (connectedComponentIn {x | t ≤ (e x).2} p ∩ {x | (e x).2 = t}) := by
  let : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hpath (x : M) (hx : (e x).2 = a) :
      ∃ γ : Icc a b → M, Continuous γ ∧
        (∀ t, e (γ t) = (Φ t.val (e x).1, t.val)) ∧
        γ ⟨a, le_rfl, hab⟩ = x := by
    have hrange (t : Icc a b) : (Φ t.val (e x).1, t.val) ∈ range e := by
      have hm : Φ t.val (e x).1 ∈ (fun x => (e x).1) '' {x | (e x).2 = t.val} := by
        rw [← hlevels t.val t.property]
        exact ⟨(e x).1, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := hm
      exact ⟨y, Prod.ext hyeq hy⟩
    let γ : Icc a b → M := fun t => he.toHomeomorph.symm
      ⟨(Φ t.val (e x).1, t.val), hrange t⟩
    have heq (t : Icc a b) : e (γ t) = (Φ t.val (e x).1, t.val) :=
      congrArg Subtype.val (he.toHomeomorph.apply_symm_apply
        ⟨(Φ t.val (e x).1, t.val), hrange t⟩)
    refine ⟨γ, he.toHomeomorph.symm.continuous.comp
      (((continuousOn_iff_continuous_domRestrict.mp (hΦ x hx)).prodMk
        continuous_subtype_val).subtype_mk _), heq, ?_⟩
    apply he.injective
    rw [heq]
    exact Prod.ext (hΦa ⟨x, hx, rfl⟩) hx.symm
  have hpathmem (x : M) (hx : (e x).2 = a) (t : Icc a b) :
      ∃ y ∈ connectedComponentIn {x | a ≤ (e x).2} x,
        e y = (Φ t.val (e x).1, t.val) := by
    obtain ⟨γ, hγ, heq, hγa⟩ := hpath x hx
    refine ⟨γ t, ?_, heq t⟩
    apply (isPreconnected_range hγ).subset_connectedComponentIn
      (show x ∈ range γ from ⟨⟨a, le_rfl, hab⟩, hγa⟩)
    · rintro _ ⟨u, rfl⟩
      change a ≤ (e (γ u)).2
      rw [heq]
      exact u.property.1
    · exact mem_range_self t
  intro t ht
  have hnested := connectedComponentIn_superlevel_inter_eq_of_no_critical_values hf ht.1
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨hx.1, hx.2.trans ht.2⟩))
    (fun x hx => hregular x ⟨hx.1, hx.2.trans ht.2⟩) (ht.2.trans hp)
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨x, ⟨hxC, hxlevel⟩, rfl⟩, rfl⟩
    obtain ⟨y, hyC, hyeq⟩ := hpathmem x hxlevel ⟨t, ht⟩
    have hylevel : (e y).2 = t := congrArg Prod.snd hyeq
    refine ⟨y, ⟨?_, hylevel⟩, congrArg Prod.fst hyeq⟩
    rw [← hnested]
    refine ⟨?_, hylevel.ge⟩
    rw [connectedComponentIn_eq hxC]
    exact hyC
  · rintro _ ⟨y, ⟨hyC, hylevel⟩, rfl⟩
    have hymem : (e y).1 ∈ (fun x => (e x).1) '' {x | (e x).2 = t} :=
      ⟨y, hylevel, rfl⟩
    rw [← hlevels t ht] at hymem
    obtain ⟨_, ⟨x, hxlevel, rfl⟩, hxy⟩ := hymem
    obtain ⟨z, hzC, hzeq⟩ := hpathmem x hxlevel ⟨t, ht⟩
    have hzy : z = y := he.injective (hzeq.trans (Prod.ext hxy hylevel.symm))
    subst z
    refine ⟨(e x).1, ⟨x, ⟨?_, hxlevel⟩, rfl⟩, hxy⟩
    have hyCa : y ∈ connectedComponentIn {x | a ≤ (e x).2} p :=
      connectedComponentIn_mono p (fun z hz => ht.1.trans (show t ≤ (e z).2 from hz)) hyC
    rw [connectedComponentIn_eq hyCa, ← connectedComponentIn_eq hzC]
    exact mem_connectedComponentIn hxlevel.ge

end DifferentialGeometry.Topology.Morse
