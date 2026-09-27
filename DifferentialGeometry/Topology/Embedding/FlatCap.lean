import DifferentialGeometry.Topology.Embedding.CompactReplacement
import DifferentialGeometry.Topology.Embedding.CylinderCap

open Set Metric

namespace EuclideanGeometry

theorem mem_range_flat_cap_iff
    {X E F : Type*} [NormedAddCommGroup E]
    {e g : X → F} {Ψ : E × ℝ → F} (hΨ : Function.Injective Ψ) (χ : E → X)
    {D : Set X} {U : Set (E × ℝ)} {r σ : ℝ} (hχD : χ '' closedBall (0 : E) r = D)
    (hflat : ∀ x ∈ closedBall (0 : E) r, g (χ x) = Ψ (x, 0))
    (hgfix : EqOn g e Dᶜ)
    (hret : ∀ p ∈ U,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = r ∧ 0 < σ * p.2) :
    ∀ p ∈ U,
      Ψ p ∈ range g ↔ (‖p.1‖ ≤ r ∧ p.2 = 0) ∨ (‖p.1‖ = r ∧ 0 < σ * p.2) := by
  intro p hp
  constructor
  · rintro ⟨x, hx⟩
    by_cases hxD : x ∈ D
    · obtain ⟨y, hy, rfl⟩ := hχD.symm.subset hxD
      have he : p = (y, 0) := hΨ (hx.symm.trans (hflat y hy))
      exact Or.inl ⟨by rw [he]; exact mem_closedBall_zero_iff.mp hy, by rw [he]⟩
    · exact Or.inr ((hret p hp).mp ⟨x, hxD, (hgfix hxD).symm.trans hx⟩)
  · rintro (⟨hn, ht⟩ | hh)
    · refine ⟨χ p.1, (hflat p.1 (mem_closedBall_zero_iff.mpr hn)).trans ?_⟩
      congr 1
      exact Prod.ext rfl ht.symm
    · obtain ⟨x, hx, hxp⟩ := (hret p hp).mpr hh
      exact ⟨x, (hgfix hx).trans hxp⟩

end EuclideanGeometry

namespace Topology.IsEmbedding

variable {X Y E : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E]

theorem exists_flat_cap_replacement
    {e : X → Y} (he : IsEmbedding e) {Ψ : E × ℝ → Y} (hΨ : IsEmbedding Ψ)
    (χ : OpenPartialHomeomorph E X) (hχ : closedBall (0 : E) 1 ⊆ χ.source)
    {a : ℝ} {f : X → Y} (hf : Continuous f)
    (hcap : ∀ x ∈ closedBall (0 : E) 1, f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hfix : EqOn f e (χ '' closedBall (0 : E) 1)ᶜ)
    (hdisj : Disjoint (Ψ '' (closedBall (0 : E) 1 ×ˢ {0}))
      (e '' (χ '' closedBall (0 : E) 1)ᶜ)) :
    ∃ g : X → Y, IsEmbedding g ∧
      (∀ x ∈ closedBall (0 : E) 1, g (χ x) = Ψ (x, 0)) ∧
      EqOn g e (χ '' closedBall (0 : E) 1)ᶜ ∧
      range g = Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) ∪
        e '' (χ '' closedBall (0 : E) 1)ᶜ := by
  have hχimage : χ.IsImage (closedBall (0 : E) 1) (χ '' closedBall (0 : E) 1) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (χ.injOn (hχ hy) hx hyx) ▸ hy
    · exact mem_image_of_mem χ
  have hboundary : ∀ x ∈ frontier (closedBall (0 : E) 1), Ψ (x, 0) = e (χ x) := by
    intro x hx
    have hxball := sphere_subset_closedBall (frontier_closedBall_subset_sphere hx)
    have hxfront := (hχimage.frontier (hχ hxball)).mpr hx
    have hxcompl : χ x ∈ closure (χ '' closedBall (0 : E) 1)ᶜ := by
      apply frontier_subset_closure
      rwa [frontier_compl]
    rw [← EuclideanGeometry.cylinderCap_of_norm_eq_one a
      (mem_sphere_zero_iff_norm.mp (frontier_closedBall_subset_sphere hx)), ← hcap x hxball]
    exact hfix.closure hf he.continuous hxcompl
  have himage : (fun x : E => Ψ (x, 0)) '' closedBall 0 1 =
      Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hformula, hgfix, hgrange⟩ := he.exists_replacement_of_openPartialHomeomorph χ
    (isCompact_closedBall 0 1) hχ
    (hΨ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun x _ y _ hxy => congrArg Prod.fst (hΨ.injective hxy))
    hboundary (himage.symm ▸ hdisj)
  exact ⟨g, hg, hformula, hgfix, himage ▸ hgrange⟩

theorem exists_flat_cap_replacement_of_cylinder_side
    {e : X → Y} (he : IsEmbedding e) {Ψ : E × ℝ → Y} (hΨ : IsEmbedding Ψ)
    (χ : OpenPartialHomeomorph E X) (hχ : closedBall (0 : E) 1 ⊆ χ.source)
    {a R ε σ : ℝ} (hR : 1 < R) (hε : 0 < ε) {f : X → Y} (hf : Continuous f)
    (hcap : ∀ x ∈ closedBall (0 : E) 1, f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hfix : EqOn f e (χ '' closedBall (0 : E) 1)ᶜ)
    (hside : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' (χ '' closedBall (0 : E) 1)ᶜ → 0 < σ * p.2) :
    ∃ g : X → Y, IsEmbedding g ∧
      (∀ x ∈ closedBall (0 : E) 1, g (χ x) = Ψ (x, 0)) ∧
      EqOn g e (χ '' closedBall (0 : E) 1)ᶜ ∧
      range g = Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) ∪
        e '' (χ '' closedBall (0 : E) 1)ᶜ := by
  apply he.exists_flat_cap_replacement hΨ χ hχ hf hcap hfix
  apply disjoint_left.mpr
  rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ hy
  have ht0 : t = 0 := ht
  subst t
  have hh := hside (x, 0)
    ⟨closedBall_subset_ball hR hx, neg_lt_zero.mpr hε, hε⟩ hy
  simp at hh

theorem exists_two_flat_cap_replacements
    {e : X → Y} (he : IsEmbedding e) {Ψ : E × ℝ → Y} (hΨ : IsEmbedding Ψ)
    (χ : Fin 2 → OpenPartialHomeomorph E X) {D : Fin 2 → Set X}
    {a σ : Fin 2 → ℝ} {R ε : ℝ} (hR : 1 < R) (hε : 0 < ε)
    (hcover : D 0 ∪ D 1 = univ)
    (hinter : e '' (D 0 ∩ D 1) ⊆ Ψ '' (closedBall (0 : E) 1 ×ˢ {0}))
    (hχ : ∀ i, closedBall (0 : E) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' closedBall (0 : E) 1 = D i)
    {f : Fin 2 → X → Y} (hf : ∀ i, Continuous (f i))
    (hcap : ∀ i, ∀ x ∈ closedBall (0 : E) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x))
    (hfix : ∀ i, EqOn (f i) e (D i)ᶜ)
    (hside : ∀ i, ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' (D i)ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ i * p.2) :
    ∃ g : Fin 2 → X → Y,
      (∀ i, IsEmbedding (g i) ∧
        (∀ x ∈ closedBall (0 : E) 1, g i (χ i x) = Ψ (x, 0)) ∧
        EqOn (g i) e (D i)ᶜ ∧
        (range (g i) = Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) ∪ e '' (D i)ᶜ) ∧
        ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε,
          Ψ p ∈ range (g i) ↔
            (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < σ i * p.2)) ∧
      range (g 0) ∩ range (g 1) = Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) ∧
      range (g 0) ∪ range (g 1) = range e ∪ Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) := by
  classical
  have hflat (i : Fin 2) : ∃ g : X → Y, IsEmbedding g ∧
      (∀ x ∈ closedBall (0 : E) 1, g (χ i x) = Ψ (x, 0)) ∧
      EqOn g e (D i)ᶜ ∧
      range g = Ψ '' (closedBall (0 : E) 1 ×ˢ {0}) ∪ e '' (D i)ᶜ := by
    have hfix' : EqOn (f i) e (χ i '' closedBall (0 : E) 1)ᶜ := by
      simpa only [hχD] using hfix i
    have hside' : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε,
        Ψ p ∈ e '' (χ i '' closedBall (0 : E) 1)ᶜ → 0 < σ i * p.2 := by
      intro p hp hh
      apply ((hside i p hp).mp _).2
      simpa only [hχD] using hh
    have hh := he.exists_flat_cap_replacement_of_cylinder_side hΨ (χ i) (hχ i) hR hε
      (hf i) (hcap i) hfix' hside'
    simpa only [hχD] using hh
  choose g hg using hflat
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hg i).1, (hg i).2.1, (hg i).2.2.1, (hg i).2.2.2, ?_⟩
    exact EuclideanGeometry.mem_range_flat_cap_iff hΨ.injective (χ i) (hχD i)
      (hg i).2.1 (hg i).2.2.1 (hside i)
  · ext z
    rw [(hg 0).2.2.2, (hg 1).2.2.2]
    constructor
    · rintro ⟨hz0 | hz0, hz1 | hz1⟩
      · exact hz0
      · exact hz0
      · exact hz1
      · obtain ⟨x, hx, rfl⟩ := hz0
        obtain ⟨y, hy, hye⟩ := hz1
        have hyx := he.injective hye
        subst y
        have hc : x ∈ D 0 ∪ D 1 := hcover.symm ▸ mem_univ x
        exact False.elim (hc.elim hx hy)
    · exact fun hz => ⟨Or.inl hz, Or.inl hz⟩
  · ext z
    rw [(hg 0).2.2.2, (hg 1).2.2.2]
    constructor
    · rintro ((hz | hz) | (hz | hz))
      · exact Or.inr hz
      · exact Or.inl (image_subset_range _ _ hz)
      · exact Or.inr hz
      · exact Or.inl (image_subset_range _ _ hz)
    · rintro (⟨x, rfl⟩ | hz)
      · by_cases hx0 : x ∈ D 0
        · by_cases hx1 : x ∈ D 1
          · exact Or.inl (Or.inl (hinter (mem_image_of_mem e ⟨hx0, hx1⟩)))
          · exact Or.inr (Or.inr ⟨x, hx1, rfl⟩)
        · exact Or.inl (Or.inr ⟨x, hx0, rfl⟩)
      · exact Or.inl (Or.inl hz)

end Topology.IsEmbedding
