import DifferentialGeometry.Topology.Embedding.CylinderCapChart
import DifferentialGeometry.Topology.SphereSeparation.SourceCylinderSides

open Set Metric Manifold TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

private local instance : Fact (Module.finrank ℝ Schoenflies.Plane = 1 + 1) := ⟨by simp⟩

theorem exists_cylinderCap_replacement
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {b : ClosedCell 2 → SphereTwo} (hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b)
    (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree) {ε a σ : ℝ}
    (ha : a ≠ 0) (haε : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : Opens SphereTwo)
    (C : (AddCircle (1 : ℝ) × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (q : AddCircle (1 : ℝ) → Schoenflies.Plane)
    (hwall : ∀ x ∈ closedBall (0 : Schoenflies.Plane) 1, ∀ t ∈ Ioo (-ε) ε,
      Ψ (x, t) ∈ range e ↔ ‖x‖ = 1)
    (hV : (V : Set SphereTwo) = e ⁻¹' (Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : SphereTwo) ∈ range b ↔ σ * p.2.val ≤ 0)
    (hboundary : e '' range (b ∘ cellBoundaryInclusion 2) =
      Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0})) :
    ∃ (χ : PartialDiffeomorph (𝓡 2) (𝓡 2) Schoenflies.Plane SphereTwo ∞)
      (f : SphereTwo → EuclideanThree),
      closedBall (0 : Schoenflies.Plane) 1 ⊆ χ.source ∧
      χ '' closedBall (0 : Schoenflies.Plane) 1 = range b ∧
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
      (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
        f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x)) ∧
      EqOn f e (range b)ᶜ ∧
      ∀ y ∈ range b, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ χ.symm := by
  obtain ⟨_, φ, hφsrc, _, hφ⟩ := Handle.exists_partialDiffeomorph_extension_closedCell_sphere 1 hb
  have hφb : (φ : Schoenflies.Plane → SphereTwo) ∘ Subtype.val = b := funext hφ
  have hballφ : closedBall (0 : Schoenflies.Plane) 1 ⊆ φ.source := by
    rw [hφsrc]
    exact subset_univ _
  have hφball : φ '' closedBall (0 : Schoenflies.Plane) 1 = range b := by
    rw [← range_closedCell 2, ← range_comp, hφb]
  have hφboundary : φ '' sphere (0 : Schoenflies.Plane) 1 =
      range (b ∘ cellBoundaryInclusion 2) := by
    rw [← range_cellBoundary 2, ← range_comp]
    congr 1
    exact funext fun x => hφ (cellBoundaryInclusion 2 x)
  obtain ⟨χ, hχ, hχD, hχcollar⟩ := he.exists_cylinderCap_chart Ψ ha haε hσa V C q
    hwall hV hC hside φ hballφ hφball (hφboundary ▸ hboundary)
  obtain ⟨f, hf, hmap, hfix, hnear⟩ := he.exists_cylinderCap_replacement Ψ ha haε hσa V C q
    (fun x hx t ht hh => (hwall x hx t ht).mp hh) hV hC hside χ hχ hχD hχcollar
  exact ⟨χ, f, hχ, hχD, hf, hmap, hfix, hnear⟩

private theorem cylinder_wall_iff
    {e : SphereTwo → EuclideanThree}
    {Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree} {R ε : ℝ}
    (h : Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
      sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε) (hR : 1 ≤ R) :
    ∀ x ∈ closedBall (0 : Schoenflies.Plane) 1, ∀ t ∈ Ioo (-ε) ε,
      Ψ (x, t) ∈ range e ↔ ‖x‖ = 1 := by
  intro x hx t ht
  constructor
  · intro hh
    have hp : (x, t) ∈ sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε :=
      h.subset ⟨hh, ⟨closedBall_subset_closedBall hR hx, Ioo_subset_Icc_self ht⟩⟩
    exact mem_sphere_zero_iff_norm.mp hp.1
  · intro hh
    have hp : (x, t) ∈ Ψ ⁻¹' range e ∩
        (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) :=
      h.symm.subset ⟨mem_sphere_zero_iff_norm.mpr hh, Ioo_subset_Icc_self ht⟩
    exact hp.1

private theorem retained_cylinder_side_iff
    {e : SphereTwo → EuclideanThree}
    (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree) {R ε σ : ℝ}
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
      sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε)
    (V : Opens SphereTwo)
    (C : (AddCircle (1 : ℝ) × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (q : AddCircle (1 : ℝ) → Schoenflies.Plane) {D : Set SphereTwo}
    (hV : (V : Set SphereTwo) = e ⁻¹' (Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : SphereTwo) ∈ D ↔ σ * p.2.val ≤ 0)
    (p : Schoenflies.Plane × ℝ) (hp : p ∈ ball 0 R ×ˢ Ioo (-ε) ε) :
    Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2 := by
  have hmem (y : SphereTwo) (hy : e y = Ψ p) (hn : ‖p.1‖ = 1) :
      y ∈ D ↔ σ * p.2 ≤ 0 := by
    have hyV : y ∈ V := by
      change y ∈ (V : Set SphereTwo)
      rw [hV]
      exact ⟨p, ⟨mem_sphere_zero_iff_norm.mpr hn, hp.2⟩, hy.symm⟩
    let z := C.symm ⟨y, hyV⟩
    have hz : (C z : SphereTwo) = y := congrArg Subtype.val (C.apply_symm_apply ⟨y, hyV⟩)
    have hzt : z.2.val = p.2 := congrArg Prod.snd
      (Ψ.injective ((hC z).symm.trans ((congrArg e hz).trans hy)))
    rw [← hz, hside, hzt]
  constructor
  · rintro ⟨y, hy, hye⟩
    have hn : ‖p.1‖ = 1 := mem_sphere_zero_iff_norm.mp
      (hS.subset ⟨⟨y, hye⟩, ball_subset_closedBall hp.1, Ioo_subset_Icc_self hp.2⟩).1
    exact ⟨hn, lt_of_not_ge (fun hh => hy ((hmem y hye hn).mpr hh))⟩
  · rintro ⟨hn, ht⟩
    have hpS : Ψ p ∈ range e := (hS.symm.subset
      ⟨mem_sphere_zero_iff_norm.mpr hn, Ioo_subset_Icc_self hp.2⟩).1
    obtain ⟨y, hy⟩ := hpS
    exact ⟨y, fun hh => not_le.mpr ht ((hmem y hy hn).mp hh), hy⟩

theorem exists_two_cylinderCap_replacements_of_regular_height
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {c : ℝ} (hne : ∃ x, e x 2 = c)
    (hr : ∀ x, e x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (hcW : c ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (c - ε) (c + ε) ⊆ W ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree)
        (b : Fin 2 → ClosedCell 2 → SphereTwo) (σ : ℝ),
        (σ = 1 ∨ σ = -1) ∧ IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i)) ∧
        (∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η) ∧
        range (b 0) ∪ range (b 1) = univ ∧ range (b 0) ∩ range (b 1) = range η ∧
        e '' range η = Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) ∧
        (∀ p, Ψ p 2 = c + p.2) ∧
        Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε ∧
        let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
        ∃ (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) Schoenflies.Plane SphereTwo ∞)
          (f : Fin 2 → SphereTwo → EuclideanThree),
          ∀ i, closedBall (0 : Schoenflies.Plane) 1 ⊆ (χ i).source ∧
            χ i '' closedBall (0 : Schoenflies.Plane) 1 = range (b i) ∧
            IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i) ∧
            (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
              f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x)) ∧
            EqOn (f i) e (range (b i))ᶜ ∧
            (∀ y ∈ range (b i), f i =ᶠ[nhds y]
              (Ψ ∘ EuclideanGeometry.cylinderCap (a i)) ∘ (χ i).symm) ∧
            ∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
              Ψ p ∈ e '' (range (b i))ᶜ ↔
                ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2 := by
  classical
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, q, V, C, hη, _, hqrange, hheight,
    hsphere, hV, hC, _, hCzero, b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁,
    hcover, hinter, σ, hσ, _, _, hside₀, hside₁⟩ :=
    exists_innermost_source_height_cylinder_with_disk_sides he hne hr hW hcW
  let T : Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
  let t₀ : T := ⟨0, neg_lt_zero.mpr hε, hε⟩
  have hboundary : e '' range η = Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) := by
    ext z
    constructor
    · rintro ⟨y, ⟨θ, rfl⟩, rfl⟩
      refine ⟨(q θ, 0), ⟨hqrange.subset (mem_range_self θ), rfl⟩, ?_⟩
      exact (hC (θ, t₀)).symm.trans (congrArg e (hCzero θ t₀ rfl))
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      obtain ⟨θ, rfl⟩ := hqrange.symm.subset hx
      exact ⟨η θ, mem_range_self θ, (congrArg e (hCzero θ t₀ rfl)).symm.trans (hC (θ, t₀))⟩
  have hwall := cylinder_wall_iff hsphere hR.le
  let b : Fin 2 → ClosedCell 2 → SphereTwo := fun i => if i = 0 then b₀ else b₁
  let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
  have hb (i : Fin 2) : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i) := by
    dsimp [b]
    split_ifs
    · exact hb₀
    · exact hb₁
  have hbboundary (i : Fin 2) : range (b i ∘ cellBoundaryInclusion 2) = range η := by
    dsimp [b]
    split_ifs
    · exact hboundary₀
    · exact hboundary₁
  have hcap (i : Fin 2) :
      ∃ (χ : PartialDiffeomorph (𝓡 2) (𝓡 2) Schoenflies.Plane SphereTwo ∞)
        (f : SphereTwo → EuclideanThree),
        closedBall (0 : Schoenflies.Plane) 1 ⊆ χ.source ∧
        χ '' closedBall (0 : Schoenflies.Plane) 1 = range (b i) ∧
        IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
        (∀ x ∈ closedBall (0 : Schoenflies.Plane) 1,
          f (χ x) = Ψ (EuclideanGeometry.cylinderCap (a i) x)) ∧
        EqOn f e (range (b i))ᶜ ∧
        ∀ y ∈ range (b i), f =ᶠ[nhds y]
          (Ψ ∘ EuclideanGeometry.cylinderCap (a i)) ∘ χ.symm := by
    let τ : ℝ := if i = 0 then σ else -σ
    have hτ : τ = 1 ∨ τ = -1 := by
      dsimp [τ]
      split_ifs
      · exact hσ
      · rcases hσ with h | h <;> simp [h]
    have ha : a i = τ * ε / 2 := by
      dsimp [a, τ]
      split_ifs <;> ring
    have hazero : a i ≠ 0 := by
      rw [ha]
      rcases hτ with h | h <;> rw [h] <;> nlinarith
    have haε : |a i| < ε := by
      rw [ha]
      rcases hτ with h | h <;> rw [h] <;> simp only [one_mul, neg_one_mul]
      · rw [abs_of_pos (by linarith : 0 < ε / 2)]
        linarith
      · rw [neg_div, abs_neg, abs_of_pos (by linarith : 0 < ε / 2)]
        linarith
    have hτa : 0 ≤ τ * a i := by
      rw [ha]
      rcases hτ with h | h <;> rw [h] <;> nlinarith
    have hside : ∀ p, (C p : SphereTwo) ∈ range (b i) ↔ τ * p.2.val ≤ 0 := by
      intro p
      dsimp [b, τ]
      split_ifs
      · exact hside₀ p
      · rw [hside₁ p, neg_mul]
        exact neg_nonpos.symm
    exact exists_cylinderCap_replacement he (hb i) Ψ hazero haε hτa V C.toHomeomorph q
      hwall hV hC hside ((hbboundary i).symm ▸ hboundary)
  have hretained (i : Fin 2) :
      ∀ p ∈ ball (0 : Schoenflies.Plane) R ×ˢ Ioo (-ε) ε,
        Ψ p ∈ e '' (range (b i))ᶜ ↔
          ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2 := by
    apply retained_cylinder_side_iff Ψ hsphere V C.toHomeomorph q hV hC
    intro p
    dsimp [b]
    split_ifs
    · exact hside₀ p
    · rw [hside₁ p, neg_mul]
      exact neg_nonpos.symm
  choose χ f hχ using hcap
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbboundary, ?_, ?_,
    hboundary, hheight, hsphere, χ, f, fun i => ⟨(hχ i).1, (hχ i).2.1,
      (hχ i).2.2.1, (hχ i).2.2.2.1, (hχ i).2.2.2.2.1,
      (hχ i).2.2.2.2.2, hretained i⟩⟩
  · simpa [b] using hcover
  · simpa [b] using hinter

end DifferentialGeometry.Topology.SphereSeparation
