import DifferentialGeometry.Topology.SphereSeparation.FlatCapAbsorption
import DifferentialGeometry.Topology.SphereSeparation.FlatCapReconstruction

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_diffeomorph_ball_of_flat_caps (m : ℕ)
    (hm : 0 < m) {X : Type*}
    {e : X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    {f g : Fin 2 → X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    (d : SphereSides (range e)) (df : ∀ i, SphereSides (range (f i)))
    (dg : ∀ i, SphereSides (range (g i)))
    (Ψ : (EuclideanSpace ℝ (Fin (m + 1)) × ℝ) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    (χ : Fin 2 → EuclideanSpace ℝ (Fin (m + 1)) → X)
    (D : Fin 2 → EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    {S : Fin 2 → Set X} {R b σ : ℝ} {a : Fin 2 → ℝ}
    (hR : 1 < R) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b) (hσ : σ = 1 ∨ σ = -1)
    (hχS : ∀ i, χ i '' closedBall 0 1 = S i)
    (hcap : ∀ i, ∀ x ∈ closedBall 0 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hflat : ∀ i, ∀ x ∈ closedBall 0 1, g i (χ i x) = Ψ (x, 0))
    (hfix : ∀ i, EqOn (f i) e (S i)ᶜ) (hgfix : ∀ i, EqOn (g i) e (S i)ᶜ)
    (hret : ∀ i, ∀ p ∈ ball 0 R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' (S i)ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (hS : ∀ p ∈ ball 0 R ×ˢ Ioo (-b) b, Ψ p ∈ range e ↔ ‖p.1‖ = 1)
    (hshared : range (g 0) ∩ range (g 1) = Ψ '' (closedBall 0 1 ×ˢ {(0 : ℝ)}))
    (hrel : (Disjoint (dg 0).compactSide (dg 1).compactSide ∧
        closure d.compactSide = closure (dg 0).compactSide ∪ closure (dg 1).compactSide ∧
        closure (dg 0).compactSide ∩ closure (dg 1).compactSide =
          Ψ '' (closedBall 0 1 ×ˢ {(0 : ℝ)})) ∨
      ((dg 0).compactSide ⊆ (dg 1).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 1).compactSide) \ closure (dg 0).compactSide) ∧
        closure (dg 1).compactSide = closure d.compactSide ∪ closure (dg 0).compactSide) ∨
      ((dg 1).compactSide ⊆ (dg 0).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 0).compactSide) \ closure (dg 1).compactSide) ∧
        closure (dg 0).compactSide = closure d.compactSide ∪ closure (dg 1).compactSide))
    (hD : ∀ i, D i '' closedBall 0 1 = closure (df i).compactSide) :
    ∃ H : EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      H '' closedBall 0 1 = closure d.compactSide ∧ H '' sphere 0 1 = range e := by
  let M := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  have hfinish (H : M ≃ₘ[ℝ] M) (hH : H '' closedBall 0 1 = closure d.compactSide) :
      H '' sphere 0 1 = range e := by
    have hh : H '' frontier (closedBall 0 1) = frontier (H '' closedBall 0 1) :=
      H.toHomeomorph.image_frontier _
    rw [frontier_closedBall _ one_ne_zero, hH, frontier, closure_closure, d.interior_closure_compactSide,
      ← d.isOpen_compactSide.frontier_eq, d.frontier_compactSide] at hh
    exact hh
  have hforward (hcase :
      (Disjoint (dg 0).compactSide (dg 1).compactSide ∧
        closure d.compactSide = closure (dg 0).compactSide ∪ closure (dg 1).compactSide ∧
        closure (dg 0).compactSide ∩ closure (dg 1).compactSide = Ψ '' (closedBall 0 1 ×ˢ {(0 : ℝ)})) ∨
      ((dg 0).compactSide ⊆ (dg 1).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 1).compactSide) \ closure (dg 0).compactSide) ∧
        closure (dg 1).compactSide = closure d.compactSide ∪ closure (dg 0).compactSide)) :
      ∃ H : M ≃ₘ[ℝ] M, H '' closedBall 0 1 = closure d.compactSide := by
    obtain ⟨H, hH, _⟩ := exists_diffeomorph_flat_cap_absorption m hm d df dg Ψ χ (D 0)
      hR ha hab hσ hχS hcap hflat hfix hgfix hret hS hshared hcase (hD 0)
    refine ⟨(D 1).trans H, ?_⟩
    change (H ∘ D 1) '' _ = _
    rw [image_comp, hD 1, hH]
  rcases hrel with hdisj | hnest | hnest
  · obtain ⟨H, hH⟩ := hforward (Or.inl hdisj)
    exact ⟨H, hH, hfinish H hH⟩
  · obtain ⟨H, hH⟩ := hforward (Or.inr hnest)
    exact ⟨H, hH, hfinish H hH⟩
  · let τ : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
    have hsign (i : Fin 2) : (if τ i = 0 then σ else -σ) = (if i = 0 then -σ else - -σ) := by
      fin_cases i <;> simp [τ]
    have hnegσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
    obtain ⟨H, hH, _⟩ := exists_diffeomorph_flat_cap_absorption m hm d
      (fun i => df (τ i)) (fun i => dg (τ i)) Ψ (fun i => χ (τ i)) (D 1)
      hR (fun i => ha (τ i)) (fun i => hab (τ i)) hnegσ (fun i => hχS (τ i))
      (by intro i x hx; simpa only [hsign] using hcap (τ i) x hx)
      (fun i => hflat (τ i)) (fun i => hfix (τ i)) (fun i => hgfix (τ i))
      (by intro i p hp; simpa only [hsign] using hret (τ i) p hp) hS
      (by simpa [τ, inter_comm] using hshared)
      (Or.inr (by simpa [τ] using hnest))
      (by simpa [τ] using hD 1)
    have hball : ((D 0).trans H) '' closedBall 0 1 = closure d.compactSide := by
      change (H ∘ D 0) '' _ = _
      rw [image_comp, hD 0]
      simpa [τ] using hH
    exact ⟨(D 0).trans H, hball, hfinish _ hball⟩

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_diffeomorph_ball_of_flat_cap_reconstruction
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {b : Fin 2 → ClosedCell 2 → SphereTwo}
    (hb : ∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i))
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hbboundary : ∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η)
    (hcover : range (b 0) ∪ range (b 1) = univ)
    (hinter : range (b 0) ∩ range (b 1) = range η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    {R ε : ℝ} (hR : 1 < R)
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Icc (-ε) ε) =
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (-ε) ε)
    (hboundary : e '' range η = Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : ∀ i, closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = range (b i))
    {a : Fin 2 → ℝ} {σ : ℝ} (ha : ∀ i, 0 < a i) (haε : ∀ i, a i < ε)
    (hσ : σ = 1 ∨ σ = -1)
    {f g : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hffix : ∀ i, EqOn (f i) e (range (b i))ᶜ)
    (hret : ∀ i, ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' (range (b i))ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (hflat : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, g i (χ i x) = Ψ (x, 0))
    (hgfix : ∀ i, EqOn (g i) e (range (b i))ᶜ)
    (hrange : ∀ i, range (g i) = Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) ∪
      e '' (range (b i))ᶜ)
    (hgin : range (g 0) ∩ range (g 1) =
      Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (hgun : range (g 0) ∪ range (g 1) = range e ∪
      Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (D : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (hD : ∀ i, D i '' closedBall 0 1 = closure
      (jordanBrouwer_openThreeSpace (f i) (hf i)
        (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides.compactSide) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ H : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      H '' closedBall 0 1 = closure d.compactSide ∧ H '' sphere 0 1 = range e := by
  let s : Fin 2 → ℝ := fun i => if i = 0 then σ else -σ
  have hs (i : Fin 2) : s i = 1 ∨ s i = -1 := by
    dsimp [s]
    split_ifs
    · exact hσ
    · rcases hσ with rfl | rfl <;> norm_num
  have hsa (i : Fin 2) : s i * a i ≠ 0 :=
    mul_ne_zero (by rcases hs i with hh | hh <;> rw [hh] <;> norm_num) (ha i).ne'
  have hab (i : Fin 2) : |s i * a i| < ε := by
    have habs : |s i| = 1 := by rcases hs i with hh | hh <;> rw [hh] <;> norm_num
    rw [abs_mul, habs, one_mul, abs_of_pos (ha i)]
    exact haε i
  have hside (i : Fin 2) (p : EuclideanSpace ℝ (Fin 2) × ℝ)
      (hp : p ∈ ball 0 R ×ˢ Ioo (-ε) ε) (hh : Ψ p ∈ e '' (range (b i))ᶜ) :
      ‖p.1‖ = 1 ∧ 0 ≤ (s i * a i) * p.2 := by
    have ht := (hret i p hp).mp hh
    refine ⟨ht.1, ?_⟩
    have hn : 0 ≤ a i * (s i * p.2) := mul_nonneg (ha i).le ht.2.le
    nlinarith
  obtain ⟨Φ, C, dg, _, hrel⟩ := exists_flat_cap_reconstruction_regions he hb hbboundary hcover
    hinter Ψ hR hS hboundary χ hχ hχD hsa hab hf hcap hffix hside hflat hgfix hrange hgin hgun
  let d := (jordanBrouwer_openThreeSpace e he
    (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
  let df := fun i => (jordanBrouwer_openThreeSpace (f i) (hf i)
    (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
  have hcyl : ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ range e ↔ ‖p.1‖ = 1 := by
    intro p hp
    have hclosed : p ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Icc (-ε) ε :=
      ⟨ball_subset_closedBall hp.1, Ioo_subset_Icc_self hp.2⟩
    constructor
    · intro hh
      have hh' := hS.subset ⟨hh, hclosed⟩
      exact mem_sphere_zero_iff_norm.mp hh'.1
    · intro hh
      exact (hS.symm.subset ⟨mem_sphere_zero_iff_norm.mpr hh, hclosed.2⟩).1
  apply exists_diffeomorph_ball_of_flat_caps 1 (by norm_num) d df dg Ψ (fun i => χ i) D hR ha haε hσ hχD
    hcap hflat hffix hgfix hret hcyl hgin _ hD
  rcases hrel with hh | hh | hh
  · exact Or.inl hh
  · exact Or.inr (Or.inl ⟨hh.1.subset, hh.2.2.1, hh.2.2.2.1⟩)
  · exact Or.inr (Or.inr ⟨hh.1.subset, hh.2.2.1, hh.2.2.2.1⟩)

end DifferentialGeometry.Topology.SphereSeparation
