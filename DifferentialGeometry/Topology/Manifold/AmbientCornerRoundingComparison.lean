import DifferentialGeometry.Topology.Manifold.AmbientCornerRounding
import DifferentialGeometry.Topology.Manifold.RoundingComparison

open Set Metric
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G G' H : Type*} [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E G} {I' : ModelWithCorners ℝ E' G'}
  {J : ModelWithCorners ℝ F H}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G' N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace H P] [CompactSpace P]

theorem exists_diffeomorph_smoothAbs_corner_comparison
    (c : PartialDiffeomorph I I' M N ∞)
    (e : PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ × ℝ)) M (P × (ℝ × ℝ)) ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hstrip : (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ (c.symm.trans e).target) :
    let f := c.symm.trans e
    let C := (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε
    let Z := (univ : Set P) ×ˢ {(0 : ℝ × ℝ)}
    ∃ R₀ : M ≃ₜ M, ∃ R₁ : N ≃ₜ N,
      (∀ x ∈ e.source, R₀ x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hε (e x).2)) ∧
      (∀ x ∈ e.source, R₀.symm x =
        e.symm ((e x).1, (Homeomorph.smoothAbsCorner hε).symm (e x).2)) ∧
      IsCompact (e.symm '' C) ∧ e.symm '' C ⊆ e.source ∧
      EqOn R₀ id (e.symm '' C)ᶜ ∧ EqOn R₀.symm id (e.symm '' C)ᶜ ∧
      (∀ A : Set M, (∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) →
        R₀ '' A = e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε) ∧
      (∀ A : Set M, (∀ p ∈ e.target, e.symm p ∈ A ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0) →
        R₀ '' A = (A \ e.source) ∪ e.symm ''
          (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)})) ∧
      (∀ x : M, x ∉ e.symm '' Z →
        IsLocalDiffeomorphAt I I ∞ R₀ x ∧ IsLocalDiffeomorphAt I I ∞ R₀.symm (R₀ x)) ∧
      (∀ x ∈ f.source, R₁ x = f.symm ((f x).1, Homeomorph.smoothAbsCorner hε (f x).2)) ∧
      (∀ x ∈ f.source, R₁.symm x =
        f.symm ((f x).1, (Homeomorph.smoothAbsCorner hε).symm (f x).2)) ∧
      IsCompact (f.symm '' C) ∧ f.symm '' C ⊆ f.source ∧
      EqOn R₁ id (f.symm '' C)ᶜ ∧ EqOn R₁.symm id (f.symm '' C)ᶜ ∧
      (∀ A : Set N, (∀ p ∈ f.target, f.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) →
        R₁ '' A = f.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε) ∧
      (∀ A : Set N, (∀ p ∈ f.target, f.symm p ∈ A ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0) →
        R₁ '' A = (A \ f.source) ∪ f.symm ''
          (f.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)})) ∧
      (∀ x : N, x ∉ f.symm '' Z →
        IsLocalDiffeomorphAt I' I' ∞ R₁ x ∧ IsLocalDiffeomorphAt I' I' ∞ R₁.symm (R₁ x)) ∧
      e.symm '' C ⊆ c.source ∧ R₀ '' c.source = c.source ∧
      (∀ x ∈ c.source, R₁ (c x) = c (R₀ x)) ∧
      c '' (e.symm '' Z) = f.symm '' Z ∧
      ∀ (Q : Diffeomorph I I' M N ∞) (W : Set M), IsOpen W →
        R₀ '' (e.symm '' Z) ⊆ W → EqOn Q c (W ∩ c.source) →
        ∀ (A : Set M) (B : Set N), Q '' (R₀ '' A) = R₁ '' B →
          ∃ F : Diffeomorph I I' M N ∞,
            (F : M → N) = R₁.symm ∘ Q ∘ R₀ ∧ F '' A = B ∧
            IsOpen (c.source ∩ R₀ ⁻¹' W) ∧ e.symm '' Z ⊆ c.source ∩ R₀ ⁻¹' W ∧
            EqOn F c (c.source ∩ R₀ ⁻¹' W) := by
  let f := c.symm.trans e
  let C := (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε
  let Z := (univ : Set P) ×ˢ {(0 : ℝ × ℝ)}
  have hCe : C ⊆ e.target := fun p hp => (hstrip hp).1
  have hCc : e.symm '' C ⊆ c.source := by
    rintro x ⟨p, hp, rfl⟩
    exact (hstrip hp).2
  have hZC : Z ⊆ C := by
    rintro p ⟨hp, hpz⟩
    exact ⟨hp, by simpa only [mem_singleton_iff.mp hpz, mem_closedBall, dist_self] using hε.le⟩
  obtain ⟨R₀, h₀, hi₀, hC₀, hCs₀, hf₀, hfi₀, hq₀, hr₀, hd₀⟩ :=
    e.exists_homeomorph_smoothAbs_corner hε hCe
  obtain ⟨R₁, h₁, hi₁, hC₁, hCs₁, hf₁, hfi₁, hq₁, hr₁, hd₁⟩ :=
    f.exists_homeomorph_smoothAbs_corner hε hstrip
  have hcomm := OpenPartialHomeomorph.eqOn_comp_of_chart_extensions
    c.toOpenPartialHomeomorph e.toOpenPartialHomeomorph
    ((Homeomorph.refl P).prodCongr (Homeomorph.smoothAbsCorner hε))
    hstrip R₀ R₁ h₀ h₁ hf₀ hf₁
  have hcomm' (x : M) (hx : x ∈ c.source) : R₁ (c x) = c (R₀ x) := hcomm hx
  have hRc : R₀ '' c.source = c.source := by
    have heq : EqOn R₀ id c.sourceᶜ := fun x hx => hf₀ (fun h => hx (hCc h))
    have hc := heq.image_eq_self
    rw [R₀.image_compl] at hc
    exact compl_injective hc
  have hZ : c '' (e.symm '' Z) = f.symm '' Z := by
    rw [image_image]
    rfl
  refine ⟨R₀, R₁, h₀, hi₀, hC₀, hCs₀, hf₀, hfi₀, hq₀, hr₀, hd₀,
    h₁, hi₁, hC₁, hCs₁, hf₁, hfi₁, hq₁, hr₁, hd₁, hCc, hRc, hcomm', hZ, ?_⟩
  intro Q W hW hZW hQc A B hQAB
  have hU : IsOpen (c.source ∩ R₀ ⁻¹' W) := c.open_source.inter (hW.preimage R₀.continuous)
  have hZU : e.symm '' Z ⊆ c.source ∩ R₀ ⁻¹' W := by
    intro x hx
    exact ⟨hCc (image_mono hZC hx), hZW ⟨x, hx, rfl⟩⟩
  have hcommQ : ∀ x ∈ c.source ∩ R₀ ⁻¹' W, R₁ (c x) = Q (R₀ x) := by
    intro x hx
    exact (hcomm' x hx.1).trans (hQc ⟨hx.2, hRc ▸ mem_image_of_mem R₀ hx.1⟩).symm
  obtain ⟨F, hF, hFAB, hFc⟩ := c.exists_diffeomorph_unrounding R₀ R₁ Q
    (fun x hx => (hd₀ x hx).1) (fun y hy => (hd₁ y hy).1) hZ hU hZU
    inter_subset_left hcommQ hQAB
  exact ⟨F, hF, hFAB, hU, hZU, hFc⟩

end PartialDiffeomorph
