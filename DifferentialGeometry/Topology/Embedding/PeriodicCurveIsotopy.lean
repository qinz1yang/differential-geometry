import DifferentialGeometry.Topology.Manifold.AddCircle.SmoothEmbedding
import DifferentialGeometry.Topology.Embedding.AmbientIsotopy

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PeriodicCurve

theorem exists_compactly_supported_ambient_isotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : ℝ × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (hp : ∀ τ, Function.Periodic (fun t => F (τ, t)) 1) {a b : ℝ}
    (hi : ∀ τ ∈ Icc a b, InjOn (fun t => F (τ, t)) (Ico (0 : ℝ) 1))
    (hr : ∀ τ ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun x => F (τ, x)) t ≠ 0)
    {U : Set E} (hU : IsOpen U) (hFU : F '' (Icc a b ×ˢ Icc (0 : ℝ) 1) ⊆ U) :
    ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun q : ℝ × E => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ τ ∈ Icc a b, ∀ t : ℝ, Φ τ (F (a, t)) = F (τ, t) ∧
        (Φ τ).symm (F (τ, t)) = F (a, t)) ∧
      ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧ ∀ τ : ℝ,
        EqOn (Φ τ) id Sᶜ ∧ EqOn (Φ τ).symm id Sᶜ := by
  let e : ℝ × AddCircle (1 : ℝ) → E := fun q => (hp q.1).lift q.2
  have he : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ e (Icc a b ×ˢ univ) := by
    apply AddCircle.contMDiffOn_of_comp_coe
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hF.contMDiff.contMDiffOn
  have hemb (τ : ℝ) (hτ : τ ∈ Icc a b) :
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun z => e (τ, z)) :=
    AddCircle.isSmoothEmbedding_periodic_lift
      (hF.comp (contDiff_const.prodMk contDiff_id)) (hp τ) (hi τ hτ) (hr τ hτ)
  have heU : e '' (Icc a b ×ˢ univ) ⊆ U := by
    rintro _ ⟨⟨τ, z⟩, hz, rfl⟩
    let t : ℝ := AddCircle.equivIco 1 0 z
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      have h := (AddCircle.equivIco 1 0 z).property
      exact ⟨h.1, by simpa using h.2.le⟩
    have heq : e (τ, z) = F (τ, t) := by
      change (hp τ).lift z = (hp τ).lift (t : AddCircle (1 : ℝ))
      rw [show (t : AddCircle (1 : ℝ)) = z from AddCircle.coe_equivIco]
    rw [heq]
    exact hFU ⟨(τ, t), ⟨hz.1, ht⟩, rfl⟩
  obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, hS⟩ :=
    Manifold.exists_contDiff_compact_ambient_isotopy_Icc he hemb hU heU
  exact ⟨Φ, hΦ, hΦi, hΦa, fun τ hτ t => hΦe τ hτ (t : AddCircle (1 : ℝ)), hS⟩

theorem exists_compactly_supported_ambient_isotopy_of_increasing_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : AddCircle (1 : ℝ) → E}
    (hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ f)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hp : ∀ x, g (x + 1) = g x + 1)
    (hder : ∀ x, 0 < deriv g x)
    {U : Set E} (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℝ,
        Φ t (f (x : AddCircle (1 : ℝ))) =
          f (((1 - t) * x + t * g x : ℝ) : AddCircle (1 : ℝ))) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧ ∀ t,
        EqOn (Φ t) id Kᶜ ∧ EqOn (Φ t).symm id Kᶜ := by
  let γ : ℝ → E := fun x => f (x : AddCircle (1 : ℝ))
  have hγ : ContDiff ℝ ∞ γ :=
    (hf.contMDiff.comp AddCircle.isLocalDiffeomorph_coe.contMDiff).contDiff
  let β : ℝ × ℝ → ℝ := fun z => (1 - z.1) * z.2 + z.1 * g z.2
  have hβ : ContDiff ℝ ∞ β :=
    ((contDiff_const.sub contDiff_fst).mul contDiff_snd).add
      (contDiff_fst.mul (hg.comp contDiff_snd))
  have hβp (t x : ℝ) : β (t, x + 1) = β (t, x) + 1 := by
    dsimp only [β]
    rw [hp]
    ring
  have hβd (t x : ℝ) : HasDerivAt (fun x => β (t, x)) (1 - t + t * deriv g x) x := by
    convert! (((hasDerivAt_id x).const_mul (1 - t)).add
      ((hg.differentiable (by simp) x).hasDerivAt.const_mul t)) using 1
    simp
  have hβpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) : 0 < 1 - t + t * deriv g x := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos htp (hder x))
  have hβmono (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : StrictMono (fun x => β (t, x)) := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hβd t x).deriv]
    exact hβpos t ht x
  let F : ℝ × ℝ → E := fun z => γ (β z)
  have hFp (t : ℝ) : Function.Periodic (fun x => F (t, x)) 1 := by
    intro x
    change f (β (t, x + 1) : AddCircle (1 : ℝ)) = f (β (t, x) : AddCircle (1 : ℝ))
    rw [hβp]
    simp
  have hFi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : InjOn (fun x => F (t, x)) (Ico 0 1) := by
    intro x hx y hy heq
    have hm := hβmono t ht
    apply hm.injective
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ))
      (show β (t, x) ∈ Ico (β (t, 0)) (β (t, 0) + 1) from
        ⟨hm.monotone hx.1, by rw [← hβp]; exact hm (by simpa using hx.2)⟩)
      (show β (t, y) ∈ Ico (β (t, 0)) (β (t, 0) + 1) from
        ⟨hm.monotone hy.1, by rw [← hβp]; exact hm (by simpa using hy.2)⟩)).mp
    exact hf.isEmbedding.injective heq
  have hFr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) : deriv (fun x => F (t, x)) x ≠ 0 := by
    have hd := (hγ.differentiable (by simp) (β (t, x))).hasDerivAt.scomp x (hβd t x)
    change deriv (γ ∘ fun x => β (t, x)) x ≠ 0
    rw [hd.deriv]
    exact smul_ne_zero (hβpos t ht x).ne' (AddCircle.deriv_comp_coe_ne_zero hf _)
  obtain ⟨Φ, hΦ, hΦi, hΦ0, htrack, hsupport⟩ :=
    exists_compactly_supported_ambient_isotopy (hγ.comp hβ) hFp hFi
      (fun t ht x _ => hFr t ht x) hU
      (by rintro _ ⟨⟨t, x⟩, _, rfl⟩; exact hfU (mem_range_self _))
  refine ⟨Φ, hΦ, hΦi, hΦ0, ?_, hsupport⟩
  intro t ht x
  simpa only [Function.comp_apply, F, γ, β, sub_zero, zero_mul, add_zero, one_mul] using
    (htrack t ht x).1

end DifferentialGeometry.Topology.PeriodicCurve
