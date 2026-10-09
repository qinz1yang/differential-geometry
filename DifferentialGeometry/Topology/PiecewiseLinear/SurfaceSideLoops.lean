/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceLoopDecomposition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_path_homotopic_map_of_loops {T V : Type*} [TopologicalSpace T]
    [TopologicalSpace V] [PathConnectedSpace T] (f : C(T, V)) {R : Set V} (hR : range f ⊆ R)
    (x₀ : T)
    (hloop : ∀ γ : Path (f x₀) (f x₀), (∀ s, γ s ∈ R) →
      ∃ σ : Path x₀ x₀, γ.Homotopic (σ.map f.continuous))
    {a b : T} (p : Path (f a) (f b)) (hp : ∀ s, p s ∈ R) :
    ∃ τ : Path a b, p.Homotopic (τ.map f.continuous) := by
  let ωa := PathConnectedSpace.somePath x₀ a
  let ωb := PathConnectedSpace.somePath x₀ b
  let ℓ := (ωa.map f.continuous).trans (p.trans (ωb.map f.continuous).symm)
  have hℓ : ∀ s, ℓ s ∈ R := by
    intro s
    have hs : ℓ s ∈ range ℓ := mem_range_self s
    rw [Path.trans_range, Path.trans_range, Path.symm_range] at hs
    rcases hs with ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
    · rw [← hu]
      exact hR ⟨ωa u, rfl⟩
    · rw [← hu]
      exact hp u
    · rw [← hu]
      exact hR ⟨ωb u, rfl⟩
  obtain ⟨σ, hσ⟩ := hloop ℓ hℓ
  refine ⟨(ωa.symm.trans σ).trans ωb, ?_⟩
  rw [← Path.Homotopic.Quotient.eq] at hσ ⊢
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm, ← hσ]
  simp only [ℓ, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.symm _),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]

theorem exists_surface_loop_homotopic_of_level {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W S O₁ O₂ Y : Set E} (hW : IsOpen W) (hS : IsCompact S) (hSW : S ⊆ W)
    [LocallyPathConnectedSpace S] (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hO : Disjoint O₁ O₂)
    (hWS : W \ S ⊆ O₁ ∪ O₂) {Φ : E → ℝ → E} {β : E → E} {τ : E → ℝ}
    (hΦc : ContinuousOn (fun q : E × ℝ => Φ q.1 q.2) (Y ×ˢ Icc 0 1))
    (hΦW : ∀ b ∈ Y, ∀ t ∈ Ioo (0 : ℝ) 1, Φ b t ∈ W)
    (hβc : ContinuousOn β W) (hτc : ContinuousOn τ W)
    (hinv : ∀ z ∈ W, β z ∈ Y ∧ τ z ∈ Ioo (0 : ℝ) 1 ∧ Φ (β z) (τ z) = z)
    (x₀ : S) (hlev : ∀ b ∈ Y, Φ b (τ x₀) ∈ O₂ ∪ S)
    (γ : Path (Set.inclusion hSW x₀) (Set.inclusion hSW x₀))
    (hγ : ∀ s, (γ s : E) ∈ O₁ ∪ S) :
    ∃ σ : Path x₀ x₀, γ.Homotopic (σ.map (continuous_inclusion hSW)) := by
  have hx₀W : (x₀ : E) ∈ W := hSW x₀.2
  let g : ℝ → E := fun s => (γ.extend s : E)
  have hg : Continuous g := continuous_subtype_val.comp γ.continuous_extend
  have hgW : ∀ s, g s ∈ W := fun s => (γ.extend s).2
  have hg0 : g 0 = x₀ := by
    change ((γ.extend 0 : W) : E) = x₀
    rw [Path.extend_zero]
  have hg1 : g 1 = x₀ := by
    change ((γ.extend 1 : W) : E) = x₀
    rw [Path.extend_one]
  let lev : ℝ × ℝ → ℝ := fun q => (1 - q.2) * τ (g q.1) + q.2 * τ x₀
  have hlevI : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, lev q ∈ Ioo (0 : ℝ) 1 := fun q hq =>
    convex_Ioo (0 : ℝ) 1 (hinv _ (hgW q.1)).2.1 (hinv _ hx₀W).2.1 (sub_nonneg.mpr hq.2.2)
      hq.2.1 (by ring)
  have hβg : Continuous fun q : ℝ × ℝ => β (g q.1) :=
    hβc.comp_continuous (hg.comp continuous_fst) fun q => hgW q.1
  have hτg : Continuous fun q : ℝ × ℝ => τ (g q.1) :=
    hτc.comp_continuous (hg.comp continuous_fst) fun q => hgW q.1
  have hlevc : Continuous lev :=
    ((continuous_const.sub continuous_snd).mul hτg).add (continuous_snd.mul continuous_const)
  let Ψ : ℝ × ℝ → E := fun q => Φ (β (g q.1)) (lev q)
  have hΨc : ContinuousOn Ψ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hΦc.comp (hβg.prodMk hlevc).continuousOn fun q hq =>
      ⟨(hinv _ (hgW q.1)).1, (hlevI q hq).1.le, (hlevI q hq).2.le⟩
  have hΨW : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, Ψ q ∈ W := fun q hq =>
    hΦW _ (hinv _ (hgW q.1)).1 _ (hlevI q hq)
  have hside : ∀ s, g s = x₀ → ∀ u : ℝ, Ψ (s, u) = x₀ := by
    intro s hs u
    change Φ (β (g s)) ((1 - u) * τ (g s) + u * τ x₀) = x₀
    rw [hs, ← add_mul, sub_add_cancel, one_mul]
    exact (hinv _ hx₀W).2.2
  have hΨ0 : ∀ s, Ψ (s, 0) = g s := by
    intro s
    change Φ (β (g s)) ((1 - 0) * τ (g s) + 0 * τ x₀) = g s
    rw [sub_zero, one_mul, zero_mul, add_zero]
    exact (hinv _ (hgW s)).2.2
  refine exists_surface_path_homotopic_of_square hW hS hSW hO₁ hO₂ hO hWS hΨc hΨW
    (fun u _ => hside 0 hg0 u) (fun u _ => hside 1 hg1 u) (fun s hs => ?_) (fun s _ => ?_) γ
    (fun t => ?_)
  · rw [hΨ0]
    change ((γ.extend s : W) : E) ∈ O₁ ∪ S
    rw [show γ.extend s = γ ⟨s, hs⟩ from Path.extend_extends' γ ⟨s, hs⟩]
    exact hγ _
  · change Φ (β (g s)) ((1 - 1) * τ (g s) + 1 * τ x₀) ∈ O₂ ∪ S
    rw [sub_self, zero_mul, zero_add, one_mul]
    exact hlev _ (hinv _ (hgW s)).1
  · rw [hΨ0]
    exact congrArg Subtype.val (Path.extend_extends' γ t).symm

end DifferentialGeometry.Topology.PiecewiseLinear
