/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.AnnulusCoreSteps
import DifferentialGeometry.Topology.PlanarJordan.PlaneRectNeighborhood
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Determinant

open Set Metric Filter Topology Manifold
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]

theorem exists_smooth_arc_in_charts (h : M ≃ₜ N)
    (a : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane M ∞)
    (b : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    {τa τb ρ₀ W : ℝ} (hρ₀ : 0 < ρ₀) (hρW : ρ₀ ≤ W)
    (hab : τa + 2 * ρ₀ < τb - 2 * ρ₀)
    (hR : planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W ⊆ a.source)
    (hRb : ∀ v ∈ planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W, h (a v) ∈ b.source)
    (hends : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h
      (a '' (ball (Plane.mk τa 0) ρ₀ ∪ ball (Plane.mk τb 0) ρ₀))) :
    ∃ ρ > 0, ρ ≤ ρ₀ ∧ ∃ δ > 0, δ < W ∧ ∃ g : M ≃ₜ N,
      EqOn g h (a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W)ᶜ ∧
      g '' (a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W) =
        h '' (a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W) ∧
      (∀ v ∈ a.source, |v 1| < δ → (v 0 ≤ τa - ρ ∨ τb + ρ ≤ v 0) →
        g (a v) = h (a v)) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g
        (a '' planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ) ∧
      g '' (a '' planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ) ⊆ b.source ∧
      ∀ x ∉ a '' planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
  let R := planeRect (τa - 3 * ρ₀) (τb + 3 * ρ₀) (-W) W
  let K := a '' R
  have hW : 0 < W := hρ₀.trans_le hρW
  have hK : IsCompact K := (isCompact_planeRect (by linarith) (by linarith)).image_of_continuousOn
    (a.toOpenPartialHomeomorph.continuousOn.mono hR)
  have hballs : ball (Plane.mk τa 0) ρ₀ ∪ ball (Plane.mk τb 0) ρ₀ ⊆ R := by
    apply union_subset
    · apply ball_subset_planeRect <;>
        norm_num [Schoenflies.Plane.mk] <;> linarith
    · apply ball_subset_planeRect <;>
        norm_num [Schoenflies.Plane.mk] <;> linarith
  let κ := a.toOpenPartialHomeomorph.trans h.toOpenPartialHomeomorph
  have hκR : R ⊆ κ.source := fun v hv => ⟨hR hv, trivial⟩
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
      (fun v => b (κ v)) (ball (Plane.mk τa 0) ρ₀ ∪ ball (Plane.mk τb 0) ρ₀) := by
    intro v
    exact ((a.isLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
      (hR (hballs v.property))).comp 𝓘(ℝ, Plane) _
      (hends ⟨a v, ⟨v, v.property, rfl⟩⟩)).comp 𝓘(ℝ, Plane) _
      (b.isLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ (hRb v (hballs v.property)))
  have hleft : ContDiffOn ℝ ∞ (fun v => b (κ v)) (ball (Plane.mk τa 0) ρ₀) :=
    hlocal.contMDiffOn.contDiffOn.mono subset_union_left
  have hright : ContDiffOn ℝ ∞ (fun v => b (κ v)) (ball (Plane.mk τb 0) ρ₀) :=
    hlocal.contMDiffOn.contDiffOn.mono subset_union_right
  obtain ⟨ρ, hρ, hρρ₀, δ, hδ, hδW, η, hηends, hmaps, hsm, hdet,
    G, -, -, -, hGfix, hGκ⟩ :=
    DifferentialGeometry.Manifold.exists_isotopy_smooth_arc_chart κ b.toOpenPartialHomeomorph
      hρ₀ hW hab hκR hRb hleft hright
      (fun v hv => (hlocal ⟨v, Or.inl hv⟩).det_fderiv_ne_zero (by simp))
      (fun v hv => (hlocal ⟨v, Or.inr hv⟩).det_fderiv_ne_zero (by simp))
  let g := h.trans (G 1)
  let T := planeOpenRect (τa - 3 * ρ) (τb + 3 * ρ) (-δ) δ
  have hT : IsOpen T := isOpen_planeOpenRect _ _ _ _
  have hTR : T ⊆ R := fun v hv =>
    ⟨by linarith [hv.1], by linarith [hv.2.1],
      by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩
  have hframe (v : Plane) (hv : v ∈ a.source) : g (a v) = κ (η v) :=
    hGκ v ⟨hv, trivial⟩
  have hgout : EqOn g h Kᶜ := by
    intro x hx
    apply hGfix 1
    rintro ⟨v, hv, heq⟩
    exact hx ⟨v, hv, h.injective heq⟩
  have hgK : g '' K = h '' K := by
    apply compl_injective
    rw [← g.image_compl, ← h.image_compl]
    exact image_congr fun x hx => hgout hx
  have hglocal : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a '' T) := by
    rintro ⟨x, v, hv, rfl⟩
    let ψ : Plane → Plane := fun w => b (κ (η w))
    have hψ : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ ψ v := by
      apply
        DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
          hT hv hsm.contMDiffOn
      have hinv : (fderiv ℝ ψ v).IsInvertible :=
        ⟨(fderiv ℝ ψ v).toContinuousLinearEquivOfDetNeZero (hdet v hv),
          ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩
      simpa only [mfderiv_eq_fderiv] using! hinv
    have hψb : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
        (fun w => b.symm (ψ w)) v :=
      hψ.comp 𝓘(ℝ, Plane) N
        (b.symm.isLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ (b.map_source (hmaps v hv)))
    have hva : v ∈ a.source := hR (hTR hv)
    have hav : a.symm (a v) = v := a.left_inv hva
    have hlift : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞
        (fun y => b.symm (ψ (a.symm y))) (a v) :=
      (a.symm.isLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ (a.map_source hva)).comp
        𝓘(ℝ, Plane) N (g := fun w => b.symm (ψ w))
        (by simpa only [hav] using hψb)
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := fun y =>
      b.symm (ψ (a.symm y))) _ hlift
    have hTa : IsOpen (a '' T) :=
      a.toOpenPartialHomeomorph.isOpen_image_of_subset_source hT (hTR.trans hR)
    filter_upwards [hTa.mem_nhds ⟨v, hv, rfl⟩] with y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have haw : a.symm (a w) = w := a.left_inv (hR (hTR hw))
    rw [haw, hframe w (hR (hTR hw))]
    exact (b.toPartialEquiv.left_inv (hmaps w hw)).symm
  refine ⟨ρ, hρ, hρρ₀, δ, hδ, hδW, g, hgout, hgK, ?_, hglocal, ?_, ?_⟩
  · intro v hv hδv hend
    rw [hframe v hv, hηends v hδv hend]
    rfl
  · rintro y ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    rw [hframe v (hR (hTR hv))]
    exact hmaps v hv
  · intro x hx hlocalx
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ hlocalx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hgout hy

end Homeomorph
