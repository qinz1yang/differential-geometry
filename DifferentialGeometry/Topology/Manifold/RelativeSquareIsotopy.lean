import DifferentialGeometry.Topology.Manifold.SquareFlowIsotopy
import DifferentialGeometry.Topology.Manifold.RectangleFieldDeformation
import DifferentialGeometry.Geometry.VectorField.ConstantPushforward

noncomputable section
open Set
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

open Poincare.Geometry.VectorField

theorem exists_relative_square_isotopy
    (f : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞) {δ : ℝ} (hδ : 0 < δ)
    (hfixed : ∀ z : ℂ, z.re ≤ δ ∨ 1 - δ ≤ z.re ∨ z.im ≤ δ ∨ 1 - δ ≤ z.im → f z = z) :
    ∃ H : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (H q.1).symm q.2) ∧
      H 0 = f ∧ H 1 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (∀ p, HasCompactSupport (fun z ↦ H p z - z)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ p z,
        z.re ≤ ε ∨ 1 - ε ≤ z.re ∨ z.im ≤ ε ∨ 1 - ε ≤ z.im → H p z = z := by
  let W : ℂ → ℂ := DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ (1 : ℂ))
  have hW : ContDiff ℝ ∞ W := contDiff_pushforward_const f 1
  have hWne (z : ℂ) : W z ≠ 0 := pushforward_const_ne_zero f one_ne_zero z
  let Q : Set ℂ := Complex.reProdIm (Icc δ (1 - δ)) (Icc δ (1 - δ))
  have hQ : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hfSupport : tsupport (fun z ↦ f z - z) ⊆ Q := by
    apply closure_minimal _ hQ.isClosed
    intro z hz
    by_contra hn
    apply hz
    apply sub_eq_zero.mpr
    apply hfixed z
    by_contra h
    push Not at h
    exact hn ⟨⟨h.1.le, h.2.1.le⟩, h.2.2.1.le, h.2.2.2.le⟩
  have hWSupport : tsupport (fun z ↦ W z - 1) ⊆ Q :=
    (tsupport_pushforward_const_sub_subset f 1).trans hfSupport
  have hWfixed (z : ℂ)
      (hz : z.re ≤ δ / 2 ∨ 1 - δ / 2 ≤ z.re ∨ z.im ≤ δ / 2 ∨ 1 - δ / 2 ≤ z.im) : W z = 1 := by
    have hn : z ∉ Q := by
      intro hzin
      rcases hz with hz | hz | hz | hz
      · linarith [hzin.1.1]
      · linarith [hzin.1.2]
      · linarith [hzin.2.1]
      · linarith [hzin.2.2]
    have hzsupport : z ∉ tsupport (fun z ↦ W z - 1) := fun h ↦ hn (hWSupport h)
    have he := image_eq_zero_of_notMem_tsupport (f := fun z ↦ W z - 1) hzsupport
    exact sub_eq_zero.mp he
  obtain ⟨V, hV, hnz, hVzero, _, hout, φ, hφ, hderiv, hterminal⟩ :=
    exists_rectangle_deformation_with_smooth_flows hW hWne
      (δ / 2) (1 - δ / 2) (δ / 2) (1 - δ / 2) hWfixed
  have hφzero (t : ℝ) (z : ℂ) : φ 0 t z = f (f.symm z + t • (1 : ℂ)) := by
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hd (s : ℝ) : HasDerivAt (fun s ↦ φ 0 s z) (W (φ 0 s z)) s := by
      simpa only [hVzero] using hderiv 0 (by norm_num) z s
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth (hW.of_le (by simp))
      (a := -R) (b := R) (t₀ := 0) ⟨by linarith, hR⟩ (fun s _ ↦ hd s)
      (fun s _ ↦ hasDerivAt_pushforward_const_orbit f (1 : ℂ) z s)
      (by simp only [(φ 0).map_zero_apply, zero_smul, add_zero, f.apply_symm_apply])
    exact he ⟨by dsimp [R]; linarith [neg_abs_le t], by dsimp [R]; linarith [le_abs_self t]⟩
  apply exists_relative_isotopy_of_square_flow f (half_pos hδ) _ hV φ hφ
    (fun p _ ↦ hnz p) hderiv (fun p _ ↦ hout p) hφzero hterminal
  intro z hz
  apply hfixed z
  rcases hz with hz | hz | hz | hz
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

end Poincare.Topology.Manifold
