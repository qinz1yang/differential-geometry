/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CornerRounding.Domain
import DifferentialGeometry.Topology.Manifold.CornerRounding.Chart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumers of corner rounding

* `roundedSolidCylinder`: the solid cylinder `D² × [0,1] = {1 - ‖z‖² ≥ 0, t (1 - t) ≥ 0}` has two
  corner circles; for `0 < ε ≤ 1/12` its regularized-minimum rounding is a compact smooth
  3-manifold with boundary inside the cylinder, equal to it off the rim band, invariant under
  rotations of the disk factor, with the complementary side also a smooth manifold with the same
  boundary.
* `roundedCircleCorner`: in `Circle × ℝ²` (the product chart of a circle bundle near a corner
  circle) the PC corner homeomorphism maps `Circle × quadrant` onto the rounded piece and the
  complementary side onto the rounded complementary side, preserving every circle coordinate.
* `roundedMin_opposite_faces`: positive independence cannot be dropped — for opposite normals the
  cornered set is nonempty and its rounding is empty.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Topology.Manifold.CornerRounding

private theorem apply_eq_zero_of_mfderiv_eq_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : V → ℝ} {D : V →L[ℝ] ℝ} {x : V} (hf : HasFDerivAt f D x)
    (h0 : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) f x = 0) (v : V) : D v = 0 := by
  rw [hf.hasMFDerivAt.mfderiv] at h0
  exact DFunLike.congr_fun h0 v

private theorem cylinder_mfderiv_ne_zero (a b : ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ)
    (h : (a ≠ 0 ∧ p.1 ≠ 0) ∨ (b ≠ 0 ∧ 2 * p.2 ≠ 1)) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ)
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => a * (1 - ‖q.1‖ ^ 2) + b * (q.2 * (1 - q.2)))
      p ≠ 0 := by
  have hside := (hasFDerivAt_fst (p := p) (𝕜 := ℝ)).norm_sq.const_sub 1
  have hend := (hasFDerivAt_snd (p := p) (𝕜 := ℝ)).mul
    ((hasFDerivAt_snd (p := p) (𝕜 := ℝ)).const_sub 1)
  have hG : HasFDerivAt
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => a * (1 - ‖q.1‖ ^ 2) + b * (q.2 * (1 - q.2)))
      _ p := (hside.const_mul a).add (hend.const_mul b)
  intro h0
  have e1 := apply_eq_zero_of_mfderiv_eq_zero hG h0 (p.1, 0)
  have e2 := apply_eq_zero_of_mfderiv_eq_zero hG h0 (0, 1)
  simp only [smul_neg, smul_add, add_apply, neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', coe_innerSL_apply, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_real_eq_id, id_eq, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul,
    ContinuousLinearMap.coe_snd', mul_zero, neg_zero, add_zero, neg_eq_zero, mul_eq_zero,
    OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero, false_or,
    inner_zero_right, mul_one, zero_add] at e1 e2
  rcases h with ⟨ha, hp⟩ | ⟨hb, ht⟩
  · rcases e1 with e1 | e1
    · exact ha e1
    · exact hp e1
  · have e2' : b * (1 - 2 * p.2) = 0 := by linear_combination e2
    rcases mul_eq_zero.mp e2' with e2'' | e2''
    · exact hb e2''
    · exact ht (by linarith)

private theorem side_nonneg_iff {z : EuclideanSpace ℝ (Fin 2)} :
    0 ≤ 1 - ‖z‖ ^ 2 ↔ ‖z‖ ≤ 1 := by
  constructor
  · intro h
    nlinarith [norm_nonneg z]
  · intro h
    nlinarith [norm_nonneg z]

private theorem ends_nonneg_iff {t : ℝ} : 0 ≤ t * (1 - t) ↔ t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    constructor
    · by_contra ht
      nlinarith
    · by_contra ht
      nlinarith
  · rintro ⟨h0, h1⟩
    exact mul_nonneg h0 (by linarith)

/-- **Consumer: the rounded solid cylinder.** -/
theorem roundedSolidCylinder {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 12) :
    {p : EuclideanSpace ℝ (Fin 2) × ℝ | 0 ≤ roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))} ⊆
        closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (0 : ℝ) 1 ∧
      (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (0 : ℝ) 1) \
          {p | 0 ≤ roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))} ⊆
        {p | 1 - 3 * ε < ‖p.1‖ ^ 2 ∧ p.2 * (1 - p.2) < 3 * ε} ∧
      IsCompact
        {p : EuclideanSpace ℝ (Fin 2) × ℝ | 0 ≤ roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))} ∧
      (∀ z z' : EuclideanSpace ℝ (Fin 2), ‖z‖ = ‖z'‖ → ∀ t : ℝ,
        roundedMin ε (1 - ‖z‖ ^ 2) (t * (1 - t)) = roundedMin ε (1 - ‖z'‖ ^ 2) (t * (1 - t))) ∧
      (∀ p : EuclideanSpace ℝ (Fin 2) × ℝ, roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2)) = 0 →
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ)
          (fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
            roundedMin ε (1 - ‖q.1‖ ^ 2) (q.2 * (1 - q.2))) p ≠ 0) ∧
      (∃ m : ℕ, Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = m + 1 ∧
        ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1))
            {p : EuclideanSpace ℝ (Fin 2) × ℝ //
              0 ≤ roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))},
          letI := cs
          IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
            {p : EuclideanSpace ℝ (Fin 2) × ℝ //
              0 ≤ roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))} ∧
          ∀ x : {p : EuclideanSpace ℝ (Fin 2) × ℝ //
              0 ≤ roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))},
            (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔
              roundedMin ε (1 - ‖x.1.1‖ ^ 2) (x.1.2 * (1 - x.1.2)) = 0) ∧
      (∃ m : ℕ, Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = m + 1 ∧
        ∃ cs : ChartedSpace (EuclideanHalfSpace (m + 1))
            (Morse.SublevelSpace (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
              roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))) 0),
          letI := cs
          IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) ∞
            (Morse.SublevelSpace (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
              roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))) 0) ∧
          ∀ x : Morse.SublevelSpace (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
              roundedMin ε (1 - ‖p.1‖ ^ 2) (p.2 * (1 - p.2))) 0,
            (modelWithCornersEuclideanHalfSpace (m + 1)).IsBoundaryPoint x ↔
              roundedMin ε (1 - ‖x.1.1‖ ^ 2) (x.1.2 * (1 - x.1.2)) = 0) := by
  set φ : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ := fun q => 1 - ‖q.1‖ ^ 2 with hφdef
  set ψ : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ := fun q => q.2 * (1 - q.2) with hψdef
  have hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ) ∞ φ :=
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst)).contMDiff
  have hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ) ∞ ψ :=
    (contDiff_snd.mul (contDiff_const.sub contDiff_snd)).contMDiff
  have hφreg : ∀ x, φ x = 0 → 0 ≤ ψ x →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ) φ x ≠ 0 := by
    intro x hx _
    have hf : φ = fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
        1 * (1 - ‖q.1‖ ^ 2) + 0 * (q.2 * (1 - q.2)) := by
      funext q
      simp only [hφdef]
      ring
    rw [hf]
    apply cylinder_mfderiv_ne_zero
    refine Or.inl ⟨one_ne_zero, fun h0 => ?_⟩
    simp only [hφdef, h0, norm_zero] at hx
    norm_num at hx
  have hψreg : ∀ x, ψ x = 0 → 0 ≤ φ x →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ) ψ x ≠ 0 := by
    intro x hx _
    have hf : ψ = fun q : EuclideanSpace ℝ (Fin 2) × ℝ =>
        0 * (1 - ‖q.1‖ ^ 2) + 1 * (q.2 * (1 - q.2)) := by
      funext q
      simp only [hψdef]
      ring
    rw [hf]
    apply cylinder_mfderiv_ne_zero
    refine Or.inr ⟨one_ne_zero, fun h0 => ?_⟩
    simp only [hψdef] at hx
    have ht : x.2 = 1 / 2 := by linarith
    rw [ht] at hx
    norm_num at hx
  have hband : ∀ x, 0 ≤ φ x → 0 ≤ ψ x → φ x + ψ x < 1 / 4 → ∀ t ∈ Icc (0 : ℝ) 1,
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, ℝ)
        (fun y => (1 - t) * φ y + t * ψ y) x ≠ 0 := by
    intro x hx0 hy0 hs t ht
    apply cylinder_mfderiv_ne_zero
    by_cases h1 : t = 1
    · refine Or.inr ⟨by rw [h1]; norm_num, fun h2 => ?_⟩
      have hx2 : x.2 = 1 / 2 := by linarith
      have hψx : ψ x = 1 / 4 := by
        simp only [hψdef, hx2]
        norm_num
      linarith
    · refine Or.inl ⟨sub_ne_zero.mpr (Ne.symm h1), fun h2 => ?_⟩
      have hφx : φ x = 1 := by
        simp only [hφdef, h2, norm_zero]
        norm_num
      linarith
  have hεδ : 3 * ε ≤ 1 / 4 := by linarith
  obtain ⟨-, hreg, hsub, hdiff, -, -, -⟩ :=
    roundedMin_corner_rounding hφ hψ hφreg hψreg hband hε hεδ
  have hcyl : {p : EuclideanSpace ℝ (Fin 2) × ℝ | 0 ≤ φ p ∧ 0 ≤ ψ p} =
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (0 : ℝ) 1 := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_closedBall, dist_zero_right, hφdef, hψdef,
      side_nonneg_iff, ends_nonneg_iff]
  have hsub' : {p : EuclideanSpace ℝ (Fin 2) × ℝ | 0 ≤ roundedMin ε (φ p) (ψ p)} ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (0 : ℝ) 1 := hcyl ▸ hsub
  obtain ⟨m₁, hm₁, cs₁, hman₁, -, -, hbd₁⟩ :=
    exists_isManifold_roundedPiece hφ hψ hφreg hψreg hband hε hεδ
  obtain ⟨m₂, hm₂, cs₂, hman₂, -, -, hbd₂⟩ :=
    exists_isManifold_roundedComplement hφ hψ hφreg hψreg hband hε hεδ
  refine ⟨hsub', ?_, ?_, ?_, hreg, ⟨m₁, hm₁, cs₁, hman₁, hbd₁⟩, ⟨m₂, hm₂, cs₂, hman₂, hbd₂⟩⟩
  · rw [← hcyl]
    intro p hp
    obtain ⟨hp0, hp1, hp2⟩ := hdiff hp
    simp only [hφdef, hψdef] at hp0 hp1 hp2
    exact ⟨by linarith, by linarith⟩
  · apply ((isCompact_closedBall _ _).prod isCompact_Icc).of_isClosed_subset _ hsub'
    exact isClosed_le continuous_const
      ((contDiff_roundedMin ε).continuous.comp (hφ.continuous.prodMk hψ.continuous))
  · intro z z' hz t
    rw [hz]

/-- **Consumer: corner of a circle bundle.**  In `Circle × ℝ²` the PC corner homeomorphism maps
`Circle × quadrant` onto the rounded piece and the complementary side onto the rounded
complementary side, keeps every circle coordinate, and is a local diffeomorphism off the corner
circle. -/
theorem roundedCircleCorner {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : (Circle × (ℝ × ℝ)) ≃ₜ (Circle × (ℝ × ℝ)),
      Φ '' {p | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2} = {p | 0 ≤ roundedMin ε p.2.1 p.2.2} ∧
      Φ '' {p | p.2.1 ≤ 0 ∨ p.2.2 ≤ 0} = {p | roundedMin ε p.2.1 p.2.2 ≤ 0} ∧
      (∀ p, (Φ p).1 = p.1) ∧
      ∀ p : Circle × (ℝ × ℝ), p.2 ≠ 0 →
        IsLocalDiffeomorphAt ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ∞ Φ p := by
  let e := (Diffeomorph.refl ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (Circle × (ℝ × ℝ)) ∞).toPartialDiffeomorph
  obtain ⟨Φ, hΦ, -, -, -, -, hquad, hreflex, hloc⟩ :=
    exists_homeomorph_roundedMin_corner e hε (subset_univ _)
  have hs : e.source = univ := rfl
  refine ⟨Φ, ?_, ?_, fun p => ?_, fun p hp => (hloc p ?_).1⟩
  · rw [hquad _ (fun p _ => Iff.rfl), hs, sdiff_univ, empty_union]
    ext p
    simp only [mem_univ, true_and]
    exact Iff.rfl
  · rw [hreflex _ (fun p _ => Iff.rfl), hs, sdiff_univ, empty_union]
    ext p
    simp only [mem_univ, true_and]
    exact Iff.rfl
  · rw [hΦ p (mem_univ p)]
    rfl
  · rintro ⟨q, hq, hqp⟩
    apply hp
    rw [← hqp]
    exact hq.2

/-- **Positive independence is necessary.**  With opposite normals the cornered set
`{y ≥ 0, -y ≥ 0}` is the nonempty line `{y = 0}`, but its regularized-minimum rounding is empty for
every `ε > 0`; no homeomorphism can relate them. -/
theorem roundedMin_opposite_faces {ε : ℝ} (hε : 0 < ε) :
    {p : ℝ × ℝ | 0 ≤ p.2 ∧ 0 ≤ -p.2}.Nonempty ∧
      {p : ℝ × ℝ | 0 ≤ roundedMin ε p.2 (-p.2)} = ∅ := by
  refine ⟨⟨(0, 0), by simp⟩, ?_⟩
  ext p
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
  exact roundedMin_neg_of_eq_neg hε p.2

end DifferentialGeometry.Topology.Manifold.CornerRounding
