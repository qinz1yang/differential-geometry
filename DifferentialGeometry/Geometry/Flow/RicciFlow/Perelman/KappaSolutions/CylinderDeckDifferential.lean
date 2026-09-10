import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev CylinderI := (𝓡 2).prod (𝓘(ℝ, ℝ))
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderDeckDifferentialSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

variable (Phi : (SphereTwo × ℝ) ≃ₘ⟮CylinderI, CylinderI⟯ (SphereTwo × ℝ))
  {T t₀ t₁ : ℝ} (hdifferent : t₀ ≠ t₁)
  (hmetric : ∀ t : ℝ, t = t₀ ∨ t = t₁ →
    ∀ (p : SphereTwo × ℝ) (v w : TangentSpace (𝓡 2) p.1) (a c : ℝ),
      (2 * (T - t)) * (sphereMetric).inner (Phi p).1
          (mfderiv CylinderI CylinderI Phi p (v, a)).1
          (mfderiv CylinderI CylinderI Phi p (w, c)).1 +
        (mfderiv CylinderI CylinderI Phi p (v, a)).2 *
          (mfderiv CylinderI CylinderI Phi p (w, c)).2 =
      (2 * (T - t)) * (sphereMetric).inner p.1 v w + a * c)

include hdifferent hmetric

theorem cylinderDeck_mfderiv_block_inner (p : SphereTwo × ℝ)
    (v w : TangentSpace (𝓡 2) p.1) (a c : ℝ) :
    (sphereMetric).inner (Phi p).1
        (mfderiv CylinderI CylinderI Phi p (v, a)).1
        (mfderiv CylinderI CylinderI Phi p (w, c)).1 =
      (sphereMetric).inner p.1 v w ∧
    (mfderiv CylinderI CylinderI Phi p (v, a)).2 *
        (mfderiv CylinderI CylinderI Phi p (w, c)).2 = a * c := by
  have h₀ := hmetric t₀ (Or.inl rfl) p v w a c
  have h₁ := hmetric t₁ (Or.inr rfl) p v w a c
  have hfactor : (t₁ - t₀) *
      ((sphereMetric).inner (Phi p).1
          (mfderiv CylinderI CylinderI Phi p (v, a)).1
          (mfderiv CylinderI CylinderI Phi p (w, c)).1 -
        (sphereMetric).inner p.1 v w) = 0 := by
    nlinarith [h₀, h₁]
  have htime : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr hdifferent.symm
  have hsphere := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left htime)
  refine ⟨hsphere, ?_⟩
  rw [hsphere] at h₀
  exact add_left_cancel h₀

theorem cylinderDeck_mfderiv_preserves_factors (p : SphereTwo × ℝ)
    (v : TangentSpace (𝓡 2) p.1) (a : ℝ) :
    (mfderiv CylinderI CylinderI Phi p (v, 0)).2 = 0 ∧
      (mfderiv CylinderI CylinderI Phi p (0, a)).1 = 0 := by
  have hhorizontal := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p v v 0 0
  have hvertical := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p (0 : TangentSpace (𝓡 2) p.1)
      (0 : TangentSpace (𝓡 2) p.1) a a
  constructor
  · have hsquare : (mfderiv CylinderI CylinderI Phi p (v, 0)).2 *
        (mfderiv CylinderI CylinderI Phi p (v, 0)).2 = 0 := by
      simpa only [zero_mul] using hhorizontal.2
    exact mul_self_eq_zero.mp hsquare
  · have hinner : (sphereMetric).inner (Phi p).1
        (mfderiv CylinderI CylinderI Phi p (0, a)).1
        (mfderiv CylinderI CylinderI Phi p (0, a)).1 = 0 := by
      simpa only [map_zero, zero_apply] using hvertical.1
    by_contra hne
    have hpos := (sphereMetric).pos (Phi p).1
      (mfderiv CylinderI CylinderI Phi p (0, a)).1 hne
    rw [hinner] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos

theorem cylinderDeck_mfderiv_block_diagonal (p : SphereTwo × ℝ)
    (v : TangentSpace (𝓡 2) p.1) (a : ℝ) :
    mfderiv CylinderI CylinderI Phi p (v, a) =
      ((mfderiv CylinderI CylinderI Phi p (v, 0)).1,
        (mfderiv CylinderI CylinderI Phi p (0, a)).2) := by
  obtain ⟨hhorizontal, hvertical⟩ := cylinderDeck_mfderiv_preserves_factors
    Phi hdifferent hmetric p v a
  have hp : (v, a) = (v, 0) + (0, a) := by
    ext <;> simp
  calc
    mfderiv CylinderI CylinderI Phi p (v, a) =
        mfderiv CylinderI CylinderI Phi p (v, 0) +
          mfderiv CylinderI CylinderI Phi p (0, a) := by
      rw [hp]
      exact (mfderiv CylinderI CylinderI Phi p).map_add (v, 0) (0, a)
    _ = _ := by
      apply Prod.ext
      · change (mfderiv CylinderI CylinderI Phi p (v, 0)).1 +
          (mfderiv CylinderI CylinderI Phi p (0, a)).1 =
            (mfderiv CylinderI CylinderI Phi p (v, 0)).1
        rw [hvertical, add_zero]
      · change (mfderiv CylinderI CylinderI Phi p (v, 0)).2 +
          (mfderiv CylinderI CylinderI Phi p (0, a)).2 =
            (mfderiv CylinderI CylinderI Phi p (0, a)).2
        rw [hhorizontal, zero_add]

theorem cylinderDeck_mfderiv_block_norms (p : SphereTwo × ℝ)
    (v : TangentSpace (𝓡 2) p.1) (a : ℝ) :
    Real.sqrt ((sphereMetric).inner (Phi p).1
        (mfderiv CylinderI CylinderI Phi p (v, 0)).1
        (mfderiv CylinderI CylinderI Phi p (v, 0)).1) =
      Real.sqrt ((sphereMetric).inner p.1 v v) ∧
    |(mfderiv CylinderI CylinderI Phi p (0, a)).2| = |a| := by
  have hhorizontal := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p v v 0 0
  have hvertical := cylinderDeck_mfderiv_block_inner
    Phi hdifferent hmetric p (0 : TangentSpace (𝓡 2) p.1)
      (0 : TangentSpace (𝓡 2) p.1) a a
  refine ⟨congrArg Real.sqrt hhorizontal.1, ?_⟩
  apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
  simpa only [pow_two] using hvertical.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
