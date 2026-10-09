/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveDepthMap
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ShiftedModelFrame

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₃" => Fin 3 → ℝ
local notation "V₂" => Fin 2 → ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H : FiniteVolumeHyperbolicModel}

theorem positiveMap_mfderiv_injective (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (x : positiveDepth) :
    Function.Injective (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x) := by
  apply (injective_iff_map_eq_zero
    (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x)).mpr
  intro u hu
  have hm := positiveMap_metric Tr i hq hqmetric x u u
  rw [hu] at hm
  simp only [map_zero] at hm
  have he : 0 < Real.exp (-x.val 0) := Real.exp_pos _
  have hnonneg : 0 ≤ Real.exp (-x.val 0) * ((u 1)^2 + (u 2)^2) :=
    mul_nonneg he.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have h₀ : (u 0)^2 = 0 := by nlinarith [sq_nonneg (u 0)]
  have hweighted : Real.exp (-x.val 0) * ((u 1)^2 + (u 2)^2) = 0 := by
    nlinarith
  have hsum : (u 1)^2 + (u 2)^2 = 0 :=
    (mul_eq_zero.mp hweighted).resolve_left (Real.exp_ne_zero _)
  have h₁ : u 1 = 0 := by nlinarith [sq_nonneg (u 2)]
  have h₂ : u 2 = 0 := by nlinarith [sq_nonneg (u 1)]
  funext j
  fin_cases j
  · exact sq_eq_zero_iff.mp h₀
  · exact h₁
  · exact h₂

def positiveMapTangentEquiv (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (x : positiveDepth) : V₃ ≃L[ℝ] TangentSpace (𝓡 3) (positiveMap Tr i q x) := by
  let A : V₃ →L[ℝ] E₃ := mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x
  have hi : Function.Injective A := positiveMap_mfderiv_injective Tr i hq hqmetric x
  have hs : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := V₃) («V₂» := E₃) (f := A.toLinearMap) (by simp)).mp hi
  exact ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)

theorem positiveMapTangentEquiv_apply (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (x : positiveDepth) (v : V₃) :
    positiveMapTangentEquiv Tr i hq hqmetric x v =
      mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x v := rfl

theorem positiveMap_isLocalDiffeomorph (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1) :
    IsLocalDiffeomorph 𝓘(ℝ, V₃) (𝓡 3) ∞ (positiveMap Tr i q) := by
  intro x
  apply
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      (positiveMap Tr i q) (U := Set.univ)
      (positiveMap_contMDiff Tr i hq).contMDiffOn isOpen_univ x
      (Set.mem_univ x) (positiveMapTangentEquiv Tr i hq hqmetric x)
  change HasMFDerivAt 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x
    (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x)
  exact ((positiveMap_contMDiff Tr i hq).mdifferentiableAt (by simp)).hasMFDerivAt

theorem exists_cover_projection_with_positiveMap (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) :
    ∃ q : V₂ → Torus,
      IsCoveringMap q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph 𝓘(ℝ, V₂) torusModel ∞ q ∧
      (∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
        (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
          v 0 * w 0 + v 1 * w 1) ∧
      IsLocalDiffeomorph 𝓘(ℝ, V₃) (𝓡 3) ∞ (positiveMap Tr i q) := by
  obtain ⟨q, hcover, hsurj, hlocal, hmetric⟩ :=
    (Tr.cusp i).exists_orthonormal_cover_projection
  exact ⟨q, hcover, hsurj, hlocal, hmetric,
    positiveMap_isLocalDiffeomorph Tr i hlocal.contMDiff hmetric⟩

def comparisonFrame (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (r₀ : ℝ) (x : positiveDepth) :
    E₃ ≃L[ℝ] TangentSpace (𝓡 3) (positiveMap Tr i q x) :=
  (Horospherical.shiftedModelTangentEquiv r₀ x.val).symm.trans
    (positiveMapTangentEquiv Tr i hq hqmetric x)

theorem comparisonFrame_comp_model_derivative (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) {q : V₂ → Torus}
    (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (r₀ : ℝ) (x : positiveDepth) (v : V₃) :
    comparisonFrame Tr i hq hqmetric r₀ x
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (Horospherical.shiftedModel r₀) x.val v) =
        mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x v := by
  change positiveMapTangentEquiv Tr i hq hqmetric x
    ((Horospherical.shiftedModelTangentEquiv r₀ x.val).symm
      (Horospherical.shiftedModelTangentEquiv r₀ x.val v)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem comparisonFrame_metric (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (r₀ : ℝ) (x : positiveDepth) (v w : E₃) :
    (1 / 4) * H.metric.inner (positiveMap Tr i q x)
      (comparisonFrame Tr i hq hqmetric r₀ x v)
      (comparisonFrame Tr i hq hqmetric r₀ x w) =
        Hyperboloid.riemannianMetric.inner (Horospherical.shiftedModel r₀ x.val) v w := by
  let L := Horospherical.shiftedModelTangentEquiv r₀ x.val
  have hL (u : E₃) :
      mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (Horospherical.shiftedModel r₀) x.val (L.symm u) = u := by
    change L (L.symm u) = u
    exact L.apply_symm_apply u
  have hm := Horospherical.shiftedModel_metric r₀ x.val (L.symm v) (L.symm w)
  rw [hL v, hL w] at hm
  change (1 / 4) * H.metric.inner (positiveMap Tr i q x)
    (positiveMapTangentEquiv Tr i hq hqmetric x (L.symm v))
    (positiveMapTangentEquiv Tr i hq hqmetric x (L.symm w)) = _
  rw [positiveMapTangentEquiv_apply, positiveMapTangentEquiv_apply,
    positiveMap_metric Tr i hq hqmetric]
  exact hm.symm

def basePoint (r₀ : ℝ) (hr₀ : 0 < r₀) : positiveDepth :=
  ⟨![r₀, 0, 0], hr₀⟩

theorem comparisonFrame_base_metric (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (v w : E₃) :
    (1 / 4) * H.metric.inner (positiveMap Tr i q (basePoint r₀ hr₀))
      (comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀) v)
      (comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀) w) = inner ℝ v w := by
  have h := comparisonFrame_metric Tr i hq hqmetric r₀ (basePoint r₀ hr₀) v w
  have hb : Horospherical.shiftedModel r₀ (basePoint r₀ hr₀).val =
      Hyperboloid.origin := Horospherical.shiftedModel_base r₀
  calc
    _ = Hyperboloid.riemannianMetric.inner
        (Horospherical.shiftedModel r₀ (basePoint r₀ hr₀).val) v w := h
    _ = Hyperboloid.riemannianMetric.inner Hyperboloid.origin v w :=
      congrArg (fun y : Hyperboloid E₃ => Hyperboloid.riemannianMetric.inner y v w) hb
    _ = inner ℝ v w := by
      change inner ℝ v w - (1 + ‖(0 : E₃)‖ ^ 2)⁻¹ *
        (inner ℝ (0 : E₃) v * inner ℝ (0 : E₃) w) = inner ℝ v w
      simp

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
