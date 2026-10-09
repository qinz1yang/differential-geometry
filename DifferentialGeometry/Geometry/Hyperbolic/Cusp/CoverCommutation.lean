/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveMetric
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Rigidity

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₃" => Fin 3 → ℝ
local notation "V₂" => Fin 2 → ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {H : FiniteVolumeHyperbolicModel}

theorem positiveMap_eq_cover_comp_of_first_jet (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) {q : V₂ → Torus}
    (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (P : Hyperboloid E₃ → H.Carrier)
    (hP : IsLocalDiffeomorph 𝓘(ℝ, E₃) (𝓡 3) ∞ P)
    (hPmetric : ∀ (y : Hyperboloid E₃) (v w : E₃),
      Hyperboloid.riemannianMetric.inner y v w =
        (scaleMetric (-(-(1 / 4 : ℝ)))
          (neg_pos.mpr (by norm_num : -(1 / 4 : ℝ) < 0)) H.metric).inner (P y)
          (mfderiv 𝓘(ℝ, E₃) (𝓡 3) P y v)
          (mfderiv 𝓘(ℝ, E₃) (𝓡 3) P y w))
    (hPbase : P Hyperboloid.origin = positiveMap Tr i q (basePoint r₀ hr₀))
    (hPjet : ∀ v : E₃,
      mfderiv 𝓘(ℝ, E₃) (𝓡 3) P Hyperboloid.origin v =
        comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀) v) :
    positiveMap Tr i q = P ∘ positiveModel r₀ := by
  have hcomp : IsLocalDiffeomorph 𝓘(ℝ, V₃) (𝓡 3) ∞ (P ∘ positiveModel r₀) :=
    isLocalDiffeomorph_comp hP (positiveModel_isLocalDiffeomorph r₀)
  have hderiv (x : positiveDepth) (v : V₃) :
      mfderiv 𝓘(ℝ, V₃) (𝓡 3) (P ∘ positiveModel r₀) x v =
        mfderiv 𝓘(ℝ, E₃) (𝓡 3) P (positiveModel r₀ x)
          (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) x v) := by
    rw [mfderiv_comp x
      (hP.contMDiff.mdifferentiableAt (x := positiveModel r₀ x) (by simp))
      ((positiveModel_contMDiff r₀).mdifferentiableAt (by simp))]
    rfl
  have hpres (x : positiveDepth) (v w : V₃) :
      positiveMetric.inner x v w =
        (scaleMetric (-(-(1 / 4 : ℝ)))
          (neg_pos.mpr (by norm_num : -(1 / 4 : ℝ) < 0)) H.metric).inner
            ((P ∘ positiveModel r₀) x)
          (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (P ∘ positiveModel r₀) x v)
          (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (P ∘ positiveModel r₀) x w) := by
    rw [hderiv x v, hderiv x w]
    exact (positiveModel_preserves_positiveMetric r₀ x v w).trans
      (hPmetric (positiveModel r₀ x) _ _)
  have hb : positiveModel r₀ (basePoint r₀ hr₀) = Hyperboloid.origin :=
    Horospherical.shiftedModel_base r₀
  apply Geometry.Riemannian.localIso_rigid positiveMetric
    (scaleMetric (-(-(1 / 4 : ℝ)))
      (neg_pos.mpr (by norm_num : -(1 / 4 : ℝ) < 0)) H.metric)
    (positiveMap_isLocalDiffeomorph Tr i hq hqmetric) hcomp
    (positiveMap_preserves_positiveMetric Tr i hq hqmetric) hpres (basePoint r₀ hr₀)
  · change positiveMap Tr i q (basePoint r₀ hr₀) = P (positiveModel r₀ (basePoint r₀ hr₀))
    rw [hb, hPbase]
  · ext v
    have hm := congrArg (fun L : V₃ →L[ℝ] E₃ => L v)
      (positiveModel_mfderiv r₀ (basePoint r₀ hr₀))
    have ht := congrArg (fun y : Hyperboloid E₃ =>
      (mfderiv 𝓘(ℝ, E₃) (𝓡 3) P y
        (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) (basePoint r₀ hr₀) v) : E₃)) hb
    have hf :
        (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) (basePoint r₀ hr₀) v : E₃) =
          comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀)
            (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (Horospherical.shiftedModel r₀)
              (basePoint r₀ hr₀).val v) :=
      (comparisonFrame_comp_model_derivative Tr i hq hqmetric
        r₀ (basePoint r₀ hr₀) v).symm
    have hmodel :
        (comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀)
          (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (Horospherical.shiftedModel r₀)
            (basePoint r₀ hr₀).val v) : E₃) =
          comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀)
            (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) (basePoint r₀ hr₀) v) :=
      congrArg (fun w : E₃ =>
        (comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀) w : E₃)) hm.symm
    have hj :
        (comparisonFrame Tr i hq hqmetric r₀ (basePoint r₀ hr₀)
          (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) (basePoint r₀ hr₀) v) : E₃) =
          mfderiv 𝓘(ℝ, E₃) (𝓡 3) P Hyperboloid.origin
            (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) (basePoint r₀ hr₀) v) :=
      (hPjet _).symm
    exact hf.trans (hmodel.trans (hj.trans (ht.symm.trans (hderiv (basePoint r₀ hr₀) v).symm)))

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
