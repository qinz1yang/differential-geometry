/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveDepthFrame
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₃" => Fin 3 → ℝ
local notation "V₂" => Fin 2 → ℝ
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

instance positiveDepth_preconnected : PreconnectedSpace positiveDepth := by
  apply isPreconnected_iff_preconnectedSpace.mp
  exact ((convex_Ioi (0 : ℝ)).linear_preimage
    (ContinuousLinearMap.proj 0 : V₃ →L[ℝ] ℝ).toLinearMap).isPreconnected

def positiveModel (r₀ : ℝ) : positiveDepth → Hyperboloid E₃ :=
  fun x => Horospherical.shiftedModel r₀ x.val

theorem positiveModel_contMDiff (r₀ : ℝ) :
    ContMDiff 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ (positiveModel r₀) :=
  (Horospherical.contMDiff_shiftedModel r₀).comp contMDiff_subtype_val

theorem positiveModel_mfderiv (r₀ : ℝ) (x : positiveDepth) :
    mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) x =
      mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (Horospherical.shiftedModel r₀) x.val :=
  mfderiv_restrict_open (Horospherical.shiftedModel r₀) positiveDepth x

theorem positiveModel_isLocalDiffeomorph (r₀ : ℝ) :
    IsLocalDiffeomorph 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) ∞ (positiveModel r₀) := by
  intro x
  apply
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      (positiveModel r₀) (U := Set.univ)
      (positiveModel_contMDiff r₀).contMDiffOn isOpen_univ x (Set.mem_univ x)
      (Horospherical.shiftedModelTangentEquiv r₀ x.val)
  have hd := ((positiveModel_contMDiff r₀).mdifferentiableAt (x := x) (by simp)).hasMFDerivAt
  rw [positiveModel_mfderiv] at hd
  exact hd

theorem positiveModel_metric (r₀ : ℝ) (x : positiveDepth) (v w : V₃) :
    Hyperboloid.riemannianMetric.inner (positiveModel r₀ x)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) x v)
      (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) x w) =
        (1 / 4) * (v 0 * w 0 + Real.exp (-x.val 0) *
          (v 1 * w 1 + v 2 * w 2)) := by
  rw [positiveModel_mfderiv]
  exact Horospherical.shiftedModel_metric r₀ x.val v w

def positiveMetric : SmoothRiemannianMetric 𝓘(ℝ, V₃) positiveDepth :=
  localPullMetric Hyperboloid.riemannianMetric (positiveModel 0)
    (positiveModel_isLocalDiffeomorph 0)

theorem positiveMetric_inner (x : positiveDepth) (v w : V₃) :
    positiveMetric.inner x v w =
      (1 / 4) * (v 0 * w 0 + Real.exp (-x.val 0) *
        (v 1 * w 1 + v 2 * w 2)) := by
  exact (localPullMetric_inner Hyperboloid.riemannianMetric (positiveModel 0)
    (positiveModel_isLocalDiffeomorph 0) x v w).trans (positiveModel_metric 0 x v w)

theorem positiveModel_preserves_positiveMetric (r₀ : ℝ)
    (x : positiveDepth) (v w : V₃) :
    positiveMetric.inner x v w =
      Hyperboloid.riemannianMetric.inner (positiveModel r₀ x)
        (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) x v)
        (mfderiv 𝓘(ℝ, V₃) 𝓘(ℝ, E₃) (positiveModel r₀) x w) := by
  rw [positiveMetric_inner, positiveModel_metric]

variable {H : FiniteVolumeHyperbolicModel}

theorem positiveMap_preserves_positiveMetric (Tr : HyperbolicTruncation H)
    (i : Fin Tr.count) {q : V₂ → Torus}
    (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (x : positiveDepth) (v w : V₃) :
    positiveMetric.inner x v w =
      (scaleMetric (- (-(1 / 4 : ℝ)))
        (neg_pos.mpr (by norm_num : -(1 / 4 : ℝ) < 0)) H.metric).inner
          (positiveMap Tr i q x)
        (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x v)
        (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x w) := by
  rw [positiveMetric_inner, scaleMetric_inner, neg_neg, positiveMap_metric Tr i hq hqmetric]

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
