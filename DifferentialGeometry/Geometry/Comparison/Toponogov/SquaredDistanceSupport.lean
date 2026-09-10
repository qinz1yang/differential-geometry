/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Curvature.Nonnegative
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy
import DifferentialGeometry.Geometry.Comparison.Variation.RadialEndpoint
import DifferentialGeometry.Geometry.Comparison.Toponogov.ConnectorSmooth
import DifferentialGeometry.Geometry.Comparison.Toponogov.ConvexityBridge
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianComparisonAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.SupportAlgebra

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ENNReal Manifold ContDiff Topology
open DifferentialGeometry

namespace Poincare.Toponogov

open Poincare.Geometry
open Poincare.Geometry.Riemannian
open Poincare.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

def squaredRiemannianDistanceDefect (g : SmoothRiemannianMetric I M)
    (p : M) (β : ℝ → M) (r : ℝ) : ℝ :=
  r ^ 2 - riemannianDistance (I := I) g p (β r) ^ 2

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
theorem exists_squaredDistanceLowerSupport_of_positive
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    (p : M) (β γ : ℝ → M) (J : Set ℝ) (r₀ L : ℝ)
    (hJ : r₀ ∈ interior J) (hL : 0 < L)
    (hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγunit : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1)
    (hγ0 : γ 0 = p) (hγL : γ L = β r₀)
    (hdist : riemannianDistance (I := I) g p (β r₀) = L)
    (vL : TangentSpace I (γ L))
    (hvLunit : g.inner (γ L) vL vL = 1)
    (hβgeo : IsGeodesicAt (I := I) g (fun s : ℝ ↦ β (r₀ + s)) 0)
    (hβvel : (mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ ↦ β (r₀ + s)) 0 (1 : ℝ) : E) = vL) :
    ∃ S : LowerSupportAt
        (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
      S.supportDeriv r₀ =
        2 * r₀ - 2 * L * g.inner (γ L)
          (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ))
          vL ∧
      ∃ C : C2LowerSupportAt
          (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
        deriv C.support r₀ =
          2 * r₀ - 2 * L * g.inner (γ L)
            (mfderiv 𝓘(ℝ, ℝ) I γ L (1 : ℝ)) vL := by
  sorry

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem exists_squaredDistanceLowerSupport_of_zero
    (g : SmoothRiemannianMetric I M) (p : M) (β : ℝ → M)
    (J : Set ℝ) (r₀ : ℝ) (hJ : r₀ ∈ interior J)
    (hzero : riemannianDistance (I := I) g p (β r₀) = 0)
    (hlocal : ∀ᶠ r in 𝓝 r₀,
      riemannianDistance (I := I) g p (β r) ≤ |r - r₀|) :
    ∃ S : LowerSupportAt
        (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
      S.supportDeriv r₀ = 2 * r₀ ∧ S.supportSecondDeriv = 0 ∧
        ∃ C : C2LowerSupportAt
            (squaredRiemannianDistanceDefect (I := I) g p β) J r₀,
          deriv C.support r₀ = 2 * r₀ ∧
            deriv (deriv C.support) r₀ = 0 := by
  have hJnhds : J ∈ 𝓝 r₀ := mem_interior_iff_mem_nhds.mp hJ
  let U : Set ℝ :=
    {r | riemannianDistance (I := I) g p (β r) ≤ |r - r₀|} ∩ J
  have hU : U ∈ 𝓝 r₀ := inter_mem hlocal hJnhds
  have hUJ : U ⊆ J := inter_subset_right
  let S := lowerSupportAt_sq_sub_sq_of_zero hU hUJ
    (fun r _hr ↦ ENNReal.toReal_nonneg)
    (fun _r hr ↦ hr.1) hzero
  obtain ⟨left, right, hcenter, hinterval⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hU
  let C : C2LowerSupportAt
      (squaredRiemannianDistanceDefect (I := I) g p β) J r₀ :=
    { left := left
      right := right
      center_mem := hcenter
      interval_subset := fun r hr ↦ hUJ (hinterval hr)
      support := fun r ↦ 2 * r₀ * r - r₀ ^ 2
      contDiffOn_support :=
        ((contDiff_const.mul contDiff_id).sub contDiff_const).contDiffOn
      support_le := by
        intro r hr
        unfold squaredRiemannianDistanceDefect
        have hdistNonneg :
            0 ≤ riemannianDistance (I := I) g p (β r) := ENNReal.toReal_nonneg
        have hdistLe := (hinterval hr).1
        have hsq : riemannianDistance (I := I) g p (β r) ^ 2 ≤
            |r - r₀| ^ 2 :=
          (sq_le_sq₀ hdistNonneg (abs_nonneg _)).2 hdistLe
        rw [sq_abs] at hsq
        nlinarith
      support_eq := by
        unfold squaredRiemannianDistanceDefect
        rw [hzero]
        ring
      secondDeriv_nonneg := by
        simp }
  exact ⟨S, by simp [S, lowerSupportAt_sq_sub_sq_of_zero],
    by simp [S, lowerSupportAt_sq_sub_sq_of_zero], C, by simp [C], by simp [C]⟩

end Poincare.Toponogov
