import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientCriticalSet
import Mathlib.LinearAlgebra.Complex.Module

noncomputable section

open Set Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

/-- A weakly conformal disk differential is injective precisely when it is nonzero.
The metric in the conformality hypothesis is the original target metric. -/
theorem DiskMapConformalAt.injective_mfderiv_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) ↔
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z ≠ 0 := by
  let D : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U z) :=
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  change Function.Injective D ↔ D ≠ 0
  have horth : g.inner (U z) (D 1) (D Complex.I) = 0 := h.1
  have hlen : g.inner (U z) (D 1) (D 1) =
      g.inner (U z) (D Complex.I) (D Complex.I) := h.2
  have hD_apply (v : ℂ) : D v = v.re • D 1 + v.im • D Complex.I := by
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
    calc
      D v = D (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg D hv
      _ = _ := by rw [map_add, map_smul, map_smul]
  constructor
  · intro hinj hzero
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    apply hinj
    simp only [hzero, zero_apply]
  · intro hnonzero
    have hOne : D 1 ≠ 0 := by
      intro hzero
      have hI : D Complex.I = 0 := by
        by_contra hI
        have hpos := g.pos (U z) (D Complex.I) hI
        have heq : g.inner (U z) (D Complex.I) (D Complex.I) = 0 := by
          rw [← hlen, hzero]
          simp only [map_zero]
        exact (ne_of_gt hpos) heq
      apply hnonzero
      ext v
      simp only [hD_apply v, hzero, hI, smul_zero, add_zero,
        zero_apply]
    have hpos : 0 < g.inner (U z) (D 1) (D 1) := g.pos (U z) (D 1) hOne
    have horth' : g.inner (U z) (D Complex.I) (D 1) = 0 := by
      rw [g.symm]
      exact horth
    have hmetric (v : ℂ) :
        g.inner (U z) (D v) (D v) =
          (v.re ^ 2 + v.im ^ 2) * g.inner (U z) (D 1) (D 1) := by
      rw [hD_apply v]
      simp only [map_add, map_smul, add_apply,
        smul_apply, smul_eq_mul]
      rw [horth, horth', ← hlen]
      ring
    intro v w hvw
    have hzero : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hsq : (v - w).re ^ 2 + (v - w).im ^ 2 = 0 := by
      have hh := hmetric (v - w)
      rw [hzero] at hh
      simp only [map_zero] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt hpos)
    have hre : (v - w).re = 0 := by nlinarith [sq_nonneg (v - w).im]
    have him : (v - w).im = 0 := by nlinarith [sq_nonneg (v - w).re]
    exact sub_eq_zero.mp (Complex.ext hre him)

/-- The original Morrey disk has finitely many noninjective differentials on
any compact subset of its interior. -/
theorem IsMorreyDisk.finite_not_injective_mfderiv_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ ball (0 : ℂ) 1) :
    {z ∈ K | ¬ Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)}.Finite := by
  apply (hu.finite_mfderiv_eq_zero_of_isCompact hγ hK hKD).subset
  intro z hz
  refine ⟨hz.1, ?_⟩
  by_contra hnonzero
  exact hz.2 ((hu.conformal z (hKD hz.1)).injective_mfderiv_iff.mpr hnonzero)

end DifferentialGeometry.Geometry
