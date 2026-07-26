import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false

/-!
# Completeness of a smooth Riemannian metric

This file packages completeness of the extended distance induced by a smooth
Riemannian metric without choosing a basepoint.  It also transfers completeness
across a global uniform equivalence of smooth metrics.
-/

noncomputable section

universe u uE uH

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace DifferentialGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Completeness of the extended distance induced by a smooth Riemannian
metric, independently of any distinguished point. -/
structure RiemannianMetricComplete
    (g : SmoothRiemannianMetric I M) : Prop where
  complete :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M

namespace RiemannianMetricComplete

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Global uniform equivalence of smooth Riemannian metrics preserves
completeness. -/
theorem of_uniformEquiv
    {g h : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Real} (hC : 1 ≤ C)
    (hcomp : ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ C * g.inner x v v) :
    RiemannianMetricComplete (I := I) h := by
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  refine ⟨?_⟩

  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M

  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hCpos
  let a : ENNReal := ENNReal.ofReal (Real.sqrt C⁻¹)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hCinv))
  have hatop : a ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hdist : ∀ x y : M,
      a * riemannianEDistOf (I := I) g x y ≤
        riemannianEDistOf (I := I) h x y := by
    intro x y
    rw [← edistOf_scale (I := I) C⁻¹ hCinv g x y]
    exact edistOf_mono (I := I) _ _ (by
      intro z v
      simpa only [scaleMetric_inner] using (hcomp z v).1) x y

  refine EMetric.complete_of_cauchySeq_tendsto (α := M) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf (I := I) h (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change edist (s m) (s n) < ε
    exact hN m hm n hn

  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := hg.complete
  have hsSource : CauchySeq s := EMetric.cauchySeq_iff.mpr (by
    intro ε hε
    have haε : 0 < a * ε := ENNReal.mul_pos ha0 (ne_of_gt hε)
    obtain ⟨N, hN⟩ := hsTarget (a * ε) haε
    refine ⟨N, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I) g (s m) (s n) < ε
    apply (ENNReal.mul_lt_mul_iff_right ha0 hatop).mp
    exact lt_of_le_of_lt (hdist (s m) (s n)) (hN m hm n hn))
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsSource
  exact ⟨x, hx⟩

end RiemannianMetricComplete
end DifferentialGeometry

end
