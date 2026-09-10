import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace Poincare.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_minimal_displacement_geodesic
    (g : SmoothRiemannianMetric I M) (F : M → M)
    (hF : Continuous F) (hfree : ∀ x, F x ≠ x) :
    ∃ (p : M) (L : ℝ) (γ : ℝ → M),
      0 < L ∧
      riemannianEDistOf (I := I) g p (F p) = ENNReal.ofReal L ∧
      (∀ x, L ≤ (riemannianEDistOf (I := I) g x (F x)).toReal) ∧
      γ 0 = p ∧ γ L = F p ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ IsGeodesic (I := I) g γ ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      curveEnergy (I := I) g γ 0 L = L ∧
      (∀ c : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc 0 L) →
        IntegrableOn (fun t => g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)
          (mfderiv 𝓘(ℝ, ℝ) I c t 1)) (Icc 0 L) →
        c L = F (c 0) → L ≤ curveEnergy (I := I) g c 0 L) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hcompat : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hfinite (x y : M) : edist x y ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x y
  have hcont : Continuous (fun x => (edist x (F x)).toReal) :=
    continuous_iff_continuousAt.mpr fun x =>
      (ENNReal.continuousAt_toReal (hfinite x (F x))).comp (f := fun y : M => edist y (F y)) (g := ENNReal.toReal) (x := x)
        (continuous_id.edist hF).continuousAt
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  let L := (edist p (F p)).toReal
  have hL : 0 < L := ENNReal.toReal_pos (fun h => hfree p (edist_eq_zero.mp h).symm) (hfinite _ _)
  have hmin (x : M) : L ≤ (riemannianEDistOf (I := I) g x (F x)).toReal := hp (mem_univ x)
  obtain ⟨v, hv, hnorm⟩ := minExp_of_ne_top (I := I) g hcompat p (F p) (hfinite _ _)
  let w : TangentSpace I p := L⁻¹ • v
  let γ := intrinsicGeodesic (I := I) g hcompat p w
  have hscale : L • w = v := by simp [w, smul_smul, ne_of_gt hL]
  have hw : g.inner p w w = 1 := by
    have hvv : g.inner p v v = L ^ 2 := by
      rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hnorm]
      rfl
    rw [gInner_smul_self, hvv, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hL), one_pow]
  have hspeed (t : ℝ) : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hcompat p w t).trans hw
  refine ⟨p, L, γ, hL, (ENNReal.ofReal_toReal (hfinite _ _)).symm, hmin,
    intrinsicGeodesic_zero (I := I) g hcompat p w, ?_,
    intrinsicGeodesic_contMDiff (I := I) g hcompat p w,
    intrinsicGeodesic_isGeodesic (I := I) g hcompat p w, hspeed, ?_, ?_⟩
  · change intrinsicGeodesic (I := I) g hcompat p w L = F p
    rw [← intrinsicGeodesic_smul (I := I) g hcompat p w L]
    change expMapIntrinsic (I := I) g hcompat p (L • w) = F p
    rw [hscale]
    exact hv
  · change (∫ t in (0 : ℝ)..L, g.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)) = L
    simp only [hspeed, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  · intro c hc hE htwist
    have hb := riemannianEDistOf_toReal_sq_le_curveEnergy g hL.le hc hE
    have hm := hmin (c 0)
    rw [← htwist] at hm
    simp only [sub_zero] at hb
    have hs := sq_le_sq₀ hL.le ENNReal.toReal_nonneg |>.mpr hm
    nlinarith

end Poincare.Geometry.Riemannian
