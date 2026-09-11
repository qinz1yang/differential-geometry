/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianDistance
import DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceDefectConvexity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ENNReal Manifold ContDiff Topology

namespace DifferentialGeometry.Toponogov

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)]
    [BoundarylessManifold I M] in
theorem eq_of_riemannianDistance_eq_zero
    (g : SmoothRiemannianMetric I M) {p q : M}
    (hfinite : riemannianEDistOf (I := I) g p q ≠ ⊤)
    (hzero : riemannianDistance (I := I) g p q = 0) : p = q := by
  have hedist : riemannianEDistOf (I := I) g p q = 0 := by
    unfold riemannianDistance at hzero
    rw [ENNReal.toReal_eq_zero_iff] at hzero
    exact hzero.resolve_right hfinite
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  apply riemannianEDist_eq_zero_imp_eq (I := I) p q
  simpa only [riemannianEDistOf] using hedist

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
theorem eventually_riemannianDistance_le_abs_sub_of_unitSpeed
    (g : SmoothRiemannianMetric I M) (p : M) {beta : ℝ → M}
    {J : Set ℝ} {r₀ : ℝ} (hJ : Convex ℝ J)
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta J)
    (hr₀ : r₀ ∈ interior J) (hp : p = beta r₀) :
    ∀ᶠ r in 𝓝 r₀,
      riemannianDistance (I := I) g p (beta r) ≤ |r - r₀| := by
  filter_upwards [isOpen_interior.mem_nhds hr₀] with r hr
  rw [hp]
  rcases le_total r₀ r with hle | hle
  · simpa [abs_of_nonneg (sub_nonneg.mpr hle)] using
      riemannianDistance_le_sub_of_unitSpeed
        (I := I) g hJ hbeta hr₀ hr hle
  · rw [riemannianDistance_comm (I := I)]
    simpa [abs_of_nonpos (sub_nonpos.mpr hle)] using
      riemannianDistance_le_sub_of_unitSpeed
        (I := I) g hJ hbeta hr hr₀ hle

omit [T2Space (TangentBundle I M)] in
theorem exists_squaredDistanceC2LowerSupport
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    (p : M) (beta : ℝ → M) (J : Set ℝ) (r₀ : ℝ)
    (hJconvex : Convex ℝ J) (hr₀ : r₀ ∈ interior J)
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta J)
    (hfinite : riemannianEDistOf (I := I) g p (beta r₀) ≠ ⊤)
    (hconnector : 0 < riemannianDistance (I := I) g p (beta r₀) →
      Nonempty (RealizedMinimizingConnector (I := I) g p (beta r₀))) :
    ∃ C : C2LowerSupportAt
        (squaredRiemannianDistanceDefect (I := I) g p beta) J r₀,
      (riemannianDistance (I := I) g p (beta r₀) = 0 →
        deriv C.support r₀ = 2 * r₀ ∧
          deriv (deriv C.support) r₀ = 0) ∧
      (0 < riemannianDistance (I := I) g p (beta r₀) →
        ∃ c : RealizedMinimizingConnector (I := I) g p (beta r₀),
          c.length = riemannianDistance (I := I) g p (beta r₀) ∧
          ∃ gamma : SmoothGeodesicRepresentative (I := I) c,
            deriv C.support r₀ =
              2 * r₀ - 2 * c.length * g.inner (gamma.curve c.length)
                (mfderiv 𝓘(ℝ, ℝ) I gamma.curve c.length (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I beta r₀ (1 : ℝ))) := by
  let L := riemannianDistance (I := I) g p (beta r₀)
  have hLnonneg : 0 ≤ L := riemannianDistance_nonneg (I := I) g p (beta r₀)
  rcases hLnonneg.eq_or_lt with hzero | hpositive
  · have hzero' : riemannianDistance (I := I) g p (beta r₀) = 0 := by
      exact hzero.symm
    have hp : p = beta r₀ :=
      eq_of_riemannianDistance_eq_zero (I := I) g hfinite hzero'
    have hlocal := eventually_riemannianDistance_le_abs_sub_of_unitSpeed
      (I := I) g p hJconvex hbeta hr₀ hp
    obtain ⟨_S, _hfirst, _hsecond, C, hCfirst, hCsecond⟩ :=
      exists_squaredDistanceLowerSupport_of_zero
        (I := I) g p beta J r₀ hr₀ hzero' hlocal
    refine ⟨C, ?_, ?_⟩
    · intro _
      exact ⟨hCfirst, hCsecond⟩
    · intro hpos
      exact (hpos.ne' hzero').elim
  · obtain ⟨c⟩ := hconnector hpositive
    have hcLength : c.length = L := by
      rw [← c.riemannianDistance_eq_length]
    let gamma := Classical.choice c.exists_smoothGeodesicRepresentative
    have hbetaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I beta r₀ :=
      ((hbeta.smoothOn_interior r₀ hr₀).mdifferentiableWithinAt
        (by norm_num)).mdifferentiableAt (isOpen_interior.mem_nhds hr₀)
    have htarget : gamma.curve c.length = beta r₀ :=
      gamma.toSmoothRepresentative.target
    let v : TangentSpace I (gamma.curve c.length) :=
      (mfderiv 𝓘(ℝ, ℝ) I beta r₀ (1 : ℝ) : E)
    have hv : g.inner (gamma.curve c.length) v v = 1 := by
      rw [htarget]
      exact hbeta.unitSpeed r₀ (interior_subset hr₀)
    have hvel :
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ beta (r₀ + s)) 0 (1 : ℝ) : E) = v := by
      simpa only [v] using mfderiv_shift_zero_apply_one hbetaDiff
    obtain ⟨_S, _hfirst, C, hCfirst⟩ :=
      exists_squaredDistanceLowerSupport_of_positive
        (I := I) g hsec p beta gamma.curve J r₀ c.length hr₀
          (hcLength.symm ▸ hpositive) gamma.smooth gamma.geodesicOn
          (gamma.unitSpeed_Icc (hcLength.symm ▸ hpositive))
          gamma.toSmoothRepresentative.source gamma.toSmoothRepresentative.target
          c.riemannianDistance_eq_length v hv
          (hbeta.geodesicAt_shift r₀ (interior_subset hr₀)) hvel
    refine ⟨C, ?_, ?_⟩
    · intro hzero'
      exact (hpositive.ne' hzero').elim
    · intro _
      refine ⟨c, hcLength, gamma, ?_⟩
      simpa only [v] using hCfirst

end DifferentialGeometry.Toponogov
