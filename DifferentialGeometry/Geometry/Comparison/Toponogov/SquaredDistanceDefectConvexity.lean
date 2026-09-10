/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Comparison.Toponogov.Convexity
import DifferentialGeometry.Geometry.Comparison.Toponogov.RealizedConnectors
import DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceSupport
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.CurveEnergy

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Topology
open scoped ENNReal Manifold ContDiff Topology

namespace Poincare.Toponogov

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open Poincare.Geometry
open Poincare.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

structure UnitSpeedGeodesicOn (g : SmoothRiemannianMetric I M)
    (beta : ℝ → M) (J : Set ℝ) : Prop where
  continuousOn : ContinuousOn beta J
  smoothOn_interior : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ beta (interior J)
  geodesicAt_shift : ∀ r ∈ J,
    IsGeodesicAt (I := I) g (fun s : ℝ ↦ beta (r + s)) 0
  unitSpeed : ∀ r ∈ J,
    g.inner (beta r)
      (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ)) = 1

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
theorem mfderiv_shift_zero_apply_one
    {beta : ℝ → M} {r : ℝ}
    (hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta r) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ beta (r + s)) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ) := by
  have hshift : HasDerivAt ((fun _ : ℝ ↦ r) + id) 1 0 :=
    by simpa only [zero_add] using
      (hasDerivAt_const (x := 0) r).add (hasDerivAt_id 0)
  have hbetaZero : MDifferentiableAt 𝓘(ℝ, ℝ) I beta (r + 0) := by
    simpa only [add_zero] using hbeta
  have hcomp := hbetaZero.hasMFDerivAt.comp 0 hshift.hasFDerivAt.hasMFDerivAt
  have happly := congrArg (fun D ↦ D (1 : ℝ)) hcomp.mfderiv
  change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ beta (r + s)) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, ℝ) I beta (r + 0)
      ((ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) 1) at happly
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at happly
  rw [add_zero] at happly
  exact happly

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
theorem riemannianDistance_le_sub_of_unitSpeed
    (g : SmoothRiemannianMetric I M) {beta : ℝ → M} {J : Set ℝ}
    (hJ : Convex ℝ J) (hbeta : UnitSpeedGeodesicOn (I := I) g beta J)
    {s t : ℝ} (hs : s ∈ interior J) (ht : t ∈ interior J) (hst : s ≤ t) :
    riemannianDistance (I := I) g (beta s) (beta t) ≤ t - s := by
  have hInteriorConvex : Convex ℝ (interior J) := hJ.interior
  have hIcc : Icc s t ⊆ interior J := hInteriorConvex.ordConnected.out hs ht
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 beta (Icc s t) :=
    (hbeta.smoothOn_interior.mono hIcc).of_le (by norm_num)
  let speedSq : ℝ → ℝ := fun u ↦
    g.inner (beta u)
      (mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ))
  have hspeed : Set.EqOn speedSq (fun _ : ℝ ↦ 1) (Icc s t) := by
    intro u hu
    exact hbeta.unitSpeed u (interior_subset (hIcc hu))
  have hspeedIntegrable : IntegrableOn speedSq (Icc s t) := by
    rw [integrableOn_congr_fun hspeed measurableSet_Icc]
    exact integrableOn_const measure_Icc_lt_top.ne
  have henergy : curveEnergy (I := I) g beta s t = t - s := by
    unfold curveEnergy
    calc
      ∫ u in s..t, speedSq u = ∫ _u in s..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hst] at hu
        exact hspeed hu
      _ = t - s := by simp
  have hsq := riemannianEDistOf_toReal_sq_le_curveEnergy
    (I := I) g hst hsmooth hspeedIntegrable
  rw [henergy] at hsq
  change riemannianDistance (I := I) g (beta s) (beta t) ^ 2 ≤
    (t - s) * (t - s) at hsq
  have hdistNonneg : 0 ≤ riemannianDistance (I := I) g (beta s) (beta t) :=
    ENNReal.toReal_nonneg
  have hsubNonneg : 0 ≤ t - s := sub_nonneg.mpr hst
  exact (sq_le_sq₀ hdistNonneg hsubNonneg).mp (by simpa [pow_two] using hsq)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem riemannianDistance_comm
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianDistance (I := I) g x y =
      riemannianDistance (I := I) g y x := by
  unfold riemannianDistance
  let : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  change (Manifold.riemannianEDist I x y).toReal =
    (Manifold.riemannianEDist I y x).toReal
  rw [Manifold.riemannianEDist_comm]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    [BoundarylessManifold I M] in
private theorem continuousOn_riemannianDistance_comp
    (g : SmoothRiemannianMetric I M) (p : M) {beta : ℝ → M} {J : Set ℝ}
    (hbeta : ContinuousOn beta J)
    (hfinite : ∀ r ∈ J, riemannianEDistOf (I := I) g p (beta r) ≠ ⊤) :
    ContinuousOn (fun r : ℝ ↦ riemannianDistance (I := I) g p (beta r)) J := by
  have hed : Continuous (fun q : M ↦ riemannianEDistOf (I := I) g p q) := by
    simpa only [riemannianEDistOf] using
      (continuous_riemannianEDist (I := I) g p)
  intro r hr
  unfold riemannianDistance
  have hcomp : ContinuousWithinAt
      ((fun q : M ↦ riemannianEDistOf (I := I) g p q) ∘ beta) J r :=
    hed.continuousAt.comp_continuousWithinAt (hbeta r hr)
  have hout := (ENNReal.continuousAt_toReal (hfinite r hr)).tendsto.comp hcomp
  change Tendsto (fun r : ℝ ↦ (riemannianEDistOf (I := I) g p (beta r)).toReal)
    (nhdsWithin r J) (nhds (riemannianEDistOf (I := I) g p (beta r)).toReal)
  simpa only [Function.comp_def] using hout

omit [T2Space (TangentBundle I M)] in
theorem squaredDistanceDefect_convexOn_of_realizedConnectors
    (g : SmoothRiemannianMetric I M)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    (p : M) (beta : ℝ → M) (J : Set ℝ)
    (hJ : Convex ℝ J)
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta J)
    (hconnectors : RealizedConnectors (I := I) g p beta J) :
    ConvexOn ℝ J (squaredRiemannianDistanceDefect (I := I) g p beta) := by
  have hfinite : ∀ r ∈ J,
      riemannianEDistOf (I := I) g p (beta r) ≠ ⊤ := by
    intro r hr
    obtain ⟨c⟩ := hconnectors r hr
    rw [c.realizes]
    exact ENNReal.ofReal_ne_top
  have hdistContinuous : ContinuousOn
      (fun r : ℝ ↦ riemannianDistance (I := I) g p (beta r)) J :=
    continuousOn_riemannianDistance_comp (I := I) g p hbeta.continuousOn hfinite
  have hdefectContinuous : ContinuousOn
      (squaredRiemannianDistanceDefect (I := I) g p beta) J := by
    exact (continuousOn_id.pow 2).sub (hdistContinuous.pow 2)
  apply convexOn_of_lowerSupport hJ hdefectContinuous
  intro r₀ hr₀
  apply Classical.choice
  let c := Classical.choice (hconnectors r₀ (interior_subset hr₀))
  rcases eq_or_lt_of_le c.length_nonneg with hzero | hpositive
  · have hp : p = beta r₀ := by
      calc
        p = c.curve 0 := c.source.symm
        _ = c.curve c.length := by rw [hzero]
        _ = beta r₀ := c.target
    have hdistZero : riemannianDistance (I := I) g p (beta r₀) = 0 := by
      rw [hp]
      unfold riemannianDistance
      rw [riemannianEDistOf_self, ENNReal.toReal_zero]
    have hlocal : ∀ᶠ r in 𝓝 r₀,
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
    obtain ⟨S, _hfirst, _hsecond⟩ :=
      exists_squaredDistanceLowerSupport_of_zero
        (I := I) g p beta J r₀ hr₀ hdistZero hlocal
    exact ⟨S⟩
  · let gamma := Classical.choice c.exists_smoothGeodesicRepresentative
    have hdist : riemannianDistance (I := I) g p (beta r₀) = c.length := by
      unfold riemannianDistance
      rw [c.realizes, ENNReal.toReal_ofReal c.length_nonneg]
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
    obtain ⟨S, _hfirst⟩ := exists_squaredDistanceLowerSupport_of_positive
      (I := I) g hsec p beta gamma.curve J r₀ c.length hr₀ hpositive
        gamma.smooth gamma.geodesicOn (gamma.unitSpeed_Icc hpositive)
        gamma.toSmoothRepresentative.source gamma.toSmoothRepresentative.target
        hdist v hv (hbeta.geodesicAt_shift r₀ (interior_subset hr₀)) hvel
    exact ⟨S⟩

theorem squaredDistanceDefect_convexOn_of_complete
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : HasNonnegativeSectionalCurvature (I := I) g)
    (p : M) (beta : ℝ → M) (J : Set ℝ)
    (hJ : Convex ℝ J)
    (hbeta : UnitSpeedGeodesicOn (I := I) g beta J) :
    ConvexOn ℝ J (squaredRiemannianDistanceDefect (I := I) g p beta) := by
  exact squaredDistanceDefect_convexOn_of_realizedConnectors
    (I := I) g hsec p beta J hJ hbeta
      (realizedConnectors_of_complete (I := I) g hcomplete p beta J)

end Poincare.Toponogov
