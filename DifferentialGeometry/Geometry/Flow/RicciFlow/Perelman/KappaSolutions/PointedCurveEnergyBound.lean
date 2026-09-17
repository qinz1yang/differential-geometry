import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAmbientMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalCurveHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimMetricControl

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology Interval

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance curveBoundTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance curveBoundCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance curveBoundSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance curveBoundC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance curveBoundT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

private local instance curveBoundMetricTopology
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace F.M := F.topology
private local instance curveBoundMetricCharted
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H F.M := F.charted
private local instance curveBoundMetricSmooth
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ F.M := F.smooth
private local instance curveBoundMetricC1
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance curveBoundMetricT2
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space F.M := F.t2

theorem exists_pointed_curve_ricci_energy_bound
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (C : MetricConvergenceData (I := I) (Phi.atTime (L := L) 0))
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) 0) k)
    (gamma : ℝ → L.M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {a b : ℝ} (hb : b ≤ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ i in atTop,
      ∃ U : Set ℝ, IsOpen U ∧ Icc a b ⊆ U ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s => Phi.map i (gamma s)) U ∧
        ∀ s ∈ Icc a b,
          ‖smoothCurveRicciEnergy (X.term (phi i)).S
            (fun t => Phi.map i (gamma t)) (s, s)‖ ≤ B := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    have hdim := (hsource 0).dimension_ge_two
    omega⟩
  have hzero : (0 : ℝ) ∈ X.D.carrier := by
    rw [(hsource 0).carrier_eq]
    exact (le_rfl : (0 : ℝ) ≤ 0)
  let K : Set L.M := gamma '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image hgamma.continuous
  obtain ⟨C0, hC0, hscalar⟩ := exists_pointed_scalar_bound_on_compact C hcanonical K hK
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    rfl
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C href K hK 1 zero_lt_one
  let v : (t : ℝ) → TangentSpace I (gamma t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)
  let speedSq : ℝ → ℝ := fun t => (L.S.base.metric 0).inner (gamma t) (v t) (v t)
  have hv : Continuous (fun t : ℝ =>
      TotalSpace.mk' E (E := fun y : L.M => TangentSpace I y) (gamma t) (v t)) := by
    have h := MFDerivAlongCurve.continuous_tangentMap_unitLift
      (I := I) (M := L.M) (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  have hs : Continuous speedSq := by
    have heval := L.isSolution.smoothMetric.metricTensor_cont.eval_continuous
      (P := ℝ) (τ := fun _ => 0) (b := gamma)
      continuous_const (fun _ => hzero) hgamma.continuous
      (v := fun _i t => v t) (fun _i => hv)
    refine heval.congr (fun t => ?_)
    simp only [metricTensorField_apply]
    rfl
  obtain ⟨B0, hB0⟩ := (isCompact_Icc.image hs).bddAbove
  let Bv : ℝ := 2 * (max B0 0 + 1)
  have hBv : 0 < Bv := by dsimp only [Bv]; positivity
  refine ⟨((C0 / 2) * Real.exp (C0 * (-a))) * Bv, by positivity, ?_⟩
  filter_upwards [hscalar, Filter.eventually_ge_atTop k0] with i hi hik
  let U : Set ℝ := gamma ⁻¹' Phi.source i
  have hU : IsOpen U := (Phi.source_open i).preimage hgamma.continuous
  have hcurve : Icc a b ⊆ U := fun t ht => hi.1 ⟨t, ht, rfl⟩
  have hlocal : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun s => Phi.map i (gamma s)) U := by
    exact ((Phi.partialDiffeomorph i).contMDiffOn_toFun.of_le (by simp)).comp
      hgamma.contMDiffOn subset_rfl
  refine ⟨U, hU, hcurve, hlocal, fun s hsab => ?_⟩
  have hpoint : gamma s ∈ K := ⟨s, hsab, rfl⟩
  have hmap : MDifferentiableAt I I (Phi.map i) (gamma s) :=
    ((Phi.partialDiffeomorph i).contMDiffOn_toFun.contMDiffAt
      ((Phi.source_open i).mem_nhds (hi.1 hpoint))).mdifferentiableAt (by simp)
  have hvelocity : mfderiv 𝓘(ℝ, ℝ) I (fun t => Phi.map i (gamma t)) s (1 : ℝ) =
      mfderiv I I (Phi.map i) (gamma s) (v s) := by
    change mfderiv 𝓘(ℝ, ℝ) I (Phi.map i ∘ gamma) s (1 : ℝ) = _
    rw [mfderiv_comp s hmap (hgamma.mdifferentiableAt (x := s) (by norm_num))]
    rfl
  have hquad := (hk0 i hik).2 (gamma s) hpoint (v s)
  have hspeed : (L.S.base.metric 0).inner (gamma s) (v s) (v s) ≤ max B0 0 + 1 :=
    (hB0 ⟨s, hsab, rfl⟩).trans (by linarith [le_max_left B0 0])
  have hspeedSource : ((X.term (phi i)).S.base.metric 0).inner (Phi.map i (gamma s))
      (mfderiv I I (Phi.map i) (gamma s) (v s))
      (mfderiv I I (Phi.map i) (gamma s) (v s)) ≤ Bv := by
    have hupper := (abs_le.mp hquad).2
    change _ ≤ 2 * (max B0 0 + 1)
    change ((X.term (phi i)).S.base.metric 0).inner (Phi.map i (gamma s))
        (mfderiv I I (Phi.map i) (gamma s) (v s))
        (mfderiv I I (Phi.map i) (gamma s) (v s)) -
      (L.S.base.metric 0).inner (gamma s) (v s) (v s) ≤
        (1 : ℝ) * (L.S.base.metric 0).inner (gamma s) (v s) (v s) at hupper
    linarith
  have hscalarSource : (X.term (phi i)).S.scalar 0 (Phi.map i (gamma s)) ≤ C0 :=
    (le_abs_self _).trans (hi.2 (gamma s) hpoint)
  have hbound := (hsource (phi i)).ricci_energy_bound_on_backward_slab
    (s := s) (a := a) ⟨hsab.1, hsab.2.trans hb⟩ (Phi.map i (gamma s)) hscalarSource
      (mfderiv I I (Phi.map i) (gamma s) (v s)) hspeedSource
  change ‖metricRicciAt (I := I) ((X.term (phi i)).S.base.metric s) (Phi.map i (gamma s))
    (vec2 (mfderiv I I (Phi.map i) (gamma s) (v s))
      (mfderiv I I (Phi.map i) (gamma s) (v s)))‖ ≤ _ at hbound
  rw [metricRicciAt_apply_eq_ricciTensor] at hbound
  simpa only [smoothCurveRicciEnergy, hvelocity] using hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
