import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.CompactTrajectory
import DifferentialGeometry.Geometry.Exponential.IntrinsicExpContinuity
import DifferentialGeometry.Geometry.Topology.FiberBundleT2

/-!
# The intrinsic geodesic velocity lift

This file packages the complete intrinsic geodesic as a trajectory in `TM`.
Its velocity lift starts at the supplied tangent vector and is an integral
curve of the globally smooth basepoint-free geodesic spray.
-/

noncomputable section

open Set Filter Topology Metric Bundle Manifold Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The tangent-bundle velocity lift of the complete intrinsic geodesic. -/
def intrinsicVelocityLift
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (s : ℝ) : TangentBundle I M :=
  ⟨intrinsicGeodesic (I := I) g hEnorm p v s,
    (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) s :
      ℝ →L[ℝ] TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p v s)) 1⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem velocityLift_proj
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (s : ℝ) :
    (intrinsicVelocityLift (I := I) g hEnorm p v s).proj =
      intrinsicGeodesic (I := I) g hEnorm p v s := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem velocityLift_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    intrinsicVelocityLift (I := I) g hEnorm p v 0 =
      (⟨p, v⟩ : TangentBundle I M) := by
  apply TotalSpace.ext
  · exact intrinsicGeodesic_zero (I := I) g hEnorm p v
  · apply heq_of_eq
    exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic velocity lift is an integral curve of the basepoint-free
geodesic spray. -/
theorem lift_isIntegral
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    IsMIntegralCurve (intrinsicVelocityLift (I := I) g hEnorm p v)
      (geodesicVectorField (I := I) g) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveAt]
  intro t
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v
  obtain ⟨f, hfproj_t, hf, hproj⟩ :=
    intrinsicGeodesic_hasGeodesicEquationAt_to_lift (I := I) g
      (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p v) t
  let alpha : M := gamma t
  have ht_src : (f t).proj ∈ (chartAt H alpha).source := by
    rw [hfproj_t]
    exact mem_chart_source H alpha
  have hproj_cont : ContinuousAt (fun s => (f s).proj) t :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hf.continuousAt
  have hsrc : ∀ᶠ s in nhds t, (f s).proj ∈ (chartAt H alpha).source :=
    hproj_cont.preimage_mem_nhds ((chartAt H alpha).open_source.mem_nhds ht_src)
  obtain ⟨S, hS, hfS⟩ := isMIntegralCurveAt_iff.mp hf
  obtain ⟨O, hOS, hOopen, htO⟩ := _root_.mem_nhds_iff.mp hS
  have hO : O ∈ nhds t := hOopen.mem_nhds htO
  have hf_eq_lift : f =ᶠ[nhds t]
      intrinsicVelocityLift (I := I) g hEnorm p v := by
    filter_upwards [hO, hproj, hsrc, hproj.eventually_nhds]
      with s hsO hsproj hfsrc hsproj_nhds
    have hf_at_s : IsMIntegralCurveAt f
        (geodesicVectorFieldChart (I := I) g alpha) s :=
      (hfS.mono hOS).isMIntegralCurveAt (hOopen.mem_nhds hsO)
    have hvel := hf_at_s.mfderiv_proj_one (I := I) hfsrc
    have hmf := Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(ℝ, ℝ)) (I' := I) hsproj_nhds
    rw [intrinsicVelocityLift]
    apply TotalSpace.ext hsproj.symm
    apply heq_of_eq
    rw [← hvel]
    exact congrArg (fun L => L 1) hmf.symm
  have hf_global : IsMIntegralCurveAt f (geodesicVectorField (I := I) g) t := by
    rw [IsMIntegralCurveAt] at hf ⊢
    filter_upwards [hf, hsrc] with s hs hfsrc
    rw [geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g alpha hfsrc] at hs
    exact hs
  rw [IsMIntegralCurveAt] at hf_global ⊢
  filter_upwards [hf_global, hf_eq_lift, hf_eq_lift.eventually_nhds]
    with s hs_int hs_eq hs_eq_nhds
  rw [← hs_eq]
  refine hs_int.congr_of_eventuallyEq ?_
  filter_upwards [hs_eq_nhds] with u hu
  exact hu.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The time-one intrinsic velocity lift depends smoothly on its initial tangent
vector. -/
theorem velocityLift_one
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    ContMDiff I.tangent I.tangent ∞
      (fun u : TangentBundle I M =>
        intrinsicVelocityLift (I := I) g hEnorm u.proj u.snd 1) := by
  have hslice :=
    DifferentialGeometry.PDE.RicciFlow.ODE.flow_slice_smooth
      (I := I.tangent) (v := geodesicVectorField (I := I) g)
      (Geodesic.geodesicVF_smooth (I := I) g)
      (D := Set.univ) isOpen_univ (a := (-1 : ℝ)) (b := 2) (t₀ := 0)
      (by norm_num)
      (F := fun u t => intrinsicVelocityLift (I := I) g hEnorm u.proj u.snd t)
      (by
        intro u _
        simp)
      (by
        intro u _
        exact (lift_isIntegral (I := I) g hEnorm u.proj u.snd).continuous.continuousOn)
      (by
        intro u _ t _
        exact lift_isIntegral (I := I) g hEnorm u.proj u.snd t)
  exact contMDiffOn_univ.mp (hslice 1 (by norm_num))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The complete intrinsic exponential is globally smooth on the tangent
bundle. -/
theorem intrinsicExp_smooth
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    ContMDiff I.tangent I ∞
      (fun u : TangentBundle I M =>
        expMapIntrinsic (I := I) g hEnorm u.proj u.snd) := by
  have hproj : ContMDiff I.tangent I ∞
      (fun u : TangentBundle I M =>
        (intrinsicVelocityLift (I := I) g hEnorm u.proj u.snd 1).proj) :=
    (contMDiff_proj (TangentSpace I)).comp (velocityLift_one (I := I) g hEnorm)
  simpa only [velocityLift_proj, expMapIntrinsic_def] using hproj

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- For a fixed basepoint, the intrinsic exponential map is globally smooth in
its tangent-vector argument. -/
theorem intrinsicFiber_smooth
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContMDiff 𝓘(ℝ, E) I ∞
      (fun v : E => expMapIntrinsic (I := I) g hEnorm p
        (show TangentSpace I p from v)) := by
  let e := trivializationAt E (TangentSpace I) p
  have hp : p ∈ e.baseSet := by
    change p ∈ (trivializationAt E (TangentSpace I) p).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have hpair : ContMDiff 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ∞
      (fun v : E => (p, v)) := contMDiff_const.prodMk contMDiff_id
  have hmaps : ∀ v : E, (p, v) ∈ e.target := by
    intro v
    rw [Bundle.Trivialization.target_eq]
    exact ⟨hp, Set.mem_univ _⟩
  have hsymm : ContMDiff 𝓘(ℝ, E) I.tangent ∞
      (fun v : E => e.toOpenPartialHomeomorph.symm (p, v)) := by
    apply contMDiffOn_univ.mp
    exact e.contMDiffOn_symm.comp hpair.contMDiffOn (fun v _ => hmaps v)
  have heq : (fun v : E => e.toOpenPartialHomeomorph.symm (p, v)) =
      (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
    funext v
    have hsrc : (⟨p, v⟩ : TangentBundle I M) ∈ e.source := by
      rw [e.mem_source]
      exact hp
    have heval : e.toOpenPartialHomeomorph (⟨p, v⟩ : TangentBundle I M) = (p, v) := by
      apply Prod.ext
      · rfl
      · exact Geodesic.chartFiberCoord_mk_self (I := I) p v
    rw [← heval]
    exact e.left_inv hsrc
  have htotal : ContMDiff 𝓘(ℝ, E) I.tangent ∞
      (fun v : E => (⟨p, v⟩ : TangentBundle I M)) := by
    rw [← heq]
    exact hsymm
  simpa only [Function.comp_apply] using
    (intrinsicExp_smooth (I := I) g hEnorm).comp htotal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesics launched from one point form a globally smooth
two-parameter variation under an affine change of initial velocity. -/
theorem intrinsicVar_smooth
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (x w : E) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : ℝ × ℝ =>
        intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from x + q.1 • w) q.2) := by
  let launch : ℝ × ℝ → E := fun q => q.2 • (x + q.1 • w)
  have hlaunch : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ launch :=
    contMDiff_snd.smul (contMDiff_const.add (contMDiff_fst.smul contMDiff_const))
  have htotal : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun q : ℝ × ℝ =>
        (⟨p, launch q⟩ : TangentBundle I M)) := by
    let e := trivializationAt E (TangentSpace I) p
    have hp : p ∈ e.baseSet := by
      change p ∈ (trivializationAt E (TangentSpace I) p).baseSet
      rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H p
    have hpair : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, E)) ∞ (fun q : ℝ × ℝ => (p, launch q)) :=
      contMDiff_const.prodMk hlaunch
    have hmaps : ∀ q : ℝ × ℝ, (p, launch q) ∈ e.target := by
      intro q
      rw [Bundle.Trivialization.target_eq]
      exact ⟨hp, Set.mem_univ _⟩
    have hsymm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
        (fun q : ℝ × ℝ => e.toOpenPartialHomeomorph.symm (p, launch q)) := by
      apply contMDiffOn_univ.mp
      exact e.contMDiffOn_symm.comp hpair.contMDiffOn (fun q _ => hmaps q)
    have heq : (fun q : ℝ × ℝ => e.toOpenPartialHomeomorph.symm (p, launch q)) =
        (fun q : ℝ × ℝ => (⟨p, launch q⟩ : TangentBundle I M)) := by
      funext q
      have hsrc : (⟨p, launch q⟩ : TangentBundle I M) ∈ e.source := by
        rw [e.mem_source]
        exact hp
      have heval : e.toOpenPartialHomeomorph (⟨p, launch q⟩ : TangentBundle I M) =
          (p, launch q) := by
        apply Prod.ext
        · rfl
        · exact Geodesic.chartFiberCoord_mk_self (I := I) p (launch q)
      rw [← heval]
      exact e.left_inv hsrc
    rw [← heq]
    exact hsymm
  have hcomp := (intrinsicExp_smooth (I := I) g hEnorm).comp htotal
  have heq :
      ((fun u : TangentBundle I M => expMapIntrinsic (I := I) g hEnorm u.proj u.snd) ∘
          (fun q : ℝ × ℝ => (⟨p, launch q⟩ : TangentBundle I M))) =
        (fun q : ℝ × ℝ =>
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + q.1 • w) q.2) := by
    funext q
    change intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from launch q) 1 =
      intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x + q.1 • w) q.2
    simpa only [launch] using
      intrinsicGeodesic_smul (I := I) g hEnorm p
        (show TangentSpace I p from x + q.1 • w) q.2
  rw [heq] at hcomp
  exact hcomp

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
