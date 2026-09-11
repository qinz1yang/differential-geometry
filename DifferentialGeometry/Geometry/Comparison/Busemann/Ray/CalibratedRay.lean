import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.Busemann
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Metric

private theorem busemann_tendsto_moving_point
    {M : Type*} [PseudoMetricSpace M] {gamma : ℝ → M}
    (hgamma : Isometry gamma) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {y : ℕ → M} {z : M} (hy : Tendsto y atTop (𝓝 z)) :
    Tendsto (fun i ↦ dist (y i) (gamma (T i)) - T i) atTop
      (𝓝 (busemannFunction gamma z)) := by
  have hfixed := (busemannFunction_tendsto hgamma z).comp hT
  have hbound (i : ℕ) :
      dist (((fun t : ℝ ↦ dist z (gamma t) - t) ∘ T) i)
        (dist (y i) (gamma (T i)) - T i) ≤ dist z (y i) := by
    simpa only [Function.comp_apply, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_dist_sub_le z (y i) (gamma (T i))
  have hzero : Tendsto (fun i ↦ dist z (y i)) atTop (𝓝 0) := by
    simpa only [dist_self] using
      (tendsto_const_nhds.dist hy :
        Tendsto (fun i ↦ dist z (y i)) atTop (𝓝 (dist z z)))
  exact hfixed.congr_dist (squeeze_zero (fun _ ↦ dist_nonneg) hbound hzero)

section CompatibleMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem fixed_fiber_unit_compact
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsCompact {v : E | g.inner x (show TangentSpace I x from v) v = 1} :=
  gUnitSphere_isCompact g x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem fixed_fiber_geodesic_eval_continuous
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (x : M) (s : ℝ) :
    Continuous (fun v : E ↦ intrinsicGeodesic g hEnorm x
      (show TangentSpace I x from v) s) := by
  have hexp := (intrinsicFiber_smooth g hEnorm x).continuous.comp
    (continuous_const.smul continuous_id : Continuous (fun v : E ↦ s • v))
  apply hexp.congr
  intro v
  change expMapIntrinsic g hEnorm x (s • v) = intrinsicGeodesic g hEnorm x v s
  exact (expMapIntrinsic_def g hEnorm x (s • (show TangentSpace I x from v))).trans
    (intrinsicGeodesic_smul g hEnorm x v s)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem unit_geodesic_dist_le
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (x : M) (v : TangentSpace I x) (hv : g.inner x v v = 1)
    {s t : ℝ} (hst : s ≤ t) :
    dist (intrinsicGeodesic g hEnorm x v s) (intrinsicGeodesic g hEnorm x v t)
      ≤ t - s := by
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm x v hst
  rw [hv, Real.sqrt_one, one_mul] at h
  apply (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hst)).mp
  rw [← edist_dist, IsRiemannianManifold.out (I := I)]
  exact h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem normalized_minimizing_vector
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (x q : M) (hxq : x ≠ q) :
    ∃ v : E, g.inner x (show TangentSpace I x from v) v = 1 ∧
      intrinsicGeodesic g hEnorm x v (dist x q) = q := by
  have hfin : riemannianEDist I x q ≠ (⊤ : ENNReal) := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x q
  obtain ⟨w, hw, hlength⟩ := minExp_of_ne_top g hEnorm x q hfin
  have hlength' : Real.sqrt (g.inner x w w) = dist x q := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hlength
    exact hlength
  have hd : 0 < dist x q := dist_pos.mpr hxq
  have hww : g.inner x w w = dist x q ^ 2 := by
    rw [← hlength', Real.sq_sqrt (gInner_self_nonneg g x w)]
  let v : TangentSpace I x := (dist x q)⁻¹ • w
  have hv : g.inner x v v = 1 := by
    dsimp only [v]
    rw [gInner_smul_self, hww, ← mul_pow, inv_mul_cancel₀ hd.ne', one_pow]
  refine ⟨v, hv, ?_⟩
  have hscale : dist x q • v = w := by
    dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  rw [← intrinsicGeodesic_smul g hEnorm x v (dist x q), hscale]
  exact hw

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calibrated_intrinsic_ray
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (gamma : ℝ → M) (hgamma : Isometry gamma) (x : M) :
    ∃ w : TangentSpace I x, g.inner x w w = 1 ∧
      let sigma : ℝ → M := intrinsicGeodesic g hEnorm x w
      ContMDiff 𝓘(ℝ, ℝ) I ∞ sigma ∧ IsGeodesic g sigma ∧ sigma 0 = x ∧
      (∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t → dist (sigma s) (sigma t) = |s - t|) ∧
      (∀ s : ℝ, 0 ≤ s → busemannFunction gamma (sigma s) = busemannFunction gamma x - s) := by
  classical
  let T : ℕ → ℝ := fun i ↦ (i : ℝ) + dist x (gamma 0) + 1
  have hTnonneg (i : ℕ) : 0 ≤ T i := by
    dsimp only [T]
    positivity
  have hlength (i : ℕ) : (i : ℝ) + 1 ≤ dist x (gamma (T i)) := by
    have htri := dist_triangle (gamma 0) x (gamma (T i))
    rw [hgamma.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (hTnonneg i), dist_comm (gamma 0) x] at htri
    dsimp only [T] at htri
    linarith
  have hne (i : ℕ) : x ≠ gamma (T i) := by
    apply dist_pos.mp
    have h := hlength i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  choose v hvunit hvend using fun i : ℕ ↦
    normalized_minimizing_vector g hEnorm x (gamma (T i)) (hne i)
  obtain ⟨w, hw, phi, hphi, hvlim⟩ :=
    (fixed_fiber_unit_compact g x).tendsto_subseq (fun i ↦ hvunit i)
  have hwunit : g.inner x (show TangentSpace I x from w) w = 1 := hw
  let sigma : ℝ → M := intrinsicGeodesic g hEnorm x w
  have hTtop : Tendsto T atTop atTop := by
    apply tendsto_atTop_mono (f := fun i : ℕ ↦ (i : ℝ))
      (fun i ↦ by
        have hd : 0 ≤ dist x (gamma 0) := dist_nonneg
        dsimp only [T]
        linarith)
    exact tendsto_natCast_atTop_atTop
  have hLtop : Tendsto (fun i ↦ dist x (gamma (T i))) atTop atTop := by
    apply tendsto_atTop_mono (f := fun i : ℕ ↦ (i : ℝ)) (fun i ↦ by
      have h := hlength i
      linarith)
    exact tendsto_natCast_atTop_atTop
  have hTphi : Tendsto (fun i ↦ T (phi i)) atTop atTop := hTtop.comp hphi.tendsto_atTop
  have hpoint (s : ℝ) :
      Tendsto (fun i ↦ intrinsicGeodesic g hEnorm x (v (phi i)) s) atTop (𝓝 (sigma s)) :=
    (fixed_fiber_geodesic_eval_continuous g hEnorm x s).continuousAt.tendsto.comp hvlim
  have hfinite (i : ℕ) (s : ℝ) (hs : 0 ≤ s) (hsl : s ≤ dist x (gamma (T i))) :
      dist (intrinsicGeodesic g hEnorm x (v i) s) (gamma (T i)) =
        dist x (gamma (T i)) - s := by
    have hright := unit_geodesic_dist_le g hEnorm x (v i) (hvunit i) hsl
    rw [hvend i] at hright
    have hleft := unit_geodesic_dist_le g hEnorm x (v i) (hvunit i) hs
    have hleft' : dist x (intrinsicGeodesic g hEnorm x (v i) s) ≤ s := by
      have heq := congrArg (fun y => dist y (intrinsicGeodesic g hEnorm x (v i) s))
        (intrinsicGeodesic_zero g hEnorm x (v i))
      have hleft0 : dist (intrinsicGeodesic g hEnorm x (v i) 0)
          (intrinsicGeodesic g hEnorm x (v i) s) ≤ s :=
        hleft.trans (le_of_eq (sub_zero s))
      exact heq ▸ hleft0
    have htri := dist_triangle x (intrinsicGeodesic g hEnorm x (v i) s) (gamma (T i))
    exact le_antisymm hright (by linarith)
  have hcalib (s : ℝ) (hs : 0 ≤ s) :
      busemannFunction gamma (sigma s) = busemannFunction gamma x - s := by
    have hleft := busemann_tendsto_moving_point hgamma hTphi (hpoint s)
    have hright := ((busemannFunction_tendsto hgamma x).comp hTphi).sub_const s
    have heq :
        (fun i ↦ dist (intrinsicGeodesic g hEnorm x (v (phi i)) s)
          (gamma (T (phi i))) - T (phi i)) =ᶠ[atTop]
        (fun i ↦ (dist x (gamma (T (phi i))) - T (phi i)) - s) := by
      filter_upwards [(hLtop.comp hphi.tendsto_atTop).eventually (eventually_ge_atTop s)] with i hi
      rw [hfinite (phi i) s hs hi]
      ring
    exact tendsto_nhds_unique hleft (hright.congr' heq.symm)
  refine ⟨w, hwunit, intrinsicGeodesic_contMDiff g hEnorm x w,
    intrinsicGeodesic_isGeodesic g hEnorm x w, intrinsicGeodesic_zero g hEnorm x w,
    ?_, hcalib⟩
  intro s hs t ht
  apply le_antisymm
  · rcases le_total s t with hst | hts
    · have h := unit_geodesic_dist_le g hEnorm x w hwunit hst
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      simpa only [neg_sub] using h
    · have h := unit_geodesic_dist_le g hEnorm x w hwunit hts
      rw [dist_comm] at h
      rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact h
  · have hlip := (busemannFunction_lipschitz hgamma).dist_le_mul (sigma s) (sigma t)
    have hbdist : dist (busemannFunction gamma (sigma s)) (busemannFunction gamma (sigma t)) =
        |s - t| := by
      rw [hcalib s hs, hcalib t ht, Real.dist_eq]
      rw [show (busemannFunction gamma x - s) - (busemannFunction gamma x - t) = t - s by ring]
      exact abs_sub_comm t s
    simpa only [hbdist, NNReal.coe_one, one_mul] using hlip

end CompatibleMetric

section ActualMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calibrated_ray_with_initial_velocity_of_complete_metric
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (gamma : ℝ → M)
    (hgamma : ∀ s t : ℝ,
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    (x : M) :
    ∃ w : TangentSpace I x, ∃ sigma : ℝ → M,
      g.inner x w w = 1 ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ sigma ∧ IsGeodesic g sigma ∧ sigma 0 = x ∧
      (mfderiv 𝓘(ℝ, ℝ) I sigma 0 (1 : ℝ) : E) = (w : E) ∧
      (∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
        riemannianEDistOf g (sigma s) (sigma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : M → ℝ := fun y ↦ ⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t
      ∀ s : ℝ, 0 ≤ s → bplus (sigma s) = bplus x - s := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let m : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  let : MetricSpace M := m
  let : PseudoMetricSpace M := m.toPseudoMetricSpace
  let : PseudoEMetricSpace M := m.toPseudoEMetricSpace
  let : UniformSpace M := m.toUniformSpace
  let : IsRiemannianManifold I M := ⟨by intro y z; rfl⟩
  let : @CompleteSpace M m.toUniformSpace := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm g y v
  have hed (y z : M) : edist y z = riemannianEDistOf g y z := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact IsRiemannianManifold.out (I := I) y z
  have hdist (y z : M) : dist y z = (riemannianEDistOf g y z).toReal := by
    rw [← hed, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hisometry : Isometry gamma := by
    intro s t
    rw [hed, hgamma, edist_dist, Real.dist_eq]
  obtain ⟨w, hunit, hsmooth, hgeo, hzero, hmin, hcalib⟩ :=
    exists_calibrated_intrinsic_ray g hEnorm gamma hisometry x
  let sigma : ℝ → M := intrinsicGeodesic g hEnorm x w
  refine ⟨w, sigma, hunit, hsmooth, hgeo, hzero,
    intrinsicGeodesic_mfderiv_zero g hEnorm x w, ?_, ?_⟩
  · intro s hs t ht
    rw [← hed, edist_dist, hmin s hs t ht]
  · dsimp only
    intro s hs
    simpa only [busemannFunction, hdist] using hcalib s hs

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calibrated_ray_of_complete_metric
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (gamma : ℝ → M)
    (hgamma : ∀ s t : ℝ,
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    (x : M) :
    ∃ sigma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I ∞ sigma ∧ IsGeodesic g sigma ∧ sigma 0 = x ∧
      (∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 ≤ t →
        riemannianEDistOf g (sigma s) (sigma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : M → ℝ := fun y ↦ ⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t
      ∀ s : ℝ, 0 ≤ s → bplus (sigma s) = bplus x - s := by
  obtain ⟨w, sigma, _hunit, hsmooth, hgeo, hzero, _hvelocity, hmin, hcalib⟩ :=
    exists_calibrated_ray_with_initial_velocity_of_complete_metric g hcomplete gamma hgamma x
  exact ⟨sigma, hsmooth, hgeo, hzero, hmin, hcalib⟩

end ActualMetric

end DifferentialGeometry.Geometry.Metric
end
