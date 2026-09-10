import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerSupportConvexity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

private theorem second_deriv_sub {f h : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    deriv (deriv (fun t => f t - h t)) x =
      deriv (deriv f) x - deriv (deriv h) x := by
  have hnf : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t :=
    (hf.eventually (by norm_num)).mono fun _ ht => ht.differentiableAt (by norm_num)
  have hnh : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ h t :=
    (hh.eventually (by norm_num)).mono fun _ ht => ht.differentiableAt (by norm_num)
  have heq : deriv (fun t => f t - h t) =ᶠ[𝓝 x] fun t => deriv f t - deriv h t := by
    filter_upwards [hnf, hnh] with t htf hth
    exact deriv_sub htf hth
  rw [heq.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hh.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem support_comp_intrinsic_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {p : M} (hp : p ∈ U)
    (v : TangentSpace I p) :
    ContDiffAt ℝ 2 (f ∘ intrinsicGeodesic (I := I) g hEnorm p v) 0 := by
  have hfp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f
      (intrinsicGeodesic (I := I) g hEnorm p v 0) := by
    simpa only [intrinsicGeodesic_zero] using (hf p hp).contMDiffAt (hU.mem_nhds hp)
  have hc := hfp.comp 0 (intrinsicGeodesic_contMDiff (I := I) g hEnorm p v).contMDiffAt
  exact (contMDiffAt_iff_contDiffAt.mp hc).of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

private theorem second_deriv_intrinsic_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {p : M} (hp : p ∈ U)
    (v : TangentSpace I p) :
    deriv (deriv (f ∘ intrinsicGeodesic (I := I) g hEnorm p v)) 0 =
      hessFun (I := I) g f p v v := by
  let eta : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v
  have hzero : eta 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  have h := deriv2_comp_geo_on (I := I) g hU hf
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm p v)
    (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v)
    (by simpa only [hzero] using hp : eta 0 ∈ U)
  change deriv (deriv (f ∘ eta)) 0 = hessFun (I := I) g f (eta 0)
    (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E)
    (mfderiv 𝓘(ℝ, ℝ) I eta 0 (1 : ℝ) : E) at h
  rw [hvel, hzero] at h
  exact h

theorem hessFun_sub_diagonal_on
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {f h : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U)
    {p : M} (hp : p ∈ U) (v : TangentSpace I p) :
    hessFun (I := I) g (fun x => f x - h x) p v v =
      hessFun (I := I) g f p v v - hessFun (I := I) g h p v v := by
  rw [← second_deriv_intrinsic_zero (I := I) g hEnorm hU (hf.sub hh) hp v,
    ← second_deriv_intrinsic_zero (I := I) g hEnorm hU hf hp v,
    ← second_deriv_intrinsic_zero (I := I) g hEnorm hU hh hp v]
  exact second_deriv_sub
    (support_comp_intrinsic_contDiffAt_two (I := I) g hEnorm hU hf hp v)
    (support_comp_intrinsic_contDiffAt_two (I := I) g hEnorm hU hh hp v)


theorem hessFun_neg_diagonal_on
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {p : M} (hp : p ∈ U) (v : TangentSpace I p) :
    hessFun (I := I) g (fun x => -f x) p v v = -hessFun (I := I) g f p v v := by
  rw [← second_deriv_intrinsic_zero (I := I) g hEnorm hU hf.neg hp v,
    ← second_deriv_intrinsic_zero (I := I) g hEnorm hU hf hp v]
  change deriv (deriv (-(f ∘ intrinsicGeodesic (I := I) g hEnorm p v))) 0 = _
  rw [deriv.neg']
  exact deriv.neg

theorem hessFun_le_of_smooth_upper_support
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {f h : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U)
    {p : M} (hp : p ∈ U) (hcontact : f p = h p)
    (hupper : ∀ᶠ y in 𝓝 p, f y ≤ h y) (v : TangentSpace I p) :
    hessFun (I := I) g f p v v ≤ hessFun (I := I) g h p v v := by
  let eta : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v
  have hmax : IsLocalMax (fun x => f x - h x) p := by
    filter_upwards [hupper] with y hy
    change f y - h y ≤ f p - h p
    rw [hcontact, sub_self]
    exact sub_nonpos.mpr hy
  have hmaxEta : IsLocalMax ((fun x => f x - h x) ∘ eta) 0 := by
    have hm : IsLocalMax (fun x => f x - h x) (eta 0) := by
      simpa only [eta, intrinsicGeodesic_zero] using hmax
    have he : ContinuousAt eta 0 :=
      (intrinsicGeodesic_contMDiff (I := I) g hEnorm p v).continuous.continuousAt
    exact hm.comp_continuous he
  have hc := support_comp_intrinsic_contDiffAt_two (I := I) g hEnorm hU (hf.sub hh) hp v
  have hnonpos := second_deriv_nonpos_of_isLocalMax hmaxEta hc.continuousAt
  rw [second_deriv_intrinsic_zero (I := I) g hEnorm hU (hf.sub hh) hp v,
    hessFun_sub_diagonal_on (I := I) g hEnorm hU hf hh hp v] at hnonpos
  exact sub_nonpos.mp hnonpos

theorem hessFun_add_nonpos_of_zero_contact
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {f h : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U)
    {p : M} (hp : p ∈ U) (hcontact : f p + h p = 0)
    (hupper : ∀ᶠ y in 𝓝 p, f y + h y ≤ 0) (v : TangentSpace I p) :
    hessFun (I := I) g f p v v + hessFun (I := I) g h p v v ≤ 0 := by
  have hc : f p = -h p := by linarith
  have hb : ∀ᶠ y in 𝓝 p, f y ≤ -h y := hupper.mono fun y hy => by linarith
  have hle := hessFun_le_of_smooth_upper_support (I := I) g hEnorm hU hf hh.neg hp hc hb v
  rw [hessFun_neg_diagonal_on (I := I) g hEnorm hU hh hp v] at hle
  linarith

end DifferentialGeometry.Geometry.Topology

end
