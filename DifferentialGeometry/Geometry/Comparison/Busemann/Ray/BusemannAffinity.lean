import DifferentialGeometry.Geometry.Comparison.Busemann.Support.HorosphereHessianZero
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannLine
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.ApproximateSupportConvexity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

private theorem affine_of_convex_of_neg_convex {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (hn : ConvexOn ℝ univ (fun t => -f t)) (x : ℝ) :
    f x = f 0 + x * (f 1 - f 0) := by
  have hseg (a b t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      f ((1 - t) * a + t * b) = (1 - t) * f a + t * f b := by
    have hp := hf.2 (mem_univ a) (mem_univ b) (sub_nonneg.mpr ht1) ht (sub_add_cancel 1 t)
    have hm := hn.2 (mem_univ a) (mem_univ b) (sub_nonneg.mpr ht1) ht (sub_add_cancel 1 t)
    simp only [smul_eq_mul] at hp hm
    linarith
  by_cases hx : 0 ≤ x
  · by_cases hx1 : x ≤ 1
    · have h := hseg 0 1 x hx hx1
      simp only [mul_zero, mul_one, zero_add] at h
      linarith
    · have hx1' : 1 < x := lt_of_not_ge hx1
      have hxpos : 0 < x := zero_lt_one.trans hx1'
      have h := hseg 0 x (1 / x) (by positivity) ((div_le_one hxpos).mpr hx1'.le)
      simp only [mul_zero, zero_add, one_div_mul_cancel (ne_of_gt hxpos)] at h
      field_simp [ne_of_gt hxpos] at h
      nlinarith
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hden : 0 < 1 - x := by linarith
    have ht : 0 ≤ -x / (1 - x) := div_nonneg (neg_nonneg.mpr hxneg.le) hden.le
    have ht1 : -x / (1 - x) ≤ 1 := (div_le_one hden).mpr (by linarith)
    have h := hseg x 1 (-x / (1 - x)) ht ht1
    have harg : (1 - -x / (1 - x)) * x + (-x / (1 - x)) * 1 = 0 := by
      field_simp [ne_of_gt hden]
      ring
    rw [harg] at h
    field_simp [ne_of_gt hden] at h
    nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_busemann_support_hessian_gt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) (p : M) (v : TangentSpace I p) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : M → ℝ) (U : Set M), IsOpen U ∧ p ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ U ∧
      φ p = busemann (fun t : ℝ≥0 => γ t) p ∧
      (∀ x, φ x ≤ busemann (fun t : ℝ≥0 => γ t) x) ∧
      -ε < hessFun (I := I) g φ p v v := by
  let cp := fun t : ℝ≥0 => γ t
  let b := busemann cp
  have hcp : Isometry cp := by
    apply Isometry.of_dist_eq
    intro s t
    exact hγ.dist_eq s t
  let u := gradientFun (I := I) g b p
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  have hu : g.inner p u u = 1 := (opposite_busemann_gradient_unit (I := I) g hEnorm hRic hγ p).1
  obtain ⟨heta, _, _, hzero, hcal⟩ := opposite_busemann_gradient_line (I := I) g hEnorm hRic hγ p
  change Isometry eta at heta
  change eta 0 = p at hzero
  change ∀ t, b (eta t) = b p + t at hcal
  have hlim := (tendsto_lineDistanceSupport_hessian_zero (I := I) g hEnorm hRic p u hu heta 0 v v).1
  change Tendsto (fun R => hessFun (I := I) g (lineDistanceSupport eta R) (eta 0) (v : E) (v : E))
    atTop (𝓝 0) at hlim
  erw [hzero] at hlim
  obtain ⟨R, hR, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (eventually_gt_nhds (neg_lt_zero.mpr hε)))).exists
  obtain ⟨U, hU, hx, hf⟩ := exists_open_smooth_lineDistanceSupport (I := I) g hEnorm p u hu heta 0 R hR
  have hpU : p ∈ U := by simpa only [intrinsicGeodesic_zero] using hx
  refine ⟨fun x => b p + lineDistanceSupport eta R x, U, hU, hpU, contMDiffOn_const.add hf, ?_, ?_, ?_⟩
  · have hz := lineDistanceSupport_on_line heta hR.le
    rw [hzero] at hz
    change b p + lineDistanceSupport eta R p = b p
    rw [hz, add_zero]
  · intro x
    have h := (lipschitzWith_busemann hcp).dist_le_mul (eta R) x
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
    change |b (eta R) - b x| ≤ dist (eta R) x at h
    rw [hcal R, dist_comm] at h
    change b p + (R - dist x (eta R)) ≤ b x
    linarith [(abs_le.mp h).2]
  · rw [hessFun_add_const (I := I) g (b p) hU hf hpU]
    exact hsmall

theorem busemann_comp_geodesic_convex
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (hgeo : IsGeodesic (I := I) g c) :
    ConvexOn ℝ univ ((busemann (fun t : ℝ≥0 => γ t)) ∘ c) := by
  have hcp : Isometry (fun t : ℝ≥0 => γ t) := by
    apply Isometry.of_dist_eq
    intro s t
    exact hγ.dist_eq s t
  apply convexOn_of_approximate_lower_support convex_univ
    (((lipschitzWith_busemann hcp).continuous.comp hc.continuous).continuousOn)
  intro s _ ε hε
  let v : TangentSpace I (c s) := mfderiv 𝓘(ℝ, ℝ) I c s (1 : ℝ)
  obtain ⟨φ, U, hU, hsU, hφ, hcontact, hbelow, hsmall⟩ :=
    exists_busemann_support_hessian_gt (I := I) g hEnorm hRic hγ (c s) v ε hε
  refine ⟨φ ∘ c, ?_, hcontact, Eventually.of_forall (fun t => hbelow (c t)), ?_⟩
  · have hcomp := ((hφ (c s) hsU).contMDiffAt (hU.mem_nhds hsU)).comp s hc.contMDiffAt
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  · have hd := deriv2_comp_geo_on (I := I) g hU hφ hc hgeo hsU
    change deriv (deriv (φ ∘ c)) s = hessFun (I := I) g φ (c s) v v at hd
    rw [hd]
    exact hsmall

theorem opposite_busemann_comp_geodesic_convex
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (hgeo : IsGeodesic (I := I) g c) :
    ConvexOn ℝ univ ((busemann (fun t : ℝ≥0 => γ t)) ∘ c) ∧
    ConvexOn ℝ univ ((busemann (fun t : ℝ≥0 => γ (-(t : ℝ)))) ∘ c) := by
  refine ⟨busemann_comp_geodesic_convex (I := I) g hEnorm hRic hγ hc hgeo, ?_⟩
  have hrev : Isometry (fun t : ℝ => γ (-t)) := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hγ.dist_eq, dist_neg_neg]
  exact busemann_comp_geodesic_convex (I := I) g hEnorm hRic hrev hc hgeo

theorem busemann_comp_geodesic_affine
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    {γ : ℝ → M} (hγ : Isometry γ) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (hgeo : IsGeodesic (I := I) g c) (t : ℝ) :
    let b := busemann (fun s : ℝ≥0 => γ s)
    b (c t) = b (c 0) + t * (b (c 1) - b (c 0)) := by
  obtain ⟨hp, hm⟩ := opposite_busemann_comp_geodesic_convex (I := I) g hEnorm hRic hγ hc hgeo
  have heq : ((busemann (fun s : ℝ≥0 => γ (-(s : ℝ)))) ∘ c) =
      fun t => -busemann (fun s : ℝ≥0 => γ s) (c t) := by
    funext t
    have h := opposite_busemann_sum_eq_zero (I := I) g hEnorm hRic hγ (c t)
    change busemann (fun s : ℝ≥0 => γ s) (c t) +
      busemann (fun s : ℝ≥0 => γ (-(s : ℝ))) (c t) = 0 at h
    dsimp only [Function.comp_apply]
    linarith
  rw [heq] at hm
  exact affine_of_convex_of_neg_convex hp hm t

end DifferentialGeometry.Geometry.Topology

end
