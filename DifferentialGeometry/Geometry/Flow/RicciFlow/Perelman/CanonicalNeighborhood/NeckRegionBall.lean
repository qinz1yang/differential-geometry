import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private instance neckOuterSphereDimension : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

private theorem sphere_two_path_length_lt_four (x y : Sphere 2) :
    ∃ gamma : ℝ → Sphere 2, gamma 0 = x ∧ gamma 1 = y ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I2 1 gamma (Icc (0 : ℝ) 1) ∧
      metricPathELength (roundMetric (E := ThreeSpace) (n := 2)) gamma 0 1 <
        ENNReal.ofReal (4 : ℝ) := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  let g := roundMetric (E := ThreeSpace) (n := 2)
  have hRic := ricciBound_of_sec g 1 (fun z v w => by
    simpa only [one_mul] using roundMetric_sec_value (E := ThreeSpace) (n := 2) z v w)
  have hd : riemannianEDistOf (I := I2) g x y ≤ ENNReal.ofReal (Real.pi / Real.sqrt 1) :=
    BonnetMyers.bonnet_myers_pairwise_edist_le_of_complete_metric (I := I2) g
    (RiemannianMetricComplete.of_compact g) (by simp) zero_lt_one hRic x y
  have hdist : riemannianEDistOf g x y ≤ ENNReal.ofReal Real.pi := by
    simpa only [Real.sqrt_one, div_one] using hd
  exact exists_lt_of_edistOf_lt g
    (hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr Real.pi_lt_four))

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem neck_outer_edist_comm (g : SmoothRiemannianMetric I3 M) (x y : M) :
    riemannianEDistOf g x y = riemannianEDistOf g y x := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm (I := I3) (x := x) (y := y)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem neck_outer_edist_triangle (g : SmoothRiemannianMetric I3 M) (x y z : M) :
    riemannianEDistOf g x z ≤ riemannianEDistOf g x y + riemannianEDistOf g y z := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle (I := I3) (x := x) (y := y) (z := z)

private theorem neck_outer_transverse_edist_le {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) (p q : Sphere 2) :
    riemannianEDistOf (rescaledMetric S t (S.scalar t x) nk.Q_pos 0)
      (nk.map (p, 0)) (nk.map (q, 0)) ≤ ENNReal.ofReal (6 * Real.sqrt (1 + eps)) := by
  obtain ⟨gamma, hstart, hend, hgamma, hlength⟩ := sphere_two_path_length_lt_four p q
  have hcyl : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s => (gamma s, (0 : ℝ))) (Icc (0 : ℝ) 1) :=
    hgamma.prodMk contMDiffOn_const
  have hinside : ∀ s ∈ Icc (0 : ℝ) 1,
      (gamma s, (0 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro s _
    exact ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos), inv_pos.mpr nk.eps_pos⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I3 1
      ((nk.map : Cylinder → M) ∘ (fun s => (gamma s, (0 : ℝ)))) (Icc (0 : ℝ) 1) :=
    (nk.map.contMDiffOn_toFun.of_le (by simp)).comp hcyl (fun s hs => nk.domain (hinside s hs))
  have hdist := edistOf_le_metricPathELength
    (rescaledMetric S t (S.scalar t x) nk.Q_pos 0) (by norm_num : (0 : ℝ) ≤ 1) hcomp
  simp only [Function.comp_apply, hstart, hend] at hdist
  have hupper := (collar_pathELength_bounds nk.cylinder _ nk.map nk.comparison rfl
    nk.eps_pos.le (by linarith [nk.eps_small]) (by norm_num) nk.domain hcyl hinside).2
  have htrans := nk.cylinder.transverse_length_le 0 hgamma
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hb : metricPathELength (nk.cylinder.metric 0) (fun s => (gamma s, (0 : ℝ))) 0 1 ≤
      ENNReal.ofReal (6 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (4 : ℝ) :=
        htrans.trans (mul_le_mul' le_rfl hlength.le)
      _ = ENNReal.ofReal (Real.sqrt 2 * 4) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  exact hdist.trans (hupper.trans ((mul_le_mul' le_rfl hb).trans_eq (by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm])))


theorem StrongNeck.region_subset_ball {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    nk.region ⊆ riemannianBallOf (S.base.metric t) x (17 / Real.sqrt (S.scalar t x)) := by
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-10 : ℝ) 10 ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hi : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      (by linarith [nk.eps_small])
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  have hQ := Real.sqrt_pos.mpr nk.Q_pos
  have heq := riemannianBallOf_scaleMetric (S.scalar t x) nk.Q_pos (S.base.metric t) x
    (17 / Real.sqrt (S.scalar t x))
  rw [mul_div_cancel₀ _ hQ.ne'] at heq
  rintro y ⟨⟨p, z⟩, hz, rfl⟩
  have haxis := collar_axial_edist_le nk.cylinder _ nk.map nk.comparison rfl
    nk.eps_pos.le (by norm_num) nk.domain hslab p hz.2
  have htrans := neck_outer_transverse_edist_le nk nk.center p
  let g := rescaledMetric S t (S.scalar t x) nk.Q_pos 0
  have htri := neck_outer_edist_triangle g (nk.map (nk.center, 0)) (nk.map (p, 0)) (nk.map (p, z))
  rw [nk.center_eq] at htri htrans
  have hb : riemannianEDistOf g x (nk.map (p, z)) ≤
      ENNReal.ofReal (16 * Real.sqrt (1 + eps)) := by
    have hax : riemannianEDistOf g (nk.map (p, 0)) (nk.map (p, z)) ≤
        ENNReal.ofReal (10 * Real.sqrt (1 + eps)) := by
      rw [neck_outer_edist_comm]
      exact haxis.trans (ENNReal.ofReal_le_ofReal (by
        have habs : |z| ≤ 10 := abs_le.mpr hz.2
        nlinarith [Real.sqrt_nonneg (1 + eps)]))
    apply (htri.trans (add_le_add htrans hax)).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hbound : 16 * Real.sqrt (1 + eps) < 17 := by
    have hs := Real.sq_sqrt (by linarith [nk.eps_pos] : 0 ≤ 1 + eps)
    nlinarith [nk.eps_small, Real.sqrt_nonneg (1 + eps)]
  have hfinal := hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hbound)
  change nk.map (p, z) ∈ riemannianBallOf (S.base.metric t) x _
  rw [← heq]
  simpa only [g, rescaledMetric, parabolicTime_zero, riemannianBallOf, mem_ofPred_eq] using hfinal

variable [T2Space M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem StrongNeck.ball_subset_region {eps : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t) :
    riemannianBallOf (S.base.metric t) x
      (10 * Real.sqrt (1 - eps) / Real.sqrt (S.scalar t x)) ⊆ nk.region := by
  have hminus : 0 < 1 - eps := by linarith [nk.eps_small]
  have hsqrt : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr hminus
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-10 : ℝ) 10 ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hi : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      (by linarith [nk.eps_small])
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  have hball : riemannianClosedBallOf (nk.cylinder.metric 0) (nk.center, 0) 10 ⊆
      univ ×ˢ Icc (-10 : ℝ) 10 := by
    simpa only [zero_sub, zero_add] using
      nk.cylinder.closedBall_subset_slab (nk.center, 0) (by norm_num : (0 : ℝ) ≤ 10)
  have hcapture := ball_subset_image_of_metric_lower_crossModel (nk.cylinder.metric 0)
    (rescaledMetric S t (S.scalar t x) nk.Q_pos 0) nk.map (nk.center, 0)
    (L := (Real.sqrt (1 - eps))⁻¹) (by norm_num : (0 : ℝ) < 10) (inv_pos.mpr hsqrt)
    (nk.cylinder.isCompact_closedBall (nk.center, 0) (by norm_num : (0 : ℝ) ≤ 10))
    (hball.trans (hslab.trans nk.domain)) (by
      intro y hy v
      have he := (nk.comparison.equivalence 0 (by norm_num) y (hslab (hball hy)) v).1
      rw [nk.comparison.pullback_eq 0 y (hslab (hball hy)) (fun _ => v)] at he
      have hh := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hminus.le)
      rw [← mul_assoc, inv_mul_cancel₀ hminus.ne', one_mul] at hh
      simpa only [inv_pow, Real.sq_sqrt hminus.le] using hh)
  have hscaled := hcapture.trans (image_mono hball)
  rw [div_inv_eq_mul, nk.center_eq] at hscaled
  have hQ := Real.sqrt_pos.mpr nk.Q_pos
  have heq := riemannianBallOf_scaleMetric (S.scalar t x) nk.Q_pos (S.base.metric t) x
    (10 * Real.sqrt (1 - eps) / Real.sqrt (S.scalar t x))
  rw [mul_div_cancel₀ _ hQ.ne'] at heq
  simpa only [rescaledMetric, parabolicTime_zero, heq, StrongNeck.region] using hscaled

theorem StrongNeck.closedBall_subset_region {eps r : ℝ} {x : M} {t : ℝ}
    (nk : StrongNeck S eps x t)
    (hr : r < 10 * Real.sqrt (1 - eps) / Real.sqrt (S.scalar t x)) :
    riemannianClosedBallOf (S.base.metric t) x r ⊆ nk.region := by
  intro y hy
  apply nk.ball_subset_region
  exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
    have hminus : 0 < 1 - eps := by linarith [nk.eps_small]
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hminus))
      (Real.sqrt_pos.mpr nk.Q_pos))).mpr hr)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
