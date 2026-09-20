import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannDifferentiability
import DifferentialGeometry.Geometry.Comparison.Distance.LocalSmoothness


noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation (curveVelocity)
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem gradient_dist_of_minimizing_exp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : M) (v : TangentSpace I q) (hv : 0 < g.inner q v v)
    (hmin : Real.sqrt (g.inner q v v) =
      (riemannianEDist I q (intrinsicGeodesic (I := I) g hEnorm q v 1)).toReal)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (riemannianEDist I q y).toReal)
      (intrinsicGeodesic (I := I) g hEnorm q v 1)) :
    gradientFun (I := I) g (fun y => (riemannianEDist I q y).toReal)
        (intrinsicGeodesic (I := I) g hEnorm q v 1) =
      (Real.sqrt (g.inner q v v))⁻¹ •
        curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1 := by
  obtain ⟨rho, hrho, hcontact, hbound, hgrad⟩ :=
    smooth_distance_upper_support_of_minimizing_exp (I := I) g hEnorm q v hv
      hmin
  have heq := DifferentialGeometry.Geometry.Topology.gradientFun_eq_of_differentiable_lower_support (I := I) g
    (hrho.mdifferentiableAt (by simp)) hd
    (hmin.symm.trans hcontact.symm)
    hbound
  exact heq.symm.trans hgrad

private theorem gradient_riemannianEDist_normSq_eq_one_of_complete
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q x : M) (hqx : q ≠ x) (hfin : riemannianEDist I q x ≠ ⊤)
    (hd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (riemannianEDist I q y).toReal) x) :
    g.inner x (gradientFun (I := I) g (fun y => (riemannianEDist I q y).toReal) x)
      (gradientFun (I := I) g (fun y => (riemannianEDist I q y).toReal) x) = 1 := by
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top (I := I) g hEnorm q x hfin
  have hpos : 0 < (riemannianEDist I q x).toReal := ENNReal.toReal_pos (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact fun hz => hqx (edist_eq_zero.mp hz)) hfin
  have hv : 0 < g.inner q v v := Real.sqrt_pos.mp (hlen.symm ▸ hpos)
  have hend : intrinsicGeodesic (I := I) g hEnorm q v 1 = x := hexp
  have hmin : Real.sqrt (g.inner q v v) =
      (riemannianEDist I q (intrinsicGeodesic (I := I) g hEnorm q v 1)).toReal := by
    rw [hend]
    exact hlen
  rw [← hend] at hd ⊢
  rw [gradient_dist_of_minimizing_exp (I := I) g hEnorm q v hv hmin hd,
    gInner_smul_self (I := I) g]
  have hspeed : g.inner (intrinsicGeodesic (I := I) g hEnorm q v 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1)
      (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm q v) 1) =
        g.inner q v v := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q v 1
  rw [hspeed]
  simp only [inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

end DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem exists_open_gradient_riemannianEDistOf_normSq_eq_one_of_nonzero_finrank
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, ∀ x ∈ U, q ≠ x →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (riemannianEDistOf g q y).toReal) x →
      g.inner x (gradientFun g (fun y => (riemannianEDistOf g q y).toReal) x)
        (gradientFun g (fun y => (riemannianEDistOf g q y).toReal) x) = 1 := by
  obtain ⟨g', U, hcomplete, hU, hpU, heq, hdU⟩ :=
    exists_riemannianMetricComplete_local_distance_eq g p
  refine ⟨U, hU, hpU, ?_⟩
  intro q hq x hx hqx hd
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g'.inner, g'.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g' :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g' x v
  have hfun : (fun y => (riemannianEDist I q y).toReal) =ᶠ[𝓝 x]
      (fun y => (riemannianEDistOf g q y).toReal) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [← riemannianEDistOf_eq_riemannianEDist g' hEnorm, (hdU q hq y hy).1]
  have hfin : riemannianEDist I q x ≠ ⊤ := by
    rw [← riemannianEDistOf_eq_riemannianEDist g' hEnorm, (hdU q hq x hx).1]
    exact (hdU q hq x hx).2
  have hd' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (riemannianEDist I q y).toReal) x :=
    hd.congr_of_eventuallyEq hfun
  have hgrad : gradientFun g' (fun y => (riemannianEDist I q y).toReal) x =
      gradientFun g (fun y => (riemannianEDistOf g q y).toReal) x := by
    rw [gradientFun_congr_metric g g' _ (heq x hx)]
    apply SmoothRiemannianMetric.eq_of_inner_eq_gen g
    intro w
    rw [inner_gradientFun, inner_gradientFun, mvfderiv_real_eq_mfderiv,
      mvfderiv_real_eq_mfderiv, hfun.mfderiv_eq]
    rfl
  have h := gradient_riemannianEDist_normSq_eq_one_of_complete g' hEnorm q x hqx hfin hd'
  rw [hgrad, heq x hx] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_open_gradient_riemannianEDistOf_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, ∀ x ∈ U, q ≠ x →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => (riemannianEDistOf g q y).toReal) x →
      g.inner x (gradientFun g (fun y => (riemannianEDistOf g q y).toReal) x)
        (gradientFun g (fun y => (riemannianEDistOf g q y).toReal) x) = 1 := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : DiscreteTopology M := DifferentialGeometry.discrete_topology_of_finrank_eq_zero I hdim
    refine ⟨{p}, isOpen_discrete _, mem_singleton p, ?_⟩
    intro q hq x hx hqx _
    exact (hqx ((mem_singleton_iff.mp hq).trans (mem_singleton_iff.mp hx).symm)).elim
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact exists_open_gradient_riemannianEDistOf_normSq_eq_one_of_nonzero_finrank g p

end DifferentialGeometry.Geometry.Riemannian
