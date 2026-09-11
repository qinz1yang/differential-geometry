import DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteHinge
import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingRay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactPathAvoidance
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section CompatibleMetric

variable [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem exists_unit_minimizing_initial_vector
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) (hd : 0 < (riemannianEDist I p q).toReal) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm p u (riemannianEDist I p q).toReal = q := by
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q
    (riemannianEDist_ne_top (I := I) p q)
  let d : ℝ := (riemannianEDist I p q).toReal
  let u : TangentSpace I p := d⁻¹ • v
  have hsq : g.inner p v v = d ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hlen]
  have hunit : g.inner p u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g p d⁻¹ v, hsq, ← mul_pow,
      inv_mul_cancel₀ hd.ne', one_pow]
  have hsmul : d • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  refine ⟨u, hunit, ?_⟩
  calc
    _ = expMapIntrinsic (I := I) g hEnorm p (d • u) := by
      rw [expMapIntrinsic_def]
      exact (intrinsicGeodesic_smul (I := I) g hEnorm p u d).symm
    _ = q := by rw [hsmul, hv]

theorem remote_point_triangle_of_compatible_metric
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ D : ℝ, ∀ y : M, D < (riemannianEDist I p y).toReal →
      ∃ z : M, (riemannianEDist I y z).toReal = (riemannianEDist I p y).toReal ∧
        3 / 2 * (riemannianEDist I p y).toReal ≤ (riemannianEDist I p z).toReal := by
  classical
  by_contra hnone
  have hbad (D : ℝ) : ∃ y : M, D < (riemannianEDist I p y).toReal ∧
      ¬ ∃ z : M, (riemannianEDist I y z).toReal = (riemannianEDist I p y).toReal ∧
        3 / 2 * (riemannianEDist I p y).toReal ≤ (riemannianEDist I p z).toReal := by
    by_contra hD
    apply hnone
    refine ⟨D, fun y hy => ?_⟩
    by_contra hgoal
    exact hD ⟨y, hy, hgoal⟩
  choose y hy hyBad using fun n : ℕ => hbad ((n : ℝ) + 1)
  let d : ℕ → ℝ := fun n => (riemannianEDist I p (y n)).toReal
  have hdpos (n : ℕ) : 0 < d n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp only [d]
    linarith [hy n]
  have hd : Tendsto d atTop atTop := tendsto_atTop.2 fun B => by
    obtain ⟨N, hN⟩ := exists_nat_gt B
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    dsimp only [d]
    linarith [hy n]
  choose v hunit hend using fun n =>
    exists_unit_minimizing_initial_vector (I := I) g hEnorm p (y n) (hdpos n)
  have hmin (n : ℕ) : (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p (v n) (d n))).toReal = d n := by
    rw [hend n]
  obtain ⟨u, hu, phi, hphi, hlim, hray⟩ :=
    exists_minimizing_ray_subsequence (I := I) g hEnorm p v d hunit hdpos hmin hd
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hrayReal (L : ℝ) (hL : 0 ≤ L) :
      (riemannianEDist I p (gamma L)).toReal = L := by
    rw [hray L hL, ENNReal.toReal_ofReal hL]
  have hdiff : Tendsto (fun n => v (phi n) - u) atTop (𝓝 (0 : TangentSpace I p)) := by
    simpa only [Function.comp_def, sub_self] using hlim.sub_const u
  have hdelta : Tendsto (fun n => Real.sqrt
      (g.inner p (v (phi n) - u) (v (phi n) - u))) atTop (𝓝 (0 : ℝ)) := by
    have h := ((continuous_sqrt_gInner_self (I := I) g p).tendsto 0).comp hdiff
    simpa only [Function.comp_def, map_zero, zero_apply, Real.sqrt_zero] using h
  obtain ⟨n, hn⟩ := (hdelta.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  let j : ℕ := phi n
  let alpha : ℝ := (riemannianEDist I (y j) (gamma (d j))).toReal
  have halpha : alpha < d j / 2 := by
    have h := complete_equal_arm_norm (I := I) g hEnorm hsec p (v j) u (d j)
      (hdpos j) (hunit j) hu (hmin j)
    rw [hend j] at h
    have hsmall := mul_lt_mul_of_pos_left hn (hdpos j)
    change alpha ≤ _ at h
    dsimp only [j] at h hsmall ⊢
    linarith
  have htri (x y z : M) : (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal + (riemannianEDist I y z).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨riemannianEDist_ne_top (I := I) x y,
        riemannianEDist_ne_top (I := I) y z⟩)
      (riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z))
    simpa only [ENNReal.toReal_add (riemannianEDist_ne_top (I := I) x y)
      (riemannianEDist_ne_top (I := I) y z)] using h
  let f : ℝ → ℝ := fun t => (riemannianEDist I (y j) (gamma (d j + t))).toReal
  have hf : Continuous f := by
    have hc := radialDistToReal_continuous (I := I) g hEnorm p (y j) u
    have h := hc.comp (continuous_const_add (d j))
    simpa only [f, gamma, Function.comp_def, expMapIntrinsic_def,
      intrinsicGeodesic_smul, riemannianEDist_comm] using h
  have hf0 : f 0 < d j := by
    change (riemannianEDist I (y j) (gamma (d j + 0))).toReal < d j
    rw [add_zero]
    change alpha < d j
    linarith [hdpos j]
  have hfd : d j ≤ f (d j) := by
    have h := htri p (y j) (gamma (d j + d j))
    rw [hrayReal (d j + d j) (by linarith [hdpos j])] at h
    change d j + d j ≤ d j + f (d j) at h
    linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (hdpos j).le hf.continuousOn ⟨hf0.le, hfd⟩
  have hsegment : (riemannianEDist I (gamma (d j)) (gamma (d j + t))).toReal ≤ t := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p u
      (s := d j) (t := d j + t) (by linarith [ht.1])
    rw [hu, Real.sqrt_one, one_mul, add_sub_cancel_left] at h
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ENNReal.toReal_ofReal ht.1] using hreal
  have htLower : d j ≤ alpha + t := by
    have h := htri (y j) (gamma (d j)) (gamma (d j + t))
    change f t ≤ alpha + _ at h
    rw [hft] at h
    linarith
  apply hyBad j
  refine ⟨gamma (d j + t), hft, ?_⟩
  rw [hrayReal (d j + t) (by linarith [hdpos j, ht.1])]
  change 3 / 2 * d j ≤ d j + t
  linarith

end CompatibleMetric

theorem remotePointTriangle : RemotePointTriangle I := by
  intro M _ _ _ _ _ _ g _ hcomplete hsec p
  by_cases hz : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hz
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology H := inferInstance
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    refine ⟨0, fun y hy => ?_⟩
    have hpy : p = y := Subsingleton.elim _ _
    rw [← hpy, riemannianEDistOf_self, ENNReal.toReal_zero] at hy
    exact (lt_irrefl 0 hy).elim
  · let : NeZero (Module.finrank ℝ E) := ⟨hz⟩
    let : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : T3Space M := inferInstance
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let : PseudoEMetricSpace M := inferInstance
    let : CompleteSpace M := hcomplete.complete
    have hEnorm : IsMetricNorm (I := I) (M := M) g := fun y v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
    have hcone (y : M) : metricRm04At (I := I) g y ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) :=
      (sectionalBoundedBelowAt_zero_iff (I := I) g y).mp (hsec y)
    simpa only [riemannianEDistOf] using
      remote_point_triangle_of_compatible_metric (I := I) g hEnorm hcone p

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
