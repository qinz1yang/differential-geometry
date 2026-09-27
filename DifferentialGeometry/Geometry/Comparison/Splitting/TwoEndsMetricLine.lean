import DifferentialGeometry.Topology.Ends.FiniteEnds
import DifferentialGeometry.Topology.Ends.ProperMaps
import DifferentialGeometry.Topology.Ends.EscapingComponent
import DifferentialGeometry.Geometry.Comparison.Splitting.MetricLineLimit
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

noncomputable section

open Set Filter Metric Bundle Manifold
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

private theorem exists_isometry_of_two_ends_of_segments
    {X : Type*} [MetricSpace X] [ProperSpace X] [ConnectedSpace X]
    (hsegments : ∀ p q : X, p ≠ q → ∃ f : ℝ → X,
      LipschitzWith 1 f ∧ f 0 = p ∧ f (dist p q) = q)
    (hends : HasAtLeastEnds X 2) : ∃ gamma : ℝ → X, Isometry gamma := by
  classical
  obtain ⟨K, hK, x, _, hinj, hnc⟩ := hends
  have hne : connectedComponentIn Kᶜ (x 0) ≠ connectedComponentIn Kᶜ (x 1) :=
    fun h => (by norm_num : (0 : Fin 2) ≠ 1) (hinj h)
  have hKne : K.Nonempty := by
    by_contra hnone
    have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
    have hcc (y : X) : connectedComponentIn Kᶜ y = univ := by
      rw [hKe, compl_empty]
      exact isPreconnected_univ.connectedComponentIn trivial
    exact hne ((hcc (x 0)).trans (hcc (x 1)).symm)
  choose p hp hpFar using fun n : ℕ =>
    exists_infDist_gt_of_not_isCompact_closure hK hKne (hnc 0) (n : ℝ)
  choose q hq hqFar using fun n : ℕ =>
    exists_infDist_gt_of_not_isCompact_closure hK hKne (hnc 1) (n : ℝ)
  have hpq (n : ℕ) : p n ≠ q n := by
    intro heq
    apply hne
    have hleft := connectedComponentIn_eq (hp n)
    have hright := connectedComponentIn_eq (hq n)
    rw [heq] at hleft
    exact hleft.trans hright.symm
  choose g hLip hstart hend using fun n => hsegments (p n) (q n) (hpq n)
  let d : ℕ → ℝ := fun n => dist (p n) (q n)
  have hfull (n : ℕ) : dist (g n 0) (g n (d n)) = d n - 0 := by
    rw [hstart n, hend n, sub_zero]
  have hcross (n : ℕ) : ∃ c ∈ Icc (0 : ℝ) (d n), g n c ∈ K := by
    by_contra hnone
    have hsub : g n '' Icc (0 : ℝ) (d n) ⊆ Kᶜ := by
      rintro y ⟨t, ht, rfl⟩ hy
      exact hnone ⟨t, ht, hy⟩
    have hconn : IsPreconnected (g n '' Icc (0 : ℝ) (d n)) :=
      isPreconnected_Icc.image (g n) (hLip n).continuous.continuousOn
    have hpImage : p n ∈ g n '' Icc (0 : ℝ) (d n) :=
      ⟨0, ⟨le_rfl, dist_nonneg⟩, hstart n⟩
    have hqImage : q n ∈ g n '' Icc (0 : ℝ) (d n) :=
      ⟨d n, ⟨dist_nonneg, le_rfl⟩, hend n⟩
    have hqComp := hconn.subset_connectedComponentIn hpImage hsub hqImage
    exact hne ((connectedComponentIn_eq (hp n)).trans
      ((connectedComponentIn_eq hqComp).trans (connectedComponentIn_eq (hq n)).symm))
  choose c hc hcK using hcross
  have hleft (n : ℕ) : (n : ℝ) < c n := by
    have hdist : dist (p n) (g n (c n)) = c n := by
      have h := dist_eq_sub_of_lipschitzWith_one_of_endpoints (hLip n)
        (a := 0) (s := 0) (t := c n) (b := d n) le_rfl (hc n).1 (hc n).2 (hfull n)
      simpa only [hstart n, sub_zero] using h
    have hbound := infDist_le_dist_of_mem (x := p n) (hcK n)
    rw [hdist] at hbound
    exact (hpFar n).trans_le hbound
  have hright (n : ℕ) : (n : ℝ) < d n - c n := by
    have hdist : dist (q n) (g n (c n)) = d n - c n := by
      have h := dist_eq_sub_of_lipschitzWith_one_of_endpoints (hLip n)
        (a := 0) (s := c n) (t := d n) (b := d n) (hc n).1 (hc n).2 le_rfl (hfull n)
      rw [hend n] at h
      exact (dist_comm _ _).trans h
    have hbound := infDist_le_dist_of_mem (x := q n) (hcK n)
    rw [hdist] at hbound
    exact (hqFar n).trans_le hbound
  have hdiv (w : ℕ → ℝ) (hw : ∀ n : ℕ, (n : ℝ) < w n) : Tendsto w atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro R
    obtain ⟨N, hN⟩ := exists_nat_gt R
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    exact (hN.trans_le hcast).le.trans (hw n).le
  let f : ℕ → ℝ → X := fun n t => g n (t + c n)
  have hshift (n : ℕ) : LipschitzWith 1 (f n) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hdist : dist (s + c n) (t + c n) = dist s t := by simp [Real.dist_eq]
    simpa only [f, hdist] using (hLip n).dist_le_mul (s + c n) (t + c n)
  have hmarked (n : ℕ) : f n 0 ∈ K := by simpa only [f, zero_add] using hcK n
  have hends (n : ℕ) : dist (f n (-c n)) (f n (d n - c n)) = c n + (d n - c n) := by
    dsimp only [f]
    rw [neg_add_cancel, sub_add_cancel, hstart n, hend n]
    dsimp only [d]
    ring
  obtain ⟨gamma, hgamma, _⟩ := exists_isometry_of_two_sided_minimizing_segments
    f hshift hK hmarked c (fun n => d n - c n) (hdiv c hleft)
      (hdiv (fun n => d n - c n) hright) hends
  exact ⟨gamma, hgamma⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_riemannian_metric_line_of_two_ends (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (hends : HasAtLeastEnds M 2) :
    ∃ gamma : ℝ → M, ∀ s t : ℝ,
      riemannianEDistOf (I := I) g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  classical
  by_cases hz : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hz
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology H := inferInstance
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    exact (not_hasAtLeastEnds_of_compact (X := M) (by decide : 0 < 2) hends).elim
  · let : NeZero (Module.finrank ℝ E) := ⟨hz⟩
    let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : T3Space M := inferInstance
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let : CompleteSpace M := hcomplete.complete
    have hEnorm : IsMetricNorm (I := I) (M := M) g := fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
    let : MetricSpace M := riemMetricSpace (I := I) (M := M)
    let : ProperSpace M := properSpace_riemMetric (I := I) hcomplete.complete g hEnorm
    have hdist (p q : M) : dist p q = (riemannianEDist I p q).toReal :=
      riemMetric_dist_eq (I := I) p q
    have hsegments (p q : M) (hpq : p ≠ q) : ∃ f : ℝ → M,
        LipschitzWith 1 f ∧ f 0 = p ∧ f (dist p q) = q := by
      obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top (I := I) g hEnorm p q
        (riemannianEDist_ne_top (I := I) p q)
      let d : ℝ := dist p q
      have hd : 0 < d := dist_pos.mpr hpq
      let u : TangentSpace I p := d⁻¹ • v
      have hsq : g.inner p v v = d ^ 2 := by
        rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hlen, ← hdist p q]
      have hu : g.inner p u u = 1 := by
        dsimp only [u]
        rw [gInner_smul_self (I := I) g p d⁻¹ v, hsq, ← mul_pow,
          inv_mul_cancel₀ hd.ne', one_pow]
      have hsmul : d • u = v := by
        dsimp only [u]
        rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
      let f : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
      have hbound (s t : ℝ) (hst : s ≤ t) : dist (f s) (f t) ≤ t - s := by
        have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p u hst
        rw [hu, Real.sqrt_one, one_mul] at h
        have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] at hr
        simpa only [hdist] using hr
      refine ⟨f, ?_, intrinsicGeodesic_zero (I := I) g hEnorm p u, ?_⟩
      · apply LipschitzWith.of_dist_le_mul
        intro s t
        rcases le_total s t with hst | hts
        · simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
            abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hbound s t hst
        · simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
            abs_of_nonneg (sub_nonneg.mpr hts), dist_comm] using hbound t s hts
      · calc
          _ = expMapIntrinsic (I := I) g hEnorm p (d • u) := by
            rw [expMapIntrinsic_def]
            exact (intrinsicGeodesic_smul (I := I) g hEnorm p u d).symm
          _ = q := by rw [hsmul, hv]
    obtain ⟨gamma, hgamma⟩ := exists_isometry_of_two_ends_of_segments hsegments hends
    refine ⟨gamma, fun s t => ?_⟩
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    calc
      _ = ENNReal.ofReal (riemannianEDist I (gamma s) (gamma t)).toReal :=
        (ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) (gamma s) (gamma t))).symm
      _ = ENNReal.ofReal |s - t| := by rw [← hdist, hgamma.dist_eq, Real.dist_eq]

end DifferentialGeometry.Geometry.Topology

end

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] [NoncompactSpace Y]

theorem exists_riemannian_metric_line_of_proper_maps_into_separated_sets
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    {K A B : Set M} (hK : IsCompact K) (hA : IsOpen A) (hB : IsOpen B)
    (hdisjoint : Disjoint A B) (hcover : A ∪ B = Kᶜ)
    (f₀ f₁ : Y → M) (hf₀ : IsProperMap f₀) (hf₁ : IsProperMap f₁) (p₀ p₁ : Y)
    (h₀ : range f₀ ⊆ A) (h₁ : range f₁ ⊆ B) :
    ∃ gamma : ℝ → M, ∀ s t : ℝ,
      riemannianEDistOf (I := I) g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  exact exists_riemannian_metric_line_of_two_ends g hcomplete
    (hasAtLeastEnds_two_of_proper_maps_into_separated_sets hK hA hB hdisjoint hcover
      f₀ f₁ hf₀ hf₁ p₀ p₁ h₀ h₁)

end DifferentialGeometry.Geometry.Topology
