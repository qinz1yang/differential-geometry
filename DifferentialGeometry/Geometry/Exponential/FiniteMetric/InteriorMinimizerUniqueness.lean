import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.RayDistance
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed

/-!
Interior points of a longer minimizing radial geodesic have a unique minimizing initial
direction. Finite first variation forces every reverse minimizing velocity to oppose the
forward velocity, and uniqueness of the actual finite geodesic flow recovers the initial data.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace Bundle.ContMDiffRiemannianMetric

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [groupE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  {H : Type*} [topologyH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundarylessI : I.Boundaryless] {M : Type*} [metricM : MetricSpace M]
  [chartsM : ChartedSpace H M] [manifoldM : IsManifold I ∞ M]
  [bundleM : RiemannianBundle (fun x : M => TangentSpace I x)]
  [riemannianM : IsRiemannianManifold I M] [completeM : CompleteSpace M] {r : ℕ∞}

theorem eq_of_expMap_eq_on_interior_minimizing_ray
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {u v : E} {a s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hmin : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (heq : g.expMap (⟨o, s • v⟩ : TangentBundle I M) =
      g.expMap (⟨o, s • u⟩ : TangentBundle I M)) :
    v = u := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom (p : TangentBundle I M) (t : ℝ) : (p, t) ∈ g.geodesicFlowDomain := by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]
    exact mem_univ (p, t)
  let pu := g.geodesicFlow (⟨o, u⟩ : TangentBundle I M) s
  let pv := g.geodesicFlow (⟨o, v⟩ : TangentBundle I M) s
  let q : M := pu.proj
  let U : E := pu.snd
  let V : E := pv.snd
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner q
  have hqu : g.expMap (⟨o, s • u⟩ : TangentBundle I M) = q :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 o u s (hdom ⟨o, u⟩ s)
  have hqv : pv.proj = q :=
    (g.expMap_smul_eq_proj_geodesicFlow hr1 o v s (hdom ⟨o, v⟩ s)).symm.trans
      (heq.trans hqu)
  have hrad := (g.dist_expMap_smul_eq_of_dist_eq hr1 hnorm hu hmin).1
  have hdist : dist o q = s := by
    rw [← hqu]
    exact hrad s ⟨hs.le, hsa.le⟩
  have hqne : q ≠ o := by
    intro hqo
    rw [hqo, dist_self] at hdist
    exact hs.ne' hdist.symm
  have hU : g.inner q U U = 1 :=
    (g.inner_geodesicFlow_eq hr1 ⟨o, u⟩ s (hdom ⟨o, u⟩ s)).trans hu
  have hV : g.inner q V V = 1 := by
    rw [← hqv]
    exact (g.inner_geodesicFlow_eq hr1 ⟨o, v⟩ s (hdom ⟨o, v⟩ s)).trans hv
  change B U U = 1 at hU
  change B V V = 1 at hV
  have hback (w : E) :
      g.geodesicFlow (g.geodesicFlow (⟨o, w⟩ : TangentBundle I M) s) (-s) =
        (⟨o, w⟩ : TangentBundle I M) := by
    have h := g.geodesicFlow_add hr1 (hdom ⟨o, w⟩ s) (hdom ⟨o, w⟩ (s + -s))
    simpa only [add_neg_cancel, g.geodesicFlow_zero hr1] using h.symm
  have hreverse :
      g.expMap (⟨q, s • (-V)⟩ : TangentBundle I M) = o := by
    apply (g.expMap_smul_eq_proj_geodesicFlow hr1 q (-V) s
      (hdom ⟨q, -V⟩ s)).trans
    have h := g.geodesicFlow_smul_eq hr1 pv (-1) s (hdom pv (-1 * s))
    have hstate : g.geodesicFlow (⟨q, -V⟩ : TangentBundle I M) s =
        (⟨o, -v⟩ : TangentBundle I M) := by
      have hb : g.geodesicFlow pv (-s) = (⟨o, v⟩ : TangentBundle I M) := hback v
      have hscaled : g.geodesicFlow (⟨q, -V⟩ : TangentBundle I M) s =
          (⟨(g.geodesicFlow pv (-s)).proj, -(g.geodesicFlow pv (-s)).snd⟩ :
            TangentBundle I M) := by
        have hp : (⟨q, -V⟩ : TangentBundle I M) =
            (⟨pv.proj, -pv.snd⟩ : TangentBundle I M) := by
          apply TotalSpace.ext
          · exact hqv.symm
          · rfl
        have hsigned := congrArg
          (fun p : TangentBundle I M => g.geodesicFlow p s) hp
        have hmodel : g.geodesicFlow (⟨pv.proj, -pv.snd⟩ : TangentBundle I M) s =
            (⟨(g.geodesicFlow pv (-s)).proj, -(g.geodesicFlow pv (-s)).snd⟩ :
              TangentBundle I M) := by
          erw [neg_one_mul] at h
          simpa only [neg_one_smul] using h
        exact hsigned.trans hmodel
      exact hscaled.trans (congrArg
        (fun p : TangentBundle I M => (⟨p.proj, -(p.snd : E)⟩ : TangentBundle I M)) hb)
    exact congrArg TotalSpace.proj hstate
  have hminReverse : -V ∈ finiteMinimizingDirectionsTo g ({o} : Set M) q := by
    refine ⟨?_, ?_⟩
    · change B (-V) (-V) = 1
      simpa only [map_neg, neg_apply, neg_neg] using hV
    · rw [Metric.infDist_singleton, dist_comm, hdist]
      exact mem_singleton_iff.mpr hreverse
  let γ : ℝ → M := fun t => (g.geodesicFlow (⟨o, u⟩ : TangentBundle I M) (s + t)).proj
  have hγ0 : γ 0 = q := by simp only [γ, add_zero]; rfl
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => s + t) 0
      (ContinuousLinearMap.id ℝ ℝ) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr ((hasFDerivAt_id (0 : ℝ)).const_add s)
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight U) := by
    have hflow : HasMFDerivAt 𝓘(ℝ, ℝ) I
        (fun t => (g.geodesicFlow (⟨o, u⟩ : TangentBundle I M) t).proj) (s + 0)
        ((1 : ℝ →L[ℝ] ℝ).smulRight U) := by
      dsimp only [U, pu]
      erw [add_zero]
      exact g.hasMFDerivAt_geodesicFlow_proj hr1 (hdom ⟨o, u⟩ s)
    have h := hflow.comp 0 hshift
    convert! h using 1
  have hbound : 1 ≤ -g.inner q (-V) U := by
    by_contra hnot
    obtain ⟨c, hc, hc1⟩ := exists_between (lt_of_not_ge hnot)
    have hev := eventually_infDist_sub_le_finite_of_eq g hr hnorm isClosed_singleton
      (singleton_nonempty o) hγ0 hγ (by simpa only [mem_singleton_iff] using hqne)
      hminReverse hc
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < a - s := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by linarith : (0 : ℝ) < a - s)).filter_mono
          nhdsWithin_le_nhds] with t ht htupper
      exact ⟨ht, htupper⟩
    obtain ⟨t, ht, hineq⟩ := (hsmall.and hev).exists
    have hγdist : dist o (γ t) = s + t := by
      change dist o (g.geodesicFlow (⟨o, u⟩ : TangentBundle I M) (s + t)).proj = s + t
      rw [← g.expMap_smul_eq_proj_geodesicFlow hr1 o u (s + t)
        (hdom ⟨o, u⟩ (s + t))]
      exact hrad (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [Metric.infDist_singleton, Metric.infDist_singleton, dist_comm (γ t) o,
      dist_comm q o, hγdist, hdist] at hineq
    have htc := mul_lt_mul_of_pos_left hc1 ht.1
    linarith
  have hinner : 1 ≤ g.inner q V U := by
    have hneg : g.inner q (-V) U = -g.inner q V U := by
      change B (-V) U = -B V U
      simp only [map_neg, neg_apply]
    rwa [hneg, neg_neg] at hbound
  have hdiff : V - U = 0 := by
    by_contra hne
    have hpos := g.pos q (V - U) hne
    have hsym : B U V = B V U := g.symm q U V
    have hexpand : g.inner q (V - U) (V - U) =
        2 - 2 * g.inner q V U := by
      change B (V - U) (V - U) = 2 - 2 * B V U
      simp only [map_sub, sub_apply]
      change B V V - B U V - (B V U - B U U) = 2 - 2 * B V U
      rw [hU, hV, hsym]
      ring
    rw [hexpand] at hpos
    linarith
  have hstate : pv = pu := by
    apply TotalSpace.ext hqv
    exact heq_of_eq (show (pv.snd : E) = (pu.snd : E) from sub_eq_zero.mp hdiff)
  have hstates := congrArg (fun p : TangentBundle I M => g.geodesicFlow p (-s)) hstate
  rw [hback v, hback u] at hstates
  exact congrArg (fun p : TangentBundle I M => (p.snd : E)) hstates

theorem minimizingDirections_singleton_on_interior_radial_arm
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {u : E} {a s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hu : g.inner o u u = 1)
    (hmin : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a) :
    finiteMinimizingDirectionsTo g {g.expMap (⟨o, s • u⟩ : TangentBundle I M)} o = {u} := by
  have hdist := (g.dist_expMap_smul_eq_of_dist_eq (one_le_two.trans hr)
    hnorm hu hmin).1 s ⟨hs.le, hsa.le⟩
  ext v
  constructor
  · intro hv
    have hreach : g.expMap (⟨o, s • v⟩ : TangentBundle I M) =
        g.expMap (⟨o, s • u⟩ : TangentBundle I M) := by
      have hend := hv.2
      rw [Metric.infDist_singleton, hdist] at hend
      exact mem_singleton_iff.mp hend
    exact mem_singleton_iff.mpr
      (g.eq_of_expMap_eq_on_interior_minimizing_ray hr hnorm hs hsa hu hv.1 hmin hreach)
  · intro hv
    have hvu := mem_singleton_iff.mp hv
    subst v
    refine ⟨hu, ?_⟩
    rw [Metric.infDist_singleton, hdist]
    exact mem_singleton (g.expMap (⟨o, s • u⟩ : TangentBundle I M))

end Bundle.ContMDiffRiemannianMetric
