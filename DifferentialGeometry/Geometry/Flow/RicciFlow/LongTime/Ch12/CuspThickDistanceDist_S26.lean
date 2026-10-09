import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceVolume_S26
import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

set_option autoImplicit false
noncomputable section
open Set Function Manifold Filter DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Topology.Manifold GC.Endpoint
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- The vertical ray of a cusp has unit speed, so its length is the height. -/
theorem edist_cusp_ray_le_S26 (i : Fin T.count) (θ : Torus) {z : ℝ} (hz : 0 ≤ z) :
    riemannianEDistOf H.metric (T.cuspMap i (θ, halfSpaceOneLift 0))
      (T.cuspMap i (θ, halfSpaceOneLift z)) ≤ ENNReal.ofReal z := by
  let σ : ℝ → CuspHalfSpace := fun r => (θ, halfSpaceOneLift r)
  have hσsm : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 σ (Icc 0 z) :=
    (contMDiffOn_const.prodMk (contMDiffOn_halfSpaceOneLift.mono
      (fun r hr => hr.1))).of_le (by exact_mod_cast le_top)
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (T.cuspMap i ∘ σ) (Icc 0 z) :=
    (((T.cuspEmbedding i).contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn).comp hσsm
      Set.subset_preimage_univ
  have hspeed : ∀ r ∈ Ioo 0 z, Real.sqrt (H.metric.inner ((T.cuspMap i ∘ σ) r)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (T.cuspMap i ∘ σ) r 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (T.cuspMap i ∘ σ) r 1)) ≤ 1 := by
    intro r hr
    have hζd := hasMFDerivAt_halfSpaceOneLift_of_pos hr.1
    have hσmd : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel σ r :=
      (mdifferentiableAt_const).prodMk hζd.mdifferentiableAt
    have hed : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) (σ r) :=
      ((T.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp))
    have hchain : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (T.cuspMap i ∘ σ) r 1 =
        mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (σ r)
          (mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r 1) := by
      rw [mfderiv_comp r hed hσmd]
      rfl
    set w : TangentSpace halfCollarModel (σ r) := mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r 1 with hw
    have hder : (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift r 1 : EuclideanSpace ℝ (Fin 1)) =
        (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : EuclideanSpace ℝ (Fin 1)) := by
      rw [hζd.mfderiv]
      exact one_smul ℝ _
    have hprod : mfderiv 𝓘(ℝ, ℝ) halfCollarModel σ r =
        (mfderiv 𝓘(ℝ, ℝ) torusModel (fun _ : ℝ => θ) r).prod
          (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift r) :=
      mfderiv_prodMk (mdifferentiableAt_const) hζd.mdifferentiableAt
    have hw1 : w.1 = 0 := by
      rw [hw, hprod]
      simp [mfderiv_const]
      rfl
    have hw2 : w.2 0 = 1 := by
      rw [hw, hprod]
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hder
      exact this.trans (by simp)
    have hiso := T.cuspIsometry i (σ r) w w
    change Real.sqrt (H.metric.inner (T.cuspMap i (σ r))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (T.cuspMap i ∘ σ) r 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (T.cuspMap i ∘ σ) r 1)) ≤ 1
    have h00 : (T.cusp i).torusMetric.inner (σ r).1
        (0 : TangentSpace torusModel (σ r).1) 0 = 0 := by
      rw [map_zero]
    rw [hchain, hiso, (T.cusp i).metric_formula, hw1, hw2]
    erw [h00]
    simp
  have hd := riemannianEDistOf_le_of_curve_speed_bound H.metric hz hc hspeed
  simpa [σ, Function.comp] using hd

/-- Core points are within a uniform distance of `x`. -/
theorem exists_edist_core_le_S26 (x : H.Carrier) :
    ∃ D : ℝ, ∀ p ∈ range T.inclusion, riemannianEDistOf H.metric x p ≤ ENNReal.ofReal D := by
  have hK : IsCompact (range T.inclusion) := isCompact_range T.inclusion.continuous
  have hcont : Continuous fun p => (riemannianEDistOf H.metric x p).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous (Riemannian.continuous_riemannianEDist H.metric x)
      (fun p => riemannianEDistOf_ne_top H.metric x p)
  obtain ⟨D, hD⟩ := (hK.image hcont).bddAbove
  refine ⟨D, fun p hp => ?_⟩
  rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top H.metric x p)]
  exact ENNReal.ofReal_le_ofReal (hD ⟨p, hp, rfl⟩)

/-- Cusp points are within `D + height` of `x`. -/
theorem exists_edist_cusp_le_S26 (x : H.Carrier) (i : Fin T.count) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : CuspHalfSpace,
      riemannianEDistOf H.metric x (T.cuspMap i q) ≤ ENNReal.ofReal (D + q.2.val 0) := by
  obtain ⟨D, hD⟩ := exists_edist_core_le_S26 T x
  refine ⟨max D 0, le_max_right _ _, fun q => ?_⟩
  have hz : 0 ≤ q.2.val 0 := q.2.2
  have hq : q = (q.1, halfSpaceOneLift (q.2.val 0)) := by
    refine Prod.ext rfl ?_
    exact (halfSpaceOneLift_val_zero_self q.2).symm
  have h0 : T.cuspMap i (q.1, halfSpaceOneLift 0) = T.inclusion (T.boundary.torusMap i q.1) := by
    have := T.cusp_zero i q.1
    rw [← this]
    have hh : halfSpaceOneLift 0 = halfZero := by
      apply Subtype.ext
      ext j
      rw [Subsingleton.elim j 0]
      change max (0 : ℝ) 0 = _
      simp [halfZero]
      rfl
    rw [hh]
  have h1 := riemannianEDistOf_triangle H.metric x (T.cuspMap i (q.1, halfSpaceOneLift 0))
    (T.cuspMap i q)
  have h2 := edist_cusp_ray_le_S26 T i q.1 hz
  have h3 := hD (T.inclusion (T.boundary.torusMap i q.1)) (mem_range_self _)
  rw [← h0] at h3
  rw [← hq] at h2
  refine h1.trans ?_
  calc _ ≤ ENNReal.ofReal D + ENNReal.ofReal (q.2.val 0) := add_le_add h3 h2
    _ ≤ ENNReal.ofReal (max D 0) + ENNReal.ofReal (q.2.val 0) := by gcongr; exact le_max_left _ _
    _ = _ := (ENNReal.ofReal_add (le_max_right _ _) hz).symm

end GC.LongTime.Ch12
