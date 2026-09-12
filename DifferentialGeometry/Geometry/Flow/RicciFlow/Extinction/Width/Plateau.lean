import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ImmersionTraceLift

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

structure DiskLocalExtension (u : Disk → Q) (z : Disk) where
  map : ℂ → Q
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  mem_domain : (z : ℂ) ∈ domain
  smooth : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ map domain
  agrees : EqOn map (diskExtension u) (domain ∩ Metric.closedBall (0 : ℂ) 1)

structure SmoothDisk where
  map : C(Disk, Q)
  smooth : ∀ z : Disk, Nonempty (DiskLocalExtension (I := I) map z)

omit [IsManifold I ∞ Q] in
theorem SmoothDisk.contMDiffOn_extension (u : SmoothDisk (I := I) (Q := Q)) :
    ContMDiffOn 𝓘(ℝ, ℂ) I ∞ (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) := by
  intro z hz
  obtain ⟨F⟩ := u.smooth ⟨z, hz⟩
  have hdomain : F.domain ∈ 𝓝 z := F.isOpen_domain.mem_nhds F.mem_domain
  have hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F.map z :=
    (F.smooth z F.mem_domain).contMDiffAt hdomain
  have hdomainWithin : F.domain ∈ 𝓝[Metric.closedBall (0 : ℂ) 1] z :=
    nhdsWithin_le_nhds hdomain
  apply hF.contMDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
  filter_upwards [self_mem_nhdsWithin, hdomainWithin] with w hw hdomainw
  exact (F.agrees ⟨hdomainw, hw⟩).symm

def SmoothDisk.differential (u : SmoothDisk (I := I) (Q := Q)) (z : Disk)
    (v : ℂ) : TangentSpace I (u.map z) := by
  simpa only [diskExtension_coe] using
    mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) v

def SmoothDisk.IsConformal (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ z : Disk,
    g.inner (u.map z) (u.differential z 1) (u.differential z Complex.I) = 0 ∧
    g.inner (u.map z) (u.differential z 1) (u.differential z 1) =
      g.inner (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)

private theorem sqrt_inner_smul (g : SmoothRiemannianMetric I Q) (p : Q)
    (v : TangentSpace I p) (c : ℝ) (hc : 0 ≤ c) :
    Real.sqrt (g.inner p (c • v) (c • v)) = c * Real.sqrt (g.inner p v v) := by
  have hEq : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hEq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

private theorem disk_within_speed_bound (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ v : ℂ,
      Real.sqrt (g.inner (diskExtension u.map z)
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (v : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (v : ℂ)))
        ≤ V * ‖v‖ := by
  have hud : UniqueMDiffOn 𝓘(ℝ, ℂ) (Metric.closedBall (0 : ℂ) 1) :=
    fun z hz => (disk_uniqueDiffWithinAt ⟨z, hz⟩).uniqueMDiffWithinAt
  let j : Disk × Disk → TangentBundle 𝓘(ℝ, ℂ) ℂ := fun p =>
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm ((p.1 : ℂ), (p.2 : ℂ))
  have hj : Continuous j :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hjet := u.contMDiffOn_extension.continuousOn_tangentMapWithin (by simp) hud
  have hc : Continuous (fun p : Disk × Disk =>
      tangentMapWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) (j p)) :=
    hjet.comp_continuous hj (fun p => p.1.property)
  have hs := (continuous_tangentMetricSpeed g).comp hc
  obtain ⟨V, hV⟩ := (isCompact_range hs).bddAbove
  have hunit (z v : Disk) :
      Real.sqrt (g.inner (diskExtension u.map z)
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (v : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z (v : ℂ)))
        ≤ max 0 V := by
    exact (hV ⟨(z, v), rfl⟩).trans (le_max_right _ _)
  refine ⟨max 0 V, le_max_left _ _, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · subst v
    let A : ℂ →L[ℝ] TangentSpace I (diskExtension u.map z) :=
      mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z
    change Real.sqrt (g.inner (diskExtension u.map z) (A 0) (A 0)) ≤ max 0 V * ‖(0 : ℂ)‖
    simp
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let w : ℂ := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hn, le_refl]
    have heq : ‖v‖ • w = v := by
      simp only [w, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have hb := hunit (⟨z, hz⟩ : Disk) (⟨w, hw⟩ : Disk)
    have hscale := sqrt_inner_smul g (diskExtension u.map z)
      (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z w)
      ‖v‖ (norm_nonneg v)
    have hd : mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) z v =
      ‖v‖ • mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) z w := by
      let A : ℂ →L[ℝ] TangentSpace I (diskExtension u.map z) :=
        mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z
      change A v = ‖v‖ • A w
      calc
        A v = A (‖v‖ • w) := congrArg A heq.symm
        _ = ‖v‖ • A w := A.map_smul ‖v‖ w
    rw [hd, hscale]
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg v)).trans_eq (mul_comm _ _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem riemannianEDistOf_le_within_speed_bound
    (g : SmoothRiemannianMetric I Q) (gamma : ℝ → Q)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1))
    (V : ℝ)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, Real.sqrt (g.inner (gamma t)
      (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1)) ≤ V) :
    riemannianEDistOf g (gamma 0) (gamma 1) ≤ ENNReal.ofReal V := by
  let : RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
  have hp := Manifold.riemannianEDist_le_pathELength (I := I) hgamma rfl rfl zero_le_one
  change riemannianEDistOf g (gamma 0) (gamma 1) ≤ pathELength I gamma 0 1 at hp
  apply hp.trans
  calc
    pathELength I gamma 0 1 = ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (g.inner (gamma t)
          (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1)
          (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1))) := by
      rw [pathELength_eq_lintegral_mfderivWithin_Icc]
      apply lintegral_congr
      intro t
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      congr 2
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal V :=
      setLIntegral_mono' measurableSet_Icc (fun t ht => ENNReal.ofReal_le_ofReal (hV t ht))
    _ = ENNReal.ofReal V := by
      rw [setLIntegral_const, Real.volume_Icc]
      simp

private theorem smooth_disk_edist_bound (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ z w : Disk,
      riemannianEDistOf g (u.map z) (u.map w) ≤ ENNReal.ofReal V * edist z w := by
  obtain ⟨V, hV, hbound⟩ := disk_within_speed_bound g u
  refine ⟨V, hV, ?_⟩
  intro z w
  let line : ℝ → ℂ := fun t => (z : ℂ) + t • ((w : ℂ) - (z : ℂ))
  have hmaps : MapsTo line (Icc (0 : ℝ) 1) (Metric.closedBall (0 : ℂ) 1) :=
    fun t ht => (convex_closedBall (0 : ℂ) 1).add_smul_sub_mem z.property w.property ht
  have hline : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  let gamma : ℝ → Q := diskExtension u.map ∘ line
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc (0 : ℝ) 1) :=
    (u.contMDiffOn_extension.comp hline.contMDiff.contMDiffOn hmaps).of_le (by simp)
  have hgamma0 : gamma 0 = u.map z := by simp [gamma, line, diskExtension_coe]
  have hgamma1 : gamma 1 = u.map w := by simp [gamma, line, diskExtension_coe]
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Real.sqrt (g.inner (gamma t)
        (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1)
        (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1)) ≤ V * ‖(w : ℂ) - (z : ℂ)‖ := by
    have hud := (uniqueDiffOn_Icc_zero_one t ht).uniqueMDiffWithinAt
    have hdl : HasDerivAt line ((w : ℂ) - (z : ℂ)) t := by
      simpa only [line, id_eq, one_smul] using! ((hasDerivAt_id t).smul_const ((w : ℂ) - (z : ℂ))).const_add (z : ℂ)
    have hdu := (u.contMDiffOn_extension (line t) (hmaps ht)).mdifferentiableWithinAt (by simp)
    have hd := mfderivWithin_comp t hdu
      hdl.hasFDerivAt.hasMFDerivAt.mdifferentiableAt.mdifferentiableWithinAt hmaps hud
    have hdl' := hdl.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt.mfderivWithin hud
    rw [hdl'] at hd
    have hd1 := congrArg (fun L : ℝ →L[ℝ] TangentSpace I (gamma t) => L 1) hd
    have heq : mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1 =
        mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1)
          (line t) ((w : ℂ) - (z : ℂ)) := by
      change mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t (1 : ℝ) =
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
          (Metric.closedBall (0 : ℂ) 1) (line t) :
          ℂ →L[ℝ] TangentSpace I (gamma t)) ((1 : ℝ) • ((w : ℂ) - (z : ℂ))) at hd1
      simpa only [one_smul] using! hd1
    rw [heq]
    exact hbound (line t) (hmaps ht) ((w : ℂ) - (z : ℂ))
  have hp := riemannianEDistOf_le_within_speed_bound g gamma hgamma (V * ‖(w : ℂ) - (z : ℂ)‖) hs
  rw [hgamma0, hgamma1, ENNReal.ofReal_mul hV] at hp
  have he : edist z w = ENNReal.ofReal ‖(w : ℂ) - (z : ℂ)‖ := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (z : ℂ) (w : ℂ)) = _
    rw [dist_eq_norm, norm_sub_rev]
  simpa only [he] using hp

variable [FiniteDimensional ℝ E]

def diskLocalTension (g : SmoothRiemannianMetric I Q) (F : ℂ → Q) (z : ℂ) :
    TangentSpace I (F z) := by
  have v₁ : TangentSpace I (F z) := by
    simpa only [zero_smul, add_zero] using
      covDerivAlong g (fun t : ℝ => F (z + t • (1 : ℂ)))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I F (z + t • (1 : ℂ)) (1 : ℂ)) 0
  have v₂ : TangentSpace I (F z) := by
    simpa only [zero_smul, add_zero] using
      covDerivAlong g (fun t : ℝ => F (z + t • Complex.I))
        (fun t => mfderiv 𝓘(ℝ, ℂ) I F (z + t • Complex.I) Complex.I) 0
  exact v₁ + v₂

def SmoothDisk.IsHarmonic (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ z : Disk, ∀ F : DiskLocalExtension (I := I) u.map z,
    diskLocalTension g F.map (z : ℂ) = 0

def DiskLocalTensionClosureLocality (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ {F G : ℂ → Q} {U : Set ℂ}, IsOpen U → EqOn F G U → ∀ {z : ℂ}, z ∈ closure U →
    ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z → ContMDiffAt 𝓘(ℝ, ℂ) I ∞ G z →
    (diskLocalTension g F z : E) = (diskLocalTension g G z : E)

theorem diskLocalTension_congr_of_eqOn_of_mem_closure (g : SmoothRiemannianMetric I Q)
    (hloc : DiskLocalTensionClosureLocality (I := I) (Q := Q) g)
    {F G : ℂ → Q} {U : Set ℂ} (hU : IsOpen U) (hFG : EqOn F G U) {z : ℂ}
    (hz : z ∈ closure U) (hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z)
    (hG : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ G z) :
    (diskLocalTension g F z : E) = (diskLocalTension g G z : E) :=
  hloc hU hFG hz hF hG

theorem SmoothDisk.isHarmonic_of_localExtension (g : SmoothRiemannianMetric I Q)
    (hloc : DiskLocalTensionClosureLocality (I := I) (Q := Q) g)
    (u : SmoothDisk (I := I) (Q := Q))
    {U : ℂ → Q} {N : Set ℂ} (hN : IsOpen N) (hDN : Metric.closedBall (0 : ℂ) 1 ⊆ N)
    (hsm : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U N)
    (hag : EqOn U (diskExtension u.map) (N ∩ Metric.closedBall (0 : ℂ) 1))
    (hharm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (diskLocalTension g U z : E) = 0) :
    u.IsHarmonic g := by
  intro z F
  have hNmem : N ∈ 𝓝 (z : ℂ) := hN.mem_nhds (hDN z.property)
  have hmem : F.domain ∩ N ∈ 𝓝 (z : ℂ) :=
    Filter.inter_mem (F.isOpen_domain.mem_nhds F.mem_domain) hNmem
  have hball : (z : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact z.property
  have hzcl : (z : ℂ) ∈ closure (F.domain ∩ N ∩ Metric.ball (0 : ℂ) 1) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    have hA : t ∩ (F.domain ∩ N) ∈ 𝓝 (z : ℂ) := Filter.inter_mem ht hmem
    obtain ⟨w, hwtA, hwb⟩ := mem_closure_iff_nhds.mp hball (t ∩ (F.domain ∩ N)) hA
    obtain ⟨hwt, hwd, hwN⟩ := hwtA
    exact ⟨w, hwt, ⟨hwd, hwN⟩, hwb⟩
  have hVopen : IsOpen (F.domain ∩ N ∩ Metric.ball (0 : ℂ) 1) :=
    (F.isOpen_domain.inter hN).inter Metric.isOpen_ball
  have heq : EqOn F.map U (F.domain ∩ N ∩ Metric.ball (0 : ℂ) 1) := by
    intro w hw
    obtain ⟨⟨hwd, hwN⟩, hwb⟩ := hw
    rw [F.agrees ⟨hwd, Metric.ball_subset_closedBall hwb⟩,
      hag ⟨hwN, Metric.ball_subset_closedBall hwb⟩]
  have hFsm : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F.map (z : ℂ) :=
    (F.smooth (z : ℂ) F.mem_domain).contMDiffAt (F.isOpen_domain.mem_nhds F.mem_domain)
  have hUsm : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ U (z : ℂ) :=
    (hsm (z : ℂ) (hDN z.property)).contMDiffAt hNmem
  rw [hloc hVopen heq hzcl hFsm hUsm]
  exact hharm (z : ℂ) z.property

structure SmoothWeaklyMonotoneCircleMap where
  map : C(Surgery.Topology.Circle, Surgery.Topology.Circle)
  lift : ℝ → ℝ
  smooth_lift : ContDiff ℝ ∞ lift
  monotone_lift : Monotone lift
  increment : ∀ t, lift (t + 1) = lift t + 1
  lift_eq : ∀ t : ℝ, map (t : Surgery.Topology.Circle) = (lift t : Surgery.Topology.Circle)


theorem SmoothWeaklyMonotoneCircleMap.isWeaklyMonotone
    (σ : SmoothWeaklyMonotoneCircleMap) : IsWeaklyMonotoneCircleMap σ.map :=
  ⟨σ.lift, σ.smooth_lift.continuous, σ.monotone_lift, σ.increment, σ.lift_eq⟩

private theorem rectangle_uniqueMDiff : UniqueMDiffOn 𝓘(ℝ, ℂ) annulusRectangle := by
  have hprod := uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hrect : UniqueDiffOn ℝ annulusRectangle :=
    Complex.equivRealProdCLM.uniqueDiffOn_preimage_iff.mpr hprod
  exact fun z hz => (hrect z hz).uniqueMDiffWithinAt

private theorem periodic_lift_continuous {f : ℝ → ℝ}
    (hf : Function.Periodic f 1) (hc : Continuous f) : Continuous hf.lift := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun x : ℝ => hf.lift (x : Surgery.Topology.Circle))
  simpa only [Function.Periodic.lift_coe] using! hc


private theorem exists_short_circle_lifts (x y : Surgery.Topology.Circle) :
    ∃ a d : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ -(1 / 2 : ℝ) ≤ d ∧ d ≤ 1 / 2 ∧
      (a : Surgery.Topology.Circle) = y ∧ ((a + d : ℝ) : Surgery.Topology.Circle) = x ∧
      dist x y = |d| := by
  let a := AddCircle.equivIco (1 : ℝ) 0 y
  let d := AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (x - y)
  have ha : 0 ≤ a.1 ∧ a.1 < 1 := by simpa using a.2
  have hd : -(1 / 2 : ℝ) ≤ d.1 ∧ d.1 < 1 / 2 := by convert! d.2 using 1; norm_num
  have haq : (a.1 : Surgery.Topology.Circle) = y := AddCircle.coe_equivIco
  have hdq : (d.1 : Surgery.Topology.Circle) = x - y := AddCircle.coe_equivIco
  have hadq : ((a.1 + d.1 : ℝ) : Surgery.Topology.Circle) = x := by
    rw [AddCircle.coe_add, haq, hdq]
    abel
  have hdabs : |d.1| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]
    exact ⟨hd.1, hd.2.le⟩
  have hnorm : ‖(d.1 : Surgery.Topology.Circle)‖ = |d.1| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hdabs
  refine ⟨a.1, d.1, ha.1, ha.2.le, hd.1, hd.2.le, haq, hadq, ?_⟩
  rw [dist_eq_norm, ← hdq]
  exact hnorm

private theorem periodic_smooth_lift_lipschitz {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ L : ℝ≥0, LipschitzWith L hp.lift := by
  have hderiv := hf.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn
    hderiv.continuousOn
  refine ⟨NNReal.mk (max 0 C) (le_max_left _ _), ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨a, d, ha0, ha1, hd0, hd1, hay, hadx, hdist⟩ := exists_short_circle_lifts x y
  have ha : a ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
  have had : a + d ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
  have hconv : Convex ℝ (Icc (-1 : ℝ) 2) := convex_Icc _ _
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hC x hx).trans (le_max_right 0 C)) hconv ha had
  have hx : hp.lift x = f (a + d) := by rw [← hadx]; rfl
  have hy : hp.lift y = f a := by rw [← hay]; rfl
  rw [hx, hy, hdist, dist_eq_norm]
  simpa only [NNReal.coe_mk, add_sub_cancel_left, Real.norm_eq_abs] using hb

private theorem displacement_periodic (sigma : SmoothWeaklyMonotoneCircleMap) :
    Function.Periodic (fun x => sigma.lift x - x) 1 := by
  intro x
  change sigma.lift (x + 1) - (x + 1) = sigma.lift x - x
  rw [sigma.increment]
  ring

private def displacement (sigma : SmoothWeaklyMonotoneCircleMap) :
    Surgery.Topology.Circle → ℝ := (displacement_periodic sigma).lift

private theorem displacement_coe (sigma : SmoothWeaklyMonotoneCircleMap) (x : ℝ) :
    displacement sigma (x : Surgery.Topology.Circle) = sigma.lift x - x := rfl

private theorem displacement_continuous (sigma : SmoothWeaklyMonotoneCircleMap) :
    Continuous (displacement sigma) :=
  periodic_lift_continuous (displacement_periodic sigma)
    (sigma.smooth_lift.continuous.sub continuous_id)

private theorem displacement_lipschitz (sigma : SmoothWeaklyMonotoneCircleMap) :
    ∃ L : ℝ≥0, LipschitzWith L (displacement sigma) :=
  periodic_smooth_lift_lipschitz (sigma.smooth_lift.sub contDiff_id) (displacement_periodic sigma)

private def interpolationCircle (sigma : SmoothWeaklyMonotoneCircleMap) (z : Annulus) :
    Surgery.Topology.Circle := z.2 + (((1 - (z.1 : ℝ)) * displacement sigma z.2 : ℝ) :
      Surgery.Topology.Circle)

private theorem interpolationCircle_lipschitz (sigma : SmoothWeaklyMonotoneCircleMap) :
    ∃ L : ℝ≥0, LipschitzWith L (interpolationCircle sigma) := by
  obtain ⟨K, hK⟩ := displacement_lipschitz sigma
  obtain ⟨B1, hB1⟩ := (isCompact_range (displacement_continuous sigma).norm).bddAbove
  let B : ℝ := max 0 B1
  have hB : 0 ≤ B := le_max_left _ _
  have hb (x : Surgery.Topology.Circle) : |displacement sigma x| ≤ B := by
    simpa only [Real.norm_eq_abs] using (hB1 ⟨x, rfl⟩).trans (le_max_right 0 B1)
  let L : ℝ≥0 := NNReal.mk (1 + K + B) (by positivity)
  refine ⟨L, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  have hs : |(w.1 : ℝ) - (z.1 : ℝ)| ≤ dist z w := by
    simpa only [Prod.dist_eq, Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using
      (le_max_left (dist z.1 w.1) (dist z.2 w.2))
  have htheta : dist z.2 w.2 ≤ dist z w := le_max_right _ _
  have hunit : |1 - (z.1 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr z.1.property.2)]
    linarith [z.1.property.1]
  have hdelta : |displacement sigma z.2 - displacement sigma w.2| ≤
      (K : ℝ) * dist z.2 w.2 := by simpa only [Real.dist_eq] using hK.dist_le_mul z.2 w.2
  have hr : |(1 - (z.1 : ℝ)) * displacement sigma z.2 -
      (1 - (w.1 : ℝ)) * displacement sigma w.2| ≤ ((K : ℝ) + B) * dist z w := by
    have hsplit : (1 - (z.1 : ℝ)) * displacement sigma z.2 -
        (1 - (w.1 : ℝ)) * displacement sigma w.2 =
      (1 - (z.1 : ℝ)) * (displacement sigma z.2 - displacement sigma w.2) +
        ((w.1 : ℝ) - (z.1 : ℝ)) * displacement sigma w.2 := by ring
    rw [hsplit]
    calc
      _ ≤ |(1 - (z.1 : ℝ)) * (displacement sigma z.2 - displacement sigma w.2)| +
          |((w.1 : ℝ) - (z.1 : ℝ)) * displacement sigma w.2| := abs_add_le _ _
      _ = |1 - (z.1 : ℝ)| * |displacement sigma z.2 - displacement sigma w.2| +
          |(w.1 : ℝ) - (z.1 : ℝ)| * |displacement sigma w.2| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * ((K : ℝ) * dist z.2 w.2) + dist z w * B :=
        add_le_add (mul_le_mul hunit hdelta (abs_nonneg _) (by norm_num))
          (mul_le_mul hs (hb w.2) (abs_nonneg _) (dist_nonneg))
      _ ≤ 1 * ((K : ℝ) * dist z w) + dist z w * B := by
        gcongr
      _ = ((K : ℝ) + B) * dist z w := by ring
  have hquot (r s : ℝ) : dist (r : Surgery.Topology.Circle) (s : Surgery.Topology.Circle) ≤
      |r - s| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    simpa only [Real.norm_eq_abs] using (QuotientAddGroup.norm_mk_le_norm (m := r - s))
  calc
    dist (interpolationCircle sigma z) (interpolationCircle sigma w) ≤
        dist z.2 w.2 + dist
          (((1 - (z.1 : ℝ)) * displacement sigma z.2 : ℝ) : Surgery.Topology.Circle)
          (((1 - (w.1 : ℝ)) * displacement sigma w.2 : ℝ) : Surgery.Topology.Circle) :=
      dist_add_add_le _ _ _ _
    _ ≤ dist z w + ((K : ℝ) + B) * dist z w :=
      add_le_add htheta ((hquot _ _).trans hr)
    _ = (L : ℝ) * dist z w := by dsimp only [L, NNReal.coe_mk]; ring

private theorem interpolationCircle_coe (sigma : SmoothWeaklyMonotoneCircleMap)
    (s : Icc (0 : ℝ) 1) (x : ℝ) :
    interpolationCircle sigma (s, (x : Surgery.Topology.Circle)) =
      (((1 - (s : ℝ)) * sigma.lift x + (s : ℝ) * x : ℝ) : Surgery.Topology.Circle) := by
  unfold interpolationCircle
  rw [displacement_coe, ← AddCircle.coe_add]
  congr 1
  ring

omit [FiniteDimensional ℝ E] in
private theorem curve_phase_jacobian_zero (g : SmoothRiemannianMetric I Q)
    (f : ℝ → Q) (phase : ℂ → ℝ) (s : Set ℂ) (z : ℂ)
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f (phase z))
    (hp : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) phase s z)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) s z) :
    parametricJacobian g (f ∘ phase) s z = 0 := by
  have hc := hf.comp_mdifferentiableWithinAt z hp
  have hd := mfderivWithin_comp z hf.mdifferentiableWithinAt hp
    (show s ⊆ phase ⁻¹' (univ : Set ℝ) from fun _ _ => mem_univ _) hs
  rw [mfderivWithin_univ] at hd
  let A : ℝ →L[ℝ] TangentSpace I (f (phase z)) := mfderiv 𝓘(ℝ, ℝ) I f (phase z)
  let B : ℂ →L[ℝ] ℝ := mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) phase s z
  have hcol (i : Fin 2) :
      mfderivWithin 𝓘(ℝ, ℂ) I (f ∘ phase) s z (diskBasis i) =
        B (diskBasis i) • A 1 := by
    have he := congrArg (fun L : ℂ →L[ℝ] TangentSpace I (f (phase z)) => L (diskBasis i)) hd
    change mfderivWithin 𝓘(ℝ, ℂ) I (f ∘ phase) s z (diskBasis i) = A (B (diskBasis i)) at he
    calc
      _ = A (B (diskBasis i)) := he
      _ = A (B (diskBasis i) • (1 : ℝ)) := congrArg A (by simp)
      _ = B (diskBasis i) • A 1 := A.map_smul _ _
  unfold parametricJacobian
  rw [if_pos hc]
  let D : ℂ →L[ℝ] E := mfderivWithin 𝓘(ℝ, ℂ) I (f ∘ phase) s z
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (f (phase z))
  let v : E := A 1
  change Real.sqrt (Matrix.det (fun i j : Fin 2 => G (D (diskBasis i)) (D (diskBasis j)))) = 0
  have hcolE (i : Fin 2) : D (diskBasis i) = B (diskBasis i) • v := by
    exact hcol i
  have hmatrix : (fun i j : Fin 2 => G (D (diskBasis i)) (D (diskBasis j))) =
      (fun i j : Fin 2 => G (B (diskBasis i) • v) (B (diskBasis j) • v)) := by
    funext i j
    rw [hcolE, hcolE]
  have hgram : Matrix.det (fun i j : Fin 2 =>
      G (B (diskBasis i) • v) (B (diskBasis j) • v)) = 0 := by
    let C : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.of (fun i j => G (B (diskBasis i) • v) (B (diskBasis j) • v))
    change Matrix.det C = 0
    rw [Matrix.det_fin_two]
    dsimp only [C, Matrix.of_apply]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hmatrix, hgram, Real.sqrt_zero]
variable [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
include boundarylessI t2Q compactQ

theorem SmoothDisk.exists_lipschitz (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) :
    ∃ v : LipschitzDisk g, v.map = u.map := by
  let _ := (inferInstance : FiniteDimensional ℝ E)
  let _ := boundarylessI
  let _ := t2Q
  let _ := compactQ
  obtain ⟨V, hV, hbound⟩ := smooth_disk_edist_bound g u
  refine ⟨⟨u.map, ?_⟩, rfl⟩
  refine ⟨NNReal.mk V hV, ?_⟩
  intro z w
  simpa only [ENNReal.ofReal_eq_coe_nnreal hV] using hbound z w

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
theorem trace_interpolation_annulus (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (σ : SmoothWeaklyMonotoneCircleMap) :
    ∃ A : LipschitzAnnulus g,
      (∀ (s : Icc (0 : ℝ) 1) (x : ℝ),
        A.map (s, (x : Surgery.Topology.Circle)) =
          γ (((1 - (s : ℝ)) * σ.lift x + (s : ℝ) * x : ℝ) : Surgery.Topology.Circle)) ∧
      (∀ θ, A.map (⟨0, by simp⟩, θ) = γ (σ.map θ)) ∧
      (∀ θ, A.map (⟨1, by simp⟩, θ) = γ θ) ∧
      (∀ z ∈ annulusRectangle,
        parametricJacobian g (annulusExtension A.map) annulusRectangle z = 0) ∧
      annulusArea g A.map = 0 := by
  obtain ⟨L, hL⟩ := interpolationCircle_lipschitz σ
  obtain ⟨K, hK⟩ := RegularLoop.isLipschitz g γ
  let amap : C(Annulus, Q) :=
    ⟨fun z => γ (interpolationCircle σ z),
      γ.toContinuousLoop.continuous.comp hL.continuous⟩
  have halip : ∃ C : ℝ≥0, ∀ z w : Annulus,
      riemannianEDistOf g (amap z) (amap w) ≤ (C : ℝ≥0∞) * edist z w := by
    refine ⟨K * L, fun z w => ?_⟩
    calc
      _ ≤ (K : ℝ≥0∞) * edist (interpolationCircle σ z) (interpolationCircle σ w) :=
        hK _ _
      _ ≤ (K : ℝ≥0∞) * ((L : ℝ≥0∞) * edist z w) :=
        mul_le_mul' le_rfl (hL z w)
      _ = ((K * L : ℝ≥0) : ℝ≥0∞) * edist z w := by rw [ENNReal.coe_mul, mul_assoc]
  let A : LipschitzAnnulus g := ⟨amap, halip⟩
  have hformula (s : Icc (0 : ℝ) 1) (x : ℝ) :
      A.map (s, (x : Surgery.Topology.Circle)) =
        γ (((1 - (s : ℝ)) * σ.lift x + (s : ℝ) * x : ℝ) : Surgery.Topology.Circle) := by
    change γ (interpolationCircle σ (s, (x : Surgery.Topology.Circle))) = _
    rw [interpolationCircle_coe]
  have hzero (theta : Surgery.Topology.Circle) :
      A.map (⟨0, by simp⟩, theta) = γ (σ.map theta) := by
    refine QuotientAddGroup.induction_on theta ?_
    intro x
    rw [hformula, σ.lift_eq]
    simp
  have hone (theta : Surgery.Topology.Circle) :
      A.map (⟨1, by simp⟩, theta) = γ theta := by
    refine QuotientAddGroup.induction_on theta ?_
    intro x
    rw [hformula]
    simp
  let phase : ℂ → ℝ := fun z => (1 - z.re) * σ.lift z.im + z.re * z.im
  have hphase : ContDiff ℝ ∞ phase :=
    ((contDiff_const.sub Complex.reCLM.contDiff).mul
      (σ.smooth_lift.comp Complex.imCLM.contDiff)).add
      (Complex.reCLM.contDiff.mul Complex.imCLM.contDiff)
  have hext : EqOn (annulusExtension A.map) (loopLift γ.toContinuousLoop ∘ phase)
      annulusRectangle := by
    intro z hz
    rw [annulusExtension_agrees _ hz]
    exact hformula ⟨z.re, hz.1⟩ z.im
  have hjac (z : ℂ) (hz : z ∈ annulusRectangle) :
      parametricJacobian g (annulusExtension A.map) annulusRectangle z = 0 := by
    rw [parametricJacobian_congr_on g hext hz]
    exact curve_phase_jacobian_zero g (loopLift γ.toContinuousLoop) phase annulusRectangle z
      (hγ.mdifferentiable (by simp) (phase z))
      ((hphase.contMDiff.mdifferentiable (by simp) z).mdifferentiableWithinAt)
      (rectangle_uniqueMDiff z hz)
  refine ⟨A, hformula, hzero, hone, hjac, ?_⟩
  have hrect : MeasurableSet annulusRectangle := by unfold annulusRectangle; measurability
  change (∫ z in annulusRectangle,
    parametricJacobian g (annulusExtension A.map) annulusRectangle z) = 0
  calc
    _ = ∫ _z in annulusRectangle, (0 : ℝ) := setIntegral_congr_fun hrect hjac
    _ = 0 := integral_zero _ _

theorem zero_area_trace_annulus (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (σ : SmoothWeaklyMonotoneCircleMap) (u : LipschitzDisk g)
    (htrace : ∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) :
    ∃ v : DiskCompetitor g γ.toContinuousLoop, diskArea g v.1.map = diskArea g u.map := by
  obtain ⟨A, _, hzero, hone, _, harea⟩ := trace_interpolation_annulus g γ hγ σ
  obtain ⟨v, hv⟩ := disk_annulus_gluing g (γ.toContinuousLoop.comp σ.map)
    γ.toContinuousLoop ⟨u, htrace⟩ A hzero hone
  exact ⟨v, by simpa only [harea, add_zero] using hv⟩

theorem smooth_exact_disk_density (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (v : DiskCompetitor g γ.toContinuousLoop) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
      Filter.Tendsto (fun j => diskArea g (w j).map) Filter.atTop (𝓝 (diskArea g v.1.map)) := by
  sorry


def IsSignedWeaklyMonotoneTrace (u : Disk → Q) (γ : Surgery.Topology.ContinuousFreeLoop Q) : Prop :=
  ∃ φ : ℝ → ℝ, Continuous φ ∧
    ((Monotone φ ∧ ∀ t, φ (t + 1) = φ t + 1) ∨
      (Antitone φ ∧ ∀ t, φ (t + 1) = φ t - 1)) ∧
    ∀ t : ℝ, u (diskBoundary (t : Surgery.Topology.Circle)) = γ (φ t : Surgery.Topology.Circle)

omit boundarylessI t2Q compactQ in
def diskReflection (z : Disk) : Disk :=
  ⟨star (z : ℂ), by simpa only [Metric.mem_closedBall, dist_zero_right, norm_star] using z.property⟩


section PlateauTracedisk

omit boundarylessI t2Q compactQ

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem contDiff_star : ContDiff ℝ ∞ (fun z : ℂ => star z) := by
  have h : (fun z : ℂ => star z) = ⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    funext z
    exact congrFun Complex.star_def z
  rw [h]
  exact Complex.conjCLE.contDiff

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem contMDiff_star : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => star z) :=
  contDiff_star.contMDiff

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem mfderivWithin_star (s : Set ℂ) {z : ℂ} (hz : UniqueDiffWithinAt ℝ s z) :
    mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => star w) s z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  have h : (fun w : ℂ => star w) = ⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    funext w
    exact congrFun Complex.star_def w
  rw [h, mfderivWithin_eq_fderivWithin]
  exact (Complex.conjCLE.hasFDerivAt (x := z)).hasFDerivWithinAt.fderivWithin hz

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem star_mem_closedBall {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    star z ∈ Metric.closedBall (0 : ℂ) 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right, norm_star] using hz

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem diskReflection_involutive (z : Disk) : diskReflection (diskReflection z) = z := by
  refine Subtype.ext ?_
  simp only [diskReflection, star_star]

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem diskReflection_lipschitz : LipschitzWith 1 diskReflection := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Subtype.dist_eq, Subtype.dist_eq, NNReal.coe_one, one_mul]
  change dist (star (z : ℂ)) (star (w : ℂ)) ≤ dist (z : ℂ) (w : ℂ)
  exact (Complex.isometry_conj.dist_eq _ _).le

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem diskReflection_continuous : Continuous diskReflection :=
  diskReflection_lipschitz.continuous

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private def diskReflectionHomeo : Disk ≃ₜ Disk where
  toFun := diskReflection
  invFun := diskReflection
  left_inv := diskReflection_involutive
  right_inv := diskReflection_involutive
  continuous_toFun := diskReflection_continuous
  continuous_invFun := diskReflection_continuous

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem diskReflectionHomeo_symm : diskReflectionHomeo.symm = diskReflectionHomeo := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
private theorem diskExtension_comp_diskReflection (u : SmoothDisk (I := I) (Q := Q)) :
    diskExtension (fun z : Disk => u.map (diskReflection z)) =
      diskExtension u.map ∘ (fun z : ℂ => star z) := by
  funext z
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) 1
  · have hz' : star z ∈ Metric.closedBall (0 : ℂ) 1 := star_mem_closedBall hz
    have h1 : diskExtension (fun z : Disk => u.map (diskReflection z)) z =
        u.map (diskReflection ⟨z, hz⟩) := diskExtension_coe _ ⟨z, hz⟩
    have h2 : diskReflection (⟨z, hz⟩ : Disk) = ⟨star z, hz'⟩ := Subtype.ext rfl
    have h3 : u.map (⟨star z, hz'⟩ : Disk) = diskExtension u.map (star z) :=
      (diskExtension_coe u.map ⟨star z, hz'⟩).symm
    rw [Function.comp_apply, h1, h2, h3]
  · have hz' : star z ∉ Metric.closedBall (0 : ℂ) 1 := fun h =>
      hz (by simpa only [star_star] using star_mem_closedBall h)
    have hdc : diskReflection diskCenter = diskCenter := by
      refine Subtype.ext ?_
      simp only [diskReflection, diskCenter, star_zero]
    rw [Function.comp_apply]
    simp only [diskExtension, dif_neg hz, dif_neg hz', hdc]

omit [I.Boundaryless] t2Q compactQ in
def SmoothDisk.diskReflection (u : SmoothDisk (I := I) (Q := Q)) :
    SmoothDisk (I := I) (Q := Q) where
  map := ⟨fun z : Disk => u.map (Width.diskReflection z),
    u.map.continuous.comp diskReflection_continuous⟩
  smooth z := by
    obtain ⟨F⟩ := u.smooth (Width.diskReflection z)
    exact ⟨{
      map := fun w : ℂ => F.map (star w)
      domain := star ⁻¹' F.domain
      isOpen_domain := F.isOpen_domain.preimage contDiff_star.continuous
      mem_domain := F.mem_domain
      smooth := F.smooth.comp
        ((contMDiffOn_univ.mpr contMDiff_star).mono (subset_univ _)) (fun _ hw => hw)
      agrees := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := hw
        have hball : star w ∈ Metric.closedBall (0 : ℂ) 1 := star_mem_closedBall hw2
        exact (F.agrees ⟨hw1, hball⟩).trans
          (congrFun (diskExtension_comp_diskReflection u) w).symm }⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
theorem SmoothDisk.diskReflection_map (u : SmoothDisk (I := I) (Q := Q)) (z : Disk) :
    (SmoothDisk.diskReflection u).map z = u.map (Width.diskReflection z) := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
private theorem diskExtension_diskReflection (u : SmoothDisk (I := I) (Q := Q)) :
    diskExtension (⇑(SmoothDisk.diskReflection u).map) =
      diskExtension u.map ∘ (fun z : ℂ => star z) :=
  diskExtension_comp_diskReflection u

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
theorem SmoothDisk.differential_diskReflection (u : SmoothDisk (I := I) (Q := Q))
    (z : Disk) (v : ℂ) :
    (SmoothDisk.diskReflection u).differential z v =
      u.differential (Width.diskReflection z) ((Complex.conjCLE : ℂ →L[ℝ] ℂ) v) := by
  have hz : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) (Metric.closedBall (0 : ℂ) 1) (z : ℂ) :=
    (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt
  have hg : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (diskExtension u.map)
      (Metric.closedBall (0 : ℂ) 1) ((Width.diskReflection z : Disk) : ℂ) :=
    (u.contMDiffOn_extension _ (star_mem_closedBall z.property)).mdifferentiableWithinAt
      (by simp)
  have hf : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => star w)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) :=
    (contMDiff_star.mdifferentiableAt (by simp)).mdifferentiableWithinAt
  have hmap : Metric.closedBall (0 : ℂ) 1 ⊆ (fun w : ℂ => star w) ⁻¹'
      Metric.closedBall (0 : ℂ) 1 := fun w hw => star_mem_closedBall hw
  have hext : diskExtension (⇑(SmoothDisk.diskReflection u).map) =
      diskExtension u.map ∘ (fun w : ℂ => star w) := diskExtension_diskReflection u
  unfold SmoothDisk.differential
  rw [hext]
  rw [mfderivWithin_comp (z : ℂ) hg hf hmap hz]
  erw [ContinuousLinearMap.comp_apply, mfderivWithin_star _ hz.uniqueDiffWithinAt]
  rfl

section ReflectionConformal

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
private theorem conjCLE_one : (Complex.conjCLE : ℂ →L[ℝ] ℂ) (1 : ℂ) = 1 := by
  change Complex.conjCLE (1 : ℂ) = 1
  rw [Complex.conjCLE_apply, map_one]

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
private theorem conjCLE_I : (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I := by
  change Complex.conjCLE Complex.I = -Complex.I
  rw [Complex.conjCLE_apply, Complex.conj_I]

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
private theorem inner_neg_neg (g : SmoothRiemannianMetric I Q) (p : Q)
    (a b : TangentSpace I p) : g.inner p (-a) (-b) = g.inner p a b := by
  simp

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
private theorem inner_neg_right (g : SmoothRiemannianMetric I Q) (p : Q)
    (a b : TangentSpace I p) : g.inner p a (-b) = -g.inner p a b := by
  simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
private theorem eq_mp_neg {A : Type*} [AddGroup A] (h : A = A) (x : A) :
    h.mp (-x) = -(h.mp x) := by
  cases h
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] t2Q compactQ [IsManifold I ∞ Q] in
private theorem SmoothDisk.differential_neg (u : SmoothDisk (I := I) (Q := Q))
    (z : Disk) (v : ℂ) : u.differential z (-v) = -u.differential z v := by
  unfold SmoothDisk.differential
  erw [map_neg]
  exact eq_mp_neg _ _

private def SmoothDisk.IsConformalAt (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : Prop :=
  g.inner (u.map z) (u.differential z (1 : ℂ)) (u.differential z Complex.I) = 0 ∧
    g.inner (u.map z) (u.differential z (1 : ℂ)) (u.differential z (1 : ℂ)) =
      g.inner (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
private theorem SmoothDisk.isConformal_iff_isConformalAt (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) :
    u.IsConformal g ↔ ∀ z, u.IsConformalAt g z := Iff.rfl

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
set_option backward.isDefEq.respectTransparency false in
private theorem SmoothDisk.isConformalAt_diskReflection (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) :
    (SmoothDisk.diskReflection u).IsConformalAt g z ↔
      u.IsConformalAt g (Width.diskReflection z) := by
  have hd1 : (SmoothDisk.diskReflection u).differential z (1 : ℂ) =
      u.differential (Width.diskReflection z) (1 : ℂ) := by
    have h := SmoothDisk.differential_diskReflection u z (1 : ℂ)
    rwa [conjCLE_one] at h
  have hdI : (SmoothDisk.diskReflection u).differential z Complex.I =
      -u.differential (Width.diskReflection z) Complex.I := by
    have h := SmoothDisk.differential_diskReflection u z Complex.I
    rw [conjCLE_I] at h
    exact h.trans (SmoothDisk.differential_neg u (Width.diskReflection z) Complex.I)
  unfold SmoothDisk.IsConformalAt
  rw [SmoothDisk.diskReflection_map, hd1, hdI]
  constructor
  · intro h
    exact ⟨by simpa only [inner_neg_right, neg_eq_zero] using h.1,
      by simpa only [inner_neg_neg] using h.2⟩
  · intro h
    exact ⟨by simpa only [inner_neg_right, neg_eq_zero] using h.1,
      by simpa only [inner_neg_neg] using h.2⟩

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
theorem SmoothDisk.diskReflection_conformal_iff (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) :
    (SmoothDisk.diskReflection u).IsConformal g ↔ u.IsConformal g := by
  rw [SmoothDisk.isConformal_iff_isConformalAt, SmoothDisk.isConformal_iff_isConformalAt]
  constructor
  · intro h z
    have hz := (SmoothDisk.isConformalAt_diskReflection u g (Width.diskReflection z)).mp
      (h (Width.diskReflection z))
    rwa [diskReflection_involutive] at hz
  · intro h z
    exact (SmoothDisk.isConformalAt_diskReflection u g z).mpr (h (Width.diskReflection z))

end ReflectionConformal

section ReflectionHarmonic

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem mfderiv_star (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => star w) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  rw [mfderiv_eq_fderiv]
  exact (Complex.conjCLE.hasFDerivAt (x := z)).fderiv

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem star_add_one (z : ℂ) (t : ℝ) :
    star (z + t • (1 : ℂ)) = star z + t • (1 : ℂ) := by
  rw [Complex.real_smul]
  simp only [map_add, Complex.star_def, Complex.conj_ofReal, mul_one]

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem star_add_I (z : ℂ) (t : ℝ) :
    star (z + t • Complex.I) = star z + ((-1 : ℝ) * t) • Complex.I := by
  have h : star (z + t • Complex.I) = star z + t • star Complex.I := by
    change (Complex.conjCLE : ℂ →L[ℝ] ℂ) (z + t • Complex.I) =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z + t • (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I
    rw [map_add, map_smul]
  have hI : star Complex.I = -Complex.I := by
    rw [Complex.star_def]
    exact Complex.conj_I
  rw [h, hI, smul_neg, neg_one_mul, neg_smul]

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ [IsManifold I ∞ Q] in
private theorem mfderiv_comp_star (U : ℂ → Q) (z : ℂ) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) I (fun w : ℂ => U (star w)) z v =
      mfderiv 𝓘(ℝ, ℂ) I U (star z) ((Complex.conjCLE : ℂ →L[ℝ] ℂ) v) := by
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) I U (star z)
  · have hcomp := mfderiv_comp (x := z) (g := U) (f := fun w : ℂ => star w) hU
      (contMDiff_star.mdifferentiableAt (by simp))
    rw [mfderiv_star z] at hcomp
    exact congrArg (fun L : ℂ →L[ℝ] TangentSpace I (U (star z)) => L v) hcomp
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w : ℂ => U (star w)) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => star w) (star z) :=
        contMDiff_star.mdifferentiableAt (by simp)
      have h' : MDifferentiableAt 𝓘(ℝ, ℂ) I (fun w : ℂ => U (star w)) (star (star z)) := by
        rw [star_star]
        exact h
      have heq : ((fun w : ℂ => U (star w)) ∘ (fun w : ℂ => star w)) = U := by
        funext w
        simp only [Function.comp_apply, star_star]
      exact hU (heq ▸ h'.comp (star z) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hU]
    rfl

omit boundarylessI t2Q compactQ in
private theorem diskLocalTension_comp_star (g : SmoothRiemannianMetric I Q)
    (U : ℂ → Q) (z : ℂ) :
    diskLocalTension g (fun w : ℂ => U (star w)) z = diskLocalTension g U (star z) := by
  have hcurve1 : (fun t : ℝ => (fun w : ℂ => U (star w)) (z + t • (1 : ℂ))) =
      fun t : ℝ => U (star z + t • (1 : ℂ)) :=
    funext fun t => congrArg U (star_add_one z t)
  have hfield1 : (fun t : ℝ =>
        mfderiv 𝓘(ℝ, ℂ) I (fun w : ℂ => U (star w)) (z + t • (1 : ℂ)) (1 : ℂ)) =
      fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I U (star z + t • (1 : ℂ)) (1 : ℂ) := by
    funext t
    rw [mfderiv_comp_star, star_add_one z t, conjCLE_one]
  have hcurve2 : (fun t : ℝ => (fun w : ℂ => U (star w)) (z + t • Complex.I)) =
      fun t : ℝ => U (star z + ((-1 : ℝ) * t) • Complex.I) :=
    funext fun t => congrArg U (star_add_I z t)
  have hfield2 : (fun t : ℝ =>
        mfderiv 𝓘(ℝ, ℂ) I (fun w : ℂ => U (star w)) (z + t • Complex.I) Complex.I) =
      fun t : ℝ => (-1 : ℝ) •
        mfderiv 𝓘(ℝ, ℂ) I U (star z + ((-1 : ℝ) * t) • Complex.I) Complex.I := by
    funext t
    rw [mfderiv_comp_star, star_add_I z t, conjCLE_I]
    erw [map_neg, neg_one_smul]
  have hrev : covDerivAlong g (fun t : ℝ => U (star z + ((-1 : ℝ) * t) • Complex.I))
        (fun t : ℝ => (-1 : ℝ) •
          mfderiv 𝓘(ℝ, ℂ) I U (star z + ((-1 : ℝ) * t) • Complex.I) Complex.I) 0 =
      covDerivAlong g (fun t : ℝ => U (star z + t • Complex.I))
        (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I U (star z + t • Complex.I) Complex.I) 0 := by
    let γ : ℝ → Q := fun t => U (star z + t • Complex.I)
    let V : ∀ t, TangentSpace I (γ t) :=
      fun t => mfderiv 𝓘(ℝ, ℂ) I U (star z + t • Complex.I) Complex.I
    have hγeq : (fun t : ℝ => U (star z + ((-1 : ℝ) * t) • Complex.I)) =
        fun t : ℝ => γ ((-1) * t) := by
      funext t
      rfl
    have hVeq : (fun t : ℝ => (-1 : ℝ) •
          mfderiv 𝓘(ℝ, ℂ) I U (star z + ((-1 : ℝ) * t) • Complex.I) Complex.I) =
        fun t : ℝ => (-1 : ℝ) • V ((-1) * t) := by
      funext t
      rfl
    rw [hγeq, hVeq, covDerivAlong_smul, covDeriv_comp_mul]
    simp only [neg_smul, one_smul, neg_neg]
    exact congrArg (fun t : ℝ => (covDerivAlong g γ V t : E)) (mul_zero (-1))
  unfold diskLocalTension
  rw [hcurve1, hfield1, hcurve2, hfield2, hrev]
  change _ + _ = _ + _
  exact congrArg₂ (fun x y : E => x + y) rfl rfl

private def SmoothDisk.IsHarmonicAt (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : Prop :=
  ∀ F : DiskLocalExtension (I := I) u.map z, diskLocalTension g F.map (z : ℂ) = 0

omit boundarylessI t2Q compactQ in
private theorem SmoothDisk.isHarmonic_iff_isHarmonicAt (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) :
    u.IsHarmonic g ↔ ∀ z, u.IsHarmonicAt g z := Iff.rfl

omit boundarylessI t2Q compactQ in
private theorem SmoothDisk.isHarmonicAt_diskReflection (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) :
    (SmoothDisk.diskReflection u).IsHarmonicAt g z ↔
      u.IsHarmonicAt g (Width.diskReflection z) := by
  constructor
  · intro h F
    have hG := h {
      map := fun w : ℂ => F.map (star w)
      domain := star ⁻¹' F.domain
      isOpen_domain := F.isOpen_domain.preimage contDiff_star.continuous
      mem_domain := F.mem_domain
      smooth := F.smooth.comp
        ((contMDiffOn_univ.mpr contMDiff_star).mono (subset_univ _)) (fun _ hw => hw)
      agrees := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := hw
        have hball : star w ∈ Metric.closedBall (0 : ℂ) 1 := star_mem_closedBall hw2
        exact (F.agrees ⟨hw1, hball⟩).trans
          (congrFun (diskExtension_diskReflection u) w).symm }
    rwa [diskLocalTension_comp_star g F.map z] at hG
  · intro h G
    have hF := h {
      map := fun w : ℂ => G.map (star w)
      domain := star ⁻¹' G.domain
      isOpen_domain := G.isOpen_domain.preimage contDiff_star.continuous
      mem_domain := by
        simpa only [Set.mem_preimage, Width.diskReflection, star_star] using G.mem_domain
      smooth := G.smooth.comp
        ((contMDiffOn_univ.mpr contMDiff_star).mono (subset_univ _)) (fun _ hw => hw)
      agrees := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := hw
        have hball : star w ∈ Metric.closedBall (0 : ℂ) 1 := star_mem_closedBall hw2
        have hd := (G.agrees ⟨hw1, hball⟩).trans
          (congrFun (diskExtension_diskReflection u) (star w))
        simpa only [Function.comp_apply, star_star] using hd }
    have hcomp : diskLocalTension g (fun w : ℂ => G.map (star w))
        ((Width.diskReflection z : Disk) : ℂ) = diskLocalTension g G.map (z : ℂ) := by
      rw [diskLocalTension_comp_star g G.map (Width.diskReflection z)]
      congr 1
      simp only [Width.diskReflection, star_star]
    exact hcomp.symm.trans hF

omit boundarylessI t2Q compactQ in
theorem SmoothDisk.diskReflection_harmonic_iff (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) :
    (SmoothDisk.diskReflection u).IsHarmonic g ↔ u.IsHarmonic g := by
  rw [SmoothDisk.isHarmonic_iff_isHarmonicAt, SmoothDisk.isHarmonic_iff_isHarmonicAt]
  constructor
  · intro h z
    have hz := (SmoothDisk.isHarmonicAt_diskReflection u g (Width.diskReflection z)).mp
      (h (Width.diskReflection z))
    rwa [diskReflection_involutive] at hz
  · intro h z
    exact (SmoothDisk.isHarmonicAt_diskReflection u g z).mpr (h (Width.diskReflection z))

end ReflectionHarmonic

section ReflectionArea

private theorem diskReflectionHomeo_lipschitz : LipschitzWith 1 ⇑diskReflectionHomeo :=
  diskReflection_lipschitz

include boundarylessI t2Q compactQ in
theorem diskArea_diskReflection (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) :
    diskArea g (fun z : Disk => u.map (diskReflection z)) = diskArea g u.map := by
  obtain ⟨ul, hul⟩ := u.exists_lipschitz g
  have h1 : diskArea g (fun z : Disk => u.map (diskReflection z)) =
      diskArea g (fun z : Disk => ul.map (diskReflection z)) := by
    rw [hul]
  rw [h1, ← hul]
  exact diskArea_reparametrize g ul diskReflectionHomeo ⟨1, diskReflectionHomeo_lipschitz⟩
    ⟨1, by rw [diskReflectionHomeo_symm]; exact diskReflectionHomeo_lipschitz⟩

end ReflectionArea

section MonotoneTraceLift

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q]
  [IsManifold I ∞ Q] in
private theorem periodic_circle_coe {ψ : ℝ → ℝ} (hinc : ∀ t, ψ (t + 1) = ψ t + 1) :
    Function.Periodic (fun t : ℝ => (ψ t : Surgery.Topology.Circle)) 1 := by
  intro t
  change ((ψ (t + 1) : ℝ) : Surgery.Topology.Circle) = ((ψ t : ℝ) : Surgery.Topology.Circle)
  rw [hinc t, AddCircle.coe_add, AddCircle.coe_period, add_zero]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q]
  [IsManifold I ∞ Q] in
private def smoothWeaklyMonotoneCircleMapOfLift (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hmono : Monotone ψ) (hinc : ∀ t, ψ (t + 1) = ψ t + 1) :
    SmoothWeaklyMonotoneCircleMap where
  map := ⟨(periodic_circle_coe hinc).lift, by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : ℝ =>
      (periodic_circle_coe hinc).lift (x : Surgery.Topology.Circle))
    simpa only [Function.Periodic.lift_coe] using!
      (continuous_quotient_mk'.comp hψ.continuous :
        Continuous (fun x : ℝ => (ψ x : Surgery.Topology.Circle)))⟩
  lift := ψ
  smooth_lift := hψ
  monotone_lift := hmono
  increment := hinc
  lift_eq := fun t => Function.Periodic.lift_coe (periodic_circle_coe hinc) t

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
private theorem contMDiff_diskBoundary_coe :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (diskBoundary (t : Surgery.Topology.Circle) : ℂ)) := by
  let _ := (Complex.finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 1 + 1))
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞
      (fun t : ℝ => Circle.exp (2 * Real.pi * t)) :=
    contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff
  have h2 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => ((Circle.exp (2 * Real.pi * t) : Circle) : ℂ)) :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).comp h1
  exact h2.congr fun t => diskBoundary_coe t

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q]
  [IsManifold I ∞ Q] in
private theorem contMDiff_trace (u : SmoothDisk (I := I) (Q := Q)) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => u.map (diskBoundary (t : Surgery.Topology.Circle))) := by
  have h := (u.contMDiffOn_extension).comp_contMDiff contMDiff_diskBoundary_coe
    (fun t => (diskBoundary (t : Surgery.Topology.Circle)).property)
  exact h.congr fun t => (diskExtension_coe u.map (diskBoundary (t : Surgery.Topology.Circle))).symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q]
  [IsManifold I ∞ Q] in
private theorem injective_of_apply_one_ne_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : ℝ →L[ℝ] W) (h : L 1 ≠ 0) : Function.Injective L := by
  intro a b hab
  have hz : (a - b) • L 1 = 0 := by
    rw [← map_smul, smul_eq_mul, mul_one, map_sub, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right h)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Q] [CompactSpace Q]
  [IsManifold I ∞ Q] in
private theorem diskReflection_diskBoundary (θ : Surgery.Topology.Circle) :
    diskReflection (diskBoundary θ) = diskBoundary (-θ) := by
  refine Subtype.ext ?_
  have hneg : ((AddCircle.toCircle (-θ) : ℂ)) = ((AddCircle.toCircle θ : ℂ))⁻¹ := by
    rw [AddCircle.toCircle_neg, Circle.coe_inv]
  have hinv : ((AddCircle.toCircle θ : ℂ))⁻¹ =
      star (AddCircle.toCircle θ : ℂ) := by
    rw [Complex.inv_eq_conj (Circle.norm_coe (AddCircle.toCircle θ))]
    exact (congrFun Complex.star_def _).symm
  simp only [diskReflection, diskBoundary, Subtype.coe_mk]
  rw [hneg, hinv]

omit [I.Boundaryless] [T2Space Q] [CompactSpace Q] in
private theorem contDiff_signed_trace_lift (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (u : SmoothDisk (I := I) (Q := Q)) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (htrace : ∀ t : ℝ,
      u.map (diskBoundary (t : Surgery.Topology.Circle)) = γ (φ t : Surgery.Topology.Circle)) :
    ContDiff ℝ ∞ φ := by
  rw [contDiff_iff_contDiffAt]
  intro x
  refine Geometry.contDiffAt_parameterLift_of_manifoldImmersion
    (I := I) (E := ℝ) (G := ℝ) (M := Q)
    (f := loopLift γ.toContinuousLoop) (ψ := φ) (x := x) hγ ?_ hφ.continuousAt ?_
  · exact injective_of_apply_one_ne_zero _ (himm (φ x))
  · have htr : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
        (fun t : ℝ => u.map (diskBoundary (t : Surgery.Topology.Circle))) x :=
      (contMDiff_trace u).contMDiffAt
    exact htr.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (htrace t).symm)

end MonotoneTraceLift


end PlateauTracedisk

theorem smooth_monotone_trace (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (u : SmoothDisk (I := I) (Q := Q)) (htrace : IsSignedWeaklyMonotoneTrace u.map γ.toContinuousLoop) :
    ∃ v : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      ((∀ z, v.map z = u.map z) ∨ (∀ z, v.map z = u.map (diskReflection z))) ∧
      (∀ θ, v.map (diskBoundary θ) = γ (σ.map θ)) ∧
      diskArea g v.map = diskArea g u.map ∧
      (v.IsConformal g ↔ u.IsConformal g) ∧ (v.IsHarmonic g ↔ u.IsHarmonic g) := by
  obtain ⟨φ, hφcont, hφmono, hφtrace⟩ := htrace
  have hφsmooth : ContDiff ℝ ∞ φ :=
    contDiff_signed_trace_lift γ hγ himm u φ hφcont hφtrace
  rcases hφmono with ⟨hmono, hinc⟩ | ⟨hanti, hinc⟩
  · let σ := smoothWeaklyMonotoneCircleMapOfLift φ hφsmooth hmono hinc
    refine ⟨u, σ, Or.inl fun z => rfl, ?_, rfl, Iff.rfl, Iff.rfl⟩
    intro θ
    refine QuotientAddGroup.induction_on θ ?_
    intro t
    have hmap : σ.map (t : Surgery.Topology.Circle) = (φ t : Surgery.Topology.Circle) := by
      dsimp only [σ, smoothWeaklyMonotoneCircleMapOfLift]
      exact hemb.injective
        (congrArg γ (Function.Periodic.lift_coe (periodic_circle_coe hinc) t))
    rw [hmap]
    exact hφtrace t
  · have hψ : ContDiff ℝ ∞ (fun t : ℝ => φ (-t)) := hφsmooth.comp contDiff_id.neg
    have hmono' : Monotone (fun t : ℝ => φ (-t)) := fun a b hab => hanti (neg_le_neg hab)
    have hinc' : ∀ t, φ (-(t + 1)) = φ (-t) + 1 := by
      intro t
      have h := hinc (-t - 1)
      have h1 : (-t - 1 : ℝ) + 1 = -t := by ring
      have h2 : -(t + 1) = -t - 1 := by ring
      rw [h1] at h
      rw [h2]
      linarith
    let σ := smoothWeaklyMonotoneCircleMapOfLift (fun t : ℝ => φ (-t)) hψ hmono' hinc'
    refine ⟨SmoothDisk.diskReflection u, σ,
      Or.inr fun z => SmoothDisk.diskReflection_map u z, ?_, ?_,
      SmoothDisk.diskReflection_conformal_iff u g, SmoothDisk.diskReflection_harmonic_iff u g⟩
    · intro θ
      refine QuotientAddGroup.induction_on θ ?_
      intro t
      have hmap : σ.map (t : Surgery.Topology.Circle) = ((φ (-t) : ℝ) : Surgery.Topology.Circle) := by
        dsimp only [σ, smoothWeaklyMonotoneCircleMapOfLift]
        exact hemb.injective (congrArg γ (Function.Periodic.lift_coe
          (periodic_circle_coe (ψ := fun t : ℝ => φ (-t)) hinc') t))
      rw [hmap]
      rw [SmoothDisk.diskReflection_map, diskReflection_diskBoundary, ← AddCircle.coe_neg,
        hφtrace (-t)]
    · have hmap : (⇑(SmoothDisk.diskReflection u).map : Disk → Q) =
          fun z : Disk => u.map (diskReflection z) := by
        funext z
        exact SmoothDisk.diskReflection_map u z
      rw [hmap, diskArea_diskReflection]

theorem conformal_disk_attains_exact_area (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hctr : Surgery.Topology.IsContractibleLoop γ.toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (σ : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ θ, u.map (diskBoundary θ) = γ (σ.map θ))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ θ, v.map (diskBoundary θ) = γ θ) → diskArea g u.map ≤ diskArea g v.map) :
    diskArea g u.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  apply le_antisymm
  · apply le_csInf (competitorAreas_nonempty g γ.toContinuousLoop hctr (γ.isLipschitz g))
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, htracew, hlim⟩ := smooth_exact_disk_density g γ hγ v
    exact ge_of_tendsto' hlim (fun j => hmin (w j) (htracew j))
  · obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
    have htracelip : ∀ θ, ulip.map (diskBoundary θ) = γ (σ.map θ) := by
      simpa only [hulip] using htrace
    obtain ⟨v, hv⟩ := zero_area_trace_annulus g γ hγ σ ulip htracelip
    have hle := leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g) v
    simpa only [hv, hulip] using hle

theorem conformal_disk_producer (g : SmoothRiemannianMetric I Q)
    (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop γ.toContinuousLoop) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧
      u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) → diskArea g u.map ≤ diskArea g v.map := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
