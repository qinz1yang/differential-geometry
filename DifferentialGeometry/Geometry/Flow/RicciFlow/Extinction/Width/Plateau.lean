import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

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
  sorry

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
