import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauClassical

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Extinction

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

private theorem sqrt_inner_smul_of_nonneg (g : SmoothRiemannianMetric I Q) (p : Q)
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
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z
          (v : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z
          (v : ℂ)))
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
      tangentMapWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1)
        (j p)) :=
    hjet.comp_continuous hj (fun p => p.1.property)
  have hs := (continuous_tangentMetricSpeed g).comp hc
  obtain ⟨V, hV⟩ := (isCompact_range hs).bddAbove
  have hunit (z v : Disk) :
      Real.sqrt (g.inner (diskExtension u.map z)
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z
          (v : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map) (Metric.closedBall (0 : ℂ) 1) z
          (v : ℂ)))
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
    have hscale := sqrt_inner_smul_of_nonneg g (diskExtension u.map z)
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
        (mfderivWithin 𝓘(ℝ, ℝ) I gamma (Icc (0 : ℝ) 1) t 1))
        ≤ V * ‖(w : ℂ) - (z : ℂ)‖ := by
    have hud := (uniqueDiffOn_Icc_zero_one t ht).uniqueMDiffWithinAt
    have hdl : HasDerivAt line ((w : ℂ) - (z : ℂ)) t := by
      simpa only [line, id_eq, one_smul] using!
        ((hasDerivAt_id t).smul_const ((w : ℂ) - (z : ℂ))).const_add (z : ℂ)
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
  have hp := riemannianEDistOf_le_within_speed_bound g gamma hgamma
    (V * ‖(w : ℂ) - (z : ℂ)‖) hs
  rw [hgamma0, hgamma1, ENNReal.ofReal_mul hV] at hp
  have he : edist z w = ENNReal.ofReal ‖(w : ℂ) - (z : ℂ)‖ := by
    rw [edist_dist]
    change ENNReal.ofReal (dist (z : ℂ) (w : ℂ)) = _
    rw [dist_eq_norm, norm_sub_rev]
  simpa only [he] using hp

private theorem smoothDisk_exists_lipschitz (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) :
    ∃ v : LipschitzDisk g, v.map = u.map := by
  obtain ⟨V, hV, hbound⟩ := smooth_disk_edist_bound g u
  refine ⟨⟨u.map, ?_⟩, rfl⟩
  refine ⟨NNReal.mk V hV, ?_⟩
  intro z w
  simpa only [ENNReal.ofReal_eq_coe_nnreal hV] using hbound z w

section FiniteDimensional

variable [FiniteDimensional ℝ E]

structure PlateauInteriorMinimizer (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.ContinuousFreeLoop Q) where
  disk : InteriorSmoothDisk (I := I) (Q := Q)
  trace : ∀ theta : Surgery.Topology.Circle, disk.map (diskBoundary theta) = γ theta
  conformal : disk.IsConformal g
  harmonic : disk.IsHarmonic g
  finite : IntegrableOn (diskJacobian g disk.map) (Metric.closedBall (0 : ℂ) 1)
  minimizingLipschitz : ∀ w : LipschitzDisk g,
    (∀ theta : Surgery.Topology.Circle, w.map (diskBoundary theta) = γ theta) →
      diskArea g disk.map ≤ diskArea g w.map

theorem isSignedWeaklyMonotoneTrace_of_diskTrace_eq {u : Disk → Q}
    {γ : Surgery.Topology.ContinuousFreeLoop Q}
    (h : ∀ theta : Surgery.Topology.Circle, u (diskBoundary theta) = γ theta) :
    IsSignedWeaklyMonotoneTrace u γ :=
  ⟨id, continuous_id, Or.inl ⟨monotone_id, fun _ => rfl⟩,
    fun t => h (t : Surgery.Topology.Circle)⟩

theorem classical_plateau_morrey_of_finite_lipschitz_of_minimizer
    (g : SmoothRiemannianMetric I Q) (gamma : RegularLoop I Q)
    (h : PlateauInteriorMinimizer (I := I) (Q := Q) g gamma.toContinuousLoop) :
    ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
      u.IsConformal g ∧ u.IsHarmonic g ∧
      IsSignedWeaklyMonotoneTrace u.map gamma.toContinuousLoop ∧
      IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : LipschitzDisk g,
        (∀ theta, w.map (diskBoundary theta) = gamma theta) →
        diskArea g u.map ≤ diskArea g w.map) ∧
      ∀ w : SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (diskBoundary theta) = gamma theta) →
        diskArea g u.map ≤ diskArea g w.map := by
  obtain ⟨u, htrace, hconf, hharm, hfin, hmin⟩ := h
  refine ⟨u, hconf, hharm, isSignedWeaklyMonotoneTrace_of_diskTrace_eq htrace, hfin, hmin, ?_⟩
  intro w hw
  obtain ⟨v, hv⟩ := smoothDisk_exists_lipschitz (I := I) (Q := Q) g w
  rw [← hv]
  exact hmin v fun theta => by rw [hv]; exact hw theta

end FiniteDimensional

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
