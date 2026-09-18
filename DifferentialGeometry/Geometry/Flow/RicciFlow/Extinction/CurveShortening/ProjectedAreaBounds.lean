import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSliceRegularity

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hNonempty hBoundary

omit [SigmaCompactSpace M] hCompact hNonempty in
theorem projected_sweptDensity_le_totalCurvature
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (t : ℝ) (ht : t ∈ Icc a b) :
    c.projection.sweptDensity B.family.metric (Icc a b) t ≤
      c.totalCurvature B.family.metric lambda t := by
  have hpoint : ∀ x, Real.sqrt (c.projection.normSq B.family.metric
        (c.projection.velocity (I := I) (Icc a b)) x t) *
          c.projection.speed B.family.metric x t ≤
      c.curvature B.family.metric lambda x t * c.speed B.family.metric lambda x t := by
    intro x
    have hvel : c.projection.velocity (I := I) (Icc a b) x t =
        (c.curvatureVector B.family.metric lambda x t).1 := by
      rw [← hc.equation x t ht]
      rfl
    have hnorm : c.projection.normSq B.family.metric
        (c.projection.velocity (I := I) (Icc a b)) x t =
        (B.family.metric t).inner (c.projection.lift x t)
          (c.curvatureVector B.family.metric lambda x t).1
          (c.curvatureVector B.family.metric lambda x t).1 := by
      simp only [CurveMap.normSq, hvel]
    have hle : c.projection.normSq B.family.metric
        (c.projection.velocity (I := I) (Icc a b)) x t ≤
        c.curvatureSq B.family.metric lambda x t := by
      rw [hnorm, ProductCurve.curvatureSq, ProductCurve.normSq, ProductCurve.inner]
      nlinarith [sq_nonneg (lambda * (c.curvatureVector B.family.metric lambda x t).2)]
    have hcurv : Real.sqrt (c.projection.normSq B.family.metric
        (c.projection.velocity (I := I) (Icc a b)) x t) ≤
        c.curvature B.family.metric lambda x t := by
      simpa only [ProductCurve.curvature] using Real.sqrt_le_sqrt hle
    have hspeed : c.projection.speed B.family.metric x t ≤
        c.speed B.family.metric lambda x t := by
      have h2 : c.projection.speed B.family.metric x t ^ 2 ≤
          c.speed B.family.metric lambda x t ^ 2 := by
        rw [ProductCurve.speed_sq_add c B.family.metric lambda x t]
        nlinarith [sq_nonneg (lambda * deriv (fun z => c.y z t) x)]
      simpa only [Real.sqrt_sq (c.projection.speed_nonneg B.family.metric x t),
        Real.sqrt_sq (c.speed_nonneg B.family.metric lambda x t)] using
        Real.sqrt_le_sqrt h2
    exact mul_le_mul hcurv hspeed (c.projection.speed_nonneg B.family.metric x t)
      (ProductCurve.curvature_nonneg c B.family.metric lambda x t)
  have hint : IntegrableOn (fun x => c.curvature B.family.metric lambda x t *
      c.speed B.family.metric lambda x t) (Ioc (0 : ℝ) 1) volume :=
    by
      have hr := c.sliceRegularity_of_immersedOn B.family.metric lambda hlambda
        hc.smooth hc.immersed t ht
      exact ((hr.curvatureSq_continuous.sqrt.mul hr.speed_continuous).intervalIntegrable 0 1).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => Real.sqrt (c.projection.normSq B.family.metric
        (c.projection.velocity (I := I) (Icc a b)) x t) *
        c.projection.speed B.family.metric x t) :=
    ae_of_all _ (fun x => mul_nonneg (Real.sqrt_nonneg _)
      (c.projection.speed_nonneg B.family.metric x t))
  have hle := MeasureTheory.integral_mono_of_nonneg hnn hint (ae_of_all _ hpoint)
  simpa only [CurveMap.sweptDensity, CurveMap.integral, ProductCurve.totalCurvature,
    ProductCurve.integral,
    intervalIntegral.integral_of_le zero_le_one] using hle

omit [SigmaCompactSpace M] hNonempty in
theorem rfs_csf_projection_upper_control (B : RicciBackground (I := I) (M := M) D a b)
    (hslope : curveShorteningLeastAreaSlope (I := I) (M := M) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := M) B)
    (L₀ Theta₀ A₀ : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hA₀ : 0 ≤ A₀) :
    let delta := b - a
    let ThetaStar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let AStar := Real.exp (2 * B.B₀ * delta) * (A₀ + delta * ThetaStar)
    let C_A := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * AStar + ThetaStar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      ∀ γ : ℝ → ContinuousFreeLoop M,
        (∀ z t, t ∈ Icc a b → γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ A₀ →
        (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ AStar) ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            C_A * (t - s) := by
  dsimp only
  intro lambda hlambda hlambda_one c hc γ hagree hctr hLcont hlen htot hLa
  set d : ℝ := b - a with hd
  set T : ℝ := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * d) with hT
  set A : ℝ := Real.exp (2 * B.B₀ * d) * (A₀ + d * T) with hA
  set CA : ℝ := Real.exp (2 * B.B₀ * d) * (2 * B.B₀ * A + T) with hCA
  have hd0 : 0 ≤ d := by
    rw [hd]
    linarith [B.lt.le]
  have hB0' : 0 ≤ 2 * B.B₀ := by linarith [B.B₀_nonneg]
  have hC : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    nlinarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) := by
    rw [CurveMap.SmoothOn]
    refine hc.smooth.1.congr ?_
    intro p hp
    exact hagree (p.1 : AddCircle (1 : ℝ)) p.2 hp.2
  have hTheta : ∀ t ∈ Icc a b, c.totalCurvature B.family.metric lambda t ≤ T := by
    intro t ht
    have h := totalCurvature_le_mul_exp_of_growth_bound B hcurv lambda hlambda hlambda_one c hc
      Theta₀ L₀ htot hlen t ht
    rw [hT, hd]
    exact h
  have hSle : ∀ t ∈ Icc a b,
      (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) t ≤
        c.totalCurvature B.family.metric lambda t := by
    intro t ht
    have hcongr : (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) t =
        c.projection.sweptDensity B.family.metric (Icc a b) t :=
      CurveMap.sweptDensity_congr (fun z s hs => hagree z s hs) t ht
    rw [hcongr]
    exact projected_sweptDensity_le_totalCurvature B lambda hlambda c hc t ht
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg (add_nonneg hTheta₀ hL₀) (Real.exp_pos _).le
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg hA₀ (mul_nonneg hd0 hT0))
  have hLnn : ∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t :=
    fun t ht => loopFamilyLeastArea_nonneg B.family.metric γ hγ hctr t ht
  have hIntS : ∀ (s : ℝ) (t : ℝ), s ∈ Icc a b → t ∈ Icc s b →
      (∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) ≤
        (t - s) * T := by
    intro s t hs ht
    have hst : s ≤ t := ht.1
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hScont : ContinuousOn (fun v => (curveOfLoopFamily γ).sweptDensity
        B.family.metric (Icc a b) v) (Icc s t) :=
      (continuousOn_sweptDensity B γ hγ).mono hsub
    have hint : IntervalIntegrable (fun v => (curveOfLoopFamily γ).sweptDensity
        B.family.metric (Icc a b) v) volume s t := hScont.intervalIntegrable_of_Icc hst
    have h1 : (∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) ≤
        ∫ v in s..t, T :=
      intervalIntegral.integral_mono_on hst hint intervalIntegrable_const
        (fun v hv => (hSle v (hsub hv)).trans (hTheta v (hsub hv)))
    have h2 : (∫ v in s..t, T) = (t - s) * T := by
      rw [intervalIntegral.integral_const]
      ring
    rw [h2] at h1
    exact h1
  have htight : ∀ t ∈ Icc a b, loopFamilyLeastArea B.family.metric γ t ≤
      Real.exp (2 * B.B₀ * d) * (A₀ + d * T) := by
    intro t ht
    have hs := rfs_csf_swept_annulus B hslope γ hγ hLcont a t
      ⟨le_rfl, B.lt.le⟩ ht
    have hexp : Real.exp (2 * B.B₀ * (t - a)) ≤ Real.exp (2 * B.B₀ * d) := by
      rw [Real.exp_le_exp, hd]
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0'
    have hI := hIntS a t ⟨le_rfl, B.lt.le⟩ ht
    have hId : (∫ v in a..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) ≤
        d * T := by
      have hta : t - a ≤ d := by
        rw [hd]
        linarith [ht.2]
      nlinarith [hT0, hI, hta]
    have hInn : 0 ≤ ∫ v in a..t,
        (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v :=
      intervalIntegral.integral_nonneg (by linarith [ht.1])
        (fun v _ => CurveMap.sweptDensity_nonneg (c := curveOfLoopFamily γ)
          B.family.metric (Icc a b) v)
    have hsum : loopFamilyLeastArea B.family.metric γ a +
        (∫ v in a..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) ≤
        A₀ + d * T := add_le_add hLa hId
    have hnn_sum : 0 ≤ loopFamilyLeastArea B.family.metric γ a +
        (∫ v in a..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) := by
      linarith [hLnn a ⟨le_rfl, B.lt.le⟩, hInn]
    exact hs.trans (mul_le_mul hexp hsum hnn_sum (Real.exp_pos _).le)
  have hpart1 : ∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
      loopFamilyLeastArea B.family.metric γ t ≤ A := by
    intro t ht
    refine ⟨hLnn t ht, ?_⟩
    rw [hA]
    exact htight t ht
  have hpart2 : ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
      loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
        CA * (t - s) := by
    intro s hs t ht
    have hst : s ≤ t := ht.1
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst
    have hLsnn : 0 ≤ loopFamilyLeastArea B.family.metric γ s := (hpart1 s hs).1
    have hLAs : loopFamilyLeastArea B.family.metric γ s ≤ A := (hpart1 s hs).2
    have hInc := exp_increment_le (2 * B.B₀) (t - s) d hB0' hts
      (by rw [hd]; linarith [ht.2, hs.1])
    have hExpLe : Real.exp (2 * B.B₀ * (t - s)) ≤ Real.exp (2 * B.B₀ * d) := by
      rw [Real.exp_le_exp, hd]
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2, hs.1]) hB0'
    have hInn : 0 ≤ ∫ v in s..t,
        (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v :=
      intervalIntegral.integral_nonneg hst
        (fun v _ => CurveMap.sweptDensity_nonneg (c := curveOfLoopFamily γ)
          B.family.metric (Icc a b) v)
    have hI := hIntS s t hs ht
    have hswept' := rfs_csf_swept_annulus B hslope γ hγ hLcont s t hs ht
    have hmain : loopFamilyLeastArea B.family.metric γ t -
        loopFamilyLeastArea B.family.metric γ s ≤
        (Real.exp (2 * B.B₀ * (t - s)) - 1) * loopFamilyLeastArea B.family.metric γ s +
          Real.exp (2 * B.B₀ * (t - s)) *
            (∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) := by
      have hsplit : Real.exp (2 * B.B₀ * (t - s)) *
          (loopFamilyLeastArea B.family.metric γ s +
            ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) =
          Real.exp (2 * B.B₀ * (t - s)) * loopFamilyLeastArea B.family.metric γ s +
            Real.exp (2 * B.B₀ * (t - s)) *
              (∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) :=
        mul_add _ _ _
      linarith [hswept', hsplit]
    have h1 : (Real.exp (2 * B.B₀ * (t - s)) - 1) * loopFamilyLeastArea B.family.metric γ s ≤
        (2 * B.B₀ * Real.exp (2 * B.B₀ * d) * (t - s)) * A := by
      refine mul_le_mul hInc hLAs hLsnn ?_
      exact mul_nonneg (mul_nonneg hB0' (Real.exp_pos _).le) hts
    have h2 : Real.exp (2 * B.B₀ * (t - s)) *
        (∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) ≤
        Real.exp (2 * B.B₀ * d) * ((t - s) * T) :=
      mul_le_mul hExpLe hI hInn (Real.exp_pos _).le
    calc loopFamilyLeastArea B.family.metric γ t -
          loopFamilyLeastArea B.family.metric γ s
        ≤ (Real.exp (2 * B.B₀ * (t - s)) - 1) * loopFamilyLeastArea B.family.metric γ s +
          Real.exp (2 * B.B₀ * (t - s)) *
            (∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) := hmain
      _ ≤ (2 * B.B₀ * Real.exp (2 * B.B₀ * d) * (t - s)) * A +
          Real.exp (2 * B.B₀ * d) * ((t - s) * T) := add_le_add h1 h2
      _ = CA * (t - s) := by
        rw [hCA]
        ring
  exact ⟨hpart1, hpart2⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
