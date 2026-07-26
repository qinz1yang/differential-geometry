import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SmoothStrongPair
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Initial-edge strong Ricci--DeTurck data

This file isolates the maximal-regularity output that an initial-edge
harmonic-map gauge must provide.  The package contains only regularity,
representation, and equation fields for one geometric perturbation; in
particular, it does not assume equality with a second solution.

Two packages on the same time window are unique by the existing reverse
Duhamel and mixed forcing contraction theorem.  Their continuous `timeH1`
representatives then recover pointwise equality of the underlying smooth
covariant tensor paths, including the initial time.
-/

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Initial-edge Grönwall closure.  The energy is only differentiated on the
open positive-time interval.  Continuity to the zero edge and the zero initial
energy suffice: apply ordinary Grönwall on `[ε,t]` and send `ε → 0+`.

This is the scalar endpoint argument needed after a Ricci--DeTurck difference
energy estimate; it does not assume a right derivative at time zero. -/
theorem edgeGronwall_zero {T K : ℝ} (hT : 0 < T)
    (energy energy' : ℝ → ℝ)
    (hcont : ContinuousOn energy (Icc (0 : ℝ) T))
    (hzero : energy 0 = 0)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ energy t)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt energy (energy' t) t)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) T, energy' t ≤ K * energy t) :
    ∀ t ∈ Icc (0 : ℝ) T, energy t = 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · exact hzero
  have hlimT : Tendsto energy (nhdsWithin (0 : ℝ) (Ioo 0 T)) (𝓝 0) := by
    have hlim := (hcont 0 ⟨le_rfl, hT.le⟩).tendsto.mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
    simpa only [hzero] using hlim
  have hsub : Ioo (0 : ℝ) t ⊆ Ioo (0 : ℝ) T := fun s hs =>
    ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
  have hlim : Tendsto energy (nhdsWithin (0 : ℝ) (Ioo 0 t)) (𝓝 0) :=
    hlimT.mono_left (nhdsWithin_mono 0 hsub)
  haveI : (nhdsWithin (0 : ℝ) (Ioo 0 t)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT htpos]
    infer_instance
  have heps : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioo 0 t)) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have harg : Tendsto (fun ε : ℝ => K * (t - ε))
      (nhdsWithin (0 : ℝ) (Ioo 0 t)) (𝓝 (K * (t - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub heps)
  have hexp : Tendsto (fun ε : ℝ => Real.exp (K * (t - ε)))
      (nhdsWithin (0 : ℝ) (Ioo 0 t)) (𝓝 (Real.exp (K * (t - 0)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp harg
  have hrhs : Tendsto (fun ε : ℝ => energy ε * Real.exp (K * (t - ε)))
      (nhdsWithin (0 : ℝ) (Ioo 0 t)) (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul hexp
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioo 0 t),
      energy t ≤ energy ε * Real.exp (K * (t - ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hcontε : ContinuousOn energy (Icc ε t) :=
      hcont.mono (Icc_subset_Icc hε.1.le ht.2)
    have hslope : ∀ x ∈ Ico ε t, ∀ r, energy' x < r →
        ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (energy z - energy x) < r := by
      intro x hx r hr
      have hxT : x ∈ Ioo (0 : ℝ) T :=
        ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      exact (hderiv x hxT).hasDerivWithinAt.liminf_right_slope_le hr
    have hgr := le_gronwallBound_of_liminf_deriv_right_le hcontε hslope le_rfl
      (fun x hx => hbound x
        ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩) t
      ⟨hε.2.le, le_rfl⟩
    simpa only [gronwallBound_ε0] using hgr
  exact le_antisymm (le_of_tendsto hrhs hev) (hnonneg t ht)

/-- Exact maximal-regularity output required from one initial-edge geometric
Ricci--DeTurck perturbation.  `lo` is the continuous low-scale representative;
`hi` is its almost-everywhere high-scale realization; and `force` is the
Nemytskii remainder in the fixed-background heat equation.

The fields concern one path only.  No uniqueness or equality with another
geometric solution is included in the package. -/
structure EdgeStrongData
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    (Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun) {T : ℝ}
    (Phi : ℝ → SmoothCcTensor g₀ 0 2) where
  force : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T
  lo : timeH1 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T
  hi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T
  trace_zero : timeH1.trace0 _ T lo = 0
  scale_link :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) hi =
      timeH1.toTimeL2
        (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T lo
  heat_eq : timeH1.timeDeriv _ T lo =
    timeScaleLaplacian (I := I) (M := M) (a : ℝ) hi + force
  force_eq : force = nemytskii (I := I) (M := M) hLip hi
  hi_rep :
    (hi : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      =ᵐ[timeMeasure T] fun t =>
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t)
  path_rep : ∀ t ∈ Icc (0 : ℝ) T,
    lo.toFun t = smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t)

/-- Reverse realization at the initial edge from the two genuine parabolic
energy outputs.  Closed-window continuity is required only at the low Sobolev
scale.  The high-scale geometric path and its strong time derivative need only
belong to their time-`L²` spaces; all pointwise differentiability and PDE
identities are used on the open positive-time interval.

Thus the remaining geometric edge estimate is exactly
`L²_t H^(a+2) ∩ H¹_t H^a`, not an equality or fixed-point assumption. -/
theorem edgePath_strong
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {T : ℝ} (hT : 0 < T)
    (Phi : ℝ → SmoothCcTensor g₀ 0 2)
    (D : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hhi : MemLp
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀
        ((a : ℝ) + 2) (Phi t)) 2 (timeMeasure T))
    (hD : MemLp D 2 (timeMeasure T))
    (hlo : ContinuousOn
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t))
      (Icc (0 : ℝ) T))
    (hzero : smoothCcToTensorHs (I := I) (M := M) g₀
      (a : ℝ) (Phi 0) = 0)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt
        (fun s => smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi s))
        (D t) t)
    (hpde : ∀ t ∈ Ioo (0 : ℝ) T,
      D t = tensorScaleLaplacian (I := I) (M := M) (a : ℝ)
          (smoothCcToTensorHs (I := I) (M := M) g₀
            ((a : ℝ) + 2) (Phi t)) +
        Nfun (smoothCcToTensorHs (I := I) (M := M) g₀
          ((a : ℝ) + 2) (Phi t))) :
    EdgeStrongData (I := I) (M := M) g₀ a Nfun hLip Phi := by
  let Fhi : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := fun t =>
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (Phi t)
  let Flow : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) := fun t =>
    smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) (Phi t)
  let hi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T :=
    hhi.toLp Fhi
  let derivL2 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    hD.toLp D
  let lo : timeH1 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    timeH1.mk 0 derivL2
  let force : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
    nemytskii (I := I) (M := M) hLip hi
  have hhiRep :
      (hi : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        =ᵐ[timeMeasure T] Fhi := by
    simpa only [hi] using hhi.coeFn_toLp Fhi
  have hDRep :
      (derivL2 : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
        =ᵐ[timeMeasure T] D := by
    simpa only [derivL2] using hD.coeFn_toLp D
  have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Ioo (0 : ℝ) T := by
    have hrestrict : timeMeasure T = volume.restrict (Ioo (0 : ℝ) T) := by
      rw [timeMeasure,
        Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm]
    rw [hrestrict]
    exact ae_restrict_mem measurableSet_Ioo
  have htoFun : ∀ t ∈ Icc (0 : ℝ) T, lo.toFun t = Flow t := by
    intro t ht
    have hzeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hrepVol : ∀ᵐ s ∂volume,
        s ∈ Icc (0 : ℝ) T → derivL2 s = D s := by
      have hrep := hDRep
      rw [timeMeasure] at hrep
      exact (ae_restrict_iff' measurableSet_Icc).1 hrep
    have hintEq : (∫ s in (0 : ℝ)..t, derivL2 s) = ∫ s in (0 : ℝ)..t, D s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hrepVol] with s hs hsI
      exact hs ((Set.uIoc_subset_uIcc).trans
        (uIcc_subset_Icc hzeroMem ht) hsI)
    have hDint : IntegrableOn D (Icc (0 : ℝ) T) volume := by
      simpa only [timeMeasure] using hD.integrable (by norm_num)
    have hint : IntervalIntegrable D volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable
        (hDint.mono_set (uIcc_subset_Icc hzeroMem ht))
    have hFTC : (∫ s in (0 : ℝ)..t, D s) = Flow t - Flow 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hlo.mono (Icc_subset_Icc le_rfl ht.2))
        (fun s hs => hderiv s
          ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩) hint
    simp only [lo, timeH1.toFun_apply, timeH1.init_mk, timeH1.deriv_mk]
    rw [hintEq, hFTC, show Flow 0 = 0 by simpa only [Flow] using hzero]
    simp
  refine
    { force := force
      lo := lo
      hi := hi
      trace_zero := ?_
      scale_link := ?_
      heat_eq := ?_
      force_eq := rfl
      hi_rep := by simpa only [Fhi] using hhiRep
      path_rep := by simpa only [Flow] using htoFun }
  · simp only [lo, timeH1.trace0_mk]
  · refine Lp.ext ?_
    have hinclAE :
        ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) hi) =ᵐ[timeMeasure T]
          fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (hi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
          (p := 2) (μ := timeMeasure T) hi
    have hloAE :
        ⇑(timeH1.toTimeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T lo)
            =ᵐ[timeMeasure T] lo.toFun := by
      simpa only [timeH1.toTimeL2_apply] using
        TimeSobolev.coeFn_ofContinuousOn lo.continuousOn_toFun
    filter_upwards [hinclAE, hhiRep, hloAE, hmem] with t hit hhit hlot ht
    rw [hit, hhit, hlot, htoFun t (Set.mem_Icc_of_Ioo ht)]
    exact tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (Phi t)
  · refine Lp.ext ?_
    have hderivAE :
        ⇑(timeH1.timeDeriv (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T lo)
            =ᵐ[timeMeasure T] D := by
      simpa only [lo, derivL2, timeH1.timeDeriv_mk] using hD.coeFn_toLp D
    have hLap := timeScaleLaplacian_coeFn (I := I) (M := M) (τ := (a : ℝ)) hi
    have hforce := nemytskii_coeFn (I := I) (M := M) hLip hi
    have hadd := Lp.coeFn_add
      (timeScaleLaplacian (I := I) (M := M) (a : ℝ) hi) force
    filter_upwards [hderivAE, hhiRep, hLap, hforce, hadd, hmem]
      with t hdt hhit hLapt hft haddt ht
    rw [hdt, haddt, hLapt, hhit, force, hft, hhit, hpde t ht]

/-- Two geometric perturbations carrying the exact initial-edge strong data
are pointwise equal on the closed window whenever the existing mixed forcing
map is contractive on their common force ball. -/
theorem edgeStrong_unique
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (v v' :
      tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun v - Nfun v'‖ ≤
        (C₁ : ℝ) * max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) v'‖ * ‖v - v'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (v - v')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsmall :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    (Phi₁ Phi₂ : ℝ → SmoothCcTensor g₀ 0 2)
    (d₁ : EdgeStrongData (I := I) (M := M) g₀ a Nfun hLip Phi₁)
    (d₂ : EdgeStrongData (I := I) (M := M) g₀ a Nfun hLip Phi₂)
    (hball₁ : ‖d₁.force‖ ≤ ρ) (hball₂ : ‖d₂.force‖ ≤ ρ) :
    ∀ t ∈ Icc (0 : ℝ) T, Phi₁ t = Phi₂ t := by
  have huniq := deTurckStrong_unique (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρ hsmall d₁.force d₂.force d₁.lo d₂.lo d₁.hi d₂.hi
    d₁.trace_zero d₂.trace_zero d₁.scale_link d₂.scale_link
    d₁.heat_eq d₂.heat_eq d₁.force_eq d₂.force_eq hball₁ hball₂
  intro t ht
  have hu := congrArg
    (fun u : timeH1 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T =>
      u.toFun t) huniq.2.2
  rw [d₁.path_rep t ht, d₂.path_rep t ht] at hu
  apply ccToHs_injective (I := I) (M := M) g₀ 2 (a : ℝ)
  simpa only [ccHs_eq_smoothHs] using hu

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
