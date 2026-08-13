import DifferentialGeometry.Analysis.Parabolic.Euclidean.Cutoff

noncomputable section

open Asymptotics Filter Matrix MeasureTheory Real Set
open scoped NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem heatScaled_add
    (t : Real) (u v : BoundedContinuousFunction V F) (x : V) :
    heatScaled t (u + v) x = heatScaled t u x + heatScaled t v x := by
  unfold heatScaled
  rw [← integral_add (heatScaled_integrable t u x)
    (heatScaled_integrable t v x)]
  apply integral_congr_ae
  filter_upwards with z
  change baseHeat z • (u (x - heatScale t • z) +
    v (x - heatScale t • z)) = _
  rw [smul_add]

omit [CompleteSpace F] in
theorem heatScaled_sub
    (t : Real) (u v : BoundedContinuousFunction V F) (x : V) :
    heatScaled t (u - v) x = heatScaled t u x - heatScaled t v x := by
  unfold heatScaled
  rw [← integral_sub (heatScaled_integrable t u x)
    (heatScaled_integrable t v x)]
  apply integral_congr_ae
  filter_upwards with z
  change baseHeat z • (u (x - heatScale t • z) -
    v (x - heatScale t • z)) = _
  rw [smul_sub]

omit [Nontrivial V] [CompleteSpace F] in
theorem heatScaled_smul
    (t c : Real) (u : BoundedContinuousFunction V F) (x : V) :
    heatScaled t (c • u) x = c • heatScaled t u x := by
  unfold heatScaled
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  change baseHeat z • (c • u (x - heatScale t • z)) =
    c • (baseHeat z • u (x - heatScale t • z))
  exact smul_comm _ _ _

omit [Nontrivial V] [CompleteSpace F] in
@[simp]
theorem heatScaled_zero_bcf
    (t : Real) (x : V) :
    heatScaled t (0 : BoundedContinuousFunction V F) x = 0 := by
  have h := heatScaled_smul t 0
    (0 : BoundedContinuousFunction V F) x
  simpa only [zero_smul] using h

omit [CompleteSpace F] in
theorem tendsto_heatScaled_of_tendsto
    {A : Type*} {l : Filter A} {q : A → Real} {q₀ : Real}
    {u : A → BoundedContinuousFunction V F}
    {u₀ : BoundedContinuousFunction V F}
    (hq : Tendsto q l (nhds q₀)) (hu : Tendsto u l (nhds u₀)) (x : V) :
    Tendsto (fun a ↦ heatScaled (q a) (u a) x) l
      (nhds (heatScaled q₀ u₀ x)) := by
  have hdiff : Tendsto (fun a ↦ u a - u₀) l (nhds 0) := by
    simpa only [sub_self] using hu.sub
      (tendsto_const_nhds : Tendsto (fun _ : A ↦ u₀) l (nhds u₀))
  have hnorm : Tendsto (fun a ↦ ‖u a - u₀‖) l (nhds 0) := by
    simpa only [norm_zero] using hdiff.norm
  have hscaledNorm : Tendsto
      (fun a ↦ ‖heatScaled (q a) (u a - u₀) x‖) l (nhds 0) := by
    exact squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _)
      (Eventually.of_forall fun a ↦ heatScaled_norm _ _ _) hnorm
  have hscaledZero : Tendsto
      (fun a ↦ heatScaled (q a) (u a - u₀) x) l (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hscaledNorm
  have hfixed : Tendsto (fun a ↦ heatScaled (q a) u₀ x) l
      (nhds (heatScaled q₀ u₀ x)) :=
    (heatScaled_cont u₀ x).tendsto q₀ |>.comp hq
  convert hscaledZero.add hfixed using 1
  · funext a
    rw [← heatScaled_add]
    congr 2
    abel
  · simp only [zero_add]

omit [CompleteSpace F] in
theorem heatScaled_sub_time_hasDerivAt
    {t s : Real} (hst : s < t)
    (u dtU : Real → BoundedContinuousFunction V F)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (d2u : Real →
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (huTime : HasDerivAt u (dtU s) s)
    (hu : ∀ x, HasFDerivAt (u s : V → F) (du s x) x)
    (hdu : ∀ x, HasFDerivAt
      (du s : V → V →L[Real] F) (d2u s x) x)
    (x : V) :
    HasDerivAt (fun r ↦ heatScaled (t - r) (u r) x)
      (heatScaled (t - s) (dtU s) x -
        heatScaled (t - s) (coreLap (d2u s)) x) s := by
  let q : Real → Real := fun r ↦ t - r
  let R : Real → BoundedContinuousFunction V F := fun r ↦
    u r - u s - (r - s) • dtU s
  let D : Real → F := fun r ↦
    heatScaled (q r) (dtU s) x - heatScaled (q s) (dtU s) x
  have hq : HasDerivAt q (-1) s := by
    simpa only [q, zero_sub] using
      (hasDerivAt_const s t).sub (hasDerivAt_id s)
  have htime : HasDerivAt
      (fun r ↦ heatScaled (q r) (u s) x)
      (-heatScaled (q s) (coreLap (d2u s)) x) s := by
    have hpositive : HasDerivAt
        (fun z ↦ heatScaled z (u s) x)
        (heatScaled (q s) (coreLap (d2u s)) x) (q s) := by
      have hraw := heatSup_time (sub_pos.mpr hst)
        (u s) (du s) (d2u s) hu hdu x
      have heq : (fun z ↦ heatScaled z (u s) x) =ᶠ[nhds (q s)]
          fun z ↦ heatSup z (u s) x := by
        filter_upwards [Ioi_mem_nhds (sub_pos.mpr hst)] with z hz
        exact (heatSup_scaled hz (u s) x).symm
      have hconverted := hraw.congr_of_eventuallyEq heq
      exact hconverted.congr_deriv
        (heatSup_scaled (sub_pos.mpr hst) (coreLap (d2u s)) x)
    have hraw := hpositive.scomp s hq
    simpa only [q, neg_one_smul] using hraw
  have hR : R =o[nhds s] fun r ↦ r - s := by
    simpa only [R] using huTime.isLittleO
  have hscaledR : (fun r ↦ heatScaled (q r) (R r) x) =o[nhds s]
      fun r ↦ r - s := by
    apply (IsBigO.of_bound' (Eventually.of_forall fun r ↦
      heatScaled_norm (q r) (R r) x)).trans_isLittleO hR
  have hDlim : Tendsto D (nhds s) (nhds 0) := by
    have hqTend : Tendsto q (nhds s) (nhds (q s)) := hq.continuousAt
    have hheat := (heatScaled_cont (dtU s) x).tendsto (q s) |>.comp hqTend
    simpa only [D, sub_self] using
      hheat.sub_const (heatScaled (q s) (dtU s) x)
  have hDo : D =o[nhds s] fun _ ↦ (1 : Real) :=
    (isLittleO_one_iff Real).mpr hDlim
  have hcross : (fun r ↦ (r - s) • D r) =o[nhds s]
      fun r ↦ r - s := by
    simpa only [smul_eq_mul, mul_one] using
      (isBigO_refl (fun r ↦ r - s) (nhds s)).smul_isLittleO hDo
  apply HasDerivAt.of_isLittleO
  have hsum := htime.isLittleO.add (hscaledR.add hcross)
  apply hsum.congr'
  · apply Eventually.of_forall
    intro r
    have hRscaled : heatScaled (q r) (R r) x =
        heatScaled (q r) (u r) x - heatScaled (q r) (u s) x -
          (r - s) • heatScaled (q r) (dtU s) x := by
      dsimp only [R]
      rw [heatScaled_sub, heatScaled_sub, heatScaled_smul]
    change
      heatScaled (q r) (u s) x - heatScaled (q s) (u s) x -
          (r - s) • (-heatScaled (q s) (coreLap (d2u s)) x) +
        (heatScaled (q r) (R r) x + (r - s) • D r) =
      heatScaled (t - r) (u r) x - heatScaled (t - s) (u s) x -
        (r - s) • (heatScaled (t - s) (dtU s) x -
          heatScaled (t - s) (coreLap (d2u s)) x)
    rw [hRscaled]
    dsimp only [D, q]
    simp only [smul_sub, smul_neg]
    abel
  · exact Eventually.of_forall fun _ ↦ rfl

omit [CompleteSpace F] in
theorem heatScaled_timeSource_intervalIntegrable_of_parabolic_holder
    {alpha K B : NNReal} (halpha0 : 0 < alpha)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) t) Set.univ).restrict
        (fun p ↦ f p.time p.space)))
    (x : V) :
    IntervalIntegrable
      (fun s ↦ heatScaled (t - s) (f s) x) volume 0 t := by
  have hsup : IntervalIntegrable
      (fun s ↦ heatSup (t - s) (f s) x) volume 0 t :=
    heatDuh_int ht f hbound x
      (heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ⟨ht, le_rfl⟩ f hsource x)
  apply hsup.congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : Real) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  exact heatSup_scaled (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (f s) x

theorem heatDuh_eq_of_zero_initial
    {t : Real} (ht : 0 < t)
    (u dtU : Real → BoundedContinuousFunction V F)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (d2u : Real →
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (huTime : ∀ s ∈ Ioo (0 : Real) t, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (u s : V → F) (du s x) x)
    (hdu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (du s : V → V →L[Real] F) (d2u s x) x)
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (x : V)
    (hint : IntervalIntegrable
      (fun s ↦ heatScaled (t - s) (dtU s - coreLap (d2u s)) x)
      volume 0 t) :
    heatDuh t (fun s ↦ dtU s - coreLap (d2u s)) x = u t x := by
  let source : Real → BoundedContinuousFunction V F :=
    fun s ↦ dtU s - coreLap (d2u s)
  let w : Real → F := fun s ↦ heatScaled (t - s) (u s) x
  have hwderiv : ∀ s ∈ Ioo (0 : Real) t,
      HasDerivAt w (heatScaled (t - s) (source s) x) s := by
    intro s hs
    have h := heatScaled_sub_time_hasDerivAt hs.2 u dtU du d2u
      (huTime s hs) (hu s hs) (hdu s hs) x
    simpa only [w, source, heatScaled_sub] using h
  have hleft : Tendsto w (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hq : Tendsto (fun s : Real ↦ t - s) (nhdsWithin 0 (Ioi 0))
        (nhds t) := by
      have hc : ContinuousAt (fun s : Real ↦ t - s) 0 :=
        continuousAt_const.sub continuousAt_id
      simpa only [sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have huT : Tendsto u (nhdsWithin 0 (Ioi 0)) (nhds (u 0)) :=
      huCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h := tendsto_heatScaled_of_tendsto hq huT x
    simpa only [w, hu0, heatScaled_zero_bcf] using h
  have hright : Tendsto w (nhdsWithin t (Iio t)) (nhds (u t x)) := by
    have hq : Tendsto (fun s : Real ↦ t - s) (nhdsWithin t (Iio t))
        (nhds 0) := by
      have hc : ContinuousAt (fun s : Real ↦ t - s) t :=
        continuousAt_const.sub continuousAt_id
      simpa only [sub_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have huT : Tendsto u (nhdsWithin t (Iio t)) (nhds (u t)) :=
      huCont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h := tendsto_heatScaled_of_tendsto hq huT x
    simpa only [w, heatScaled_zero] using h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht hwderiv (by simpa only [source] using hint) hleft hright
  unfold heatDuh
  rw [show (∫ s : Real in 0..t, heatSup (t - s) (source s) x) =
      ∫ s : Real in 0..t, heatScaled (t - s) (source s) x by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hst
    intro hs
    rw [uIoc_of_le ht.le] at hs
    exact heatSup_scaled (sub_pos.mpr (lt_of_le_of_ne hs.2 hst))
      (source s) x]
  simpa only [source, sub_zero] using hftc

theorem heatDuh_eq_of_zero_initial_of_parabolic_holder
    {alpha K B : NNReal} (halpha0 : 0 < alpha)
    {t : Real} (ht : 0 < t)
    (u dtU : Real → BoundedContinuousFunction V F)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (d2u : Real →
      BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (huTime : ∀ s ∈ Ioo (0 : Real) t, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (u s : V → F) (du s x) x)
    (hdu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (du s : V → V →L[Real] F) (d2u s x) x)
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (hbound : ∀ s ∈ Icc (0 : Real) t,
      ‖dtU s - coreLap (d2u s)‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) t) Set.univ).restrict
        (fun p ↦ (dtU p.time - coreLap (d2u p.time)) p.space)))
    (x : V) :
    heatDuh t (fun s ↦ dtU s - coreLap (d2u s)) x = u t x := by
  apply heatDuh_eq_of_zero_initial ht u dtU du d2u huTime hu hdu
    huCont hu0 x
  exact heatScaled_timeSource_intervalIntegrable_of_parabolic_holder
    halpha0 ht (fun s ↦ dtU s - coreLap (d2u s)) hbound hsource x

def linPullBcfCLM (L : V ≃L[Real] V) :
    BoundedContinuousFunction V F →L[Real]
      BoundedContinuousFunction V F :=
  LinearMap.mkContinuous
    { toFun := linPullBcf L
      map_add' := by
        intro u v
        ext x
        rfl
      map_smul' := by
        intro c u
        ext x
        rfl }
    1
    (fun u ↦ by
      change ‖linPullBcf L u‖ ≤ 1 * ‖u‖
      rw [norm_linPullBcf, one_mul])

omit [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [CompleteSpace F] in
@[simp]
theorem linPullBcfCLM_apply
    (L : V ≃L[Real] V) (u : BoundedContinuousFunction V F) :
    linPullBcfCLM L u = linPullBcf L u := rfl

private abbrev Euc (n : Type*) := EuclideanSpace Real n

section SPD

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [CompleteSpace F] [Nonempty n] in
theorem coreLap_pullJet2_spd
    (A : Matrix n n Real) (hA : A.PosDef)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (x : Euc n) :
    coreLap (pullJet2 (spdSqrtEquiv A hA) d2u) x =
      matrixLap A (d2u (spdSqrtEquiv A hA x)) := by
  let L := spdSqrtEquiv A hA
  change lapEval (pullJet2 L d2u x) = matrixLap A (d2u (L x))
  calc
    lapEval (pullJet2 L d2u x) =
        ∑ i : n, pullJet2 L d2u x
          (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real i) :=
      lapEval_basis (EuclideanSpace.basisFun n Real) _
    _ = factorLap L (d2u (L x)) := by
      simp only [factorLap, pullJet2_apply]
    _ = matrixLap A (d2u (L x)) := spd_factorLap A hA _

theorem spdHeatDuh_eq_of_zero_initial
    {t : Real} (ht : 0 < t)
    (A : Matrix n n Real) (hA : A.PosDef)
    (u dtU f : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Ioo (0 : Real) t, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hf : ∀ s x, f s x = dtU s x - matrixLap A (d2u s x))
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (x : Euc n)
    (hint : IntervalIntegrable
      (fun s ↦ heatScaled (t - s) (spdHeatSource A hA f s)
        ((spdSqrtEquiv A hA).symm x)) volume 0 t) :
    spdHeatDuh A hA t f x = u t x := by
  let L := spdSqrtEquiv A hA
  let up : Real → BoundedContinuousFunction (Euc n) F :=
    fun s ↦ linPullBcf L (u s)
  let dtp : Real → BoundedContinuousFunction (Euc n) F :=
    fun s ↦ linPullBcf L (dtU s)
  let dup : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F) :=
    fun s ↦ pullJet1 L (du s)
  let d2p : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F) :=
    fun s ↦ pullJet2 L (d2u s)
  have hupTime : ∀ s ∈ Ioo (0 : Real) t,
      HasDerivAt up (dtp s) s := by
    intro s hs
    simpa only [up, dtp, linPullBcfCLM_apply] using
      (linPullBcfCLM L).hasFDerivAt.comp_hasDerivAt s (huTime s hs)
  have hup : ∀ s ∈ Ioo (0 : Real) t, ∀ z,
      HasFDerivAt (up s : Euc n → F) (dup s z) z := by
    intro s hs z
    exact linPull_fderiv L (u s) (du s) (hu s hs) z
  have hdup : ∀ s ∈ Ioo (0 : Real) t, ∀ z,
      HasFDerivAt (dup s : Euc n → Euc n →L[Real] F)
        (d2p s z) z := by
    intro s hs z
    exact pullJet1_fderiv L (du s) (d2u s) (hdu s hs) z
  have hupCont : Continuous up :=
    (linPullBcfCLM L).continuous.comp huCont
  have hup0 : up 0 = 0 := by
    rw [show up 0 = linPullBcfCLM L (u 0) by rfl, hu0, map_zero]
  have hsource : (fun s ↦ dtp s - coreLap (d2p s)) =
      spdHeatSource A hA f := by
    funext s
    ext z
    change dtU s (L z) - coreLap (pullJet2 L (d2u s)) z = f s (L z)
    rw [coreLap_pullJet2_spd A hA (d2u s) z, hf]
  have hint' : IntervalIntegrable
      (fun s ↦ heatScaled (t - s) (dtp s - coreLap (d2p s))
        (L.symm x)) volume 0 t := by
    have hintegrand :
        (fun s ↦ heatScaled (t - s) (dtp s - coreLap (d2p s))
          (L.symm x)) =
        fun s ↦ heatScaled (t - s) (spdHeatSource A hA f s)
          (L.symm x) := by
      funext s
      rw [congrFun hsource s]
    rw [hintegrand]
    exact hint
  have hiso := heatDuh_eq_of_zero_initial ht up dtp dup d2p
    hupTime hup hdup hupCont hup0 (L.symm x)
      hint'
  rw [hsource] at hiso
  simpa only [spdHeatDuh, L, up, linPullBcf_apply,
    ContinuousLinearEquiv.apply_symm_apply] using hiso

theorem spdHeatDuh_eq_of_zero_initial_of_parabolic_holder
    {alpha K B : NNReal} (halpha0 : 0 < alpha)
    {t : Real} (ht : 0 < t)
    (A : Matrix n n Real) (hA : A.PosDef)
    (u dtU f : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Ioo (0 : Real) t, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Ioo (0 : Real) t, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hf : ∀ s x, f s x = dtU s x - matrixLap A (d2u s x))
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) t) Set.univ).restrict
        (fun p ↦ f p.time p.space)))
    (x : Euc n) :
    spdHeatDuh A hA t f x = u t x := by
  apply spdHeatDuh_eq_of_zero_initial ht A hA u dtU f du d2u
    huTime hu hdu hf huCont hu0 x
  apply heatScaled_timeSource_intervalIntegrable_of_parabolic_holder
    (K := spdSourceHolderConst A hA alpha K) halpha0 ht
      (spdHeatSource A hA f)
  · intro s hs
    rw [spdHeatSource_norm]
    exact hbound s hs
  · exact spdHeatSource_parabolic_holder A hA f hsource

theorem spdHeatDuh_eqOn_of_zero_initial_of_parabolic_holder
    {alpha K B : NNReal} (halpha0 : 0 < alpha)
    {S : Real}
    (A : Matrix n n Real) (hA : A.PosDef)
    (u dtU f : Real → BoundedContinuousFunction (Euc n) F)
    (du : Real →
      BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : Real → BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huTime : ∀ s ∈ Ioo (0 : Real) S, HasDerivAt u (dtU s) s)
    (hu : ∀ s ∈ Ioo (0 : Real) S, ∀ x,
      HasFDerivAt (u s : Euc n → F) (du s x) x)
    (hdu : ∀ s ∈ Ioo (0 : Real) S, ∀ x,
      HasFDerivAt (du s : Euc n → Euc n →L[Real] F) (d2u s x) x)
    (hf : ∀ s x, f s x = dtU s x - matrixLap A (d2u s x))
    (huCont : Continuous u) (hu0 : u 0 = 0)
    (hbound : ∀ s ∈ Icc (0 : Real) S, ‖f s‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).restrict
        (fun p ↦ f p.time p.space))) :
    Set.EqOn
      (fun p ↦ spdHeatDuh A hA p.time f p.space)
      (fun p ↦ u p.time p.space)
      (parabolicCylinder (Ioo (0 : Real) S) Set.univ) := by
  intro p hp
  apply spdHeatDuh_eq_of_zero_initial_of_parabolic_holder
    halpha0 hp.1.1 A hA u dtU f du d2u
  · intro s hs
    exact huTime s ⟨hs.1, hs.2.trans hp.1.2⟩
  · intro s hs
    exact hu s ⟨hs.1, hs.2.trans hp.1.2⟩
  · intro s hs
    exact hdu s ⟨hs.1, hs.2.trans hp.1.2⟩
  · exact hf
  · exact huCont
  · exact hu0
  · intro s hs
    exact hbound s ⟨hs.1, hs.2.trans hp.1.2.le⟩
  · rw [HolderWith.restrict_iff] at hsource ⊢
    exact hsource.mono fun q hq ↦
      ⟨⟨hq.1.1, hq.1.2.trans hp.1.2.le⟩, hq.2⟩

end SPD

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
