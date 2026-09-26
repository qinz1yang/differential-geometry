import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckScaleStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonParabolicScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBoundary

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]

private local instance canonicalWitnessComparisonTransportC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem StrongNeck.comparison_jet_differentiableWithinAt_of_buffer
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {eps a t : ℝ} {x : P} (nk : StrongNeck S eps x t)
    (hbuffer : a < t - (S.scalar t x)⁻¹) (hslab : Icc a t ⊆ D.carrier)
    (hreg : Ioo a t ⊆ D.regular)
    (q : ℕ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0)
    (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)
    (v : Fin 2 → TangentSpace IC y) :
    DifferentiableWithinAt ℝ (fun r => nk.comparison.jet q r y v) (Icc (-1 : ℝ) 0) s := by
  let Q : ℝ := S.scalar t x
  have hQ : 0 < Q := nk.Q_pos
  have hstart : parabolicTime t Q (-1) = t - Q⁻¹ := by
    simp only [parabolicTime, neg_div, one_div, sub_eq_add_neg]
  have hat : a < parabolicTime t Q (-1) := by rw [hstart]; exact hbuffer
  have hct : parabolicTime t Q (-1) < t := by
    rw [hstart]
    exact sub_lt_self _ (inv_pos.mpr hQ)
  let w : Fin 2 → TangentSpace I3 (nk.map y) := fun j => mfderiv IC I3 nk.map y (v j)
  have hsource0 := (tensor0SEvalCLM (I := I3) (x := nk.map y) w).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time S hS hat hct hslab hreg (nk.map y))
  have htime : ContDiff ℝ ∞ (parabolicTime t Q) :=
    contDiff_const.add (contDiff_id.div_const Q)
  have hmap : MapsTo (parabolicTime t Q) (Icc (-1) 0)
      (Icc (parabolicTime t Q (-1)) t) := by
    intro r hr
    constructor
    · dsimp only [parabolicTime]
      linarith [div_le_div_of_nonneg_right hr.1 hQ.le]
    · change t + r / Q ≤ t
      exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hr.2 hQ.le)
  have hsource : ContDiffOn ℝ ∞
      (fun r => (S.base.metric (parabolicTime t Q r)).inner (nk.map y) (w 0) (w 1))
      (Icc (-1) 0) := by
    have hh := hsource0.comp htime.contDiffOn hmap
    change ContDiffOn ℝ ∞
      (fun r => metricTensorField (S.base.metric (parabolicTime t Q r)) (nk.map y) w)
      (Icc (-1) 0) at hh
    simpa only [metricTensorField_apply] using hh
  have hscaled : ContDiffOn ℝ ∞
      (fun r => (rescaledMetric S t (S.scalar t x) nk.Q_pos r).inner
        (nk.map y) (w 0) (w 1)) (Icc (-1) 0) := by
    simpa only [rescaledMetric, scaleMetric_inner, SolutionOn.family,
      Function.comp_def, smul_eq_mul, Q] using hsource.const_smul Q
  have hpull : ContDiffOn ℝ ∞ (fun r => nk.comparison.pullback r y v) (Icc (-1) 0) :=
    hscaled.congr (fun r _ => nk.comparison.pullback_eq r y hy v)
  have hcylinder : ContDiffOn ℝ ∞
      (fun r => (nk.cylinder.metric r).inner y (v 0) (v 1)) (Icc (-1) 0) := by
    have hh : ContDiff ℝ ∞ (fun r : ℝ =>
        2 * (1 - r) * inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 (v 0).1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 (v 1).1) +
            (v 0).2 * (v 1).2) := by fun_prop
    exact hh.contDiffOn.congr (fun r hr => nk.cylinder.inner_eq r hr.2 y (v 0) (v 1))
  have hzero : ContDiffOn ℝ ∞ (fun r => nk.comparison.jet 0 r y v) (Icc (-1) 0) :=
    (hpull.sub hcylinder).congr (fun r _ => nk.comparison.jet_zero r y v)
  exact (DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
    (f := fun b r => nk.comparison.jet b r y v)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hs (hzero s hs)
    (fun b r hr => nk.comparison.jet_succ b r hr y hy v) q).differentiableWithinAt (by simp)

theorem StrongNeck.exists_rescaled_transport_tolerances
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {alpha a t : ℝ} {p : P} (nk : StrongNeck S (neckModelTolerance alpha) p t)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hbuffer : a < t - (S.scalar t p)⁻¹) (hslab : Icc a t ⊆ D.carrier)
    (hreg : Ioo a t ⊆ D.regular)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ K) :
    ∃ eta beta : ℝ, 0 < eta ∧ 0 < beta ∧
      ∀ c : ℝ, ∀ hc : 0 < c, |c - S.scalar t p| < eta →
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N],
      ∀ {D' : RealTimeInterval} (S' : SolutionOn (I := I3) (M := N) D'), IsSolutionOn S' →
      ∀ {x : N} {t' : ℝ} (hQ : 0 < S'.scalar t' x) {b : ℝ}, b < -1 →
      MapsTo (parabolicTime t' (S'.scalar t' x)) (Icc b 0) D'.carrier →
      MapsTo (parabolicTime t' (S'.scalar t' x)) (Ioo b 0) D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P N ∞, (U : Set P) ⊆ F.source → F p = x →
      MetricComparisonOn (rescaledMetric S t c hc) (rescaledMetric S' t' (S'.scalar t' x) hQ)
        F U (Icc (-1 : ℝ) 0) ⌈(2 * alpha)⁻¹⌉₊ beta →
      ∃ nk' : StrongNeck S' (2 * alpha) x t',
        nk'.map = partialDiffeomorphTransMixed nk.map F := by
  have htarget : 0 < neckSourceTolerance alpha := neckSourceTolerance_pos ha
  have hQ₀ : 0 < S.scalar t p := nk.Q_pos
  obtain ⟨eta, beta, heta, hbeta, htransfer⟩ :=
    exists_rescaledMetric_comparison_tolerance_on_compact S hS (a := a) (t := t) (depth := 1)
      (Q := S.scalar t p) zero_lt_one hQ₀ (by rwa [one_div]) hslab hreg U hUcompact hK hKU
      ⌈(2 * alpha)⁻¹⌉₊ htarget
  refine ⟨eta, beta, heta, hbeta, ?_⟩
  intro c hc hnear N _ _ _ _ _ D' S' hS' x t' hQ b hb hdomain hregular F hF hbase C
  have ht' : t' ∈ D'.carrier := by
    have hh := hdomain (show (0 : ℝ) ∈ Icc b 0 from ⟨by linarith, le_rfl⟩)
    simpa only [parabolicTime_zero] using hh
  let T := parabolicSolution S' t' (S'.scalar t' x) hQ ht'
  have hT : IsSolutionOn T := parabolicSolution_isSolutionOn S' hS' t' (S'.scalar t' x) hQ ht'
  obtain ⟨cmp⟩ := htransfer c hc hnear N T hT hb hdomain hregular F hF C
  have htime : Icc (t' - (S'.scalar t' x)⁻¹) t' ⊆ D'.carrier := by
    intro r hr
    let s := (r - t') * S'.scalar t' x
    have hs : s ∈ Icc b 0 := by
      have hlo := mul_le_mul_of_nonneg_right hr.1 hQ.le
      have hi : (S'.scalar t' x)⁻¹ * S'.scalar t' x = 1 := inv_mul_cancel₀ hQ.ne'
      dsimp only [s]
      constructor
      · nlinarith
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr.2) hQ.le
    have hh := hdomain hs
    have heq : parabolicTime t' (S'.scalar t' x) s = r := by
      dsimp only [parabolicTime, s]
      rw [mul_div_cancel_right₀ _ hQ.ne']
      ring
    rwa [heq] at hh
  have hat : a < t := hbuffer.trans (sub_lt_self _ (inv_pos.mpr hQ₀))
  have ht : t ∈ D.carrier := hslab ⟨hat.le, le_rfl⟩
  let R := parabolicSolution S t (S.scalar t p) hQ₀ ht
  have hR : IsSolutionOn R := parabolicSolution_isSolutionOn S hS t (S.scalar t p) hQ₀ ht
  have ha₁ : (a - t) * S.scalar t p < -1 := by
    have hh := mul_lt_mul_of_pos_right hbuffer hQ₀
    rw [sub_mul, inv_mul_cancel₀ hQ₀.ne'] at hh
    nlinarith
  have hRmem : ∀ r, (a - t) * S.scalar t p ≤ r → r ≤ 0 →
      a ≤ parabolicTime t (S.scalar t p) r ∧ parabolicTime t (S.scalar t p) r ≤ t := by
    intro r hr₁ hr₂
    have hlo : a - t ≤ r / S.scalar t p := (le_div_iff₀ hQ₀).mpr hr₁
    have hhi : r / S.scalar t p ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr₂ hQ₀.le
    change a ≤ t + r / S.scalar t p ∧ t + r / S.scalar t p ≤ t
    constructor <;> linarith
  have hRdomain : Icc ((a - t) * S.scalar t p) 0 ⊆
      (parabolicInterval D t (S.scalar t p) ht).carrier := fun r hr =>
    hslab (hRmem r hr.1 hr.2)
  have hRregular : Ioo ((a - t) * S.scalar t p) 0 ⊆
      (parabolicInterval D t (S.scalar t p) ht).regular := by
    intro r hr
    have hlo : a - t < r / S.scalar t p := (lt_div_iff₀ hQ₀).mpr hr.1
    have hhi : r / S.scalar t p < 0 := div_neg_of_neg_of_pos hr.2 hQ₀
    apply hreg
    change a < t + r / S.scalar t p ∧ t + r / S.scalar t p < t
    constructor <;> linarith
  apply nk.exists_transport_of_local_comparisons hQ F cmp ha hsmall htarget.le le_rfl
    le_rfl hbase houter (hKU.trans hF) htime
  · intro q s hs z hz v
    obtain ⟨y, hy, rfl⟩ := hz
    exact (cmp.jet_contDiffOn_of_solutions R hR T hT ha₁ hb (by norm_num : (-1 : ℝ) < 0)
      hRdomain hRregular hdomain hregular q (nk.map y) (houter y hy) v s hs
      ).differentiableWithinAt (by simp)
  · intro q s hs _hu y hy v
    have hsub := neck_window_subset_of_le (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    exact nk.comparison_jet_differentiableWithinAt_of_buffer hS hbuffer hslab hreg q hs y
      (hsub hy) v

theorem exists_tolerance_abs_metricScalarAt_sub_lt (h : ℝ → SmoothRiemannianMetric I3 P)
    (s : ℝ) (y : P) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
        {g : ℝ → SmoothRiemannianMetric I3 N} {F : PartialDiffeomorph I3 I3 P N ∞}
        {A : Set P} {times : Set ℝ} {order : ℕ},
        MetricComparisonOn h g F A times order delta →
        ∀ U : TopologicalSpace.Opens P, (U : Set P) ⊆ F.source → (U : Set P) ⊆ A →
        s ∈ times → 2 ≤ order → y ∈ U →
        |metricScalarAt (g s) (F y) - metricScalarAt (h s) y| < eta := by
  let B := normSq0S (h s) y 4 (metricRm04At (h s) y)
  let Kb := (Module.finrank ℝ ThreeSpace : ℝ) * Real.sqrt B
  have hRic : ∀ v w : TangentSpace I3 y, |ricciTensor (h s) y v w| ≤
      Kb * Real.sqrt ((h s).inner y v v) * Real.sqrt ((h s).inner y w w) := by
    apply abs_ricciTensor_le_of_riemannOp_le (h s)
    intro a b c
    have hh := riemannOp_normSq_le_of_rmNormSq_le (h s) y (le_refl B) a b c
    refine (Real.sqrt_le_sqrt hh).trans (le_of_eq ?_)
    rw [Real.sqrt_mul' _ (inner_self_nonneg (h s) y c),
      Real.sqrt_mul' _ (inner_self_nonneg (h s) y b),
      Real.sqrt_mul' _ (inner_self_nonneg (h s) y a)]
  have hlim := scalarComparisonC_tendsto 3 Kb
  have h0 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  have h1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have h2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), scalarComparisonC 3 e Kb < eta := hlim (Iio_mem_nhds heta)
  obtain ⟨delta, hpos, hone, hsmall⟩ := (h0.and (h1.and h2)).exists
  refine ⟨delta, hpos, ?_⟩
  intro N _ _ _ _ _ g F A times order C U hU hUA hs horder hy
  exact (C.scalar_sub_le_of_ricci_bound U hU hUA hs hpos.le hone horder hy hRic).trans_lt hsmall

theorem StrongNeck.exists_transport_tolerance_of_metricComparisonOn
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {alpha a t : ℝ} {p : P} (nk : StrongNeck S (neckModelTolerance alpha) p t)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hbuffer : a < t - 2 * (S.scalar t p)⁻¹) (hslab : Icc a t ⊆ D.carrier)
    (hreg : Ioo a t ⊆ D.regular)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ K) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N],
      ∀ {D' : RealTimeInterval} (S' : SolutionOn (I := I3) (M := N) D'), IsSolutionOn S' →
      Icc a t ⊆ D'.carrier → Ioo a t ⊆ D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P N ∞, (U : Set P) ⊆ F.source →
      MetricComparisonOn S.base.metric S'.base.metric F U
        (Icc (t - 2 * (S.scalar t p)⁻¹) t) ⌈(2 * alpha)⁻¹⌉₊ delta →
      ∃ nk' : StrongNeck S' (2 * alpha) (F p) t,
        nk'.map = partialDiffeomorphTransMixed nk.map F := by
  set Q := S.scalar t p
  have hQ : 0 < Q := nk.Q_pos
  have hQinv : 0 < Q⁻¹ := inv_pos.mpr hQ
  have hbuffer' : a < t - Q⁻¹ := by linarith
  obtain ⟨eta, beta, heta, hbeta, htransfer⟩ := nk.exists_rescaled_transport_tolerances hS ha
    hsmall hbuffer' hslab hreg U hUcompact hK hKU houter
  obtain ⟨delta₁, hdelta₁, hscalar⟩ :=
    exists_tolerance_abs_metricScalarAt_sub_lt S.base.metric t p (lt_min heta (half_pos hQ))
  set order := ⌈(2 * alpha)⁻¹⌉₊
  set L := (max 1 (Real.sqrt (Q / 2))⁻¹) ^ order
  have hL1 : 1 ≤ L := one_le_pow₀ (le_max_left _ _)
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨min delta₁ (beta / L), lt_min hdelta₁ (div_pos hbeta hLpos), ?_⟩
  intro N _ _ _ _ _ D' S' hS' hslab' hreg' F hF C
  have ht : t ∈ Icc (t - 2 * Q⁻¹) t := ⟨by linarith, le_rfl⟩
  have horder2 : 2 ≤ order := by
    have h1 : (1 : ℝ) < (2 * alpha)⁻¹ := (one_lt_inv₀ (by linarith)).mpr (by linarith)
    have h2 : 1 < order := Nat.lt_ceil.mpr (by exact_mod_cast h1)
    omega
  have hcenter : (nk.center, (0 : ℝ)) ∈ (univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ : Set Cylinder) :=
    ⟨trivial, neg_neg_of_pos (inv_pos.mpr ha), inv_pos.mpr ha⟩
  have hpU : p ∈ (U : Set P) := by
    have hh := hKU (houter _ hcenter)
    rwa [nk.center_eq] at hh
  have hclose := hscalar N (C.mono (subset_refl _) le_rfl (min_le_left _ _)) U hF
    (subset_refl _) ht horder2 hpU
  change |S'.scalar t (F p) - Q| < min eta (Q / 2) at hclose
  set c := S'.scalar t (F p)
  have hceta : |c - Q| < eta := hclose.trans_le (min_le_left _ _)
  have hcQ : Q / 2 < c := by
    have hh := (abs_lt.mp (hclose.trans_le (min_le_right _ _))).1
    linarith
  have hc : 0 < c := (half_pos hQ).trans hcQ
  have hcinv : c⁻¹ ≤ 2 * Q⁻¹ := by
    have hh := inv_anti₀ (half_pos hQ) hcQ.le
    rw [inv_div, div_eq_mul_inv] at hh
    exact hh
  have hmap : MapsTo (parabolicTime t c) (Icc (-1) 0) (Icc (t - 2 * Q⁻¹) t) := by
    intro s hs
    have hlo : -1 / c ≤ s / c := div_le_div_of_nonneg_right hs.1 hc.le
    rw [neg_div, one_div] at hlo
    have hhi : s / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hc.le
    change t - 2 * Q⁻¹ ≤ t + s / c ∧ t + s / c ≤ t
    constructor <;> linarith
  have hat : a < t - 2 * Q⁻¹ := hbuffer
  have hwin : t - 2 * Q⁻¹ < t := by linarith
  have hdiff : ∀ b s, s ∈ Icc (-1 : ℝ) 0 → ∀ y ∈ (U : Set P),
      ∀ v : Fin 2 → TangentSpace I3 y,
        DifferentiableWithinAt ℝ (fun r => C.jet b r y v) (Icc (t - 2 * Q⁻¹) t)
          (parabolicTime t c s) := by
    intro b s hs y hy v
    exact (C.jet_contDiffOn_of_solutions S hS S' hS' hat hat hwin hslab hreg hslab' hreg'
      b y hy v (parabolicTime t c s) (hmap hs)).differentiableWithinAt (by simp)
  have hscaled := C.parabolicRescale t c hc order le_rfl (Icc (-1) 0)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hmap hdiff
  have hroot : Real.sqrt (Q / 2) ≤ Real.sqrt c := Real.sqrt_le_sqrt hcQ.le
  have hfactor : (max 1 (Real.sqrt c)⁻¹) ^ order ≤ L := by
    apply pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
    exact max_le_max le_rfl (inv_anti₀ (Real.sqrt_pos.mpr (half_pos hQ)) hroot)
  have hdelta : (max 1 (Real.sqrt c)⁻¹) ^ order * min delta₁ (beta / L) ≤ beta := by
    have hm : min delta₁ (beta / L) ≤ beta / L := min_le_right _ _
    have hm0 : 0 ≤ min delta₁ (beta / L) := (lt_min hdelta₁ (div_pos hbeta hLpos)).le
    calc (max 1 (Real.sqrt c)⁻¹) ^ order * min delta₁ (beta / L)
        ≤ L * (beta / L) := mul_le_mul hfactor hm hm0 hLpos.le
      _ = beta := mul_div_cancel₀ _ hLpos.ne'
  have hb : (a - t) * c < -1 := by
    have h1 : a - t < -c⁻¹ := by linarith
    have hh := mul_lt_mul_of_pos_right h1 hc
    rwa [neg_mul, inv_mul_cancel₀ hc.ne'] at hh
  have hmem : ∀ r, (a - t) * c ≤ r → r ≤ 0 →
      a ≤ parabolicTime t c r ∧ parabolicTime t c r ≤ t := by
    intro r hr₁ hr₂
    have hlo : a - t ≤ r / c := (le_div_iff₀ hc).mpr hr₁
    have hhi : r / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr₂ hc.le
    change a ≤ t + r / c ∧ t + r / c ≤ t
    constructor <;> linarith
  have hdomain : MapsTo (parabolicTime t c) (Icc ((a - t) * c) 0) D'.carrier :=
    fun r hr => hslab' (hmem r hr.1 hr.2)
  have hregular : MapsTo (parabolicTime t c) (Ioo ((a - t) * c) 0) D'.regular := by
    intro r hr
    have hlo : a - t < r / c := (lt_div_iff₀ hc).mpr hr.1
    have hhi : r / c < 0 := div_neg_of_neg_of_pos hr.2 hc
    apply hreg'
    change a < t + r / c ∧ t + r / c < t
    constructor <;> linarith
  exact htransfer c hc hceta N S' hS' hc hb hdomain hregular F hF rfl
    (hscaled.mono (subset_refl _) le_rfl hdelta)

theorem LocalNeck.exists_transport_tolerance_of_metricComparisonOn
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {alpha a t : ℝ} {p : P} {V : Set P} (L : LocalNeck S (neckModelTolerance alpha) p t V)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hbuffer : a < t - 2 * (S.scalar t p)⁻¹) (hslab : Icc a t ⊆ D.carrier)
    (hreg : Ioo a t ⊆ D.regular)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, L.strong.map y ∈ K) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N],
      ∀ {D' : RealTimeInterval} (S' : SolutionOn (I := I3) (M := N) D'), IsSolutionOn S' →
      Icc a t ⊆ D'.carrier → Ioo a t ⊆ D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P N ∞, (U : Set P) ⊆ F.source →
      MetricComparisonOn S.base.metric S'.base.metric F U
        (Icc (t - 2 * (S.scalar t p)⁻¹) t) ⌈(2 * alpha)⁻¹⌉₊ delta →
      ∃ L' : LocalNeck S' (2 * alpha) (F p) t (F '' V),
        L'.strong.map = partialDiffeomorphTransMixed L.strong.map F := by
  obtain ⟨delta, hdelta, htransport⟩ := L.strong.exists_transport_tolerance_of_metricComparisonOn
    hS ha hsmall hbuffer hslab hreg U hUcompact hK hKU houter
  refine ⟨delta, hdelta, ?_⟩
  intro N _ _ _ _ _ D' S' hS' hslab' hreg' F hF C
  obtain ⟨nk', hmap⟩ := htransport N S' hS' hslab' hreg' F hF C
  have hregion : nk'.region = F '' V := by
    change nk'.map '' (univ ×ˢ Icc (-10 : ℝ) 10) = F '' V
    rw [hmap]
    exact (Set.image_image (fun y : P => F y) L.strong.map (univ ×ˢ Icc (-10 : ℝ) 10)).symm.trans
      (congrArg (fun W : Set P => F '' W) L.region_eq.symm)
  have hout : ∃ out : LocalNeck S' (2 * alpha) (F p) t nk'.region,
      out.strong.map = partialDiffeomorphTransMixed L.strong.map F :=
    ⟨nk'.toLocalNeck, hmap⟩
  rwa [hregion] at hout

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
