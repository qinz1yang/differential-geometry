import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialFirstDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialConnectionClosedSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem curvature_norm_continuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) (k : ℕ) (x : M) :
    ContinuousOn (fun t => nablaKRm04NormSqIntrinsic S k t x) (Icc 0 T) := by
  have hn : ContinuousOn
      (fun q : ℝ × M => nablaKRm04NormSqIntrinsic S k q.1 q.2) (Icc 0 T ×ˢ univ) := by
    have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
      (uniqueDiffOn_Icc hT) hgram k).continuousOn
    apply hh.congr
    intro q _
    dsimp only
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm_eq_iterCov]
    rfl
  exact ContinuousOn.comp
    (g := fun q : ℝ × M => nablaKRm04NormSqIntrinsic S k q.1 q.2)
    (f := fun t : ℝ => (t,x)) hn (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht,mem_univ x⟩)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem initial_laplacian_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioc 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (p : M)
    (hu : ∀ t ∈ Icc 0 T, ∀ y : M,
      riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic S 0 t y ≤ 1) :
    ∀ r ∈ Ioc (R/2) R,
      InitialDistanceFlowLaplacianBound S T p
        {y : M | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R}
        r (-1) (shiLocalClap (Module.finrank ℝ E) T R)
        (shiLocalCconn (Module.finrank ℝ E) T) (nablaRmSupWeight S) := by
  have hlap := initialDistanceFlowLaplacianBound_of_metric_regular (Ksec := -1) S hS p hT
    hslab hreg hgram hu (show 0 < R/2 by positivity)
  intro r hr
  rw [← shiLocalClap_eq (Module.finrank ℝ E) T R (show Real.sqrt (-(-1:ℝ)) = 1 by norm_num),
    ← shiLocalCconn_eq (Module.finrank ℝ E) T]
  exact hlap.mono_radius hr.1.le

universe u
omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
private theorem initial_curvature_derivative_bound_of_unit_curvature_bound
    (N : ℕ) (T R : ℝ) (hT : 0 < T) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X],
      ∀ (D : RealTimeInterval) (S : SolutionOn (I := I) (M := X) D), IsSolutionOn S →
      Icc 0 T ⊆ D.carrier → Ioc 0 T ⊆ D.regular →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric q.1) x₀ q.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ p : X,
      IsCompact {x : X | riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R} →
      (∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S 0 t x ≤ 1) →
      (∀ j, 1 ≤ j → j ≤ N → ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S j 0 x ≤ A j) →
      ∀ j ≤ N, ∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R/2) →
          nablaKRm04NormSqIntrinsic S j t x ≤ B := by
  classical
  let Clap := shiLocalClap (Module.finrank ℝ E) T R
  let Cconn := shiLocalCconn (Module.finrank ℝ E) T
  let Hb := shiLocalFirstDerivativeConst (Module.finrank ℝ E) T R Clap Cconn
  let eps := fun k : Fin N =>
    shiLocalCutoffError (Module.finrank ℝ E) T R Clap Cconn Hb k.val
  obtain ⟨B,hB,hbound⟩ :=
    exists_uniform_curvature_derivative_bound_on_closed_interval_of_fixedCutoffs
    (I := I) N T hT eps A hA
  refine ⟨B,hB,?_⟩
  intro X _ _ _ _ _ D S hS hslab hreg hgram p hball hu hinit
  have hClap : 0 ≤ Clap := shiLocalClap_nonneg _ _ hR
  have hCconn : 0 ≤ Cconn := shiLocalCconn_nonneg _ _
  have hHb0 : 0 ≤ Hb := shiLocalFirstDerivativeConst_nonneg _ _ _ _ _
  have hsec : ∀ y : X, riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R →
      Geometry.Riemannian.SectionalBoundedBelowAt (S.base.metric 0) y (-1) := by
    intro y hy
    apply sectionalBoundedBelowAt_of_curvature_bound S zero_le_one y
    simpa only [one_pow] using hu 0 ⟨le_rfl,hT.le⟩ y hy
  have hlap := initial_laplacian_bound S hS hT hR hslab hreg hgram p hu
  have hHb := shiFirstDerivative_local_nablaRmSupWeight_of_closed_slab S hS
    (a := 32) (r₁ := 3*R/4) (r₂ := R) p hT le_rfl hslab hreg hgram hball
    (by norm_num) hsec hu (by positivity) (by linarith) le_rfl hClap hCconn
    (hlap (3*R/4) ⟨by linarith,by linarith⟩)
  have hcut : ∀ k : Fin N, ∃ fc : ShiFixedCutoff (flowG S) T (eps k),
      (∀ t : ℝ, ∀ x : X, riemannianEDistOf (S.base.metric 0) p x ≤
        ENNReal.ofReal (shiLocalRadius R (k.val+1)) → fc.chi t x = 1) ∧
      fc.support ⊆ {x : X | riemannianEDistOf (S.base.metric 0) p x <
        ENNReal.ofReal (shiLocalRadius R k.val)} := by
    intro k
    apply exists_shiFixedCutoff_ball_error_of_curvature_continuousOn S hS p hT hslab hreg
      (curvature_norm_continuous S hT hgram 1) hball (by norm_num) hsec hu
      (shiLocalRadius_pos hR _) (shiLocalRadius_succ_lt hR _) (shiLocalRadius_le hR _)
      hClap hCconn
      (hlap (shiLocalRadius R (k.val+1))
        ⟨half_lt_shiLocalRadius hR _,shiLocalRadius_le hR _⟩) hHb0
    intro t ht x hx
    apply hHb t ht x
    apply hx.trans (ENNReal.ofReal_le_ofReal ?_)
    have hb := shiLocalRadius_antitone hR (Nat.zero_le k.val)
    rwa [shiLocalRadius_zero] at hb
  choose fc hone hsupp using hcut
  let Ω := fun k : ℕ => {x : X | riemannianEDistOf (S.base.metric 0) p x ≤
    ENNReal.ofReal (shiLocalRadius R k)}
  have houter (x : X) (hx : x ∈ Ω 0) :
      riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R :=
    hx.trans (ENNReal.ofReal_le_ofReal (shiLocalRadius_le hR _))
  intro j hj t ht x hx
  apply hbound X D S hS hreg hgram Ω fc
    (fun k _ x hx => hx.trans (ENNReal.ofReal_le_ofReal
      (shiLocalRadius_antitone hR (Nat.le_succ k))))
    (fun k x hx => show riemannianEDistOf (S.base.metric 0) p x ≤
      ENNReal.ofReal (shiLocalRadius R k.val) from (hsupp k hx).le)
    (fun k t _ x hx => hone k t x hx)
    (fun t ht x hx => hu t ht x (houter x hx))
    (fun k hk hkN y hy => hinit k hk hkN y (houter y hy)) j hj t ht x
  exact hx.trans (ENNReal.ofReal_le_ofReal (half_lt_shiLocalRadius hR N).le)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

universe u

theorem exists_uniform_initial_curvature_derivative_bound_on_compact_ball
    (N : ℕ) (T R K : ℝ) (hT : 0 < T) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X],
      ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), IsSolutionOn S →
      Icc 0 T ⊆ D.carrier → Ioc 0 T ⊆ D.regular →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ p : X,
      IsCompact {x : X | riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R} →
      (∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S k 0 x ≤ A k) →
      ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          nablaKRm04NormSqIntrinsic S k t x ≤ B := by
  let c : ℝ := max 1 K
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let A' := fun k => c⁻¹ ^ (2 + k) * A k
  have hA' : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A' j := by
    intro j hj hjN
    exact mul_nonneg (pow_nonneg (inv_pos.mpr hc).le _) (hA j hj hjN)
  obtain ⟨B, hB, hbound⟩ :=
    initial_curvature_derivative_bound_of_unit_curvature_bound
      (I := I) N (c*T) (Real.sqrt c * R) (mul_pos hc hT)
    (mul_pos (Real.sqrt_pos.mpr hc) hR) A' hA'
  refine ⟨c^(2+N)*B, ?_, ?_⟩
  · have hp : 1 ≤ c^(2+N) := one_le_pow₀ hc1
    nlinarith
  · intro X _ _ _ _ _ D S hS hslab hreg hgram p hcompact hcurv hinit k hk t ht x hx
    have hzero : (0 : ℝ) ∈ D.carrier := hslab ⟨le_rfl, hT.le⟩
    let P := parabolicSolution S 0 c hc hzero
    have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS 0 c hc hzero
    have htime : ∀ s ∈ Icc 0 (c*T), s / c ∈ Icc 0 T := by
      intro s hs
      refine ⟨div_nonneg hs.1 hc.le, (div_le_iff₀ hc).mpr ?_⟩
      simpa only [mul_comm] using hs.2
    have hpslab : Icc 0 (c*T) ⊆ (parabolicInterval D 0 c hzero).carrier := by
      intro s hs
      change parabolicTime 0 c s ∈ D.carrier
      simpa only [parabolicTime, zero_add] using hslab (htime s hs)
    have hpreg : Ioc 0 (c*T) ⊆ (parabolicInterval D 0 c hzero).regular := by
      intro s hs
      change parabolicTime 0 c s ∈ D.regular
      simpa only [parabolicTime, zero_add] using
        hreg ⟨div_pos hs.1 hc, (htime s ⟨hs.1.le,hs.2⟩).2⟩
    have hmetric0 : P.base.metric 0 = scaleMetric c hc (S.base.metric 0) := by
      simp only [P, parabolicSolution, parabolicFamily, parabolicTime, zero_div, zero_add]
    have hpgram : ∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (P.base.metric q.1) x₀ q.2 i j)
          (Icc 0 (c*T) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      have hm : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun q : ℝ × X => (q.1/c,q.2)) :=
        (contMDiff_fst.div_const c).prodMk contMDiff_snd
      have hmap : MapsTo (fun q : ℝ × X => (q.1/c,q.2))
          (Icc 0 (c*T) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
        fun q hq => ⟨htime q.1 hq.1,hq.2⟩
      have hh := (contMDiffOn_const (c := c)).mul
        ((hgram x₀ i j).comp hm.contMDiffOn hmap)
      apply hh.congr
      intro q _
      simp only [Function.comp_def, P, parabolicSolution, parabolicFamily,
        parabolicTime, zero_add, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
        scaleMetric_inner, Pi.mul_apply]
    have hball (r : ℝ) : {y : X | riemannianEDistOf (P.base.metric 0) p y ≤
        ENNReal.ofReal (Real.sqrt c*r)} =
      {y : X | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal r} := by
      rw [hmetric0]
      exact closedBall_scaleMetric_eq (S.base.metric 0) c hc p r
    have hpcompact : IsCompact {y : X | riemannianEDistOf (P.base.metric 0) p y ≤
        ENNReal.ofReal (Real.sqrt c*R)} := by
      rw [hball R]
      exact hcompact
    have hpcurv : ∀ s ∈ Icc 0 (c*T), ∀ y : X,
        riemannianEDistOf (P.base.metric 0) p y ≤ ENNReal.ofReal (Real.sqrt c*R) →
          nablaKRm04NormSqIntrinsic P 0 s y ≤ 1 := by
      intro s hs y hy
      have hy' : riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R := by
        change y ∈ {y : X | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R}
        rw [← hball R]
        exact hy
      rw [parabolicNablaKRmNormSq S 0 c hc hzero]
      have hraw := hcurv (s/c) (htime s hs) y hy'
      have hK : K ≤ c^2 := by
        have hKc : K ≤ c := le_max_right _ _
        nlinarith
      have heq : c⁻¹^2 * c^2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow]
      simpa only [parabolicTime, zero_add, heq] using
        mul_le_mul_of_nonneg_left (hraw.trans hK) (sq_nonneg c⁻¹)
    have hpinit : ∀ j, 1 ≤ j → j ≤ N → ∀ y : X,
        riemannianEDistOf (P.base.metric 0) p y ≤ ENNReal.ofReal (Real.sqrt c*R) →
          nablaKRm04NormSqIntrinsic P j 0 y ≤ A' j := by
      intro j hj hjN y hy
      have hy' : riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R := by
        change y ∈ {y : X | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R}
        rw [← hball R]
        exact hy
      rw [parabolicNablaKRmNormSq S 0 c hc hzero]
      simpa only [A',parabolicTime,zero_div,zero_add] using
        mul_le_mul_of_nonneg_left (hinit j hj hjN y hy') (pow_nonneg (inv_pos.mpr hc).le _)
    have hpt : c*t ∈ Icc 0 (c*T) :=
      ⟨mul_nonneg hc.le ht.1,mul_le_mul_of_nonneg_left ht.2 hc.le⟩
    have hpx : riemannianEDistOf (P.base.metric 0) p x ≤
        ENNReal.ofReal (Real.sqrt c*R/2) := by
      have hx' : x ∈ {y : X | riemannianEDistOf (P.base.metric 0) p y ≤
          ENNReal.ofReal (Real.sqrt c*(R/2))} := by rw [hball];exact hx
      simpa only [Set.mem_ofPred_eq, mul_div_assoc] using hx'
    have hb := hbound X _ P hP hpslab hpreg hpgram p hpcompact hpcurv hpinit k hk (c*t) hpt x hpx
    rw [parabolicNablaKRmNormSq S 0 c hc hzero] at hb
    simp only [parabolicTime,zero_add,mul_div_cancel_left₀ t hc.ne'] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (pow_pos hc (2+k)).le
    have heq : c^(2+k) * (c⁻¹^(2+k) * nablaKRm04NormSqIntrinsic S k t x) =
        nablaKRm04NormSqIntrinsic S k t x := by
      rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ hc.ne',one_pow,one_mul]
    rw [heq] at hmul
    have hp : c^(2+k) ≤ c^(2+N) := pow_le_pow_right₀ hc1 (by omega)
    exact hmul.trans (mul_le_mul_of_nonneg_right hp (zero_le_one.trans hB))

end DifferentialGeometry.PDE.RicciFlow
