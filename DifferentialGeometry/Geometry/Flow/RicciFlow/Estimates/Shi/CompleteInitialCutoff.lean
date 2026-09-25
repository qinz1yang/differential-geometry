import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.ConnectionDifferenceBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalBounds
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.SectionalFromCurvatureBound

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

universe u

omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
theorem exists_uniform_shiFixedCutoff_of_complete_bounded_curvature
    (T K r₁ r₂ R : ℝ) (hT : 0 < T) (hK : 0 ≤ K)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R) :
    ∃ eps : ℝ, 0 ≤ eps ∧
      ∀ (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
        [T2Space X] [SigmaCompactSpace X], ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), IsSolutionOn S →
      Icc 0 T ⊆ D.carrier → Ioc 0 T ⊆ D.regular →
      RiemannianMetricComplete (I := I) (S.base.metric 0) →
      (∀ t ∈ Icc 0 T, ∀ x : X, nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      ∀ p : X,
      ∃ fc : ShiFixedCutoff (flowG S) T eps,
        (∀ t : ℝ, ∀ x : X,
          riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ → fc.chi t x = 1) ∧
        fc.support ⊆ {x : X | riemannianEDistOf (S.base.metric 0) p x < ENNReal.ofReal r₂} := by
  let C : ℝ := (3 * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
        Real.exp (3 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) * T)) *
      (2 * Real.sqrt ((2 : ℝ) ^ 1 *
        (towerConst (max 0 (∑ j ∈ Finset.range 3, rmTowerCost (Module.finrank ℝ E) j))
          (max 1 K * T) 1) ^ 2 * (max 1 K) ^ 2))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let Clap := (Module.finrank ℝ E : ℝ) *
    Real.exp (2 * ((Module.finrank ℝ E : ℝ)^2 * Real.sqrt K) * T) *
      (2 / r₁ + Real.sqrt (Real.sqrt K))
  let Cconn := (Module.finrank ℝ E : ℝ) *
    Real.exp (2 * ((Module.finrank ℝ E : ℝ)^2 * Real.sqrt K) * T) * C
  have hClap : 0 ≤ Clap := by dsimp only [Clap]; positivity
  have hCconn : 0 ≤ Cconn := by dsimp only [Cconn]; positivity
  let a := shiInitialCutoffA (Module.finrank ℝ E) T K r₁ r₂
  let b := shiInitialCutoffB (Module.finrank ℝ E) T K r₁ r₂ Clap
  let d := shiInitialCutoffD r₁ r₂ Cconn
  have ha : 0 ≤ a := shiInitialCutoffA_nonneg _ _ _ _ _
  have hd : 0 ≤ d := shiInitialCutoffD_nonneg hr₁₂.le hCconn
  let eps := max a (b + d * Real.sqrt T)
  refine ⟨eps, ha.trans (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ D S hS hslab hreg hcomplete hcurv p
  have hball := hcomplete.closedEBall_isCompact p R
  have hdiff : InitialConnectionDifferenceBound S T univ C (fun t _ => Real.sqrt t) :=
    initialConnectionDifferenceBound_sqrt_of_complete_bounded_curvature
      S hS hT hslab hreg hcomplete hK hcurv
  have hdiffB : InitialConnectionDifferenceBound S T
      {x : M | riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R}
      C (fun t _ => Real.sqrt t) := fun t ht x _ => hdiff t ht x (mem_univ x)
  have hlap : InitialDistanceFlowLaplacianBound S T p
      {x : M | riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R}
      r₁ (-Real.sqrt K) Clap Cconn (fun t _ => Real.sqrt t) := by
    simpa only [neg_neg, Clap, Cconn] using
      initialDistanceFlowLaplacianBoundOn_of_solution (Ksec := -Real.sqrt K) S hS hT hslab hreg
        (fun t ht x _ => hcurv t ht x) hr₁ hC
        (fun _ _ _ => Real.sqrt_nonneg _) hdiffB p
  have hsec : ∀ x : M,
      Geometry.Riemannian.SectionalBoundedBelowAt (S.base.metric 0) x (-Real.sqrt K) := by
    intro x
    apply sectionalBoundedBelowAt_of_curvature_bound S (Real.sqrt_nonneg K) x
    rw [Real.sq_sqrt hK]
    exact hcurv 0 ⟨le_rfl, hT.le⟩ x
  obtain ⟨idc⟩ := nonempty_shiInitialDistanceCutoff_of_solution S hS p hT hslab hreg
    hball (neg_nonpos.mpr (Real.sqrt_nonneg K)) (fun x _ => hsec x)
    (fun t ht x _ => hcurv t ht x) hr₁ hr₁₂ hr₂R hClap hCconn
    (fun _ _ => Real.sqrt_nonneg _) hlap
  let fc : ShiFixedCutoff (flowG S) T eps :=
    { chi := fun _ x => idc.chi x
      support := idc.support
      err_nonneg := ha.trans (le_max_left _ _)
      support_compact := idc.support_compact
      support_zero := fun _ _ x hx => idc.support_zero x hx
      range := fun _ _ x => idc.chi_mem_Icc x
      joint_cont := (idc.chi_continuous.comp continuous_snd).continuousOn
      lower_support := ?_ }
  case refine_1 =>
    intro t ht hp x hx
    obtain ⟨low⟩ := idc.lower_support t ⟨hp, ht.2⟩ x hx
    have hchi0 : 0 ≤ idc.chi x := (idc.chi_mem_Icc x).1
    have hsqrt : Real.sqrt (idc.chi x) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (idc.chi_mem_Icc x).2
    have hbound : b + d * Real.sqrt (idc.chi x) * Real.sqrt t ≤ b + d * Real.sqrt T := by
      have he : d * Real.sqrt (idc.chi x) * Real.sqrt t ≤ d * 1 * Real.sqrt T := by
        gcongr
        exact ht.2
      have he' : d * Real.sqrt (idc.chi x) * Real.sqrt t ≤ d * Real.sqrt T := by
        simpa only [mul_one] using he
      linarith
    exact ⟨low.toCutoffLowerSupport (le_max_left _ _)
      (hbound.trans (le_max_right _ _)) hchi0⟩
  exact ⟨fc, fun _ x hx => idc.chi_eq_one x hx, idc.support_subset_ball⟩


omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
private theorem initial_curvature_bound_normalized
    (N : ℕ) (T R : ℝ) (hT : 0 < T) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X], ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), IsSolutionOn S →
      Icc 0 T ⊆ D.carrier → Ioc 0 T ⊆ D.regular →
      RiemannianMetricComplete (I := I) (S.base.metric 0) →
      (∀ t ∈ Icc 0 T, ∀ x : X, nablaKRm04NormSqIntrinsic S 0 t x ≤ 1) →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ p : X,
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S k 0 x ≤ A k) →
      ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          nablaKRm04NormSqIntrinsic S k t x ≤ B := by
  classical
  have hcut := fun k : Fin N => exists_uniform_shiFixedCutoff_of_complete_bounded_curvature
    (I := I) T 1 (shiLocalRadius R (k.val+1)) (shiLocalRadius R k.val) R
    hT zero_le_one (shiLocalRadius_pos hR _) (shiLocalRadius_succ_lt hR _)
    (shiLocalRadius_le hR _)
  choose eps heps hcut using hcut
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_curvature_derivative_bound_on_closed_interval_of_fixedCutoffs
      (I := I) N T hT eps A hA
  refine ⟨B, hB, ?_⟩
  intro X _ _ _ _ _ D S hS hslab hreg hcomplete hcurv hgram p hinit k hk t ht x hx
  have hcuts := fun j : Fin N => hcut j X D S hS hslab hreg hcomplete hcurv p
  choose fc hone hsupp using hcuts
  let Ω := fun j : ℕ => {y : X |
    riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal (shiLocalRadius R j)}
  have hnest : ∀ j, j < N → Ω (j+1) ⊆ Ω j := by
    intro j _ y hy
    exact hy.trans (ENNReal.ofReal_le_ofReal (shiLocalRadius_antitone hR (Nat.le_succ j)))
  have houter (y : X) (hy : y ∈ Ω 0) :
      riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R :=
    hy.trans (ENNReal.ofReal_le_ofReal (shiLocalRadius_le hR 0))
  apply hbound X D S hS hreg hgram Ω fc hnest
    (fun j y hy => show riemannianEDistOf (S.base.metric 0) p y ≤
      ENNReal.ofReal (shiLocalRadius R j.val) from (hsupp j hy).le)
    (fun j s _ y hy => hone j s y hy)
    (fun s hs y _ => hcurv s hs y)
    (fun j hj hjN y hy => hinit j hj hjN y (houter y hy)) k hk t ht x
  exact hx.trans (ENNReal.ofReal_le_ofReal (half_lt_shiLocalRadius hR N).le)

omit [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] in
theorem exists_uniform_initial_curvature_derivative_bound_on_ball
    (N : ℕ) (T R K : ℝ) (hT : 0 < T) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X], ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), IsSolutionOn S →
      Icc 0 T ⊆ D.carrier → Ioc 0 T ⊆ D.regular →
      RiemannianMetricComplete (I := I) (S.base.metric 0) →
      (∀ t ∈ Icc 0 T, ∀ x : X, nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ p : X,
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
  obtain ⟨B, hB, hbound⟩ := initial_curvature_bound_normalized
    (I := I) N (c*T) (Real.sqrt c * R) (mul_pos hc hT)
    (mul_pos (Real.sqrt_pos.mpr hc) hR) A' hA'
  refine ⟨c^(2+N)*B, ?_, ?_⟩
  · have hp : 1 ≤ c^(2+N) := one_le_pow₀ hc1
    nlinarith
  · intro X _ _ _ _ _ D S hS hslab hreg hcomplete hcurv hgram p hinit k hk t ht x hx
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
    have hpcomplete : RiemannianMetricComplete (P.base.metric 0) := by
      rw [hmetric0]
      exact hcomplete.scaleMetric c hc
    have hpcurv : ∀ s ∈ Icc 0 (c*T), ∀ y : X,
        nablaKRm04NormSqIntrinsic P 0 s y ≤ 1 := by
      intro s hs y
      rw [parabolicNablaKRmNormSq S 0 c hc hzero]
      have hraw := hcurv (s/c) (htime s hs) y
      have hK : K ≤ c^2 := by
        have hKc : K ≤ c := le_max_right _ _
        nlinarith
      have heq : c⁻¹^2 * c^2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hc.ne', one_pow]
      simpa only [parabolicTime, zero_add, heq] using
        mul_le_mul_of_nonneg_left (hraw.trans hK) (sq_nonneg c⁻¹)
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
    have hb := hbound X _ P hP hpslab hpreg hpcomplete hpcurv hpgram p hpinit k hk (c*t) hpt x hpx
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
