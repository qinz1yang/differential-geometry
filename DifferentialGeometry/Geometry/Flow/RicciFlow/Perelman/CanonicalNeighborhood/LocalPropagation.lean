import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open Bundle DifferentialGeometry.Tensor0SBundle
open Filter
open scoped Manifold ContDiff ENNReal Topology



section Crossing

theorem forall_le_of_no_crossing {a b B C : Real} {f : Real → Real}
    (hBC : B < C) (hcont : ContinuousOn f (Set.Icc a b))
    (hno : ∀ u v : Real, a ≤ u → u ≤ v → v ≤ b →
      (∀ w ∈ Set.Icc u v, B ≤ f w) → f u ≤ max B (f a) → C ≤ f v → False) :
    ∀ t ∈ Set.Icc a b, f t ≤ C := by
  intro t ht
  by_contra hcon
  push Not at hcon
  have hat : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  have hsubT : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl htb
  have hTclosed : IsClosed (Set.Icc a t ∩ f ⁻¹' Set.Ici C) :=
    (hcont.mono hsubT).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hTcompact : IsCompact (Set.Icc a t ∩ f ⁻¹' Set.Ici C) :=
    IsCompact.of_isClosed_subset isCompact_Icc hTclosed Set.inter_subset_left
  have hTne : (Set.Icc a t ∩ f ⁻¹' Set.Ici C).Nonempty := ⟨t, ⟨hat, le_rfl⟩, hcon.le⟩
  obtain ⟨t0, ht0mem, ht0min⟩ := hTcompact.exists_isMinOn hTne continuousOn_id
  have ht0a : a ≤ t0 := ht0mem.1.1
  have ht0t : t0 ≤ t := ht0mem.1.2
  have ht0b : t0 ≤ b := le_trans ht0t htb
  have ht0C : C ≤ f t0 := ht0mem.2
  have hUclosed : IsClosed (Set.Icc a t0 ∩ f ⁻¹' Set.Iic B) :=
    (hcont.mono (Set.Icc_subset_Icc le_rfl ht0b)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hUcompact : IsCompact (Set.Icc a t0 ∩ f ⁻¹' Set.Iic B) :=
    IsCompact.of_isClosed_subset isCompact_Icc hUclosed Set.inter_subset_left
  rcases Set.eq_empty_or_nonempty (Set.Icc a t0 ∩ f ⁻¹' Set.Iic B) with hUe | hUne
  · refine hno a t0 le_rfl ht0a ht0b ?_ (le_max_right _ _) ht0C
    intro w hw
    by_contra hlt
    push Not at hlt
    have hmem : w ∈ Set.Icc a t0 ∩ f ⁻¹' Set.Iic B := ⟨hw, hlt.le⟩
    rw [hUe] at hmem
    exact hmem.elim
  · obtain ⟨t1, ht1mem, ht1max⟩ := hUcompact.exists_isMaxOn hUne continuousOn_id
    have ht1a : a ≤ t1 := ht1mem.1.1
    have ht1t0 : t1 ≤ t0 := ht1mem.1.2
    have ht1B : f t1 ≤ B := ht1mem.2
    have ht1lt : t1 < t0 := by
      rcases lt_or_eq_of_le ht1t0 with h | h
      · exact h
      · rw [h] at ht1B
        linarith
    have habove : ∀ w : Real, t1 < w → w ≤ t0 → B < f w := by
      intro w h1 h2
      by_contra hw
      push Not at hw
      have hle : w ≤ t1 :=
        isMaxOn_iff.mp ht1max w ⟨⟨le_trans ht1a h1.le, h2⟩, hw⟩
      linarith
    have hBt1 : B ≤ f t1 := by
      have hsubIoc : Set.Ioc t1 t0 ⊆ Set.Icc a b := by
        intro w hw
        exact ⟨le_trans ht1a hw.1.le, le_trans hw.2 ht0b⟩
      have hcw : Filter.Tendsto f (nhdsWithin t1 (Set.Ioc t1 t0)) (nhds (f t1)) :=
        (hcont t1 ⟨ht1a, le_trans ht1t0 ht0b⟩).mono hsubIoc
      have hmem : Set.Ioc t1 t0 ∈ nhdsWithin t1 (Set.Ioi t1) := Ioc_mem_nhdsGT ht1lt
      have htend : Filter.Tendsto f (nhdsWithin t1 (Set.Ioi t1)) (nhds (f t1)) :=
        hcw.mono_left (nhdsWithin_le_of_mem hmem)
      refine ge_of_tendsto htend ?_
      filter_upwards [hmem] with w hw using (habove w hw.1 hw.2).le
    refine hno t1 t0 ht1a ht1t0 ht0b ?_ (le_trans ht1B (le_max_left _ _)) ht0C
    intro w hw
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h]
      exact hBt1
    · exact (habove w h hw.2).le

end Crossing



section InverseDerivatives


theorem hasDerivAt_inv_sqrt {f : Real → Real} {fp tau : Real}
    (hf : HasDerivAt f fp tau) (hpos : 0 < f tau) :
    HasDerivAt (fun sigma : Real => (Real.sqrt (f sigma))⁻¹)
      (-(1 / (2 * Real.sqrt (f tau)) * fp) / Real.sqrt (f tau) ^ 2) tau := by
  have h1 : HasDerivAt (fun sigma : Real => Real.sqrt (f sigma))
      (1 / (2 * Real.sqrt (f tau)) * fp) tau :=
    (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp tau hf
  exact h1.inv (ne_of_gt (Real.sqrt_pos.2 hpos))

theorem abs_deriv_inv_sqrt_le {R fp K : Real}
    (hpos : 0 < R) (hb : |fp| ≤ 2 * K * (R * Real.sqrt R)) :
    |-(1 / (2 * Real.sqrt R) * fp) / Real.sqrt R ^ 2| ≤ K := by
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hpos.le
  rw [abs_div, abs_neg, abs_mul, hsq, abs_of_pos hpos, div_le_iff₀ hpos,
    abs_of_pos (by positivity : (0 : Real) < 1 / (2 * Real.sqrt R)),
    div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0 : Real) < 2 * Real.sqrt R)]
  have heq : 2 * K * (R * Real.sqrt R) = K * R * (2 * Real.sqrt R) := by
    ring
  linarith [hb, heq]


theorem hasDerivAt_inv_of {f : Real → Real} {fp tau : Real}
    (hf : HasDerivAt f fp tau) (hpos : 0 < f tau) :
    HasDerivAt (fun sigma : Real => (f sigma)⁻¹) (-fp / f tau ^ 2) tau :=
  hf.inv (ne_of_gt hpos)


theorem abs_deriv_inv_le {R fp K : Real}
    (hpos : 0 < R) (hb : |fp| ≤ K * R ^ 2) :
    |-fp / R ^ 2| ≤ K := by
  have hsq : (0 : Real) < R ^ 2 := by positivity
  rw [abs_div, abs_neg, abs_of_pos hsq, div_le_iff₀ hsq]
  linarith [hb]

theorem one_div_ten_lt_inv_sqrt_two_sub_inv_sqrt_three :
    (1 : Real) / 10 < (Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹ := by
  have h2p : (0 : Real) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2 : Real.sqrt 2 ≤ 1.415 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2), Real.sqrt_nonneg (2 : Real)]
  have h3 : (1.732 : Real) ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3), Real.sqrt_nonneg (3 : Real)]
  have hA : (1 : Real) / 1.415 ≤ 1 / Real.sqrt 2 := one_div_le_one_div_of_le h2p h2
  have hB : (1 : Real) / Real.sqrt 3 ≤ 1 / 1.732 := one_div_le_one_div_of_le (by norm_num) h3
  have hnum : (1 : Real) / 10 < 1 / 1.415 - 1 / 1.732 := by norm_num
  rw [inv_eq_one_div, inv_eq_one_div]
  linarith

end InverseDerivatives



section

open MeasureTheory

theorem abs_sub_le_of_hasDerivAt_of_lintegral_le
    {f fp v : Real → Real} {a b c d K B : Real}
    (hab : a ≤ b) (hsub : Set.Icc a b ⊆ Set.Icc c d) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hderiv : ∀ w ∈ Set.Icc a b, HasDerivAt f (fp w) w)
    (hbd : ∀ w ∈ Set.Icc a b, |fp w| ≤ K * v w)
    (hint : (∫⁻ w in Set.Icc c d, ENNReal.ofReal (v w)) ≤ ENNReal.ofReal B) :
    |f b - f a| ≤ K * B := by
  have hderiv' : ∀ w ∈ Set.uIcc a b, HasDerivAt f (deriv f w) w := by
    intro w hw
    rw [Set.uIcc_of_le hab] at hw
    have h := hderiv w hw
    rw [h.deriv]
    exact h
  have hbd' : ∀ w ∈ Set.Icc a b, |deriv f w| ≤ K * v w := by
    intro w hw
    rw [(hderiv w hw).deriv]
    exact hbd w hw
  have hmono : (∫⁻ w in Set.Ioc a b, ‖deriv f w‖ₑ) ≤
      ENNReal.ofReal K * ENNReal.ofReal B := by
    have h1 : (∫⁻ w in Set.Ioc a b, ‖deriv f w‖ₑ) ≤
        ∫⁻ w in Set.Ioc a b, ENNReal.ofReal K * ENNReal.ofReal (v w) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with w hw
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (hbd' w (Set.Ioc_subset_Icc_self hw))
    have h2 : (∫⁻ w in Set.Ioc a b, ENNReal.ofReal K * ENNReal.ofReal (v w)) =
        ENNReal.ofReal K * ∫⁻ w in Set.Ioc a b, ENNReal.ofReal (v w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have h3 : (∫⁻ w in Set.Ioc a b, ENNReal.ofReal (v w)) ≤ ENNReal.ofReal B :=
      le_trans (lintegral_mono_set (Set.Ioc_subset_Icc_self.trans hsub)) hint
    calc (∫⁻ w in Set.Ioc a b, ‖deriv f w‖ₑ)
        ≤ ∫⁻ w in Set.Ioc a b, ENNReal.ofReal K * ENNReal.ofReal (v w) := h1
      _ = ENNReal.ofReal K * ∫⁻ w in Set.Ioc a b, ENNReal.ofReal (v w) := h2
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal B := mul_le_mul' le_rfl h3
  have hfin : HasFiniteIntegral (deriv f) (volume.restrict (Set.Ioc a b)) := by
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt hmono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hintg : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ⟨(stronglyMeasurable_deriv f).aestronglyMeasurable, hfin⟩
  have hFTC : ∫ w in a..b, deriv f w = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hintg
  have hnorm : ‖f b - f a‖ ≤
      (∫⁻ w in Set.Ioc a b, ENNReal.ofReal ‖deriv f w‖).toReal := by
    rw [← hFTC, intervalIntegral.integral_of_le hab]
    exact norm_integral_le_lintegral_norm _
  have heq : (∫⁻ w in Set.Ioc a b, ENNReal.ofReal ‖deriv f w‖) =
      ∫⁻ w in Set.Ioc a b, ‖deriv f w‖ₑ := by
    refine lintegral_congr fun w => ?_
    rw [ofReal_norm]
  rw [heq] at hnorm
  have htoReal : (∫⁻ w in Set.Ioc a b, ‖deriv f w‖ₑ).toReal ≤ K * B := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne hmono
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK, ENNReal.toReal_ofReal hB] at h
  rw [Real.norm_eq_abs] at hnorm
  linarith

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_path_lintegral_speed_lt_of_mem_closedBall
    (g : SmoothRiemannianMetric I M) {z y : M} {r eta : Real}
    (hr : 0 ≤ r) (heta : 0 < eta)
    (hy : y ∈ riemannianClosedBallOf (I := I) g z r) :
    ∃ gamma : Real → M, ContMDiff 𝓘(Real, Real) I 1 gamma ∧ gamma 0 = z ∧ gamma 1 = y ∧
      (∫⁻ tau in Set.Icc (0 : Real) 1, ENNReal.ofReal (Real.sqrt
        (g.inner (gamma tau) (mfderiv 𝓘(Real, Real) I gamma tau (realTangentOne tau))
          (mfderiv 𝓘(Real, Real) I gamma tau (realTangentOne tau))))) <
        ENNReal.ofReal (r + eta) := by
  have hball : riemannianEDistOf (I := I) g z y ≤ ENNReal.ofReal r := hy
  have hlt : riemannianEDistOf (I := I) g z y < ENNReal.ofReal (r + eta) :=
    lt_of_le_of_lt hball ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).2 (by linarith))
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hlt' : Manifold.riemannianEDist I z y < ENNReal.ofReal (r + eta) := hlt
  obtain ⟨gamma, h0, h1, hsm, hlen, -, -⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt' zero_lt_one
  refine ⟨gamma, hsm, h0, h1, ?_⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc] at hlen
  refine lt_of_le_of_lt (le_of_eq ?_) hlen
  refine lintegral_congr fun tau => ?_
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  congr 2

end



section Interfaces

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def GoodPointBoundsOn (S : SolutionOn (I := I) (M := M) D) (eps kappa CStar : Real) : Prop :=
  ∀ (x : M) (t : Real), IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
    (∀ v : TangentSpace I x,
        |scalarDifferential (I := I) S t x v| ≤
          2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
            Real.sqrt ((S.base.metric t).inner x v v)) ∧
      |deriv (fun tau : Real => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2

theorem goodPointBoundsOn_of_goodPointDerivativeBounds
    {kappa epsStar CStar : Real}
    (h : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
      [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
      {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (x : M) (t eps : Real),
      0 < eps → eps ≤ epsStar →
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
        (∀ v : TangentSpace I x,
            |scalarDifferential (I := I) S t x v| ≤
              2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
          |deriv (fun tau : Real => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2)
    (S : SolutionOn (I := I) (M := M) D) {eps : Real} (heps : 0 < eps)
    (hle : eps ≤ epsStar) :
    GoodPointBoundsOn.{u, uE, uH} (I := I) S eps kappa CStar :=
  fun x t hgood => h M S x t eps heps hle hgood

def localPropagationRadius (CStar : Real) : Real := 1 / (20 * (CStar + 1))

theorem localPropagationRadius_pos {CStar : Real} (h : 0 ≤ CStar) :
    0 < localPropagationRadius CStar := by
  unfold localPropagationRadius
  positivity

theorem localPropagationRadius_le {CStar : Real} (h : 0 ≤ CStar) :
    localPropagationRadius CStar ≤ 1 / 20 := by
  unfold localPropagationRadius
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem mul_localPropagationRadius_lt {CStar : Real} (h : 0 ≤ CStar) :
    CStar * localPropagationRadius CStar < 1 / 20 := by
  unfold localPropagationRadius
  rw [mul_one_div, div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

end Interfaces



section Derivatives

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem hasDerivAt_scalar_comp (S : SolutionOn (I := I) (M := M) D) (t : Real)
    {gamma : Real → M} (hgamma : ContMDiff 𝓘(Real, Real) I 1 gamma) (tau : Real) :
    HasDerivAt (fun sigma : Real => S.scalar t (gamma sigma))
      (scalarDifferential (I := I) S t (gamma tau)
        (mfderiv 𝓘(Real, Real) I gamma tau (realTangentOne tau))) tau := by
  exact hasDerivAt_comp_mfderiv_along I (S.scalar t) gamma tau
    ((scalarSmoothOfSolution (I := I) S t).mdifferentiableAt (by simp))
    (hgamma.mdifferentiableAt (by simp))

omit [SigmaCompactSpace M] in
theorem differentiableAt_scalar_time {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) {t : Real} (ht : t ∈ D.regular) (x : M) :
    DifferentiableAt Real (fun sigma : Real => S.scalar sigma x) t :=
  (hS.scalarTime ht D.regular_subset x).differentiableAt (D.regular_isOpen.mem_nhds ht)

end Derivatives



section ScalarBound

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem scalar_le_of_good_locus
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {eps kappa CStar Q Hd L t0 s v : Real} {z y : M}
    (hCStar : 0 ≤ CStar) (hQ : 0 < Q) (hL1 : 1 ≤ L)
    (hbnd : GoodPointBoundsOn.{u, uE, uH} (I := I) S eps kappa CStar)
    (hHd : 2 * localPropagationRadius CStar ≤ Hd)
    (hJ : Set.Icc (t0 - Hd / Q) t0 ⊆ D.regular)
    (hgood : ∀ (w : M) (t : Real), t ∈ Set.Icc (t0 - Hd / Q) t0 →
      2 * Q ≤ S.scalar t w → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S w t)
    (hs : s ∈ Set.Icc (t0 - Hd / (2 * Q)) t0)
    (hz : S.scalar s z ≤ Q * (L - 1))
    (hy : y ∈ riemannianClosedBallOf (I := I) (S.base.metric s) z
      (localPropagationRadius CStar / Real.sqrt (Q * L)))
    (hv : v ∈ Set.Icc (s - localPropagationRadius CStar / (Q * L)) s) :
    S.scalar v y ≤ 4 * (Q * L) := by
  have hLpos : (0 : Real) < L := lt_of_lt_of_le zero_lt_one hL1
  have hP : (0 : Real) < Q * L := mul_pos hQ hLpos
  have hQL : Q ≤ Q * L := by nlinarith
  have hcpos : 0 < localPropagationRadius CStar := localPropagationRadius_pos hCStar
  have hcsmall : CStar * localPropagationRadius CStar < 1 / 20 :=
    mul_localPropagationRadius_lt hCStar
  have hQinv : (0 : Real) < Q⁻¹ := inv_pos.2 hQ
  have hcQpos : (0 : Real) < localPropagationRadius CStar / Q := div_pos hcpos hQ
  have hshift : localPropagationRadius CStar / (Q * L) ≤ localPropagationRadius CStar / Q :=
    div_le_div_of_nonneg_left hcpos.le hQ hQL
  have hhalf : Hd / (2 * Q) + localPropagationRadius CStar / Q ≤ Hd / Q := by
    have e1 : Hd / (2 * Q) = Hd / 2 * Q⁻¹ := by
      field_simp
    have e2 : localPropagationRadius CStar / Q = localPropagationRadius CStar * Q⁻¹ :=
      div_eq_mul_inv _ _
    have e3 : Hd / Q = Hd * Q⁻¹ := div_eq_mul_inv _ _
    rw [e1, e2, e3, ← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hQinv.le
  have hsJ : s ∈ Set.Icc (t0 - Hd / Q) t0 := by
    refine ⟨?_, hs.2⟩
    have h1 := hs.1
    linarith
  have hwin : Set.Icc (s - localPropagationRadius CStar / (Q * L)) s ⊆
      Set.Icc (t0 - Hd / Q) t0 := by
    intro w hw
    refine ⟨?_, le_trans hw.2 hs.2⟩
    have h1 := hs.1
    have h2 := hw.1
    linarith
  have hradpos : 0 < localPropagationRadius CStar / Real.sqrt (Q * L) :=
    div_pos hcpos (Real.sqrt_pos.2 hP)
  have hsqP : (0 : Real) < Real.sqrt (Q * L) := Real.sqrt_pos.2 hP
  obtain ⟨gam, hgam, hgam0, hgam1, hspeed⟩ :=
    exists_path_lintegral_speed_lt_of_mem_closedBall (I := I) (S.base.metric s)
      hradpos.le hradpos hy
  have hspeed2 := hspeed.le
  rw [show localPropagationRadius CStar / Real.sqrt (Q * L) +
        localPropagationRadius CStar / Real.sqrt (Q * L) =
      2 * (localPropagationRadius CStar / Real.sqrt (Q * L)) from by ring] at hspeed2
  have hbudnn : (0 : Real) ≤ 2 * (localPropagationRadius CStar / Real.sqrt (Q * L)) := by
    positivity
  have hstep1 : S.scalar s y ≤ 3 * (Q * L) := by
    have hcont : ContinuousOn (fun sig : Real => S.scalar s (gam sig)) (Set.Icc 0 1) :=
      (((scalarSmoothOfSolution (I := I) S s).continuous).comp hgam.continuous).continuousOn
    have hkey : ∀ t ∈ Set.Icc (0 : Real) 1,
        (fun sig : Real => S.scalar s (gam sig)) t ≤ 3 * (Q * L) := by
      refine forall_le_of_no_crossing (B := 2 * Q) (by linarith) hcont ?_
      intro uu vv h0u huv hv1 hge hstart hend
      have hsub : Set.Icc uu vv ⊆ Set.Icc (0 : Real) 1 := Set.Icc_subset_Icc h0u hv1
      have hpos : ∀ w ∈ Set.Icc uu vv, 0 < S.scalar s (gam w) := by
        intro w hw
        exact lt_of_lt_of_le (by linarith) (hge w hw)
      have hderiv : ∀ w ∈ Set.Icc uu vv,
          HasDerivAt (fun sig : Real => (Real.sqrt (S.scalar s (gam sig)))⁻¹)
            (-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
                scalarDifferential (I := I) S s (gam w)
                  (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) /
                Real.sqrt (S.scalar s (gam w)) ^ 2) w := by
        intro w hw
        exact hasDerivAt_inv_sqrt (hasDerivAt_scalar_comp (I := I) S s hgam w) (hpos w hw)
      have hbdd : ∀ w ∈ Set.Icc uu vv,
          |-(1 / (2 * Real.sqrt (S.scalar s (gam w))) *
              scalarDifferential (I := I) S s (gam w)
                (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) /
              Real.sqrt (S.scalar s (gam w)) ^ 2| ≤
            CStar * Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) := by
        intro w hw
        refine abs_deriv_inv_sqrt_le (hpos w hw) ?_
        have hgp : IsGoodPoint.{u, uE, uH} (I := I) eps kappa S (gam w) s :=
          hgood (gam w) s hsJ (hge w hw)
        have hgd := (hbnd (gam w) s hgp).1 (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
        have hring : 2 * (CStar * Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w)))) *
            (S.scalar s (gam w) * Real.sqrt (S.scalar s (gam w))) =
          2 * CStar * (S.scalar s (gam w) * Real.sqrt (S.scalar s (gam w))) *
            Real.sqrt ((S.base.metric s).inner (gam w)
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
              (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))) := by
          ring
        rw [hring]
        exact hgd
      have hbud : |(Real.sqrt (S.scalar s (gam vv)))⁻¹ -
          (Real.sqrt (S.scalar s (gam uu)))⁻¹| ≤
            CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) :=
        abs_sub_le_of_hasDerivAt_of_lintegral_le
          (f := fun sig : Real => (Real.sqrt (S.scalar s (gam sig)))⁻¹)
          (a := uu) (b := vv)
          (v := fun w : Real => Real.sqrt ((S.base.metric s).inner (gam w)
            (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))
            (mfderiv 𝓘(Real, Real) I gam w (realTangentOne w))))
          huv hsub hCStar hbudnn hderiv hbdd hspeed2
      have huupos : 0 < S.scalar s (gam uu) := hpos uu (Set.left_mem_Icc.2 huv)
      have hstart' : S.scalar s (gam uu) ≤ max (2 * Q) (S.scalar s (gam 0)) := hstart
      rw [hgam0] at hstart'
      have hend' : 3 * (Q * L) ≤ S.scalar s (gam vv) := hend
      have hstart2 : S.scalar s (gam uu) ≤ 2 * (Q * L) := by
        refine le_trans hstart' (max_le (by linarith) ?_)
        nlinarith [hz, hP, hQ]
      have hA : (Real.sqrt (2 * (Q * L)))⁻¹ ≤ (Real.sqrt (S.scalar s (gam uu)))⁻¹ := by
        have h2 := one_div_le_one_div_of_le (Real.sqrt_pos.2 huupos)
          (Real.sqrt_le_sqrt hstart2)
        rwa [one_div, one_div] at h2
      have hB : (Real.sqrt (S.scalar s (gam vv)))⁻¹ ≤ (Real.sqrt (3 * (Q * L)))⁻¹ := by
        have h2 := one_div_le_one_div_of_le
          (Real.sqrt_pos.2 (by linarith : (0 : Real) < 3 * (Q * L)))
          (Real.sqrt_le_sqrt hend')
        rwa [one_div, one_div] at h2
      have hgapEq : (Real.sqrt (2 * (Q * L)))⁻¹ - (Real.sqrt (3 * (Q * L)))⁻¹ =
          ((Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹) * (Real.sqrt (Q * L))⁻¹ := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
          Real.sqrt_mul (by norm_num : (0 : Real) ≤ 3), mul_inv, mul_inv]
        ring
      have hbudEq : CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) =
          2 * (CStar * localPropagationRadius CStar) * (Real.sqrt (Q * L))⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      have hnum : 2 * (CStar * localPropagationRadius CStar) <
          (Real.sqrt 2)⁻¹ - (Real.sqrt 3)⁻¹ := by
        linarith [one_div_ten_lt_inv_sqrt_two_sub_inv_sqrt_three]
      have hfin : CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) <
          (Real.sqrt (2 * (Q * L)))⁻¹ - (Real.sqrt (3 * (Q * L)))⁻¹ := by
        rw [hgapEq, hbudEq]
        exact mul_lt_mul_of_pos_right hnum (inv_pos.2 hsqP)
      have hdrop : (Real.sqrt (2 * (Q * L)))⁻¹ - (Real.sqrt (3 * (Q * L)))⁻¹ ≤
          CStar * (2 * (localPropagationRadius CStar / Real.sqrt (Q * L))) := by
        refine le_trans ?_ hbud
        linarith [hA, hB, neg_le_abs ((Real.sqrt (S.scalar s (gam vv)))⁻¹ -
          (Real.sqrt (S.scalar s (gam uu)))⁻¹)]
      linarith
    have h1 : S.scalar s (gam 1) ≤ 3 * (Q * L) := hkey 1 ⟨by norm_num, le_rfl⟩
    rwa [hgam1] at h1
  have hvs : v ≤ s := hv.2
  have hsv : (0 : Real) ≤ s - v := by linarith
  have hsvle : s - v ≤ localPropagationRadius CStar / (Q * L) := by
    have h1 := hv.1
    linarith
  have htimes : ∀ sg ∈ Set.Icc (0 : Real) 1,
      s - sg * (s - v) ∈ Set.Icc (s - localPropagationRadius CStar / (Q * L)) s := by
    intro sg hsg
    exact ⟨by nlinarith [hsg.1, hsg.2], by nlinarith [hsg.1]⟩
  have hdiffy : ∀ rho ∈ Set.Icc (s - localPropagationRadius CStar / (Q * L)) s,
      DifferentiableAt Real (fun sigma : Real => S.scalar sigma y) rho := by
    intro rho hrho
    exact differentiableAt_scalar_time (I := I) hS (hJ (hwin hrho)) y
  have hftd : ∀ sg ∈ Set.Icc (0 : Real) 1,
      HasDerivAt (fun sig : Real => S.scalar (s - sig * (s - v)) y)
        (deriv (fun rho : Real => S.scalar rho y) (s - sg * (s - v)) * -(s - v)) sg := by
    intro sg hsg
    have hline : HasDerivAt (fun sig : Real => s - sig * (s - v)) (-(s - v)) sg := by
      simpa using ((hasDerivAt_id sg).mul_const (s - v)).const_sub s
    exact ((hdiffy _ (htimes sg hsg)).hasDerivAt).comp sg hline
  have hcontT : ContinuousOn (fun sig : Real => S.scalar (s - sig * (s - v)) y)
      (Set.Icc 0 1) := fun sg hsg => ((hftd sg hsg).continuousAt).continuousWithinAt
  have hkeyT : ∀ t ∈ Set.Icc (0 : Real) 1,
      (fun sig : Real => S.scalar (s - sig * (s - v)) y) t ≤ 4 * (Q * L) := by
    refine forall_le_of_no_crossing (B := 2 * Q) (by linarith) hcontT ?_
    intro uu vv h0u huv hv1 hge hstart hend
    have hsub : Set.Icc uu vv ⊆ Set.Icc (0 : Real) 1 := Set.Icc_subset_Icc h0u hv1
    have hpos : ∀ w ∈ Set.Icc uu vv, 0 < S.scalar (s - w * (s - v)) y := by
      intro w hw
      exact lt_of_lt_of_le (by linarith) (hge w hw)
    have hderiv : ∀ w ∈ Set.Icc uu vv,
        HasDerivWithinAt (fun sig : Real => (S.scalar (s - sig * (s - v)) y)⁻¹)
          (-(deriv (fun rho : Real => S.scalar rho y) (s - w * (s - v)) *
              -(s - v)) / S.scalar (s - w * (s - v)) y ^ 2) (Set.Icc uu vv) w := by
      intro w hw
      exact (hasDerivAt_inv_of (hftd w (hsub hw)) (hpos w hw)).hasDerivWithinAt
    have hbdd : ∀ w ∈ Set.Icc uu vv,
        ‖-(deriv (fun rho : Real => S.scalar rho y) (s - w * (s - v)) *
            -(s - v)) / S.scalar (s - w * (s - v)) y ^ 2‖ ≤ CStar * (s - v) := by
      intro w hw
      rw [Real.norm_eq_abs]
      refine abs_deriv_inv_le (hpos w hw) ?_
      have hgp : IsGoodPoint.{u, uE, uH} (I := I) eps kappa S y (s - w * (s - v)) :=
        hgood y (s - w * (s - v)) (hwin (htimes w (hsub hw))) (hge w hw)
      have htb := (hbnd y (s - w * (s - v)) hgp).2
      have habs : |deriv (fun rho : Real => S.scalar rho y) (s - w * (s - v)) * -(s - v)|
          = |deriv (fun rho : Real => S.scalar rho y) (s - w * (s - v))| * (s - v) := by
        rw [abs_mul, abs_neg, abs_of_nonneg hsv]
      rw [habs]
      nlinarith [htb, hsv, sq_nonneg (S.scalar (s - w * (s - v)) y)]
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbdd
      (convex_Icc uu vv) (Set.left_mem_Icc.2 huv) (Set.right_mem_Icc.2 huv)
    have hlen : ‖vv - uu‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : Real) ≤ vv - uu)]
      linarith
    have hCnn : (0 : Real) ≤ CStar * (s - v) := mul_nonneg hCStar hsv
    have hbud : ‖(S.scalar (s - vv * (s - v)) y)⁻¹ - (S.scalar (s - uu * (s - v)) y)⁻¹‖ ≤
        CStar * (s - v) := by
      refine le_trans hmvt ?_
      nlinarith [hlen, hCnn]
    have huupos : 0 < S.scalar (s - uu * (s - v)) y := hpos uu (Set.left_mem_Icc.2 huv)
    have hstart' : S.scalar (s - uu * (s - v)) y ≤
        max (2 * Q) (S.scalar (s - 0 * (s - v)) y) := hstart
    rw [zero_mul, sub_zero] at hstart'
    have hend' : 4 * (Q * L) ≤ S.scalar (s - vv * (s - v)) y := hend
    have hstart2 : S.scalar (s - uu * (s - v)) y ≤ 3 * (Q * L) :=
      le_trans hstart' (max_le (by linarith) hstep1)
    have hA : (3 * (Q * L))⁻¹ ≤ (S.scalar (s - uu * (s - v)) y)⁻¹ := by
      have h2 := one_div_le_one_div_of_le huupos hstart2
      rwa [one_div, one_div] at h2
    have hB : (S.scalar (s - vv * (s - v)) y)⁻¹ ≤ (4 * (Q * L))⁻¹ := by
      have h2 := one_div_le_one_div_of_le (by linarith : (0 : Real) < 4 * (Q * L)) hend'
      rwa [one_div, one_div] at h2
    have hgapEq : (3 * (Q * L))⁻¹ - (4 * (Q * L))⁻¹ = 1 / 12 * (Q * L)⁻¹ := by
      rw [mul_inv, mul_inv]
      ring
    have hbudLe : CStar * (s - v) ≤ CStar * localPropagationRadius CStar * (Q * L)⁻¹ := by
      have h1 : s - v ≤ localPropagationRadius CStar * (Q * L)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact hsvle
      nlinarith [hCStar, h1]
    have hfin : CStar * localPropagationRadius CStar * (Q * L)⁻¹ < 1 / 12 * (Q * L)⁻¹ :=
      mul_lt_mul_of_pos_right (by linarith) (inv_pos.2 hP)
    have hdrop : (3 * (Q * L))⁻¹ - (4 * (Q * L))⁻¹ ≤ CStar * (s - v) := by
      refine le_trans ?_ hbud
      rw [Real.norm_eq_abs]
      linarith [hA, hB, neg_le_abs ((S.scalar (s - vv * (s - v)) y)⁻¹ -
        (S.scalar (s - uu * (s - v)) y)⁻¹)]
    rw [hgapEq] at hdrop
    linarith
  have hfinal : S.scalar (s - 1 * (s - v)) y ≤ 4 * (Q * L) := hkeyT 1 ⟨by norm_num, le_rfl⟩
  rwa [one_mul, sub_sub_cancel] at hfinal

end ScalarBound



section LimitClause

theorem exists_pinching_error_lt {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi) {L0 eta : Real} (heta : 0 < eta) :
    ∃ Q0 : Real, 0 < Q0 ∧ ∀ Q : Real, Q0 ≤ Q → ∀ L ∈ Set.Icc (1 : Real) L0,
      (Phi (4 * Q * L) + Phi 0) / Q < eta := by
  obtain ⟨Q0, hQ0pos, hQ0⟩ := exists_forall_rescalePinchingFunction_le
    (Phi := Phi) hPhi (eps := eta / 3) (B := 4 * L0) (by positivity)
  refine ⟨Q0, hQ0pos, ?_⟩
  intro Q hQ L hL
  have hQpos : 0 < Q := lt_of_lt_of_le hQ0pos hQ
  have hL1 : (1 : Real) ≤ L := hL.1
  have hmem : 4 * L ∈ Set.Icc (0 : Real) (4 * L0) := ⟨by linarith, by linarith [hL.2]⟩
  have hzero : (0 : Real) ∈ Set.Icc (0 : Real) (4 * L0) :=
    ⟨le_rfl, by linarith [hL.2]⟩
  have hA := hQ0 Q hQ (4 * L) hmem
  have hB := hQ0 Q hQ 0 hzero
  rw [rescalePinchingFunction] at hA hB
  have hAeq : Q * (4 * L) = 4 * Q * L := by ring
  rw [hAeq] at hA
  rw [mul_zero] at hB
  rw [div_lt_iff₀ hQpos]
  have hA' : Phi (4 * Q * L) ≤ eta / 3 * Q := by
    rw [inv_mul_eq_div, div_le_iff₀ hQpos] at hA
    linarith
  have hB' : Phi 0 ≤ eta / 3 * Q := by
    rw [inv_mul_eq_div, div_le_iff₀ hQpos] at hB
    linarith
  nlinarith [hA', hB', heta, hQpos]

end LimitClause



section Pinching

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem neg_six_mul_phi_zero_le_scalar
    {S : SolutionOn (I := I) (M := M) D} {W : Set Real} {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hanc : PhiAlmostNonnegative (I := I) (M := M) S W Phi)
    (hdim : Module.finrank Real E = 3)
    {t : Real} (ht : t ∈ W) (x : M) :
    -6 * Phi 0 ≤ S.scalar t x := by
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    calc Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
      _ = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdimT
  have hscal := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt (I := I) S basis horth
  rw [Fin.sum_univ_three] at hscal
  have h0 := neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
    (I := I) hanc ht basis horth 0
  have h1 := neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
    (I := I) hanc ht basis horth 1
  have h2 := neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
    (I := I) hanc ht basis horth 2
  rcases le_or_gt (S.scalar t x) 0 with hneg | hpos
  · have hmono : Phi (S.scalar t x) ≤ Phi 0 := hPhi.mono hneg
    linarith
  · have hzero := hPhi.pos 0
    linarith

def RmNormLeOfCurvatureOperatorBounds (I : ModelWithCorners Real E H) : Prop :=
  ∃ C : Real, 0 ≤ C ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
      [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
      {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
      ∀ a : Real,
        (∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ i| ≤ a) →
          Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤ C * a


def RmNormBoundOn (S : SolutionOn (I := I) (M := M) D) (C3 : Real) : Prop :=
  ∀ (t : Real) (x : M) (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
    OrthonormalBasisAt (I := I) (S.base.metric t) x basis →
    ∀ a : Real,
      (∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ i| ≤ a) →
        Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤ C3 * a

omit [SigmaCompactSpace M] in
theorem sqrt_rmNormSq_le_of_scalar_le
    {S : SolutionOn (I := I) (M := M) D} {W : Set Real} {Phi : Real → Real} {C3 : Real}
    (hC3 : 0 ≤ C3) (hbridge : RmNormBoundOn (I := I) S C3)
    (hPhi : AdmissiblePinchingFunction Phi)
    (hanc : PhiAlmostNonnegative (I := I) (M := M) S W Phi)
    (hdim : Module.finrank Real E = 3)
    {t : Real} (ht : t ∈ W) (x : M) {P : Real} (hP : 0 < P)
    (hub : S.scalar t x ≤ 4 * P) :
    Real.sqrt (FlowMetricBall.rmNormSq (I := I) S t x) ≤ 2 * C3 * (P + Phi (4 * P) + Phi 0) := by
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    calc Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
      _ = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdimT
  have hscal := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt (I := I) S basis horth
  rw [Fin.sum_univ_three] at hscal
  have h1 := neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
    (I := I) hanc ht basis horth 1
  have h2 := neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
    (I := I) hanc ht basis horth 2
  have hmono : Phi (S.scalar t x) ≤ Phi (4 * P) := hPhi.mono hub
  have hpos4 : 0 < Phi (4 * P) := hPhi.pos _
  have hpos0 : 0 < Phi 0 := hPhi.pos 0
  have hanti := orderedSectionalCurvaturesAt_antitone (I := I) x basis
    (⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
  have hbound : ∀ i : Fin 3, |orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ i| ≤ 2 * P + 2 * Phi (4 * P) := by
    intro i
    have hlow := neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
      (I := I) hanc ht basis horth i
    have hi0 := hanti (Fin.zero_le i)
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmain := hbridge t x basis horth (2 * P + 2 * Phi (4 * P)) hbound
  nlinarith [hmain, hC3, hpos0]

end Pinching



section Rescaled

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

theorem parabolicTime_mem_window {t0 Q Hd L c sbar r : Real} (hQ : 0 < Q) (hc : 0 < c)
    (hL1 : 1 ≤ L) (hHd : 2 * c ≤ Hd) (hsbar : sbar ∈ Set.Icc (-(Hd / 2)) 0)
    (hr : r ∈ Set.Icc (sbar - c / L) sbar) :
    parabolicTime t0 Q r ∈ Set.Icc (t0 - Hd / Q) t0 := by
  have hQinv : (0 : Real) ≤ Q⁻¹ := (inv_pos.2 hQ).le
  have hcL : c / L ≤ c := div_le_self hc.le hL1
  have hrlow : -Hd ≤ r := by
    have h1 := hsbar.1
    have h2 := hr.1
    linarith [hHd, hcL]
  have hrhigh : r ≤ 0 := le_trans hr.2 hsbar.2
  have e1 : Hd / Q = Hd * Q⁻¹ := div_eq_mul_inv _ _
  have e2 : r / Q = r * Q⁻¹ := div_eq_mul_inv _ _
  have hlow : (-Hd) * Q⁻¹ ≤ r * Q⁻¹ := mul_le_mul_of_nonneg_right hrlow hQinv
  have hhigh : r * Q⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hrhigh hQinv
  simp only [parabolicTime]
  rw [e1, e2]
  constructor <;> nlinarith [hlow, hhigh]

theorem parabolicTime_mem_half_window {t0 Q Hd sbar : Real} (hQ : 0 < Q)
    (hsbar : sbar ∈ Set.Icc (-(Hd / 2)) 0) :
    parabolicTime t0 Q sbar ∈ Set.Icc (t0 - Hd / (2 * Q)) t0 := by
  have hQinv : (0 : Real) ≤ Q⁻¹ := (inv_pos.2 hQ).le
  have e1 : Hd / (2 * Q) = Hd / 2 * Q⁻¹ := by
    field_simp
  have e2 : sbar / Q = sbar * Q⁻¹ := div_eq_mul_inv _ _
  have hlow : (-(Hd / 2)) * Q⁻¹ ≤ sbar * Q⁻¹ :=
    mul_le_mul_of_nonneg_right hsbar.1 hQinv
  have hhigh : sbar * Q⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hsbar.2 hQinv
  simp only [parabolicTime]
  rw [e1, e2]
  constructor <;> nlinarith [hlow, hhigh]

omit [SigmaCompactSpace M] in
theorem rmNormSq_paraSolution (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : Real) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (sbar : Real) (x : M) :
    FlowMetricBall.rmNormSq (I := I) (parabolicSolution (I := I) S t0 Q hQ ht0) sbar x =
      Q⁻¹ ^ 2 * FlowMetricBall.rmNormSq (I := I) S (parabolicTime t0 Q sbar) x :=
  parabolicRmNormSq (I := I) S t0 Q hQ ht0 sbar x

omit [SigmaCompactSpace M] in
theorem local_propagation_paraSolution
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn (I := I) S)
    {Phi : Real → Real} {eps kappa CStar C3 Q Hd L t0 sbar vbar : Real} {z y : M}
    (hCStar : 0 ≤ CStar) (hC3 : 0 ≤ C3) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (hdim : Module.finrank Real E = 3)
    (hPhi : AdmissiblePinchingFunction Phi)
    (hanc : PhiAlmostNonnegative (I := I) (M := M) S (Set.Icc (t0 - Hd / Q) t0) Phi)
    (hbridge : RmNormBoundOn (I := I) S C3)
    (hbnd : GoodPointBoundsOn.{u, uE, uH} (I := I) S eps kappa CStar)
    (hHd : 2 * localPropagationRadius CStar ≤ Hd)
    (hJ : Set.Icc (t0 - Hd / Q) t0 ⊆ D.regular)
    (hgood : ∀ (w : M) (t : Real), t ∈ Set.Icc (t0 - Hd / Q) t0 →
      2 * Q ≤ S.scalar t w → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S w t)
    (hsbar : sbar ∈ Set.Icc (-(Hd / 2)) 0)
    (hL : L = 1 + |(parabolicSolution (I := I) S t0 Q hQ ht0).scalar sbar z|)
    (hmem : (y, vbar) ∈ frozenBackwardCylinder (I := I)
      (parabolicSolution (I := I) S t0 Q hQ ht0) z sbar
      (localPropagationRadius CStar) (localPropagationRadius CStar) L) :
    -6 * Q⁻¹ * Phi 0 ≤ (parabolicSolution (I := I) S t0 Q hQ ht0).scalar vbar y ∧
      (parabolicSolution (I := I) S t0 Q hQ ht0).scalar vbar y ≤ 4 * L ∧
      Real.sqrt (FlowMetricBall.rmNormSq (I := I) (parabolicSolution (I := I) S t0 Q hQ ht0) vbar y) ≤
        2 * C3 * (L + (Phi (4 * Q * L) + Phi 0) / Q) := by
  have hcpos : 0 < localPropagationRadius CStar := localPropagationRadius_pos hCStar
  have hscalpara := parabolicSolution_scalar (I := I) S t0 Q hQ ht0
  have hLz : |Q⁻¹ * S.scalar (parabolicTime t0 Q sbar) z| = Q⁻¹ * |S.scalar (parabolicTime t0 Q sbar) z| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hQ)]
  have hLval : L = 1 + Q⁻¹ * |S.scalar (parabolicTime t0 Q sbar) z| := by
    rw [hL, hscalpara, hLz]
  have hL1 : (1 : Real) ≤ L := by
    have := abs_nonneg (S.scalar (parabolicTime t0 Q sbar) z)
    have hinv : (0 : Real) < Q⁻¹ := inv_pos.2 hQ
    rw [hLval]
    nlinarith
  have hLpos : (0 : Real) < L := lt_of_lt_of_le zero_lt_one hL1
  have hP : (0 : Real) < Q * L := mul_pos hQ hLpos
  have hzbound : S.scalar (parabolicTime t0 Q sbar) z ≤ Q * (L - 1) := by
    have habs := le_abs_self (S.scalar (parabolicTime t0 Q sbar) z)
    have hQne : Q ≠ 0 := ne_of_gt hQ
    have hexp : Q * (L - 1) = |S.scalar (parabolicTime t0 Q sbar) z| := by
      rw [hLval]
      field_simp
      ring
    linarith [hexp, habs]
  have hs := parabolicTime_mem_half_window (t0 := t0) (Q := Q) (Hd := Hd) hQ hsbar
  have hballmem : y ∈ riemannianClosedBallOf (I := I)
      ((parabolicSolution (I := I) S t0 Q hQ ht0).base.metric sbar) z
      (localPropagationRadius CStar / Real.sqrt L) := hmem.1
  have htimemem : vbar ∈ Set.Icc (sbar - localPropagationRadius CStar / L) sbar := hmem.2
  have hmetric : (parabolicSolution (I := I) S t0 Q hQ ht0).base.metric sbar =
      scaleMetric (I := I) Q hQ (S.base.metric (parabolicTime t0 Q sbar)) := rfl
  have hsqrtQL : Real.sqrt (Q * L) = Real.sqrt Q * Real.sqrt L := Real.sqrt_mul hQ.le L
  have hQs : (0 : Real) < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hLs : (0 : Real) < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hradeq : Real.sqrt Q * (localPropagationRadius CStar / Real.sqrt (Q * L)) =
      localPropagationRadius CStar / Real.sqrt L := by
    rw [hsqrtQL]
    field_simp
  have hballeq := riemannianClosedBallOf_scaleMetric (I := I) Q hQ
    (S.base.metric (parabolicTime t0 Q sbar)) z (localPropagationRadius CStar / Real.sqrt (Q * L))
  rw [hradeq] at hballeq
  have hy : y ∈ riemannianClosedBallOf (I := I) (S.base.metric (parabolicTime t0 Q sbar)) z
      (localPropagationRadius CStar / Real.sqrt (Q * L)) := by
    rw [← hballeq]
    rw [hmetric] at hballmem
    exact hballmem
  have hv : parabolicTime t0 Q vbar ∈ Set.Icc
      (parabolicTime t0 Q sbar - localPropagationRadius CStar / (Q * L)) (parabolicTime t0 Q sbar) := by
    have hQinv : (0 : Real) ≤ Q⁻¹ := (inv_pos.2 hQ).le
    have h1 := htimemem.1
    have h2 := htimemem.2
    have hmul : (sbar - localPropagationRadius CStar / L) * Q⁻¹ ≤ vbar * Q⁻¹ :=
      mul_le_mul_of_nonneg_right h1 hQinv
    have hmul2 : vbar * Q⁻¹ ≤ sbar * Q⁻¹ := mul_le_mul_of_nonneg_right h2 hQinv
    have e1 : localPropagationRadius CStar / (Q * L) =
        localPropagationRadius CStar / L * Q⁻¹ := by
      field_simp
    simp only [parabolicTime]
    rw [e1, div_eq_mul_inv vbar Q, div_eq_mul_inv sbar Q]
    constructor <;> nlinarith [hmul, hmul2]
  have hvwin := parabolicTime_mem_window (t0 := t0) (Q := Q) (Hd := Hd) (L := L)
    (c := localPropagationRadius CStar) hQ hcpos hL1 hHd hsbar htimemem
  have hscalar := scalar_le_of_good_locus (I := I) hS hCStar hQ hL1 hbnd hHd hJ hgood
    hs hzbound hy hv
  have hlower := neg_six_mul_phi_zero_le_scalar (I := I) hPhi hanc hdim hvwin y
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I) hC3 hbridge hPhi hanc hdim hvwin y hP
    hscalar
  have hQinvpos : (0 : Real) < Q⁻¹ := inv_pos.2 hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [hscalpara]
    nlinarith [hlower, hQinvpos]
  · rw [hscalpara]
    have hQL : Q⁻¹ * (4 * (Q * L)) = 4 * L := by
      field_simp
    nlinarith [hscalar, hQinvpos, hQL]
  · rw [rmNormSq_paraSolution (I := I) S t0 Q hQ ht0 vbar y,
      Real.sqrt_mul (sq_nonneg Q⁻¹), Real.sqrt_sq hQinvpos.le]
    have hPhieq : Phi (4 * (Q * L)) = Phi (4 * Q * L) := by
      rw [mul_assoc]
    rw [hPhieq] at hrm
    have hgoal : Q⁻¹ * (2 * C3 * (Q * L + Phi (4 * Q * L) + Phi 0)) =
        2 * C3 * (L + (Phi (4 * Q * L) + Phi 0) / Q) := by
      field_simp
      ring
    calc Q⁻¹ * Real.sqrt (FlowMetricBall.rmNormSq (I := I) S (parabolicTime t0 Q vbar) y)
        ≤ Q⁻¹ * (2 * C3 * (Q * L + Phi (4 * Q * L) + Phi 0)) :=
          mul_le_mul_of_nonneg_left hrm hQinvpos.le
      _ = 2 * C3 * (L + (Phi (4 * Q * L) + Phi 0) / Q) := hgoal

end Rescaled



section Packaged

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem exists_local_propagation_constants {kappa : Real}
    (hGP : GoodPointDerivativeBounds.{u} I kappa)
    (hRm : RmNormLeOfCurvatureOperatorBounds.{u} I) :
    ∃ epsStar c C : Real, 0 < epsStar ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
        (S : SolutionOn (I := I) (M := M) D), IsSolutionOn (I := I) S →
        Module.finrank Real E = 3 →
        ∀ Phi : Real → Real, AdmissiblePinchingFunction Phi →
        ∀ eps : Real, 0 < eps → eps ≤ epsStar →
        ∀ Q : Real, ∀ hQ : 0 < Q, ∀ t0 : Real, ∀ ht0 : t0 ∈ D.carrier,
        ∀ Hd : Real, 2 * c ≤ Hd →
        Set.Icc (t0 - Hd / Q) t0 ⊆ D.regular →
        PhiAlmostNonnegative (I := I) (M := M) S (Set.Icc (t0 - Hd / Q) t0) Phi →
        (∀ (w : M) (t : Real), t ∈ Set.Icc (t0 - Hd / Q) t0 →
          2 * Q ≤ S.scalar t w → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S w t) →
        ∀ (z : M) (sbar : Real), sbar ∈ Set.Icc (-(Hd / 2)) 0 →
        ∀ L : Real, L = 1 + |(parabolicSolution (I := I) S t0 Q hQ ht0).scalar sbar z| →
          Set.Icc (sbar - c / L) sbar ⊆ (parabolicInterval D t0 Q ht0).carrier ∧
            ∀ (y : M) (vbar : Real),
              (y, vbar) ∈ frozenBackwardCylinder (I := I)
                (parabolicSolution (I := I) S t0 Q hQ ht0) z sbar c c L →
                -6 * Q⁻¹ * Phi 0 ≤ (parabolicSolution (I := I) S t0 Q hQ ht0).scalar vbar y ∧
                  (parabolicSolution (I := I) S t0 Q hQ ht0).scalar vbar y ≤ 4 * L ∧
                  Real.sqrt (FlowMetricBall.rmNormSq (I := I)
                      (parabolicSolution (I := I) S t0 Q hQ ht0) vbar y) ≤
                    C * (L + (Phi (4 * Q * L) + Phi 0) / Q) := by
  obtain ⟨epsStar, CStar, hepsStar, hCStar, hGP'⟩ := hGP
  obtain ⟨C3, hC3, hRm'⟩ := hRm
  refine ⟨epsStar, localPropagationRadius CStar, 2 * C3, hepsStar,
    localPropagationRadius_pos hCStar, by linarith, ?_⟩
  intro M instTop instCharted instMan instMan1 instT2 instSigma D S hS hdim Phi hPhi
    eps heps hepsle Q hQ t0 ht0 Hd hHd hJ hanc hgood z sbar hsbar L hL
  have hbridge : RmNormBoundOn (I := I) S C3 := fun t x basis horth a ha =>
    hRm' M S t x basis horth a ha
  have hbnd : GoodPointBoundsOn.{u, uE, uH} (I := I) S eps kappa CStar := fun x t hgp =>
    hGP' M S x t eps heps hepsle hgp
  have hL1 : (1 : Real) ≤ L := by
    have habs := abs_nonneg ((parabolicSolution (I := I) S t0 Q hQ ht0).scalar sbar z)
    rw [hL]
    linarith
  refine ⟨?_, ?_⟩
  · intro r hr
    exact D.regular_subset (hJ (parabolicTime_mem_window (t0 := t0) (Q := Q) (Hd := Hd) (L := L)
      (c := localPropagationRadius CStar) hQ (localPropagationRadius_pos hCStar) hL1 hHd
      hsbar hr))
  · intro y vbar hmem
    exact local_propagation_paraSolution (I := I) hS hCStar hC3 hQ ht0 hdim hPhi hanc hbridge
      hbnd hHd hJ hgood hsbar hL hmem

end Packaged

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
