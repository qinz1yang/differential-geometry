import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedJacobian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.JacobianLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedLengthLimit

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold _root_.Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
private theorem tendsto_lReducedJacobian_square_at_zero_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {sigma : Real}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    Tendsto
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2))
      (𝓝[>] (0 : Real))
      (𝓝 (((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hposDom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hsqrtDom : Real.sqrt sigma ∈ lRegularizedDomain S T x Z :=
    ((mem_lExpPosDom S T x Z sigma).1 hposDom).2.2
  have hzeroDom : (0 : Real) ∈ lRegularizedDomain S T x Z :=
    lRegularizedDomain_segment S T x Z hsqrtDom (by norm_num) (Real.sqrt_nonneg sigma)
  have hT : T ∈ D.regular := by
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero] using
      lRegularizedDomain_regularity S T x Z hzeroDom
  have hden := tendsto_normalized_lExpDensity_at_zero S hS T x Z hT
  have hlen := tendsto_redLength_lExp_square_at_zero_of_bdd S hS T x Z hmin hbdd
  have hexp : Tendsto
      (fun s : Real ↦ Real.exp
        (-redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2)))
      (𝓝[>] (0 : Real))
      (𝓝 (Real.exp (-(S.base.metric T).inner x Z Z))) :=
    by simpa only [Real.exp_eq_exp_ℝ] using hlen.neg.exp
  have hpi : Tendsto
      (fun _ : Real ↦ ((Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2))⁻¹)
      (𝓝[>] (0 : Real))
      (𝓝 (((Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2))⁻¹)) :=
    tendsto_const_nhds
  have hcore : Tendsto
      (fun s : Real ↦
        (lExpDensity S T x Z (s ^ 2) /
            (2 * s) ^ (Module.finrank Real E)) *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp
            (-redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2)))
      (𝓝[>] (0 : Real))
      (𝓝 (lSourceDensity S T x *
        ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) :=
    (hden.mul hpi).mul hexp
  have hsToZero : Tendsto (fun s : Real ↦ s ^ 2)
      (𝓝[>] (0 : Real)) (𝓝 (0 : Real)) := by
    have hid : Tendsto (fun s : Real ↦ s) (𝓝[>] (0 : Real))
        (𝓝 (0 : Real)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0)] using hid.pow 2
  have hsLt : ∀ᶠ s in 𝓝[>] (0 : Real), s ^ 2 < sigma :=
    hsToZero.eventually (Iio_mem_nhds hsigma)
  have heq :
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2) * lSourceDensity S T x) =ᶠ[𝓝[>] (0 : Real)]
      fun s : Real ↦
        (lExpDensity S T x Z (s ^ 2) /
            (2 * s) ^ (Module.finrank Real E)) *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp
            (-redLength S T x (lExp S T x Z (s ^ 2)) (s ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsSq0 : 0 < s ^ 2 := sq_pos_of_pos hs
    have hdom := lExpPosDom_down S T x Z hposDom hsSq0 hsSq.le
    have hnc := lMinVec_nconj_lt_of_bdd S hS T x hmin hsSq hbdd
    have hsPow : Real.exp
        ((Module.finrank Real E : Real) / 2 * Real.log (s ^ 2)) =
        s ^ (Module.finrank Real E) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hsSq0, ← Real.rpow_two s,
        ← Real.rpow_mul hs.le]
      rw [show (2 : Real) * ((Module.finrank Real E : Real) / 2) =
          (Module.finrank Real E : Real) by ring, Real.rpow_natCast]
    have hfourPi : 0 < (4 : Real) * Real.pi :=
      mul_pos (by norm_num) Real.pi_pos
    have hfourPow : Real.exp
        ((Module.finrank Real E : Real) / 2 * Real.log (4 * Real.pi)) =
        (2 : Real) ^ (Module.finrank Real E) *
          (Real.pi : Real) ^ ((Module.finrank Real E : Real) / 2) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hfourPi]
      rw [show (4 : Real) * Real.pi = (2 : Real) ^ 2 * Real.pi by ring,
        Real.mul_rpow (sq_nonneg (2 : Real)) Real.pi_pos.le,
        ← Real.rpow_two (2 : Real),
        ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
      rw [show (2 : Real) * ((Module.finrank Real E : Real) / 2) =
          (Module.finrank Real E : Real) by ring, Real.rpow_natCast]
    have hpi0 : (Real.pi : Real) ^
        ((Module.finrank Real E : Real) / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
    rw [lRedJac_mul_src_of_nonconj S T x Z (s ^ 2) hdom hnc]
    unfold redDensity
    rw [Real.exp_sub, Real.exp_sub, hsPow, hfourPow]
    field_simp [hs0, hpi0]
    ; ring
  have hprod : Tendsto
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2) * lSourceDensity S T x)
      (𝓝[>] (0 : Real))
      (𝓝 (lSourceDensity S T x *
        ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) :=
    hcore.congr' heq.symm
  have hsrc0 : lSourceDensity S T x ≠ 0 :=
    ne_of_gt (lSourceDensity_pos S T x)
  have hdiv := hprod.div_const (lSourceDensity S T x)
  have hfun :
      (fun s : Real ↦
        (lReducedJacobian S T x Z (s ^ 2) * lSourceDensity S T x) /
          lSourceDensity S T x) =
      (fun s : Real ↦ lReducedJacobian S T x Z (s ^ 2)) := by
    funext s
    exact mul_div_cancel_right₀ _ hsrc0
  have htarget :
      (lSourceDensity S T x *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp (-(S.base.metric T).inner x Z Z)) /
        lSourceDensity S T x =
      ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
    field_simp [hsrc0]
  rw [hfun, htarget] at hdiv
  exact hdiv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem tendsto_lReducedJacobian_at_zero_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {sigma : Real}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    Tendsto
      (fun tau : Real ↦ lReducedJacobian S T x Z tau)
      (𝓝[>] (0 : Real))
      (𝓝 (((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) := by
  have hsqrt : Tendsto Real.sqrt
      (𝓝[>] (0 : Real)) (𝓝[>] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨
      by
        simpa only [Real.sqrt_zero] using
          (Real.continuous_sqrt.tendsto (0 : Real)).mono_left nhdsWithin_le_nhds,
      by
        filter_upwards [self_mem_nhdsWithin] with tau htau
        exact Real.sqrt_pos.2 htau⟩
  have hlim := (tendsto_lReducedJacobian_square_at_zero_of_bdd S hS T x Z hmin hbdd).comp hsqrt
  have heq :
      (fun tau : Real ↦ lReducedJacobian S T x Z tau) =ᶠ[𝓝[>] (0 : Real)]
        (fun tau : Real ↦ lReducedJacobian S T x Z (Real.sqrt tau ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    rw [Real.sq_sqrt htau.le]
  exact hlim.congr' heq.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem tendsto_lReducedJacobian_at_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {rho : Real}
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x rho) :
    Tendsto
      (fun tau : Real ↦ lReducedJacobian S T x Z tau)
      (𝓝[>] (0 : Real))
      (𝓝 (((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) := by
  obtain ⟨sigma, _, hmin⟩ := hZ
  apply tendsto_lReducedJacobian_at_zero_of_bdd S hS T x Z hmin
  apply lRegularizedCosts_bdd_of_compact S hS T (Real.sqrt_nonneg sigma)
  intro t ht
  exact D.regular_subset (lExpPosDom_regularity S T x Z
    ((mem_lMinDomain S T x Z sigma).mp hmin).1 ht)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] in
theorem lReducedJacobian_le_gaussian_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x) (htau : 0 < tau) (hlt : tau < sigma)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    lReducedJacobian S T x Z tau ≤
      ((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
  have hsToZero : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [id_eq, zero_pow two_ne_zero] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))).pow 2)
  have hsLt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ^ 2 < tau :=
    hsToZero.eventually (Iio_mem_nhds htau)
  have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      lReducedJacobian S T x Z tau ≤ lReducedJacobian S T x Z (s ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    exact lRedJac_antitoneOn_of_bdd S hS T x hmin hbdd
      ⟨sq_pos_of_pos hs, hsSq.trans hlt⟩ ⟨htau, hlt⟩ hsSq.le
  exact ge_of_tendsto (tendsto_lReducedJacobian_square_at_zero_of_bdd S hS T x Z hmin hbdd) hle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_le_gaussian
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lReducedJacobian S T x Z tau ≤
      ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
  obtain ⟨sigma, hlt, hmin⟩ := hZ
  apply lReducedJacobian_le_gaussian_of_bdd S hS T x hmin htau hlt
  apply lRegularizedCosts_bdd_of_compact S hS T (Real.sqrt_nonneg sigma)
  intro t ht
  exact D.regular_subset (lExpPosDom_regularity S T x Z
    ((mem_lMinDomain S T x Z sigma).mp hmin).1 ht)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem tendsto_lReducedJacobian_left_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : TangentSpace I x} {tau : ℝ} (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau)
    (hbdd : BddBelow {a : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt tau) = lExp S T x Z tau ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = a}) :
    Tendsto (lReducedJacobian S T x Z) (𝓝[<] tau) (𝓝 (lReducedJacobian S T x Z tau)) := by
  have hdom := ((mem_lMinDomain S T x Z tau).mp hmin).1
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  let F : ℝ → ℝ := fun s => Real.exp (Real.log (lExpJacobian S T x Z s) -
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt s) / (2 * Real.sqrt s) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  have hact := (continuousAt_lRegularizedAction_lRegularizedCurve S hS T x (Real.sqrt_pos.mpr htau)
    ((mem_lExpPosDom S T x Z tau).mp hdom).2.2).comp (f := fun s : ℝ => ((Z : E), Real.sqrt s))
      (continuousAt_const.prodMk Real.continuous_sqrt.continuousAt)
  have hlog := (lExpJac_log_hasDeriv_of_nonconj S hS T x Z tau hdom hnconj).continuousAt
  have hF : ContinuousAt F tau := Real.continuous_exp.continuousAt.comp <|
    ((hlog.sub (hact.div (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
      (by positivity : 2 * Real.sqrt tau ≠ 0))).sub
      (continuousAt_const.mul (Real.continuousAt_log htau.ne'))).sub continuousAt_const
  have heq (s : ℝ) (hs : 0 < s) (hst : s ≤ tau) : F s = lReducedJacobian S T x Z s := by
    have hms := lMinDomain_down_of_bdd S hS T x Z hmin hs hst
      (lRegularizedCosts_prefix_bdd_of_min S hS T x Z hmin hs hst hbdd) hbdd
    have hc := ((mem_lMinDomain S T x Z s).mp hms).2
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 s = _ at hc
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ s hs.le] at hc
    simp only [F, lReducedJacobian, lRedLog, redLength, hc]
  have hlim : Tendsto F (𝓝[<] tau) (𝓝 (F tau)) := hF.tendsto.mono_left nhdsWithin_le_nhds
  have hevent : F =ᶠ[𝓝[<] tau] lReducedJacobian S T x Z := by
    filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds htau).filter_mono nhdsWithin_le_nhds] with s hs hsp
    exact heq s hsp hs.le
  rw [heq tau htau le_rfl] at hlim
  exact hlim.congr' hevent

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_le_of_le_minimizing_time_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : TangentSpace I x} {σ τ : ℝ} (hmin : (Z, σ) ∈ lMinDomain S T x)
    (hnconj : ¬ IsLConjugate S T x Z σ) (hτ : 0 < τ) (hτσ : τ ≤ σ)
    (hbdd : BddBelow {a : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt σ) = lExp S T x Z σ ∧ lRegularizedAction S T γ 0 (Real.sqrt σ) = a}) :
    lReducedJacobian S T x Z σ ≤ lReducedJacobian S T x Z τ := by
  rcases hτσ.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hlim := tendsto_lReducedJacobian_left_of_bdd S hS T x hmin hnconj hbdd
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with s hs hts
  exact lRedJac_antitoneOn_of_bdd S hS T x hmin hbdd ⟨hτ, hlt⟩ ⟨hτ.trans hts, hs⟩ hts.le


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lReducedJacobian_le_gaussian_at_minimizing_time_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : TangentSpace I x} {tau : ℝ} (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau)
    (hbdd : BddBelow {a : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt tau) = lExp S T x Z tau ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = a}) :
    lReducedJacobian S T x Z tau ≤ ((Real.pi : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
      Real.exp (-(S.base.metric T).inner x Z Z) := by
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  apply le_of_tendsto (tendsto_lReducedJacobian_left_of_bdd S hS T x hmin hnconj hbdd)
  filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds htau).filter_mono nhdsWithin_le_nhds] with s hs hsp
  exact lReducedJacobian_le_gaussian_of_bdd S hS T x hmin hsp hs hbdd

end DifferentialGeometry.PDE.RicciFlow.Perelman
end
