import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SmallJacobian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SmallTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

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
omit [NeZero (Module.finrank ℝ E)] in
theorem lRedJac_zero_lim
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {tau : Real}
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    Tendsto
      (fun s : Real ↦ lRedJac S T x Z (s ^ 2))
      (𝓝[>] (0 : Real))
      (𝓝 (((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) := by
  have hZlater := hZ
  obtain ⟨sigma, _htauSigma, hmin⟩ := hZ
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hposDom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hsqrtDom : Real.sqrt sigma ∈ lRegDomain S T x Z :=
    ((mem_lExpPosDom S T x Z sigma).1 hposDom).2.2
  have hzeroDom : (0 : Real) ∈ lRegDomain S T x Z :=
    lRegDomain_seg S T x Z hsqrtDom (by norm_num) (Real.sqrt_nonneg sigma)
  have hT : T ∈ D.regular := by
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero] using
      lRegDomain_reg S T x Z hzeroDom
  have hden := lExpDen_zero_lim S hS T x Z hT
  have hlen := lRedLen_sq_lim S hS T x Z hZlater
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
      (𝓝 (lSrcDensity S T x *
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
      (fun s : Real ↦ lRedJac S T x Z (s ^ 2) * lSrcDensity S T x) =ᶠ[𝓝[>] (0 : Real)]
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
    have hZs : Z ∈ lInjDomain (E := E) (I := I) S T x (s ^ 2) :=
      ⟨sigma, hsSq, hmin⟩
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
    rw [lRedJac_mul_src S hS T x hsSq0 hZs]
    unfold redDensity
    rw [Real.exp_sub, Real.exp_sub, hsPow, hfourPow]
    field_simp [hs0, hpi0]
    ; ring
  have hprod : Tendsto
      (fun s : Real ↦ lRedJac S T x Z (s ^ 2) * lSrcDensity S T x)
      (𝓝[>] (0 : Real))
      (𝓝 (lSrcDensity S T x *
        ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z))) :=
    hcore.congr' heq.symm
  have hsrc0 : lSrcDensity S T x ≠ 0 :=
    ne_of_gt (lSrcDensity_pos S T x)
  have hdiv := hprod.div_const (lSrcDensity S T x)
  have hfun :
      (fun s : Real ↦
        (lRedJac S T x Z (s ^ 2) * lSrcDensity S T x) /
          lSrcDensity S T x) =
      (fun s : Real ↦ lRedJac S T x Z (s ^ 2)) := by
    funext s
    exact mul_div_cancel_right₀ _ hsrc0
  have htarget :
      (lSrcDensity S T x *
          ((Real.pi : Real) ^
            ((Module.finrank Real E : Real) / 2))⁻¹ *
          Real.exp (-(S.base.metric T).inner x Z Z)) /
        lSrcDensity S T x =
      ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
    field_simp [hsrc0]
  rw [hfun, htarget] at hdiv
  exact hdiv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRedJac_tau_lim
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {rho : Real}
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x rho) :
    Tendsto
      (fun tau : Real ↦ lRedJac S T x Z tau)
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
  have hlim := (lRedJac_zero_lim S hS T x Z hZ).comp hsqrt
  have heq :
      (fun tau : Real ↦ lRedJac S T x Z tau) =ᶠ[𝓝[>] (0 : Real)]
        (fun tau : Real ↦ lRedJac S T x Z (Real.sqrt tau ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    rw [Real.sq_sqrt htau.le]
  exact hlim.congr' heq.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_le_gauss
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lRedJac S T x Z tau ≤
      ((Real.pi : Real) ^
          ((Module.finrank Real E : Real) / 2))⁻¹ *
        Real.exp (-(S.base.metric T).inner x Z Z) := by
  have hsToZero : Tendsto (fun s : Real ↦ s ^ 2)
      (𝓝[>] (0 : Real)) (𝓝 (0 : Real)) := by
    have hid : Tendsto (fun s : Real ↦ s) (𝓝[>] (0 : Real))
        (𝓝 (0 : Real)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0)] using hid.pow 2
  have hsLt : ∀ᶠ s in 𝓝[>] (0 : Real), s ^ 2 < tau :=
    hsToZero.eventually (Iio_mem_nhds htau)
  have hle : ∀ᶠ s in 𝓝[>] (0 : Real),
      lRedJac S T x Z tau ≤ lRedJac S T x Z (s ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    exact lRedJac_anti S hS T x (sq_pos_of_pos hs) hsSq.le hZ
  exact ge_of_tendsto (lRedJac_zero_lim S hS T x Z hZ) hle

end DifferentialGeometry.PDE.RicciFlow.Perelman
