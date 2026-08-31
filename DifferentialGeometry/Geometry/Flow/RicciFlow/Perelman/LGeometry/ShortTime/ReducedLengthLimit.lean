import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.EndpointVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tendsto_lRegAction_div_at_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    Tendsto
      (fun s : Real ↦
        lRegAction S T (lRegCurve S T x Z) 0 s / (2 * s))
      (𝓝[>] (0 : Real))
      (𝓝 ((S.base.metric T).inner x Z Z)) := by
  let lag : Real → Real := fun s ↦
    lRegLagrangian S T (lRegCurve S T x Z) s
  have hzero : (Z, (0 : Real)) ∈ lRegJointDom S T x := by
    exact zero_mem_lRegDomain S hS T x Z hT
  have hopen : IsOpen (lRegJointDom S T x) :=
    lRegJointDom_open S hS T x
  let z : E := Z
  let K : Set Real :=
    (fun s : Real ↦ (z, s)) ⁻¹' lRegJointDom S T x
  have hKopen : IsOpen K := by
    exact hopen.preimage (continuous_const.prodMk continuous_id)
  have hzeroK : (0 : Real) ∈ K := by
    change (Z, (0 : Real)) ∈ lRegJointDom S T x
    exact hzero
  have hcontOn : ContinuousOn lag K := by
    have hpairOn : ContinuousOn (fun s : Real ↦ (z, s)) K :=
      continuous_const.continuousOn.prodMk continuous_id.continuousOn
    have hcomp : ContinuousOn
        ((fun q : E × Real ↦
          lRegLagrangian S T (fun s ↦ lRegCurve S T x q.1 s) q.2) ∘
            fun s : Real ↦ (z, s)) K :=
      (lRayLag_smooth S hS T x).continuousOn.comp hpairOn
        (fun s hs ↦ hs)
    have heq : ((fun q : E × Real ↦
        lRegLagrangian S T (fun s ↦ lRegCurve S T x q.1 s) q.2) ∘
          fun s : Real ↦ (z, s)) = lag := by
      funext s
      rfl
    rw [heq] at hcomp
    exact hcomp
  have hcont : ContinuousAt lag 0 := by
    exact (hcontOn 0 hzeroK).continuousAt (hKopen.mem_nhds hzeroK)
  have hderiv : HasDerivAt
      (fun s : Real ↦ ∫ r in (0 : Real)..s, lag r) (lag 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hcontOn.stronglyMeasurableAtFilter hKopen 0 hzeroK) hcont
  have hlim := hderiv.tendsto_slope_zero_right
  have hhalf : Tendsto
      (fun s : Real ↦
        (1 / 2 : Real) *
          (s⁻¹ * ((∫ r in (0 : Real)..(0 + s), lag r) -
            ∫ r in (0 : Real)..(0 : Real), lag r)))
      (𝓝[>] (0 : Real)) (𝓝 ((1 / 2 : Real) * lag 0)) := by
    simpa only [smul_eq_mul] using tendsto_const_nhds.mul hlim
  have hlag0 : lag 0 = 2 * (S.base.metric T).inner x Z Z := by
    simp only [lag, lRegLagrangian]
    rw [lRegCurve_zero, lRegCurve_vel_zero S hS T x Z hT]
    norm_num only [zero_pow, sub_zero, mul_zero, add_zero]
    rw [((S.base.metric T).inner x).map_smul,
      smul_apply,
      ((S.base.metric T).inner x Z).map_smul]
    simp only [smul_eq_mul]
    ring_nf
  refine (hhalf.congr' ?_).trans_eq ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    simp only [zero_add, intervalIntegral.integral_same, sub_zero]
    change (1 / 2 : Real) * (s⁻¹ * lRegAction S T
      (lRegCurve S T x Z) 0 s) =
        lRegAction S T (lRegCurve S T x Z) 0 s / (2 * s)
    field_simp [hs0]
  · rw [hlag0]
    ring_nf

section Compact

variable {F : Type uE} [NormedAddCommGroup F] [InnerProductSpace Real F]
  [FiniteDimensional Real F] [NeZero (Module.finrank Real F)]
variable {K : Type uH} [TopologicalSpace K]
variable {J : ModelWithCorners Real F K} [J.Boundaryless]
variable {N : Type u} [PseudoMetricSpace N] [ChartedSpace K N]
  [IsManifold J ∞ N] [T2Space N] [CompactSpace N]

omit [NeZero (Module.finrank ℝ F)] in
theorem tendsto_redLength_lExp_square_at_zero
    (S : SolutionOn (I := J) (M := N) D) (hS : IsSolutionOn (I := J) S)
    (T : Real) (x : N) (Z : TangentSpace J x) {tau : Real}
    (hZ : Z ∈ lInjDomain (E := F) (I := J) S T x tau) :
    Tendsto
      (fun s : Real ↦
        redLength (I := J) S T x (lExp (I := J) S T x Z (s ^ 2))
          (s ^ 2))
      (𝓝[>] (0 : Real))
      (𝓝 ((S.base.metric T).inner x Z Z)) := by
  obtain ⟨sigma, _htauSigma, hmin⟩ := hZ
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hposDom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hsqrtDom : Real.sqrt sigma ∈ lRegDomain S T x Z :=
    ((mem_lExpPosDom S T x Z sigma).1 hposDom).2.2
  have hzeroDom : (0 : Real) ∈ lRegDomain S T x Z :=
    lRegDomain_seg S T x Z hsqrtDom (by norm_num) (Real.sqrt_nonneg sigma)
  have hT : T ∈ D.regular :=
    by
      simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero] using
        lRegDomain_reg S T x Z hzeroDom
  have hsToZero : Tendsto (fun s : Real ↦ s ^ 2)
      (𝓝[>] (0 : Real)) (𝓝 (0 : Real)) := by
    have hid : Tendsto (fun s : Real ↦ s) (𝓝[>] (0 : Real))
        (𝓝 (0 : Real)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0)] using hid.pow 2
  have hsLt : ∀ᶠ s in 𝓝[>] (0 : Real), s ^ 2 < sigma :=
    hsToZero.eventually (Iio_mem_nhds hsigma)
  have hEq :
      (fun s : Real ↦
        lRegAction S T (lRegCurve S T x Z) 0 s / (2 * s)) =ᶠ[𝓝[>] (0 : Real)]
      fun s : Real ↦
        redLength (I := J) S T x (lExp (I := J) S T x Z (s ^ 2))
          (s ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    have hs0 : 0 < s ^ 2 := sq_pos_of_pos hs
    have hminSq : (Z, s ^ 2) ∈ lMinDomain S T x :=
      lMinDomain_down S hS T x Z hmin hs0 hsSq.le
    have hcost := ((mem_lMinDomain S T x Z (s ^ 2)).1 hminSq).2
    have hlen :
        lLength S T (fun r : Real ↦ lExp S T x Z r) 0 (s ^ 2) =
          lRegAction S T (lRegCurve S T x Z) 0 s := by
      change lLength S T (squareRootReparametrization (lRegCurve S T x Z)) 0 (s ^ 2) = _
      have hlenSq := lLength_squareRootReparametrization_eq_lRegAction (I := J) S T
        (lRegCurve S T x Z) (s ^ 2) hs0.le
      rw [Real.sqrt_sq hs.le] at hlenSq
      exact hlenSq
    change lRegAction S T (lRegCurve S T x Z) 0 s / (2 * s) =
      lCost S T x (lExp S T x Z (s ^ 2)) (s ^ 2) /
        (2 * Real.sqrt (s ^ 2))
    rw [Real.sqrt_sq hs.le]
    exact congrArg (fun q : Real ↦ q / (2 * s)) (hlen.symm.trans hcost)
  exact (tendsto_lRegAction_div_at_zero S hS T x Z hT).congr' hEq

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman
