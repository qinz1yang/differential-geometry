import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
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
theorem tendsto_lRegularizedAction_div_at_zero
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    Tendsto
      (fun s : Real ↦
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s / (2 * s))
      (𝓝[>] (0 : Real))
      (𝓝 ((S.base.metric T).inner x Z Z)) := by
  let lag : Real → Real := fun s ↦
    lRegularizedLagrangian S T (lRegularizedCurve S T x Z) s
  have hzero : (Z, (0 : Real)) ∈ lRegularizedJointDom S T x := by
    exact zero_mem_lRegularizedDomain S hS T x Z hT
  have hopen : IsOpen (lRegularizedJointDom S T x) :=
    lRegularizedJointDom_open S hS T x
  let z : E := Z
  let K : Set Real :=
    (fun s : Real ↦ (z, s)) ⁻¹' lRegularizedJointDom S T x
  have hKopen : IsOpen K := by
    exact hopen.preimage (continuous_const.prodMk continuous_id)
  have hzeroK : (0 : Real) ∈ K := by
    change (Z, (0 : Real)) ∈ lRegularizedJointDom S T x
    exact hzero
  have hcontOn : ContinuousOn lag K := by
    have hpairOn : ContinuousOn (fun s : Real ↦ (z, s)) K :=
      continuous_const.continuousOn.prodMk continuous_id.continuousOn
    have hcomp : ContinuousOn
        ((fun q : E × Real ↦
          lRegularizedLagrangian S T (fun s ↦ lRegularizedCurve S T x q.1 s) q.2) ∘
            fun s : Real ↦ (z, s)) K :=
      (contDiffOn_lRegularizedLagrangian_lRegularizedCurve S hS T x).continuousOn.comp hpairOn
        (fun s hs ↦ hs)
    have heq : ((fun q : E × Real ↦
        lRegularizedLagrangian S T (fun s ↦ lRegularizedCurve S T x q.1 s) q.2) ∘
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
    simp only [lag, lRegularizedLagrangian]
    rw [lRegularizedCurve_zero, lRegularizedCurve_velocity_zero S hS T x Z hT]
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
    change (1 / 2 : Real) * (s⁻¹ * lRegularizedAction S T
      (lRegularizedCurve S T x Z) 0 s) =
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s / (2 * s)
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace N] [NeZero (Module.finrank ℝ F)] in
theorem tendsto_redLength_lExp_square_at_zero_of_bdd
    (S : SolutionOn (I := J) (M := N) D) (hS : IsSolutionOn (I := J) S)
    (T : Real) (x : N) (Z : TangentSpace J x) {sigma : Real}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → N,
      ContMDiff 𝓘(ℝ, ℝ) J 1 alpha ∧ alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    Tendsto
      (fun s : Real ↦
        redLength (I := J) S T x (lExp (I := J) S T x Z (s ^ 2))
          (s ^ 2))
      (𝓝[>] (0 : Real))
      (𝓝 ((S.base.metric T).inner x Z Z)) := by
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hposDom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hsqrtDom : Real.sqrt sigma ∈ lRegularizedDomain S T x Z :=
    ((mem_lExpPosDom S T x Z sigma).1 hposDom).2.2
  have hzeroDom : (0 : Real) ∈ lRegularizedDomain S T x Z :=
    lRegularizedDomain_segment S T x Z hsqrtDom (by norm_num) (Real.sqrt_nonneg sigma)
  have hT : T ∈ D.regular :=
    by
      simpa only [zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero] using
        lRegularizedDomain_regularity S T x Z hzeroDom
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
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s / (2 * s)) =ᶠ[𝓝[>] (0 : Real)]
      fun s : Real ↦
        redLength (I := J) S T x (lExp (I := J) S T x Z (s ^ 2))
          (s ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hsLt] with s hs hsSq
    have hs0 : 0 < s ^ 2 := sq_pos_of_pos hs
    have hminSq : (Z, s ^ 2) ∈ lMinDomain S T x :=
      lMinDomain_down_of_bdd S hS T x Z hmin hs0 hsSq.le
        (lRegularizedCosts_prefix_bdd_of_min S hS T x Z hmin hs0 hsSq.le hbdd) hbdd
    have hcost := ((mem_lMinDomain S T x Z (s ^ 2)).1 hminSq).2
    have hlen :
        lLength S T (fun r : Real ↦ lExp S T x Z r) 0 (s ^ 2) =
          lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s := by
      change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 (s ^ 2) = _
      have hlenSq := lLength_squareRootReparametrization_eq_lRegularizedAction (I := J) S T
        (lRegularizedCurve S T x Z) (s ^ 2) hs0.le
      rw [Real.sqrt_sq hs.le] at hlenSq
      exact hlenSq
    change lRegularizedAction S T (lRegularizedCurve S T x Z) 0 s / (2 * s) =
      lCost S T x (lExp S T x Z (s ^ 2)) (s ^ 2) /
        (2 * Real.sqrt (s ^ 2))
    rw [Real.sqrt_sq hs.le]
    exact congrArg (fun q : Real ↦ q / (2 * s)) (hlen.symm.trans hcost)
  exact (tendsto_lRegularizedAction_div_at_zero S hS T x Z hT).congr' hEq

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
  obtain ⟨sigma, _, hmin⟩ := hZ
  apply tendsto_redLength_lExp_square_at_zero_of_bdd S hS T x Z hmin
  apply lRegularizedCosts_bdd_of_compact S hS T (Real.sqrt_nonneg sigma)
  intro t ht
  exact D.regular_subset (lExpPosDom_regularity S T x Z
    ((mem_lMinDomain S T x Z sigma).mp hmin).1 ht)

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman
