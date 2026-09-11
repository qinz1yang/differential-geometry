import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature Set
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D} {time : D.FlowTime}

def IsParabolicallyRmControlled (B : FlowMetricBall S time) : Prop :=
  Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.carrier ∧
    ∀ s ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real),
      ∀ x ∈ B.set, B.radius ^ 4 * rmNormSq S s x ≤ 1

omit [SigmaCompactSpace M] in
theorem isSpatiallyRmControlled_of_isParabolicallyRmControlled
    {B : FlowMetricBall S time} (hB : B.IsParabolicallyRmControlled) :
    B.IsSpatiallyRmControlled :=
  hB.2 time ⟨sub_le_self _ (sq_nonneg _), le_rfl⟩

end FlowMetricBall

def ParabolicallyKappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : D.FlowTime) (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa

def ParabolicNoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ ParabolicallyKappaNoncollapsedBelowScale S kappa rho

theorem parabolicallyKappaNoncollapsedBelowScale_of_spatially
    {S : SolutionOn (I := I) (M := M) D} {kappa rho : Real}
    (h : SpatiallyKappaNoncollapsedBelowScale S kappa rho) :
    ParabolicallyKappaNoncollapsedBelowScale S kappa rho :=
  ⟨h.1, fun t B hr hB =>
    h.2 t B hr (FlowMetricBall.isSpatiallyRmControlled_of_isParabolicallyRmControlled hB)⟩

theorem parabolicNoLocalCollapsing_of_spatial
    {S : SolutionOn (I := I) (M := M) D} {rho : Real}
    (h : SpatialNoLocalCollapsing S rho) : ParabolicNoLocalCollapsing S rho := by
  obtain ⟨kappa, hkappa, hbelow⟩ := h
  exact ⟨kappa, hkappa, parabolicallyKappaNoncollapsedBelowScale_of_spatially hbelow⟩

private theorem parabolicControlWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc (s - (Real.sqrt R * r) ^ 2) s) :
    parabolicTime tau R q ∈
      Set.Icc (parabolicTime tau R s - r ^ 2) (parabolicTime tau R s) := by
  have hrad : (Real.sqrt R * r) ^ 2 = R * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
  have hlo : s - R * r ^ 2 ≤ q := by simpa only [hrad] using hq.1
  have hlo_div : (s - R * r ^ 2) / R ≤ q / R :=
    (div_le_div_iff_of_pos_right hR).2 hlo
  have hsplit : (s - R * r ^ 2) / R = s / R - r ^ 2 := by
    field_simp [ne_of_gt hR]
  rw [hsplit] at hlo_div
  have hhi_div : q / R ≤ s / R := (div_le_div_iff_of_pos_right hR).2 hq.2
  unfold parabolicTime
  constructor <;> linarith

private theorem backwardControlWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc
      (parabolicTime tau R s - (r / Real.sqrt R) ^ 2) (parabolicTime tau R s)) :
    parabolicBackward tau R q ∈ Set.Icc (s - r ^ 2) s := by
  have hrad : (r / Real.sqrt R) ^ 2 = r ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hR.le]
  have hlo0 := hq.1
  rw [hrad] at hlo0
  unfold parabolicTime at hlo0
  have hlo_div : (s - r ^ 2) / R ≤ q - tau := by
    rw [sub_div]
    linarith
  have hlo := (div_le_iff₀ hR).1 hlo_div
  have hhi0 := hq.2
  unfold parabolicTime at hhi0
  have hhi_div : q - tau ≤ s / R := by linarith
  have hhi := (le_div_iff₀ hR).1 hhi_div
  constructor
  · simpa [parabolicBackward, mul_comm] using hlo
  · simpa [parabolicBackward, mul_comm] using hhi

section Scaling

variable [CompleteSpace E]

omit [SigmaCompactSpace M] in
theorem parabolicBall_isParabolicallyRmControlled
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s))
    (hB : B.IsParabolicallyRmControlled) :
    (parabolicBall S tau R hR htau s B).IsParabolicallyRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    exact hwindow (parabolicControlWindow tau R hR (s : Real) q B.radius hq)
  · intro q hq x hx
    have hq_old := parabolicControlWindow tau R hR (s : Real) q B.radius hq
    have hx_old : x ∈ B.set := by
      rwa [parabolicBall_set] at hx
    have hold := hcurv (parabolicTime tau R q) hq_old x hx_old
    unfold FlowMetricBall.rmNormSq
    rw [parabolicRmNormSq]
    have hscale : (Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2 = B.radius ^ 4 := by
      rw [mul_pow]
      calc
        Real.sqrt R ^ 4 * B.radius ^ 4 * R⁻¹ ^ 2 =
            (Real.sqrt R ^ 2) ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by ring
        _ = R ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by rw [Real.sq_sqrt hR.le]
        _ = B.radius ^ 4 := by field_simp [ne_of_gt hR]
    change (Real.sqrt R * B.radius) ^ 4 * (R⁻¹ ^ 2 *
      Tensor0SBundle.normSq0S (I := I) (S.base.metric (parabolicTime tau R q)) x 4
        (S.base.rm04 (parabolicTime tau R q) x)) ≤ 1
    rw [← mul_assoc, hscale]
    exact hold

omit [SigmaCompactSpace M] in
theorem backBall_isParabolicallyRmControlled
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall (parabolicSolution (I := I) S tau R hR htau) s)
    (hB : B.IsParabolicallyRmControlled) :
    (backBall S tau R hR htau s B).IsParabolicallyRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    let q' : Real := parabolicBackward tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backwardControlWindow tau R hR (s : Real) q B.radius hq
    have hmem := hwindow hq_new
    change parabolicTime tau R q' ∈ D.carrier at hmem
    simpa only [q', parabolicTime_back (ne_of_gt hR)] using hmem
  · intro q hq x hx
    let q' : Real := parabolicBackward tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backwardControlWindow tau R hR (s : Real) q B.radius hq
    have hset := parabolicBall_set (I := I) S tau R hR htau s
      (backBall S tau R hR htau s B)
    rw [parabolicBall_back] at hset
    have hx_new : x ∈ B.set := by rwa [hset]
    have hold := hcurv q' hq_new x hx_new
    unfold FlowMetricBall.rmNormSq at hold ⊢
    rw [parabolicRmNormSq, parabolicTime_back (ne_of_gt hR)] at hold
    change (B.radius / Real.sqrt R) ^ 4 *
      Tensor0SBundle.normSq0S (I := I) (S.base.metric q) x 4
        (S.base.rm04 q x) ≤ 1
    have hscale : (B.radius / Real.sqrt R) ^ 4 = B.radius ^ 4 * R⁻¹ ^ 2 := by
      rw [div_pow]
      have hsqrt : Real.sqrt R ^ 4 = R ^ 2 := by
        calc
          Real.sqrt R ^ 4 = (Real.sqrt R ^ 2) ^ 2 := by ring
          _ = R ^ 2 := by rw [Real.sq_sqrt hR.le]
      rw [hsqrt, div_eq_mul_inv, inv_pow]
    rw [hscale]
    simpa only [mul_assoc] using hold

omit [SigmaCompactSpace M] in
theorem parabolicBall_isParabolicallyRmControlled_iff
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (parabolicInterval D tau R htau).FlowTime)
    (B : FlowMetricBall S (parabolicFlowTime tau R htau s)) :
    (parabolicBall S tau R hR htau s B).IsParabolicallyRmControlled ↔
      B.IsParabolicallyRmControlled := by
  constructor
  · intro h
    have hback := backBall_isParabolicallyRmControlled (I := I) S tau R hR htau s
      (parabolicBall S tau R hR htau s B) h
    rwa [backBall_parabolic] at hback
  · exact parabolicBall_isParabolicallyRmControlled (I := I) S tau R hR htau s B

theorem parabolicallyKappaNoncollapsedBelowScale_parabolicSolution
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (kappa rho : Real)
    (hS : ParabolicallyKappaNoncollapsedBelowScale S kappa rho) :
    ParabolicallyKappaNoncollapsedBelowScale
      (parabolicSolution (I := I) S tau R hR htau) kappa (Real.sqrt R * rho) := by
  refine ⟨mul_pos (Real.sqrt_pos.2 hR) hS.1, ?_⟩
  intro s B hscale hRm
  let B₀ := backBall S tau R hR htau s B
  have hradius : B₀.radius ≤ rho := by
    dsimp [B₀, backBall]
    apply (div_le_iff₀ (Real.sqrt_pos.2 hR)).2
    simpa only [mul_comm] using hscale
  have hRm₀ : B₀.IsParabolicallyRmControlled :=
    backBall_isParabolicallyRmControlled (I := I) S tau R hR htau s B hRm
  have hk₀ := hS.2 (parabolicFlowTime tau R htau s) B₀ hradius hRm₀
  have hk := parabolicBall_kappa (I := I) S tau R hR htau s B₀ kappa hk₀
  rwa [parabolicBall_back] at hk

theorem parabolicNoLocalCollapsing_parabolicSolution
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (rho : Real) (hS : ParabolicNoLocalCollapsing S rho) :
    ParabolicNoLocalCollapsing (parabolicSolution (I := I) S tau R hR htau)
      (Real.sqrt R * rho) := by
  rcases hS with ⟨kappa, hkappa, hbelow⟩
  exact ⟨kappa, hkappa,
    parabolicallyKappaNoncollapsedBelowScale_parabolicSolution
      (I := I) S tau R hR htau kappa rho hbelow⟩

end Scaling

end DifferentialGeometry.PDE.RicciFlow.Perelman
