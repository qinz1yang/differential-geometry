import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ScaleTransfer

open DifferentialGeometry.PDE.RicciFlow

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def KappaNoncollapsedOnAllScales
    (S : SolutionOn (I := I) (M := M) D) (kappa : Real) : Prop :=
  0 < kappa ∧
    ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
      (B : FlowMetricBall S t), B.IsRmControlled → B.IsKappaNoncollapsed kappa

theorem kappa_noncollapsed_on_all_scales_iff
    {S : SolutionOn (I := I) (M := M) D} {kappa : Real} :
  KappaNoncollapsedOnAllScales S kappa ↔
      0 < kappa ∧
        ∀ rho : Real, 0 < rho → KappaNoncollapsedBelowScale S kappa rho := by
  constructor
  · rintro ⟨hkappa, hS⟩
    refine ⟨hkappa, ?_⟩
    intro rho hrho
    exact ⟨hrho, by
      intro t B _hBrho hB
      exact hS t B hB⟩
  · rintro ⟨hkappa, hS⟩
    refine ⟨hkappa, ?_⟩
    intro t B hB
    let rho : Real := B.radius + 1
    have hrho : 0 < rho := by
      dsimp only [rho]
      linarith [B.radius_pos]
    have hbelow := hS rho hrho
    exact hbelow.2 t B (by
      dsimp only [rho]
      linarith) hB

theorem kappa_noncollapsed_on_all_scales_of_kappa_le
    {S : SolutionOn (I := I) (M := M) D}
    {kappa kappa' : Real}
    (hS : KappaNoncollapsedOnAllScales S kappa')
    (hkappa : 0 < kappa) (hkappa_le : kappa ≤ kappa') :
    KappaNoncollapsedOnAllScales S kappa := by
  refine ⟨hkappa, ?_⟩
  intro t B hB
  rcases hS.2 t B hB with ⟨_, hvol⟩
  refine ⟨hkappa, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hkappa_le) le_rfl).trans hvol

theorem para_noncollapse_all_scales
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    {kappa : Real} (hS : KappaNoncollapsedOnAllScales S kappa) :
    KappaNoncollapsedOnAllScales
      (paraSolution (I := I) S tau R hR htau) kappa := by
  apply (kappa_noncollapsed_on_all_scales_iff).2
  refine ⟨hS.1, ?_⟩
  intro rho hrho
  have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  let rho₀ : Real := rho / Real.sqrt R
  have hrho₀ : 0 < rho₀ := by
    dsimp only [rho₀]
    exact div_pos hrho hsqrt
  have hbelow := ((kappa_noncollapsed_on_all_scales_iff).1 hS).2 rho₀ hrho₀
  have hpara := para_noncollapse (I := I) S tau R hR htau kappa rho₀ hbelow
  have hscale : Real.sqrt R * rho₀ = rho := by
    dsimp only [rho₀]
    field_simp [ne_of_gt hsqrt]
  simpa only [hscale] using hpara

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
