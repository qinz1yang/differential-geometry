import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs

open DifferentialGeometry.PDE.RicciFlow

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open scoped Manifold ContDiff ENNReal

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

theorem kappa_noncollapsed_below_scale_mono
    {S : SolutionOn (I := I) (M := M) D}
    {kappa rho rho' : Real}
    (hS : KappaNoncollapsedBelowScale S kappa rho)
    (hrho' : 0 < rho') (hscale : rho' ≤ rho) :
    KappaNoncollapsedBelowScale S kappa rho' := by
  refine ⟨hrho', ?_⟩
  intro t B hBrho' hB
  exact hS.2 t B (hBrho'.trans hscale) hB

theorem kappa_noncollapsed_below_scale_of_kappa_le
    {S : SolutionOn (I := I) (M := M) D}
    {kappa kappa' rho : Real}
    (hS : KappaNoncollapsedBelowScale S kappa' rho)
    (hkappa : 0 < kappa) (hkappa_le : kappa ≤ kappa') :
    KappaNoncollapsedBelowScale S kappa rho := by
  refine ⟨hS.1, ?_⟩
  intro t B hBrho hB
  rcases hS.2 t B hBrho hB with ⟨_, hvol⟩
  refine ⟨hkappa, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hkappa_le) le_rfl).trans hvol

theorem no_local_collapsing_mono
    {S : SolutionOn (I := I) (M := M) D}
    {rho rho' : Real}
    (hS : NoLocalCollapsing S rho)
    (hrho' : 0 < rho') (hscale : rho' ≤ rho) :
    NoLocalCollapsing S rho' := by
  rcases hS with ⟨kappa, hkappa, hbelow⟩
  exact ⟨kappa, hkappa,
    kappa_noncollapsed_below_scale_mono hbelow hrho' hscale⟩

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
