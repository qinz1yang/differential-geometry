import RicciFlower.RicciFlow.Perelman.Noncollapsing

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# MSM135 Chapter 6.5: No finite-time local collapsing

Book-facing wrappers for labels `lbl646`-`lbl676`.
-/

namespace BK
namespace MSM135
namespace Chapter06
namespace Section05

noncomputable section

open RicciFlower.RicciFlow.Perelman

variable {M : Type*}

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl647` and
`notes_and_commentary:lbl652`. -/
theorem lbl647_kappa_noncollapsed_below_scale
    {n : Nat} {kappa rho : Real} {balls : Set (ScaleControlledBall M)}
    (h : RicciFlowKappaNoncollapsedBelowScale n kappa rho balls) :
    RicciFlowKappaNoncollapsedBelowScale n kappa rho balls := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl648`-`lbl649`. -/
theorem lbl648_kappa_noncollapsed_preserved_under_limits
    {sourceLimit targetLimit : Prop}
    (h : KappaNoncollapsedPreservedUnderLimits sourceLimit targetLimit) :
    KappaNoncollapsedPreservedUnderLimits sourceLimit targetLimit := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl650`-`lbl651`. -/
theorem lbl651_injectivity_radius_lower_bound
    {noncollapsed injectivityLowerBound : Prop}
    (h : KappaNoncollapsedImpliesInjectivityRadiusLowerBound
      noncollapsed injectivityLowerBound) :
    KappaNoncollapsedImpliesInjectivityRadiusLowerBound
      noncollapsed injectivityLowerBound := h

/-- MSM135 Chapter 6, label `notes_and_commentary:lbl653`. -/
theorem lbl653_locally_collapsing_solution
    {n : Nat} {time : Real} {collapseWitness : Prop}
    (h : LocallyCollapsingAtTime n time collapseWitness) :
    LocallyCollapsingAtTime n time collapseWitness := h

/-- MSM135 Chapter 6, label `notes_and_commentary:lbl655`. -/
theorem lbl655_no_local_collapsing_a
    {n : Nat} {T rho : Real} {balls : Set (ScaleControlledBall M)}
    (h : NoLocalCollapsingTheoremA n T rho balls) :
    NoLocalCollapsingTheoremA n T rho balls := h

/-- MSM135 Chapter 6, label `notes_and_commentary:lbl656`. -/
theorem lbl656_no_local_collapsing_b
    {n : Nat} {time : Real} {collapseWitness : Prop}
    (h : NoLocalCollapsingTheoremB n time collapseWitness) :
    NoLocalCollapsingTheoremB n time collapseWitness := h

/-- MSM135 Chapter 6, label `notes_and_commentary:lbl657`. -/
theorem lbl657_nlc_and_llc_equivalent {nlc littleLoop : Prop}
    (h : NoLocalCollapsingLittleLoopEquivalent nlc littleLoop) :
    NoLocalCollapsingLittleLoopEquivalent nlc littleLoop := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl661`-`lbl673`. -/
theorem lbl661_mu_controls_volume_ratios
    {muLower volumeRatioLower : Real}
    (h : MuControlsVolumeRatios muLower volumeRatioLower) :
    MuControlsVolumeRatios muLower volumeRatioLower := h

/-- MSM135 Chapter 6, labels `notes_and_commentary:lbl674`-`lbl676`. -/
theorem lbl674_existence_of_singularity_models
    {hypothesis conclusion : Prop}
    (h : FiniteTimeSingularityModelExists hypothesis conclusion) :
    FiniteTimeSingularityModelExists hypothesis conclusion := h

end

end Section05
end Chapter06
end MSM135
end BK
