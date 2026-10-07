/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Ergodic.HomogeneousSpace
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.MovingFrameTensor
import DifferentialGeometry.Analysis.Ergodic.InvariantFields

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.FrameTensorDynamics

open DifferentialGeometry.HomogeneousSpaceMeasure DifferentialGeometry.HomogeneousSpaceDynamics
open GeodesicFlow LorentzGenerators MovingFrameTensor

section Contraction

variable {n : ℕ} {Y : Type*} [MeasurableSpace Y]
variable [MeasurableSpace.CountablySeparated Y]

theorem ae_field_right_of_tendsto_conjugate (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (disc : IsDiscrete (SetLike.coe Γ))
    (ν : Measure (FrameQuotient Γ)) [IsFiniteMeasure ν]
    (hr : ∀ g : PO n 1, MeasurePreserving (right Γ g) ν ν)
    (F : FrameQuotient Γ → Y) (hF : Measurable F)
    {ι : Type*} {l : Filter ι} [l.NeBot] {a : ι → PO n 1} {g : PO n 1}
    (ha : ∀ᶠ i in l, (fun q => F (right Γ (a i) q)) =ᵐ[ν] F)
    (hc : Tendsto (fun i => a i * g * (a i)⁻¹) l (𝓝 1)) :
    (fun q => F (right Γ g q)) =ᵐ[ν] F := by
  apply EventuallyEq.of_forall_separating_preimage MeasurableSet
  intro U hU
  apply ae_right_of_tendsto_conjugate hn Γ disc ν hr (hF hU) _ hc
  exact ha.mono (fun i hi => hi.mono (fun q hq => congrArg (fun y => y ∈ U) hq))

variable {m : ℕ}

theorem translation_mem_rightFieldStabilizer (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    (ν : Measure (FrameQuotient Γ)) [IsFiniteMeasure ν]
    (hr : ∀ g : IsometryGroup m, MeasurePreserving (right Γ g) ν ν)
    (F : FrameQuotient Γ → Y) (hF : Measurable F)
    (hD : ∀ t : ℝ, (fun q => F (right Γ (GeodesicFlow.diagonal t) q)) =ᵐ[ν] F)
    (b : Fin m → ℝ) :
    translation b ∈ rightFieldStabilizer Γ ν hr F :=
  ae_field_right_of_tendsto_conjugate (by omega) Γ disc ν hr F hF
    (Eventually.of_forall (fun k : ℕ => hD (-(k : ℝ))))
    (tendsto_conjugate_translation hm b)

theorem oppositeTranslation_mem_rightFieldStabilizer (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    (ν : Measure (FrameQuotient Γ)) [IsFiniteMeasure ν]
    (hr : ∀ g : IsometryGroup m, MeasurePreserving (right Γ g) ν ν)
    (F : FrameQuotient Γ → Y) (hF : Measurable F)
    (hD : ∀ t : ℝ, (fun q => F (right Γ (GeodesicFlow.diagonal t) q)) =ᵐ[ν] F)
    (b : Fin m → ℝ) :
    oppositeTranslation b ∈ rightFieldStabilizer Γ ν hr F :=
  ae_field_right_of_tendsto_conjugate (by omega) Γ disc ν hr F hF
    (Eventually.of_forall (fun k : ℕ => hD (k : ℝ)))
    (tendsto_conjugate_oppositeTranslation hm b)

end Contraction

end DifferentialGeometry.FrameTensorDynamics
