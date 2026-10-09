/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Ergodic.HomogeneousSpace

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.FrameTensorDynamics

open DifferentialGeometry.HomogeneousSpaceMeasure DifferentialGeometry.HomogeneousSpaceDynamics

section Transfer

variable {G Y : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
variable [T2Space Y] [SecondCountableTopology Y]

theorem quotient_ae_eq_iff (Γ : Subgroup G) (μ : Measure G)
    (ν : Measure (FrameQuotient Γ))
    (hn : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ μ (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ ⁻¹' U) = 0))
    {F H : FrameQuotient Γ → Y} (hF : Measurable F) (hH : Measurable H) :
    F =ᵐ[ν] H ↔
      (fun g => F (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g))
        =ᵐ[μ] (fun g => H (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g)) :=
  hn {q | F q ≠ H q} (measurableSet_eq_fun hF hH).compl

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]

theorem quotient_right_invariance_iff (Γ : Subgroup G) (μ : Measure G)
    [Measure.IsMulRightInvariant μ] (ν : Measure (FrameQuotient Γ))
    (hn : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ μ (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ ⁻¹' U) = 0))
    (Fq : FrameQuotient Γ → Y) (hFq : Measurable Fq) (F : G → Y)
    (he : (fun g => Fq (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g)) =ᵐ[μ] F) (a : G) :
    (fun q => Fq (right Γ a q)) =ᵐ[ν] Fq ↔
      (fun g => F (g * a)) =ᵐ[μ] F := by
  have ht := quotient_ae_eq_iff Γ μ ν hn (hFq.comp (measurable_right Γ a)) hFq
  simp only [Function.comp_def] at ht
  rw [ht]
  have hea : (fun g => Fq (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ (g * a)))
      =ᵐ[μ] (fun g => F (g * a)) :=
    (measurePreserving_mul_right μ a).quasiMeasurePreserving.ae he
  change (fun g => Fq (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ (g * a))) =ᵐ[μ]
    (fun g => Fq (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g)) ↔ _
  exact ⟨fun h => hea.symm.trans (h.trans he), fun h => hea.trans (h.trans he.symm)⟩

def rightFieldStabilizer (Γ : Subgroup G) (ν : Measure (FrameQuotient Γ))
    (hr : ∀ g : G, MeasurePreserving (right Γ g) ν ν)
    (F : FrameQuotient Γ → Y) : Subgroup G where
  carrier := {g | (fun q => F (right Γ g q)) =ᵐ[ν] F}
  one_mem' := by
    change ∀ᵐ q ∂ν, F (right Γ 1 q) = F q
    exact Eventually.of_forall (fun q => by rw [right_one])
  mul_mem' {a b} ha hb := by
    change (fun q => F (right Γ a q)) =ᵐ[ν] F at ha
    change (fun q => F (right Γ b q)) =ᵐ[ν] F at hb
    change ∀ᵐ q ∂ν, F (right Γ (a * b) q) = F q
    filter_upwards [(hr a).quasiMeasurePreserving.ae hb, ha] with q hbq haq
    rw [right_mul]
    exact hbq.trans haq
  inv_mem' {a} ha := by
    change (fun q => F (right Γ a q)) =ᵐ[ν] F at ha
    change ∀ᵐ q ∂ν, F (right Γ a⁻¹ q) = F q
    filter_upwards [(hr a⁻¹).quasiMeasurePreserving.ae ha] with q hq
    have h := hq.symm
    rwa [← right_mul, inv_mul_cancel, right_one] at h

end Transfer

end DifferentialGeometry.FrameTensorDynamics
