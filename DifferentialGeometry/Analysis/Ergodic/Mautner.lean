/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

open Set Filter MeasureTheory
open scoped Pointwise symmDiff Topology

namespace DifferentialGeometry.Mautner

variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] (μ : Measure X) [SMulInvariantMeasure G X μ]

theorem measure_symmDiff_conjugate (s : Set X) (a g : G)
    (ha : a ∈ MulAction.aestabilizer G μ s) :
    μ (((a * g * a⁻¹) • s) ∆ s) = μ ((g • s) ∆ s) := by
  have hai : a⁻¹ • s =ᵐ[μ] s := (MulAction.aestabilizer G μ s).inv_mem ha
  have he : (a * g * a⁻¹) • s =ᵐ[μ] a • (g • s) := by
    simpa only [mul_smul] using (smul_set_ae_eq (a * g)).mpr hai
  have ha' : s =ᵐ[μ] a • s := (MulAction.mem_aestabilizer.mp ha).symm
  rw [measure_congr (he.symmDiff ha'), ← smul_set_symmDiff, measure_smul]

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace X] [BorelSpace X] [R1Space X] [ContinuousSMul G X]
variable [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

theorem mem_aestabilizer_of_tendsto_conjugate
    {ι : Type*} {l : Filter ι} [l.NeBot] {a : ι → G} {g : G} {s : Set X}
    (hs : NullMeasurableSet s μ)
    (ha : ∀ᶠ i in l, a i ∈ MulAction.aestabilizer G μ s)
    (hc : Tendsto (fun i => a i * g * (a i)⁻¹) l (𝓝 1)) :
    g ∈ MulAction.aestabilizer G μ s := by
  let F : C(G × X, X) := ⟨fun p => p.1⁻¹ • p.2, continuous_fst.inv.smul continuous_snd⟩
  have hF : Tendsto (fun i => F.curry (a i * g * (a i)⁻¹)) l (𝓝 (F.curry 1)) :=
    (F.curry.continuous.tendsto 1).comp hc
  have hz := tendsto_measure_symmDiff_preimage_nhds_zero hF
    (Eventually.of_forall (fun i => measurePreserving_smul (a i * g * (a i)⁻¹)⁻¹ μ))
    (measurePreserving_smul (1 : G)⁻¹ μ) hs (measure_ne_top μ s)
  have hz' : Tendsto (fun i => μ (((a i * g * (a i)⁻¹) • s) ∆ s)) l (𝓝 0) := by
    change Tendsto (fun i => μ (((fun x : X => (a i * g * (a i)⁻¹)⁻¹ • x) ⁻¹' s) ∆
      ((fun x : X => (1 : G)⁻¹ • x) ⁻¹' s))) l (𝓝 0) at hz
    simpa only [preimage_smul_inv, inv_one, one_smul, preimage_id'] using hz
  have he : (fun i => μ (((a i * g * (a i)⁻¹) • s) ∆ s)) =ᶠ[l]
      (fun _ => μ ((g • s) ∆ s)) :=
    ha.mono (fun i hi => measure_symmDiff_conjugate μ s (a i) g hi)
  have hm : μ ((g • s) ∆ s) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hz'.congr' he)
  exact measure_symmDiff_eq_zero_iff.mp hm

end DifferentialGeometry.Mautner
