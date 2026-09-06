import DifferentialGeometry.Analysis.ODE.InvariantSet
import DifferentialGeometry.Analysis.Convex.NormalCone
import DifferentialGeometry.Analysis.ODE.Flow.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Filter
open scoped Topology
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_contDiffAt
    [CompleteSpace E] {f : ℝ → E → E} {C : Set E}
    (hC : IsForwardInvariantForODE f C)
    (hf : ∀ t x, x ∈ C → ContDiffAt ℝ 1 (Function.uncurry f) (t, x)) :
    VectorFieldTangentTo f C := by
  apply hC.vectorFieldTangentTo_of_exists_isIntegralCurveAt
  intro t x hx
  exact Flow.exists_isIntegralCurveAt_of_contDiffAt (hf t x hx)

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_contDiff
    [CompleteSpace E] {f : ℝ → E → E} {C : Set E}
    (hC : IsForwardInvariantForODE f C)
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    VectorFieldTangentTo f C :=
  hC.vectorFieldTangentTo_of_contDiffAt (fun _ _ _ => hf.contDiffAt)

theorem IsForwardInvariantForODEOn.mem_posTangentConeAt_of_contDiffAt
    [CompleteSpace E] {f : ℝ → E → E} {C : Set E} {J : Set ℝ} {t : ℝ} {x : E}
    (hC : IsForwardInvariantForODEOn f C J) (hJ : J ∈ 𝓝 t) (hx : x ∈ C)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (t, x)) :
    f t x ∈ posTangentConeAt C x := by
  obtain ⟨γ, hγ, hγt⟩ := Flow.exists_isIntegralCurveAt_of_contDiffAt hf
  obtain ⟨ε, hε, hγball⟩ := isIntegralCurveAt_iff_exists_pos.mp hγ
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hJ
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hsub : Icc t (t + r) ⊆ Metric.ball t ε ∩ Metric.ball t δ := by
    intro s hs
    have hs' : dist s t ≤ r := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith [hs.2]
    constructor <;> apply hs'.trans_lt
    · exact (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
    · exact (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  have hγIcc := hγball.mono (fun _ hs => (hsub hs).1)
  have hmap := hC t (t + r) (by linarith) (fun _ hs => hδsub (hsub hs).2) γ hγIcc
    (hγt.symm ▸ hx)
  simpa only [hγt] using
    IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc hγIcc (by linarith) hmap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem IsIntegralCurveOn.inner_nonpos_of_mapsTo_Icc
    {f : ℝ → V → V} {γ : ℝ → V} {a b : ℝ} {C : Set V} {ν : V}
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (hab : a < b)
    (hC : MapsTo γ (Icc a b) C)
    (hnormal : ν ∈ DifferentialGeometry.Analysis.Convex.normalCone C (γ a)) :
    inner ℝ ν (f a (γ a)) ≤ 0 := by
  have hmax : IsMaxOn (fun y : V => inner ℝ ν y) C (γ a) := by
    intro y hy
    have h := hnormal.2 y hy
    rwa [inner_sub_right, sub_nonpos] at h
  have hderiv : HasFDerivAt (fun y : V => inner ℝ ν y) (innerSL ℝ ν) (γ a) :=
    (innerSL ℝ ν).hasFDerivAt
  exact hmax.localize.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt
    (IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc hγ hab hC)

theorem IsForwardInvariantForODEOn.inner_nonpos_of_contDiffAt
    [CompleteSpace V] {f : ℝ → V → V} {C : Set V} {J : Set ℝ} {t : ℝ} {x ν : V}
    (hC : IsForwardInvariantForODEOn f C J) (hJ : J ∈ 𝓝 t)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (t, x))
    (hν : ν ∈ DifferentialGeometry.Analysis.Convex.normalCone C x) :
    inner ℝ ν (f t x) ≤ 0 := by
  have hmax : IsMaxOn (fun y : V => inner ℝ ν y) C x := by
    intro y hy
    have h := hν.2 y hy
    rwa [inner_sub_right, sub_nonpos] at h
  exact hmax.localize.hasFDerivWithinAt_nonpos
    (innerSL ℝ ν).hasFDerivAt.hasFDerivWithinAt
    (hC.mem_posTangentConeAt_of_contDiffAt hJ hν.1 hf)


end DifferentialGeometry.Analysis.ODE
