/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.Interpolation.LipschitzSelection
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoEMetricSpace Q]

/-- A radial local extended-distance estimate on a convex set is a global
Lipschitz estimate. Finiteness of all distances in the actual image is derived
from continuity and preconnectedness, rather than assumed of the target.
The image pseudometric retains the original extended distance definitionally. -/
theorem lipschitzOnWith_of_eventually_edist_le
    {f : E → Q} {S : Set E} {K : ℝ≥0} (hS : Convex ℝ S)
    (hlocal : ∀ x ∈ S, ∀ᶠ y in 𝓝[S] x,
      edist (f y) (f x) ≤ (K : ℝ≥0∞) * edist y x) :
    LipschitzOnWith K f S := by
  classical
  have hf : ContinuousOn f S := by
    intro x hx
    apply tendsto_iff_edist_tendsto_0.mpr
    have hd : Tendsto (fun y : E => edist y x) (𝓝[S] x) (𝓝 0) :=
      tendsto_iff_edist_tendsto_0.mp continuousWithinAt_id
    have hb : Tendsto (fun y : E => (K : ℝ≥0∞) * edist y x) (𝓝[S] x) (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hd (Or.inr ENNReal.coe_ne_top)
    exact tendsto_const_nhds.squeeze' hb
      (Eventually.of_forall fun _ => bot_le) (hlocal x hx)
  have hconnected : IsPreconnected (f '' S) := hS.isPreconnected.image f hf
  have hfinite (a b : f '' S) : edist a b ≠ ⊤ := by
    have hc : IsClopen (Metric.eball (b : Q) ⊤) :=
      ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
    have hn : ((f '' S) ∩ Metric.eball (b : Q) ⊤).Nonempty := by
      refine ⟨b, b.property, ?_⟩
      change edist (b : Q) b < ⊤
      simp only [edist_self]
      exact bot_lt_top
    exact ne_of_lt (hconnected.subset_isClopen hc hn a.property)
  let : PseudoMetricSpace (f '' S) := PseudoEMetricSpace.toPseudoMetricSpace hfinite
  intro x hx y hy
  let F : E → f '' S := fun z =>
    if hz : z ∈ S then ⟨f z, mem_image_of_mem f hz⟩ else ⟨f x, mem_image_of_mem f hx⟩
  have hF (z : E) (hz : z ∈ S) : (F z : Q) = f z := by
    simp only [F, dite_eq_left hz]
  have hbound : LipschitzOnWith K F S := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_of_eventually_dist_le hS
    intro z hz
    filter_upwards [hlocal z hz, self_mem_nhdsWithin] with w hw hws
    have he : edist (F w) (F z) ≤ (K : ℝ≥0∞) * edist w z := by
      change edist (F w : Q) (F z : Q) ≤ (K : ℝ≥0∞) * edist w z
      simpa only [hF w hws, hF z hz] using hw
    have hre := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top w z)) he
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← dist_edist] using hre
  have hxy := hbound hx hy
  change edist (F x : Q) (F y : Q) ≤ (K : ℝ≥0∞) * edist x y at hxy
  simpa only [hF x hx, hF y hy] using hxy

/-- Lipschitz bounds on a finite relative-closed cover of a convex source
give a global bound with the supremum of the piecewise constants. Only the
whole source must be convex. No continuity or finite-distance hypothesis is
needed beyond the actual within-cell Lipschitz bounds. -/
theorem lipschitzOnWith_of_finite_closed_cover
    {ι : Type*} [Fintype ι] {f : E → Q} {S : Set E} (hS : Convex ℝ S)
    (A : ι → Set E)
    (hclosed : ∀ i, IsClosed ((Subtype.val : S → E) ⁻¹' A i))
    (hcover : ∀ x ∈ S, ∃ i, x ∈ A i)
    (K : ι → ℝ≥0) (hLip : ∀ i, LipschitzOnWith (K i) f (S ∩ A i)) :
    LipschitzOnWith (Finset.univ.sup K) f S := by
  classical
  apply lipschitzOnWith_of_eventually_edist_le hS
  intro x hx
  have hactive (i : ι) : ∀ᶠ y in 𝓝[S] x, y ∈ A i → x ∈ A i := by
    by_cases hxi : x ∈ A i
    · exact Eventually.of_forall fun _ _ => hxi
    · rw [← map_nhds_subtype_val (⟨x, hx⟩ : S)]
      change ∀ᶠ y : S in 𝓝 (⟨x, hx⟩ : S), (y : E) ∈ A i → x ∈ A i
      have hn : ((Subtype.val : S → E) ⁻¹' A i)ᶜ ∈ 𝓝 (⟨x, hx⟩ : S) :=
        (hclosed i).isOpen_compl.mem_nhds hxi
      filter_upwards [hn] with y hy
      intro hya
      exact (hy hya).elim
  filter_upwards [eventually_all.mpr hactive, self_mem_nhdsWithin] with y hy hys
  obtain ⟨i, hyi⟩ := hcover y hys
  have hKi : (K i : ℝ≥0∞) ≤ ((Finset.univ.sup K : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr (Finset.le_sup (f := K) (Finset.mem_univ i))
  exact (hLip i ⟨hys, hyi⟩ ⟨hx, hy i hyi⟩).trans (mul_le_mul_left hKi _)

end DifferentialGeometry.Analysis
