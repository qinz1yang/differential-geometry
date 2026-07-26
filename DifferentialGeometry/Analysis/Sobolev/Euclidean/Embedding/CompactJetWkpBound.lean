import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK

/-!
# Uniform chart-Sobolev bounds from compactly supported Frechet jets

This file records the quantitative Euclidean bridge needed when a geometric
argument supplies uniform pointwise bounds for a finite jet of a family of
smooth chart functions.

If every member of a family is supported in one compact set `K` contained in
an open set `Omega`, and all Frechet derivatives through order `k` have one
pointwise bound `C`, then the family has one finite `W^{k,p}` bound on `Omega`.
The proof uses the canonical smooth weak-derivative realization and estimates
each classical coordinate partial by the corresponding Frechet derivative.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

/-- A family of smooth functions with one compact support and one finite-jet
bound has a uniform finite chart-Sobolev norm.  The displayed witness is the
finite sum, over all coordinate partials of order at most `k`, of

`volume K ^ (1 / p.toReal) * ENNReal.ofReal C`.

No boundedness assumption on the ambient open set is needed. -/
theorem wkp_bdd_of_jet
    {ι : Type*} {Ω K : Set EuclN}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ)
    (F : ι → EuclN → ℝ)
    (hF_smooth : ∀ i : ι, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hF_supp : ∀ i : ι, tsupport (F i) ⊆ K)
    (C : ℝ) (hC : 0 ≤ C)
    (hF_jet : ∀ i : ι, ∀ j : ℕ, j ≤ k → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ j (F i) x‖ ≤ C) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ i : ι,
      MemWkp (d := d) k p (F i) Ω ∧
        wkpNorm (d := d) k p (F i) Ω ≤ A := by
  classical
  let A : ℝ≥0∞ :=
    ∑ j ∈ Finset.range (k + 1),
      ∑ _β : Fin j → Fin d,
        (volume : Measure EuclN) K ^ p.toReal⁻¹ * ENNReal.ofReal C
  have hA_top : A < ⊤ := by
    dsimp [A]
    refine ENNReal.sum_lt_top.mpr ?_
    intro j hj
    refine ENNReal.sum_lt_top.mpr ?_
    intro β hβ
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK.measure_lt_top.ne)
      (by
        rw [ENNReal.ofReal_eq_coe_nnreal hC]
        exact ENNReal.coe_lt_top)
  refine ⟨A, hA_top, ?_⟩
  intro i
  have hF_cpt : HasCompactSupport (F i) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hF_supp i)
  have hF_supp_Ω : tsupport (F i) ⊆ Ω := (hF_supp i).trans hKΩ
  have hF_mem : MemWkp (d := d) k p (F i) Ω :=
    MemWkp_of_smooth_compactSupport_pub
      (d := d) hΩ (hF_smooth i) hF_cpt hF_supp_Ω hp k
  refine ⟨hF_mem, ?_⟩
  rw [wkpNorm_eq_sum]
  dsimp [A]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hjk : j ≤ k := by
    rw [Finset.mem_range] at hj
    omega
  refine Finset.sum_le_sum ?_
  intro β hβ
  have hweak := iterWeakPartial_smooth_ae_eq_iterClassicalPartial
    (d := d) hp hΩ j β (hF_smooth i) hF_cpt hF_supp_Ω
  rw [eLpNorm_congr_ae hweak]
  let G : EuclN → ℝ := fun x => ‖iteratedFDeriv ℝ j (F i) x‖
  have hclass_le :
      eLpNorm (iterClassicalPartial (d := d) j β (F i)) p
          (volume.restrict Ω) ≤
        eLpNorm G p (volume.restrict Ω) := by
    refine eLpNorm_mono (fun x => ?_)
    have hx := norm_iterClassicalPartial_le_iteratedFDeriv
      (d := d) j β (hF_smooth i) x
    simpa only [G, norm_norm] using hx
  have hG_supp : Function.support G ⊆ K := by
    intro x hx
    have hx_deriv : iteratedFDeriv ℝ j (F i) x ≠ 0 := by
      intro hzero
      apply hx
      simp only [G, hzero, norm_zero]
    exact hF_supp i
      ((support_iteratedFDeriv_subset (𝕜 := ℝ) (f := F i) j) hx_deriv)
  have hG_restrict :
      eLpNorm G p (volume.restrict Ω) =
        eLpNorm G p (volume.restrict K) := by
    calc
      eLpNorm G p (volume.restrict Ω) = eLpNorm G p volume :=
        eLpNorm_restrict_eq_of_support_subset (hG_supp.trans hKΩ)
      _ = eLpNorm G p (volume.restrict K) :=
        (eLpNorm_restrict_eq_of_support_subset hG_supp).symm
  have hG_bound :
      eLpNorm G p (volume.restrict K) ≤
        (volume : Measure EuclN) K ^ p.toReal⁻¹ * ENNReal.ofReal C := by
    have hpoint : ∀ᵐ x ∂(volume : Measure EuclN).restrict K, ‖G x‖ ≤ C :=
      Filter.Eventually.of_forall fun x => by
        simpa only [G, norm_norm] using hF_jet i j hjk x
    have hbound := eLpNorm_le_of_ae_bound
      (μ := (volume : Measure EuclN).restrict K) (p := p) hpoint
    simpa only [Measure.restrict_apply_univ] using hbound
  exact hclass_le.trans (hG_restrict.le.trans hG_bound)

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
