import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CompactJetWkpBound
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.MetricJet3Intrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartL2BoundedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

/-!
# Uniform fixed-atlas metric-difference terms

This file isolates the part of the fixed-background `W^{3,p}` data argument
that does not require the tensor-space quotient or completeness layer.
Intrinsic covariant-derivative bounds through order three first give one
pointwise Frechet-jet bound for all POU-weighted metric-difference components.
The compact-jet Euclidean theorem then gives one finite `W^{3,p}` bound on
each fixed chart, uniform over the whole metric family and all components.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [BoundarylessManifold I M] in
/-- Uniform intrinsic metric bounds through order three give one uniform
Frechet-jet bound for every POU-weighted scalar component of the
fixed-background metric difference. -/
theorem metricDiff_fam_jet
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α : M) (k : ι)
        (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
        (j : ℕ), j ≤ 3 → ∀ y : EuclN,
        ‖iteratedFDeriv ℝ j
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) y‖ ≤ C := by
  classical
  obtain ⟨B₀, hB₀⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 0 gBase gBase
  obtain ⟨B₁, hB₁⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 1 gBase gBase
  obtain ⟨B₂, hB₂⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 2 gBase gBase
  obtain ⟨B₃, hB₃⟩ :=
    metricCovDerivNorm_bddOn (I := I) isCompact_univ 3 gBase gBase
  let BBase : ℝ := max (max B₀ B₁) (max B₂ B₃)
  have hbase : ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q gBase gBase BBase := by
    intro q hq x hx
    interval_cases q
    · exact (hB₀ x hx).trans
        ((le_max_left B₀ B₁).trans (le_max_left (max B₀ B₁) (max B₂ B₃)))
    · exact (hB₁ x hx).trans
        ((le_max_right B₀ B₁).trans (le_max_left (max B₀ B₁) (max B₂ B₃)))
    · exact (hB₂ x hx).trans
        ((le_max_left B₂ B₃).trans (le_max_right (max B₀ B₁) (max B₂ B₃)))
    · exact (hB₃ x hx).trans
        ((le_max_right B₂ B₃).trans (le_max_right (max B₀ B₁) (max B₂ B₃)))
  let BAll : ℝ := max B BBase
  let gAll : Option ι → SmoothRiemannianMetric I M := fun k => k.elim gBase gSeq
  have hAllBdd : ∀ k : Option ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gAll k) gBase BAll := by
    intro k q hq
    cases k with
    | none =>
        intro x hx
        exact (hbase q hq x hx).trans (le_max_right B BBase)
    | some k =>
        intro x hx
        exact (hbdd k q hq x hx).trans (le_max_left B BBase)
  have hGramPer : ∀ m : Fin 4, ∃ Cm : ℝ, 0 ≤ Cm ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : Option ι, ∀ x ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ a c : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ m
              (chartGramOnE (I := I) (gAll k) α a c)
              (extChartAt I α x)‖ ≤ Cm := by
    intro m
    exact chartGram_pou_le (I := I) gBase gAll m BAll
      (fun k q hq => hAllBdd k q (by omega))
  choose CGram hCGram_nn hCGram using hGramPer
  let Q : ℝ := ∑ m : Fin 4, CGram m
  have hQ_nn : 0 ≤ Q := Finset.sum_nonneg fun m _ => hCGram_nn m
  have hGram : ∀ m : ℕ, m ≤ 3 →
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : Option ι, ∀ x ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ a c : Fin (Module.finrank ℝ E),
            ‖iteratedFDeriv ℝ m
              (chartGramOnE (I := I) (gAll k) α a c)
              (extChartAt I α x)‖ ≤ Q := by
    intro m hm α hα k x hx a c
    let mf : Fin 4 := ⟨m, by omega⟩
    exact (hCGram mf α hα k x hx a c).trans
      (Finset.single_le_sum (fun q _ => hCGram_nn q) (Finset.mem_univ mf))
  have hPouPer : ∀ α : M, ∃ Cα : ℝ, 0 ≤ Cα ∧
      ∀ l ≤ 3, ∀ y ∈ chartPouKernel (I := I) (M := M) α,
        ‖iteratedFDeriv ℝ l
          (chartPushedRaw I α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y‖ ≤ Cα := by
    intro α
    exact exists_iteratedFDeriv_norm_bound_on_compactR
      (chartPushedRaw_chartAtlasPOU_contDiffOn (I := I) (M := M) α)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) 3
  choose CPou hCPou_nn hCPou using hPouPer
  let P : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), CPou α
  have hP_nn : 0 ≤ P := Finset.sum_nonneg fun α _ => hCPou_nn α
  have hCPou_le : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M), CPou α ≤ P := by
    intro α hα
    exact Finset.single_le_sum (fun β _ => hCPou_nn β) hα
  let R : ℝ := ∑ m ∈ Finset.range 4,
    ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m * (Q + Q)
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun m _ => by positivity
  let C : ℝ := ∑ j ∈ Finset.range 4,
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * P * R
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α k Jdx j hj y
  by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
  · let a : Fin (Module.finrank ℝ E) := Jdx 0
    let c : Fin (Module.finrank ℝ E) := Jdx 1
    have hJdx : Jdx = ![a, c] := by
      funext q
      fin_cases q <;> rfl
    rw [hJdx]
    let T : SmoothCcTensor gBase 0 2 :=
      metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α hyK
      set ρ : EuclN → ℝ :=
        chartPushedRaw I α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_def
      set raw : EuclN → ℝ :=
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) gBase 0 2 T α
            (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c]) with hraw_def
      have hev :
          tensorChartComp (I := I) (M := M) gBase 0 2 T α
              (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] =ᶠ[nhds y]
            (fun z => ρ z * raw z) := by
        simpa only [tensorChartComp_def, hρ_def, hraw_def] using
          tensorChartComponent_eventuallyEq_chartPushedRaw_pou_mul_chartPushedRaw_raw
            (I := I) (M := M) gBase 0 2 T α
            (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] hyT
      change ‖iteratedFDeriv ℝ j
        (tensorChartComp (I := I) (M := M) gBase 0 2 T α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c]) y‖ ≤ C
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev j).self_of_nhds]
      have hρ_cd : ContDiffOn ℝ ∞ ρ
          (chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [hρ_def] using
          chartPushedRaw_chartAtlasPOU_contDiffOn (I := I) (M := M) α
      have hraw_cd : ContDiffOn ℝ ∞ raw
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine (rawPullR_contDiffOn (I := I) (M := M) gBase 0 2 T α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c]).congr ?_
        intro z hz
        rw [hraw_def, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
        rfl
      have hLeib := norm_iteratedFDerivWithin_mul_le
        (𝕜 := ℝ) (f := ρ) (g := raw) (n := j) hρ_cd hraw_cd
        (chartTargetEuclid_isOpen (I := I) (M := M) α).uniqueDiffOn hyT
        (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := fun z => ρ z * raw z) j
        (chartTargetEuclid_isOpen (I := I) (M := M) α) hyT] at hLeib
      have hraw_bound : ∀ m : ℕ, m ≤ 3 →
          ‖iteratedFDerivWithin ℝ m raw
            (chartTargetEuclid (I := I) (M := M) α) y‖ ≤ R := by
        intro m hm
        rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := raw) m
          (chartTargetEuclid_isOpen (I := I) (M := M) α) hyT]
        have hraw_ev : raw =ᶠ[nhds y]
            tensorComponentEuclideanChart (I := I) (M := M) gBase 0 2 T α
              (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] := by
          filter_upwards [
            (chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hyT] with z hz
          rw [hraw_def, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
          rfl
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hraw_ev m).self_of_nhds]
        rw [chartPouKernel] at hyK
        obtain ⟨z, ⟨x, hx, hxz⟩, hzy⟩ := hyK
        have hcoord : (toEuclidean (E := E)).symm y = extChartAt I α x := by
          calc
            (toEuclidean (E := E)).symm y =
                (toEuclidean (E := E)).symm (toEuclidean (E := E) z) := by rw [hzy]
            _ = z := (toEuclidean (E := E)).symm_apply_apply z
            _ = extChartAt I α x := hxz.symm
        have hx_source : x ∈ (extChartAt I α).source := by
          rw [extChartAt_source]
          exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
        have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
          extChartAt_target_subset_interior_of_boundaryless (I := I) α
            ((extChartAt I α).map_source hx_source)
        have hy_int : (toEuclidean (E := E)).symm y ∈
            interior (extChartAt I α).target := by rwa [hcoord]
        have hbridge :=
          norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE
            (I := I) (M := M) gBase T α ![a, c] m hy_int
        have hrawComp :
            ‖iteratedFDerivWithin ℝ m
              (tensorChartComponentOnModel (I := I) (M := M) gBase T α ![a, c])
              (interior (extChartAt I α).target)
              ((toEuclidean (E := E)).symm y)‖ ≤ Q + Q := by
          have heq := gramDiff_eqOn (I := I) (M := M)
            gBase (gSeq k) gBase α a c
          change Set.EqOn
            (fun w : E => chartGramOnE (I := I) (gSeq k) α a c w -
              chartGramOnE (I := I) gBase α a c w)
            (tensorChartComponentOnModel (I := I) (M := M) gBase T α ![a, c])
            (interior (extChartAt I α).target) at heq
          rw [← iteratedFDerivWithin_congr (𝕜 := ℝ) heq hy_int m]
          rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m isOpen_interior hy_int]
          have hseq : ContDiffAt ℝ ∞
              (chartGramOnE (I := I) (gSeq k) α a c)
              ((toEuclidean (E := E)).symm y) :=
            ((chartGramOnE_contDiffOn (I := I) (gSeq k) α a c).mono
              interior_subset).contDiffAt (isOpen_interior.mem_nhds hy_int)
          have hbasecd : ContDiffAt ℝ ∞
              (chartGramOnE (I := I) gBase α a c)
              ((toEuclidean (E := E)).symm y) :=
            ((chartGramOnE_contDiffOn (I := I) gBase α a c).mono
              interior_subset).contDiffAt (isOpen_interior.mem_nhds hy_int)
          change ‖iteratedFDeriv ℝ m
            (chartGramOnE (I := I) (gSeq k) α a c -
              chartGramOnE (I := I) gBase α a c)
            ((toEuclidean (E := E)).symm y)‖ ≤ Q + Q
          rw [iteratedFDeriv_sub_apply
            (hseq.of_le (by exact_mod_cast le_top))
            (hbasecd.of_le (by exact_mod_cast le_top))]
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · rw [hcoord]
            simpa only [gAll] using hGram m hm α hα (some k) x hx a c
          · rw [hcoord]
            simpa only [gAll] using hGram m hm α hα none x hx a c
        have hterm :
            ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m *
                ‖iteratedFDerivWithin ℝ m
                  (tensorChartComponentOnModel (I := I) (M := M) gBase T α ![a, c])
                  (interior (extChartAt I α).target)
                  ((toEuclidean (E := E)).symm y)‖ ≤
              ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m *
                (Q + Q) := by
          exact mul_le_mul_of_nonneg_left hrawComp (by positivity)
        refine hbridge.trans (hterm.trans ?_)
        dsimp [R]
        exact Finset.single_le_sum
          (f := fun q : ℕ =>
            ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ q * (Q + Q))
          (fun q _ => by positivity)
          (Finset.mem_range.mpr (by omega : m < 4))
      have hterm : ∀ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) *
              ‖iteratedFDerivWithin ℝ l ρ
                (chartTargetEuclid (I := I) (M := M) α) y‖ *
              ‖iteratedFDerivWithin ℝ (j - l) raw
                (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
            (j.choose l : ℝ) * P * R := by
        intro l hl
        have hlj : l ≤ j := by rw [Finset.mem_range] at hl; omega
        have hρl : ‖iteratedFDerivWithin ℝ l ρ
            (chartTargetEuclid (I := I) (M := M) α) y‖ ≤ P := by
          rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := ρ) l
            (chartTargetEuclid_isOpen (I := I) (M := M) α) hyT]
          exact (hCPou α l (hlj.trans hj) y hyK).trans (hCPou_le α hα)
        have hrawl := hraw_bound (j - l) ((Nat.sub_le j l).trans hj)
        have hchoose : 0 ≤ (j.choose l : ℝ) := by positivity
        calc
          (j.choose l : ℝ) *
                ‖iteratedFDerivWithin ℝ l ρ
                  (chartTargetEuclid (I := I) (M := M) α) y‖ *
                ‖iteratedFDerivWithin ℝ (j - l) raw
                  (chartTargetEuclid (I := I) (M := M) α) y‖
              ≤ ((j.choose l : ℝ) * P) * R := by gcongr
          _ = (j.choose l : ℝ) * P * R := rfl
      refine hLeib.trans ((Finset.sum_le_sum hterm).trans ?_)
      dsimp [C]
      exact Finset.single_le_sum
        (f := fun q : ℕ =>
          ∑ l ∈ Finset.range (q + 1), (q.choose l : ℝ) * P * R)
        (fun q _ => Finset.sum_nonneg fun l _ => by positivity)
        (Finset.mem_range.mpr (by omega : j < 4))
    · have hev0 :
          tensorChartComp (I := I) (M := M) gBase 0 2 T α
              (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] =ᶠ[nhds y]
            (fun _ : EuclN => (0 : ℝ)) := by
        have hclosed := (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
        filter_upwards [hclosed.isOpen_compl.mem_nhds hyK] with z hz
        exact tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) gBase 0 2 T α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] hz
      change ‖iteratedFDeriv ℝ j
        (tensorChartComp (I := I) (M := M) gBase 0 2 T α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c]) y‖ ≤ C
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev0 j).self_of_nhds,
        iteratedFDeriv_fun_zero]
      simpa using hC_nn
  · have hzero := tensorChartComp_eq_zero_of_notMem_finset
      (I := I) (M := M) gBase 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
      hα (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
    rw [hzero, iteratedFDeriv_fun_zero]
    simpa using hC_nn

omit [BoundarylessManifold I M] in
/-- On every fixed atlas chart, the metric-difference components of the whole
family have one common finite `W^{3,p}` bound.  The chart may affect the bound;
the metric-family index and tensor component do not. -/
theorem metricDiff_wkp_terms
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∀ α : M, ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ w : ι × (Fin 2 → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) 3 p
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 3 p
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
          (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
  obtain ⟨C, hC, hjet⟩ := metricDiff_fam_jet
    (I := I) (M := M) gBase gSeq B hbdd
  intro α
  exact wkp_bdd_of_jet
    (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    hp 3
    (fun w : ι × (Fin 2 → Fin (Module.finrank ℝ E)) =>
      tensorChartComp (I := I) (M := M) gBase 0 2
        (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
        α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
    (fun w => tensorChartComp_contDiff (I := I) (M := M) gBase 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
      α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
    (fun w => by
      simpa only [tensorChartComp_def] using
        tensorChartComponent_tsupport_subset_chartPouKernel
          (I := I) (M := M) gBase 0 2
          (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
          α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
    C hC (fun w j hj y => hjet α w.1 w.2 j hj y)

end DifferentialGeometry.PDE.RicciFlow
