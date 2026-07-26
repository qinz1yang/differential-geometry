import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CompactJetWkpBound
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkp
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponentRawNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.MetricJet3Intrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartL2BoundedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MetricWkpTerms

/-!
# Uniform `W^{3,p}` data for bounded metric families

The order-at-most-three intrinsic metric bounds used by uniform short-time
existence also control the fixed-background metric differences in the concrete
chart-Sobolev model.  This file packages that implication in two steps:

* `metricDiff_comp_jet` gives one pointwise bound for all derivatives through
  order three of every POU-weighted scalar chart component;
* `metricDiff_wkp3_bdd` converts those bounds into `MemWkpTensor 3 p` and one
  common finite `wkpTensorNorm` radius.

The ellipticity hypothesis used by the later Ricci--DeTurck solver is not
needed for this data-size estimate.  It enters separately in uniform
parabolicity.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma secComp_to_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secChartComp (I := I) (M := M) r s S.toSection α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := rfl

/-- Uniform intrinsic metric bounds through order three give one uniform
Frechet-jet bound for every POU-weighted scalar component of the
fixed-background metric difference.  The bound is also valid at inactive
chart centres, where the component is identically zero. -/
theorem metricDiff_comp_jet
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
  let R : ℝ := ∑ m in Finset.range 4,
    ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m * (Q + Q)
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun m _ => by positivity
  let C : ℝ := ∑ j in Finset.range 4,
    ∑ l in Finset.range (j + 1), (j.choose l : ℝ) * P * R
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
              (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] =ᵉ[nhds y]
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
        have hraw_ev : raw =ᵉ[nhds y]
            rawPullR (I := I) (M := M) gBase 0 2 T α
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
              (rawCompOnE (I := I) (M := M) gBase T α ![a, c])
              (interior (extChartAt I α).target)
              ((toEuclidean (E := E)).symm y)‖ ≤ Q + Q := by
          have heq := gramDiff_eqOn (I := I) (M := M)
            gBase (gSeq k) gBase α a c
          change Set.EqOn
            (fun w : E => chartGramOnE (I := I) (gSeq k) α a c w -
              chartGramOnE (I := I) gBase α a c w)
            (rawCompOnE (I := I) (M := M) gBase T α ![a, c])
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
                  (rawCompOnE (I := I) (M := M) gBase T α ![a, c])
                  (interior (extChartAt I α).target)
                  ((toEuclidean (E := E)).symm y)‖ ≤
              ‖((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)‖ ^ m *
                (Q + Q) := by
          exact mul_le_mul_of_nonneg_left hrawComp (by positivity)
        refine hbridge.trans (hterm.trans ?_)
        exact Finset.single_le_sum
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
      exact Finset.single_le_sum
        (fun q _ => Finset.sum_nonneg fun l _ => by positivity)
        (Finset.mem_range.mpr (by omega : j < 4))
    · have hev0 :
          tensorChartComp (I := I) (M := M) gBase 0 2 T α
              (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, c] =ᵉ[nhds y]
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
  · have hzero := tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
      (I := I) (M := M) gBase 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
      hα (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
    rw [hzero, iteratedFDeriv_fun_zero]
    simpa using hC_nn

/-- The intrinsic `C^3` metric-family bound gives one real radius containing
all fixed-background metric differences in chartwise `W^{3,p}`.  In
particular, the conclusion includes both the concrete tensor-Sobolev
membership and an explicit uniform bound for `wkpTensorNorm`. -/
theorem metricDiff_wkp3_bdd
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ι,
      MemWkpTensor (I := I) (M := M) gBase 3 p
          (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection ∧
        wkpTensorNorm (I := I) (M := M) gBase 3 p
          (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection ≤
            ENNReal.ofReal C := by
  classical
  have hper : ∀ α : M, ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ w : ι × (Fin 2 → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) 3 p
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) 3 p
          (tensorChartComp (I := I) (M := M) gBase 0 2
            (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq w.1))
            α (![] : Fin 0 → Fin (Module.finrank ℝ E)) w.2)
          (chartTargetEuclid (I := I) (M := M) α) ≤ A := by
    exact metricDiff_wkp_terms (I := I) (M := M) gBase gSeq B hbdd hp
  choose A hA_top hA using hper
  let R : ℝ≥0∞ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
        ∑ _Jdx : Fin 2 → Fin (Module.finrank ℝ E), A α
  have hR_top : R < ⊤ := by
    dsimp [R]
    refine ENNReal.sum_lt_top.mpr ?_
    intro α hα
    refine ENNReal.sum_lt_top.mpr ?_
    intro Idx hIdx
    refine ENNReal.sum_lt_top.mpr ?_
    intro Jdx hJdx
    exact hA_top α
  have hR_ne : R ≠ ⊤ := hR_top.ne
  refine ⟨R.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro k
  have hmem : MemWkpTensor (I := I) (M := M) gBase 3 p
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection := by
    intro α Idx Jdx
    have hIdx : Idx = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
      Subsingleton.elim _ _
    rw [hIdx, secComp_to_smooth]
    exact (hA α (k, Jdx)).1
  refine ⟨hmem, ?_⟩
  unfold wkpTensorNorm
  have hcollapse :
      (∑' α : M,
        ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) 3 p
              (secChartComp (I := I) (M := M) 0 2
                (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
                α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) 3 p
                (secChartComp (I := I) (M := M) 0 2
                  (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
                  α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α) := by
    rw [tsum_eq_sum (s := chartAtlasPOU_finset (I := I) (M := M))]
    intro α hα
    refine Finset.sum_eq_zero ?_
    intro Idx hIdx
    refine Finset.sum_eq_zero ?_
    intro Jdx hJdx
    rw [secComp_zero_off (I := I) (M := M) 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
      hα Idx Jdx]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [hcollapse]
  calc
    (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) 3 p
                (secChartComp (I := I) (M := M) 0 2
                  (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k)).toSection
                  α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ≤ R := by
      dsimp [R]
      refine Finset.sum_le_sum ?_
      intro α hα
      refine Finset.sum_le_sum ?_
      intro Idx hIdx
      refine Finset.sum_le_sum ?_
      intro Jdx hJdx
      have hIdx0 : Idx = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
        Subsingleton.elim _ _
      rw [hIdx0, secComp_to_smooth]
      exact (hA α (k, Jdx)).2
    _ = ENNReal.ofReal R.toReal := (ENNReal.ofReal_toReal hR_ne).symm

end DifferentialGeometry.PDE.RicciFlow
