import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.DifferentiatedData
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.VariationalIdentityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BaseFChartRegularityB
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.FChartEffStepRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.NirenbergInteriorWeakened
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.BootstrapChartHm
import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.MixedPartials
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.DerivedDataCanonical

/-!
# Single-stage chart-`H^{m+1}` → chart-`H^{m+2}` boost (truly polymorphic)

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, an order
`m : ℕ`, and an element `u_h ∈ laplacianDomainPow g 2`, this module provides
the single-stage polymorphic boost: chart-`H^{m+1}` of the chart-pushed POU-cut
representative of `u_h.coeFn` together with manifold-side chart-`H^m` of the
canonical representative of the `(1 - Δ_g)`-preimage implies chart-`H^{m+2}`
of the chart-pushed POU-cut representative.

## Composition outline

For each `m`-direction multi-index `dirs : Fin m → Fin n`, we:

1. Build a level-`m` instance of `IteratedDiffChartBilinearData g α u_h m`
   whose `directions = dirs`, via `IteratedDiffChartBilinearData.ofBase`
   followed by `m` applications of `iteratedDiffChartBilinearData_step`.
   Each step requires `MemW1p 2` of the previous-level effective source on
   the chart target plus ae-vanishing of it off `chartImagePOUTsupport α`,
   both threaded inductively through a `MemWkp (m - j) 2` rank invariant
   (anchored at level `0` by `base_f_chart_memWkp_m`).

2. Apply the weakened polymorphic Nirenberg interior regularity
   `iteratedDerivedChartBilinear_memWkp_two_two_interior_weakened` to the
   level-`m` bundle, yielding `MemWkp 2 2` of `chosenMthMixed m dirs` on a
   precompact open thickening `Ω''` of `chartImagePOUTsupport α`.

3. Extend `MemWkp 2 2` from `Ω''` to the whole `chartTargetEuclid α` via
   the support-aware cutoff extension `MemWkp_extend_via_cutoff_poly`,
   using the polymorphic ae-vanishing `chosenMthMixed_ae_zero_off_Kα`.

4. Combine the per-`dirs` `MemWkp 2 2` of `chosenMthMixed m dirs` with the
   chart-`H^{m+1}` hypothesis and apply
   `chartPushed_memWkp_m_plus_two_step` to assemble chart-`H^{m+2}` of the
   chart-pushed parent.

## Main result

* `chartPushed_memWkp_succ_jump` — the headline single-stage boost.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmJump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStep
open DifferentialGeometry.Analysis.Laplacian.IteratedBaseFChartRegularityB
open DifferentialGeometry.Analysis.Laplacian.IteratedFChartEffStepRegularity
open DifferentialGeometry.Analysis.Laplacian.IteratedNirenbergInteriorWeakened
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStepScaffold
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplDataCanonical
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Pad a finite-length multi-index `dirs : Fin n → Fin (finrank ℝ E)` to an
infinite sequence `ℕ → Fin (finrank ℝ E)` by extending with a default value
beyond index `n - 1`. The padded sequence will only be queried at indices
`< n` in our use. -/
private noncomputable def padDirs {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) :
    ℕ → Fin (Module.finrank ℝ E) :=
  fun j => if h : j < n then dirs ⟨j, h⟩ else
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩

@[simp] private lemma padDirs_at_lt {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E))
    {j : ℕ} (hj : j < n) :
    padDirs dirs j = dirs ⟨j, hj⟩ := by
  unfold padDirs; rw [dif_pos hj]

/-- The level-`k` direction multi-index reconstructed from the padded
sequence for `k ≤ n`. -/
private noncomputable def dirsOf {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) (k : ℕ) :
    Fin k → Fin (Module.finrank ℝ E) :=
  fun i => padDirs dirs i.val

@[simp] private lemma dirsOf_zero {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) :
    dirsOf dirs 0 = Fin.elim0 := by
  funext i; exact i.elim0

private lemma dirsOf_succ {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) (k : ℕ) :
    dirsOf dirs (k + 1) =
      Fin.snoc (dirsOf dirs k) (padDirs dirs k) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
  · subst hj
    rw [Fin.snoc_castSucc]
    rfl
  · subst hlast
    rw [Fin.snoc_last]
    rfl

/-- The level-`n` direction multi-index reconstructed from `padDirs dirs`
agrees with the original `dirs`. -/
private lemma dirsOf_self {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) :
    dirsOf dirs n = dirs := by
  funext i
  unfold dirsOf
  rw [padDirs_at_lt dirs i.isLt]

private structure LevelBundle
    (g : SmoothRiemannianMetric I M) (α : M)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m j : ℕ) where
  data : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h j
  directions_eq : data.directions = dirsOf dirs j
  fChartEff_memWkp :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m - j) 2 data.fChartEff
      (chartTargetEuclid (I := I) (M := M) α)
  fChartEff_ae_zero_off_K :
    data.fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ))

/-- The level-`0` `LevelBundle`. The level-`0` data is
`IteratedDiffChartBilinearData.ofBase`. The rank invariant
`MemWkp m 2 base.f_chart` is discharged by
`base_f_chart_memWkp_m` at order `m`, consuming
manifold-side chart-`H^{m+1}` of `u_h.coeFn` and manifold-side chart-`H^m`
of the `(1-Δ_g)` preimage. The ae-vanishing is the public
`base_f_chart_ae_zero_off_K_α` (in
`DerivedChartBilinearH1ComplDataCanonical`). -/
private def buildLevelZero
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m : ℕ)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    LevelBundle (I := I) (M := M) g α dirs hu_h m 0 :=
  { data := IteratedDiffChartBilinearData.ofBase (I := I) (M := M) g α hu_h
    directions_eq := by
      change (Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) = dirsOf dirs 0
      rw [dirsOf_zero]
    fChartEff_memWkp := by
      change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m - 0) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)
      rw [Nat.sub_zero]
      exact base_f_chart_memWkp_m
        (I := I) (M := M) g α m
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)
        h_chart_H_m_plus_1_u h_chart_H_m_RHS
    fChartEff_ae_zero_off_K := by
      change (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
        g α (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))
      have h_ae := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)
      filter_upwards [h_ae] with y hy using hy }

/-- The inductive step `j → j + 1` of the `LevelBundle` build, given:

* the level-`j` bundle (which carries `MemWkp (m - j) 2` of `D_j.fChartEff`);
* chart-`H^{j+1}` of the parent (= a restriction of chart-`H^{m+1}` since
  `j + 1 ≤ m`);
* chart-`H^{j+2}` of the parent (= a restriction of chart-`H^{m+1}` since
  `j + 2 ≤ m + 1`);
* the bound `j + 1 ≤ m` (so the step is meaningful).

The output level-`(j+1)` bundle's `fChartEff` is `fChartEffStep ... j ...`,
satisfying `MemWkp (m - (j+1)) 2` via `fChartEffStep_memWkp_K_two` at
`K = m - j - 1`. The chart-`H` requirement of the propagator is
`chart-H^{j + 2 + (m - j - 1)} = chart-H^{m+1}` ✓.

The ae-vanishing is `fChartEffStep`'s indicator structure (automatic). -/
private def buildLevelStep
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    {hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2}
    {m j : ℕ} (hj_succ_le : j + 1 ≤ m)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    (B_j : LevelBundle (I := I) (M := M) g α dirs hu_h m j)
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    LevelBundle (I := I) (M := M) g α dirs hu_h m (j + 1) := by
  classical
  have h_chart_H_j_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (j + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1_u.le_of_le (by omega : j + 1 ≤ m + 1)
  have h_chart_H_j_plus_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (j + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1_u.le_of_le (by omega : j + 2 ≤ m + 1)
  have h_D_j_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 B_j.data.fChartEff
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_le_1 : (1 : ℕ) ≤ m - j := by omega
    have h_w1p_eq : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2 B_j.data.fChartEff
        (chartTargetEuclid (I := I) (M := M) α) :=
      B_j.fChartEff_memWkp.le_of_le h_le_1
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_w1p_eq
    exact h_w1p_eq
  let D_next : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h (j + 1) :=
    iteratedDiffChartBilinearData_step (I := I) (M := M) g α
      (u_h := u_h) j B_j.data (padDirs dirs j)
      h_chart_H_j_plus_1 h_chart_H_j_plus_2
      h_D_j_W1p B_j.fChartEff_ae_zero_off_K
  have h_directions_eq : D_next.directions = dirsOf dirs (j + 1) := by
    change Fin.snoc B_j.data.directions (padDirs dirs j) = dirsOf dirs (j + 1)
    rw [dirsOf_succ, B_j.directions_eq]
  set K_next : ℕ := m - j - 1 with hK_next_def
  have hK_succ_eq : K_next + 1 = m - j := by omega
  have hK_next_chart_eq : j + 2 + K_next = m + 1 := by omega
  have h_prev_memWkp_succ :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (K_next + 1) 2 B_j.data.fChartEff
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hK_succ_eq]; exact B_j.fChartEff_memWkp
  have h_chart_H_propagator :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (j + 2 + K_next) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hK_next_chart_eq]; exact h_chart_H_m_plus_1_u
  have h_next_memWkp_K :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) K_next 2
        (fChartEffStep (I := I) (M := M) g α u_h j B_j.data.directions
          B_j.data.fChartEff (padDirs dirs j))
        (chartTargetEuclid (I := I) (M := M) α) :=
    fChartEffStep_memWkp_K_two (I := I) (M := M) g α u_h j K_next
      B_j.data.directions B_j.data.fChartEff (padDirs dirs j)
      h_prev_memWkp_succ B_j.fChartEff_ae_zero_off_K h_chart_H_propagator
  have h_next_fChartEff_eq : D_next.fChartEff =
      fChartEffStep (I := I) (M := M) g α u_h j B_j.data.directions
        B_j.data.fChartEff (padDirs dirs j) := rfl
  have h_D_next_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m - (j + 1)) 2 D_next.fChartEff
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [h_next_fChartEff_eq]
    have h_eq : K_next = m - (j + 1) := by omega
    rw [← h_eq]
    exact h_next_memWkp_K
  have h_D_next_ae_zero :
      D_next.fChartEff =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
    rw [h_next_fChartEff_eq]
    have h_diff_open : IsOpen
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    refine (ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    unfold fChartEffStep
    exact Set.indicator_of_notMem hy.2 _
  exact
    { data := D_next
      directions_eq := h_directions_eq
      fChartEff_memWkp := h_D_next_memWkp
      fChartEff_ae_zero_off_K := h_D_next_ae_zero }

/-- Build the level-`j` bundle by induction on `j ≤ m`. -/
private def buildLevel
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m : ℕ)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (j : ℕ) (hj : j ≤ m) :
    LevelBundle (I := I) (M := M) g α dirs hu_h m j := by
  induction j with
  | zero =>
      exact buildLevelZero (I := I) (M := M) g α hu_h m dirs
        h_chart_H_m_plus_1_u h_chart_H_m_RHS
  | succ j ih =>
      have hj_le : j ≤ m := Nat.le_of_succ_le hj
      have hj_succ_le : j + 1 ≤ m := hj
      let B_j := ih hj_le
      exact buildLevelStep (I := I) (M := M) g α
        (hu_h := hu_h) (m := m) (j := j) hj_succ_le dirs B_j (h_chart_H_m_plus_1_u α)

/-- For any `m`-direction multi-index `dirs`, the chosen `m`-mixed partial
of the chart-pushed POU representative lies in `MemWkp 2 2` of the full
chart target, provided manifold-side chart-`H^{m+1}` of `u_h.coeFn` and
manifold-side chart-`H^m` of the `(1-Δ_g)`-preimage. -/
private theorem chosenMthMixed_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m : ℕ)
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  let B_m : LevelBundle (I := I) (M := M) g α dirs hu_h m m :=
    buildLevel (I := I) (M := M) g α hu_h m dirs
      h_chart_H_m_plus_1_u h_chart_H_m_RHS m (le_refl _)
  have h_directions : B_m.data.directions = dirs := by
    rw [B_m.directions_eq, dirsOf_self]
  have h_chart_H_m_plus_1_at_α :=
    h_chart_H_m_plus_1_u α
  obtain ⟨Ω'', hΩ''_open, hKα_in_Ω'', hΩ''_compact_closure,
      h_closureΩ''_in_chart, h_memWkp_22_Ω''⟩ :=
    iteratedDerivedChartBilinear_memWkp_two_two_interior_weakened
      (I := I) (M := M) g α m B_m.data h_chart_H_m_plus_1_at_α
  rw [h_directions] at h_memWkp_22_Ω''
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact Kα :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hKα_in_Ω : Kα ⊆ Ω :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hΩ''_in_Ω : Ω'' ⊆ Ω := fun y hy => h_closureΩ''_in_chart (subset_closure hy)
  have h_parent_m :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        Ω :=
    h_chart_H_m_plus_1_at_α.le_of_le (by omega : m ≤ m + 1)
  have h_chosen_ae_zero :
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h m h_parent_m dirs
  exact MemWkp_extend_via_cutoff_poly (E := E) 2
    hΩ_open hΩ''_open hΩ''_in_Ω hKα_compact hKα_in_Ω''
    h_memWkp_22_Ω'' h_chosen_ae_zero

/-- **Headline single-stage chart-`H^{m+2}` boost.**

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and any
`u_h ∈ laplacianDomainPow g 2`, manifold-side chart-`H^{m+1}` of the canonical
representative of `u_h.coeFn` together with manifold-side chart-`H^m` of the
canonical representative of the `(1-Δ_g)`-preimage gives chart-`H^{m+2}` of
the chart-pushed POU-cut representative at `α`. -/
theorem chartPushed_memWkp_succ_jump
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_top_memWkp_two : ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
        (chartTargetEuclid (I := I) (M := M) α) := fun idx =>
    chosenMthMixed_memWkp_two_two (I := I) (M := M) g α hu_h m
      h_chart_H_m_plus_1_u h_chart_H_m_RHS idx
  have h_chart_H_m_plus_1_at_α :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1_u α
  exact chartPushed_memWkp_m_plus_two_step (I := I) (M := M) g α u_h m
    h_chart_H_m_plus_1_at_α h_top_memWkp_two

end IteratedChartHmJump
end Laplacian
end Analysis
end DifferentialGeometry

end
