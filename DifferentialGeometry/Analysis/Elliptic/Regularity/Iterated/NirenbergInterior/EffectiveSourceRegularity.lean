import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.InductiveSuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm

/-!
# Polymorphic-in-`m` canonical iterated chart-bilinear data with regularity
propagation

This module assembles the canonical inductive family of level-`m` chart-
bilinear data instances and packages two propagation results:

* the canonical iterated data instance at every level, built by chaining the
  base instance `IteratedDiffChartBilinearData.ofBase` with the inductive step
  `iteratedDiffChartBilinearData_step` once per level along a fixed direction
  sequence;
* the structural ae-vanishing of the level-`m` effective chart-pulled source
  off the compact "kernel" `chartImagePOUTsupport α`, unconditional from
  level `m ≥ 1` thanks to the indicator structure of `fChartEffStep`;
* the inductive `MemWkp K 2` regularity propagation of the level-`m` effective
  chart-pulled source, threaded from chart-`H` regularity of the canonical
  chart-pushed representative of `u_h.coeFn` at every required intermediate
  level and from a per-step propagator carrying the regularity through
  `fChartEffStep`.

The canonical family is parameterised by an infinite sequence
`dirs_seq : ℕ → Fin n` of directions: at each level the new outer direction
appended via `Fin.snoc` is `dirs_seq m`. The level-`m` direction multi-index
is the first `m` entries of this sequence.

## Bundled inductive data

The recursion threads three pieces of information per level:

* the level-`m` instance `D_m : IteratedDiffChartBilinearData g α u_h m`;
* the `MemW1p 2` membership of `D_m.fChartEff` on the chart target (needed by
  the inductive step);
* the ae-vanishing of `D_m.fChartEff` off `chartImagePOUTsupport α` (also
  needed by the inductive step).

These three pieces are bundled into a single dependently-typed packaging
`CanonicalIteratedDataBundle`, with the inductive step
`CanonicalIteratedDataBundle.step` producing the level-`(m+1)` bundle from the
level-`m` bundle and the additional regularity hypotheses required to apply
the polymorphic inductive step.

## Main definitions

* `CanonicalIteratedDataBundle g α u_h m` — the level-`m` bundle.
* `iteratedDiffChartBilinearData_canonical g α u_h dirs_seq m hyp` — the
  canonical level-`m` data instance (extracted from the bundle).

## Main theorems

* `fChartEff_at_level_ae_zero_off_K_alpha` — the structural ae-vanishing,
  unconditional from level `m ≥ 1`.
* `fChartEff_at_level_memWkp_K` — the inductive regularity propagation,
  hypothesis-bearing on a per-step `MemWkp` propagator through `fChartEffStep`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedFChartEffRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStepScaffold
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStep
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The level-`m` direction multi-index from an infinite sequence
`dirs_seq : ℕ → Fin n`: the first `m` entries `(dirs_seq 0, …, dirs_seq (m-1))`. -/
private def dirsOf (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (m : ℕ) :
    Fin m → Fin (Module.finrank ℝ E) :=
  fun i => dirs_seq i.val

@[simp] private lemma dirsOf_zero (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) :
    dirsOf dirs_seq 0 = Fin.elim0 := by
  funext i; exact i.elim0

private lemma dirsOf_succ (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (m : ℕ) :
    dirsOf dirs_seq (m + 1) = Fin.snoc (dirsOf dirs_seq m) (dirs_seq m) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
  · subst hj
    rw [Fin.snoc_castSucc]
    rfl
  · subst hlast
    rw [Fin.snoc_last]
    rfl

/-- The level-`m` canonical bundle: the iterated chart-bilinear data instance
`D_m` together with the two propagated invariants needed to apply the
inductive step at level `m`:

* `D_m.fChartEff ∈ MemW1p 2 chartTargetEuclid α` (needed for the IBP in the
  step);
* `D_m.fChartEff =ᵐ 0` on the `volume`-restriction to
  `chartTargetEuclid α \ chartImagePOUTsupport α` (needed for the chart
  truncation in the step).

The level-`m` direction multi-index is `dirsOf dirs_seq m`. -/
structure CanonicalIteratedDataBundle
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (m : ℕ) where

  data : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m

  directions_eq : data.directions = dirsOf dirs_seq m

  fChartEff_memW1p :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 data.fChartEff
      (chartTargetEuclid (I := I) (M := M) α)

  fChartEff_ae_zero_off_K :
    data.fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ))

namespace CanonicalIteratedDataBundle

/-- The base `m = 0` bundle. Requires:

* `u_h ∈ laplacianDomainPow g 2` (to apply `IteratedDiffChartBilinearData.ofBase`);
* `MemW1p 2` of `base.f_chart` on the chart target (the natural `m = 1`
  base-data regularity);
* ae-vanishing of `base.f_chart` off `K_α` (supplied externally — derivable
  from the base bilinear identity, but the proof is private to its module). -/
def ofBase
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))) :
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq 0 where
  data := IteratedDiffChartBilinearData.ofBase
    (I := I) (M := M) g α hu_h
  directions_eq := by
    funext i; exact i.elim0
  fChartEff_memW1p := h_base_f_chart_memW1p
  fChartEff_ae_zero_off_K := h_base_f_chart_ae_zero

/-- The inductive step `m → m + 1`. Requires the regularity hypotheses on
`u_h.coeFn` at levels `m + 1` and `m + 2` (chart-`H^{m+1}` and chart-`H^{m+2}`),
and the level-`(m+1)` propagated regularity/vanishing of `fChartEffStep`
applied to the level-`m` data. -/
def step
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g}
    {dirs_seq : ℕ → Fin (Module.finrank ℝ E)} {m : ℕ}
    (B_m : CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq m)
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_next_fChartEff_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
          B_m.data.fChartEff (dirs_seq m))
        (chartTargetEuclid (I := I) (M := M) α)) :
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq (m + 1) where
  data := iteratedDiffChartBilinearData_step (I := I) (M := M) g α
    (u_h := u_h) m B_m.data (dirs_seq m)
    h_chart_H_m_plus_1 h_chart_H_m_plus_2
    B_m.fChartEff_memW1p B_m.fChartEff_ae_zero_off_K
  directions_eq := by
    change Fin.snoc B_m.data.directions (dirs_seq m) = dirsOf dirs_seq (m + 1)
    rw [B_m.directions_eq, dirsOf_succ]
  fChartEff_memW1p := h_next_fChartEff_memW1p
  fChartEff_ae_zero_off_K := by
    change fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
        B_m.data.fChartEff (dirs_seq m) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))
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

end CanonicalIteratedDataBundle

/-- Per-level chart-`H` regularity hypotheses for `u_h.coeFn`: at every level
`m`, chart-`H^{m+1}` and chart-`H^{m+2}` are needed by the inductive step. -/
def ChartHRegHyp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (M_max : ℕ) : Prop :=
  ∀ k ≤ M_max,
    MemWkp (d := Module.finrank ℝ E) k 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)

/-- Per-level regularity hypothesis for `fChartEffStep`: chart-`H^1` (`MemW1p`)
of the level-`(m+1)` source from chart-`H^1` of the level-`m` source. This is
the "regularity propagator" for the step; supplied externally. -/
def FChartEffStepW1pHyp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (M_max : ℕ) : Prop :=
  ∀ m < M_max,
    ∀ (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m),
    D_m.directions = dirsOf dirs_seq m →
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D_m.fChartEff
      (chartTargetEuclid (I := I) (M := M) α) →
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
        D_m.fChartEff (dirs_seq m))
      (chartTargetEuclid (I := I) (M := M) α)

/-- The canonical level-`m` bundle, built by induction. Requires:

* `u_h ∈ laplacianDomainPow g 2` (base hypothesis);
* a level-0 packaging of `MemW1p 2 base.f_chart` (call site supplies this);
* a level-0 packaging of ae-vanishing of `base.f_chart` off `K_α`;
* a per-level chart-`H` regularity bundle for `u_h.coeFn` covering levels
  `0, 1, …, m + 2`;
* a per-level `fChartEffStep` `W^{1,2}` propagator for levels `0, …, m - 1`. -/
def canonicalBundle
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (m : ℕ)
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m) :
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq m := by
  induction m with
  | zero =>
      exact CanonicalIteratedDataBundle.ofBase (I := I) (M := M) g α
        dirs_seq hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero
  | succ m ih =>
      have h_chart_H_seq_m : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2) := by
        intro k hk
        exact h_chart_H_seq k (hk.trans (by omega))
      have h_step_propagator_m : FChartEffStepW1pHyp
          (I := I) (M := M) g α u_h dirs_seq m := by
        intro k hk D_k h_dirs h_W1p
        exact h_step_propagator k (hk.trans (Nat.lt_succ_self _)) D_k h_dirs h_W1p
      let B_m := ih h_chart_H_seq_m h_step_propagator_m
      have h_chart_H_m_plus_1 := h_chart_H_seq (m + 1) (by omega)
      have h_chart_H_m_plus_2 := h_chart_H_seq (m + 2) (by omega)
      have h_next_W1p := h_step_propagator m (Nat.lt_succ_self _) B_m.data
        B_m.directions_eq B_m.fChartEff_memW1p
      exact CanonicalIteratedDataBundle.step (I := I) (M := M)
        (g := g) (α := α) (u_h := u_h) (dirs_seq := dirs_seq) (m := m)
        B_m h_chart_H_m_plus_1 h_chart_H_m_plus_2 h_next_W1p

/-- The canonical level-`m` iterated chart-bilinear data instance. -/
def iteratedDiffChartBilinearData_canonical
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (m : ℕ)
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  (canonicalBundle (I := I) (M := M) g α dirs_seq hu_h h_base_f_chart_memW1p
    h_base_f_chart_ae_zero m h_chart_H_seq h_step_propagator).data

/-- **Polymorphic vanishing-off-`K_α`.** The level-`m` effective chart-pulled
source `(iteratedDiffChartBilinearData_canonical … m).fChartEff` vanishes ae on
`chartTargetEuclid α \ chartImagePOUTsupport α`, for any level `m`.

For `m = 0`, this reduces to the supplied base-data vanishing hypothesis.
For `m ≥ 1`, this is unconditional from the indicator structure of
`fChartEffStep` (its definition is literally
`Set.indicator chartImagePOUTsupport α (_)`). -/
theorem fChartEff_at_level_ae_zero_off_K_alpha
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (m : ℕ)
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m) :
    (iteratedDiffChartBilinearData_canonical (I := I) (M := M) g α
        dirs_seq hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero m
        h_chart_H_seq h_step_propagator).fChartEff =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
  (canonicalBundle (I := I) (M := M) g α dirs_seq hu_h h_base_f_chart_memW1p
    h_base_f_chart_ae_zero m h_chart_H_seq h_step_propagator).fChartEff_ae_zero_off_K

/-- Per-level `MemWkp K 2` propagator hypothesis for `fChartEffStep`. The
propagator says: if the level-`m` source is in `MemWkp (K+1) 2`, then the
level-`(m+1)` source (built via `fChartEffStep`) is in `MemWkp K 2`. -/
def FChartEffStepMemWkpHyp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (M_max K : ℕ) : Prop :=
  ∀ (m : ℕ), m < M_max →
    ∀ (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m),
    D_m.directions = dirsOf dirs_seq m →
    MemWkp (d := Module.finrank ℝ E) ((K + (M_max - 1 - m)) + 1) 2
      D_m.fChartEff (chartTargetEuclid (I := I) (M := M) α) →
    MemWkp (d := Module.finrank ℝ E) (K + (M_max - 1 - m)) 2
      (fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
        D_m.fChartEff (dirs_seq m))
      (chartTargetEuclid (I := I) (M := M) α)

/-- The level-`m` bundle with an additional `MemWkp (K + (M - m)) 2` witness on
`data.fChartEff`, threaded inductively. The target regularity level at depth
`m` is `K + (M - m)`. Here `M` is the global maximum index of the family
(the level at which the user requests `MemWkp K 2`). -/
private structure CanonicalBundleWithMemWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (M_max K m : ℕ) extends
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq m where

  fChartEff_memWkp :
    MemWkp (d := Module.finrank ℝ E) (K + (M_max - m)) 2 data.fChartEff
      (chartTargetEuclid (I := I) (M := M) α)

namespace CanonicalBundleWithMemWkp

/-- Base case `m = 0`. The regularity hypothesis is `MemWkp (K + M_max) 2` of
`base.f_chart`. -/
private def ofBase
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (M_max K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + M_max) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq M_max K 0 :=
  { toCanonicalIteratedDataBundle :=
      CanonicalIteratedDataBundle.ofBase (I := I) (M := M) g α dirs_seq hu_h
        h_base_f_chart_memW1p h_base_f_chart_ae_zero
    fChartEff_memWkp := by
      change MemWkp (d := Module.finrank ℝ E) (K + (M_max - 0)) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)
      have h_eq : M_max - 0 = M_max := Nat.sub_zero _
      rw [h_eq]
      exact h_base_f_chart_memWkp }

/-- Inductive step `m → m + 1`. Threads the `MemWkp` regularity using the
per-step propagator. Note: the target regularity level decreases by 1 at each
step, going from `K + (M_max - m)` at level `m` to `K + (M_max - (m+1))` at
level `m + 1`. -/
private def step
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g}
    {dirs_seq : ℕ → Fin (Module.finrank ℝ E)}
    {M_max K m : ℕ}
    (_hm : m + 1 ≤ M_max)
    (B_m : CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq
      M_max K m)
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_step_W1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
          B_m.data.fChartEff (dirs_seq m))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_step_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + (M_max - (m + 1))) 2
        (fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
          B_m.data.fChartEff (dirs_seq m))
        (chartTargetEuclid (I := I) (M := M) α)) :
    CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq
      M_max K (m + 1) :=
  { toCanonicalIteratedDataBundle :=
      CanonicalIteratedDataBundle.step (I := I) (M := M)
        (g := g) (α := α) (u_h := u_h) (dirs_seq := dirs_seq) (m := m)
        B_m.toCanonicalIteratedDataBundle h_chart_H_m_plus_1 h_chart_H_m_plus_2
        h_step_W1p
    fChartEff_memWkp := h_step_memWkp }

end CanonicalBundleWithMemWkp

/-- Build the `MemWkp`-strengthened canonical bundle at level `m ≤ M_max`. The
result has `MemWkp (K + (M_max - m)) 2` of the level-`m` source. -/
private def canonicalBundleWithMemWkp_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (M_max K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + M_max) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (M_max + 2))
    (h_step_W1p : FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq M_max)
    (h_step_memWkp :
      FChartEffStepMemWkpHyp (I := I) (M := M) g α u_h dirs_seq M_max K)
    (m : ℕ) (hm : m ≤ M_max) :
    CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq
      M_max K m := by
  induction m with
  | zero =>
      exact CanonicalBundleWithMemWkp.ofBase (I := I) (M := M) g α dirs_seq
        M_max K hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero
        h_base_f_chart_memWkp
  | succ m ih =>
      have hm_le : m ≤ M_max := (Nat.le_succ _).trans hm
      let B_m := ih hm_le
      have h_chart_H_m_plus_1 := h_chart_H_seq (m + 1) (by omega)
      have h_chart_H_m_plus_2 := h_chart_H_seq (m + 2) (by omega)
      have h_step_w1p_m :=
        h_step_W1p m hm B_m.data B_m.directions_eq B_m.fChartEff_memW1p
      have h_idx_eq : M_max - 1 - m = M_max - (m + 1) := by omega
      have h_idx_eq_2 : K + (M_max - m) = (K + (M_max - 1 - m)) + 1 := by
        omega
      have h_Bm_memWkp := B_m.fChartEff_memWkp
      have h_Bm_memWkp' :
          MemWkp (d := Module.finrank ℝ E) ((K + (M_max - 1 - m)) + 1) 2
            B_m.data.fChartEff
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [← h_idx_eq_2]; exact h_Bm_memWkp
      have h_step_memWkp_m :=
        h_step_memWkp m hm B_m.data B_m.directions_eq h_Bm_memWkp'
      rw [h_idx_eq] at h_step_memWkp_m
      exact CanonicalBundleWithMemWkp.step (I := I) (M := M)
        (g := g) (α := α) (u_h := u_h) (dirs_seq := dirs_seq)
        (M_max := M_max) (K := K) (m := m) hm B_m
        h_chart_H_m_plus_1 h_chart_H_m_plus_2 h_step_w1p_m h_step_memWkp_m

/-- The level-`m` iterated chart-bilinear data instance built from the
`MemWkp`-strengthened canonical bundle. This is the data instance exposed by
the regularity-propagation theorem. -/
def iteratedDiffChartBilinearData_canonicalMemWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (m K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + m) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m)
    (h_step_memWkp :
      FChartEffStepMemWkpHyp (I := I) (M := M) g α u_h dirs_seq m K) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  (canonicalBundleWithMemWkp_aux (I := I) (M := M) g α dirs_seq m K
    hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero h_base_f_chart_memWkp
    h_chart_H_seq h_step_propagator h_step_memWkp m (le_refl _)).data

/-- **Polymorphic `MemWkp K 2` regularity of the level-`m` source.** The
`MemWkp`-tagged level-`m` effective chart-pulled source has `MemWkp K 2`
regularity provided:

* `u_h ∈ laplacianDomainPow g 2` (to apply the base instance);
* `MemW1p 2` and ae-vanishing of `base.f_chart` on the chart target (the level-0
  data invariants);
* `MemWkp (K + m) 2` of `base.f_chart` (the base-level regularity at the
  highest needed rank, recovered from
  `base_f_chart_memWkp_m` by the caller);
* chart-`H` regularity of `u_h.coeFn` up to chart-`H^{m + 2}` (needed for the
  inductive steps);
* a per-step `W^{1,2}` propagator (for assembling the canonical bundle);
* a per-step `MemWkp` propagator (the regularity propagator). -/
theorem fChartEff_at_level_memWkp_K
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (m K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + m) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m)
    (h_step_memWkp :
      FChartEffStepMemWkpHyp (I := I) (M := M) g α u_h dirs_seq m K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (iteratedDiffChartBilinearData_canonicalMemWkp (I := I) (M := M) g α
        dirs_seq m K hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero
        h_base_f_chart_memWkp h_chart_H_seq h_step_propagator
        h_step_memWkp).fChartEff
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_mem := (canonicalBundleWithMemWkp_aux (I := I) (M := M) g α dirs_seq
    m K hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero h_base_f_chart_memWkp
    h_chart_H_seq h_step_propagator h_step_memWkp m (le_refl _)).fChartEff_memWkp
  have h_idx_eq : K + (m - m) = K := by
    rw [Nat.sub_self, Nat.add_zero]
  rw [h_idx_eq] at h_mem
  exact h_mem

end IteratedFChartEffRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
