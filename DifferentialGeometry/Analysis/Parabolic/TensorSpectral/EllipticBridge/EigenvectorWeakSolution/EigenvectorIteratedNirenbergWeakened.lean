import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedRegularityHigher

/-!
# Weakened Nirenberg interior `W^{2,2}` regularity of the iterated mixed partial

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, and a
component multi-index `P₀`, the iterated divergence-form datum
`eigenvectorIteratedTensorChartBilinearData g r s h_atlas i α P₀ m` packages
the `m`-fold-differentiated weak-elliptic identity satisfied by the eigenvector
chart component. Its principal factor is the recursive `m`-fold mixed weak
partial `eigenvectorChartIteratedPartial g r s h_atlas i α P₀ m directions`.

To raise the regularity of that `m`-fold mixed weak partial by two — running the
order-2 interior elliptic engine on it — we need a `TensorChartBilinearH1ComplData`,
the per-component scalar divergence-form datum the engine consumes. The iterated
carrier `eigenvectorIteratedTensorChartBilinearData` is **not** such a datum: it
carries the level index `m` and its principal block is the *level-`(m+1)`* mixed
weak partial `eigenvectorChartIteratedPartial … (m+1) (Fin.cons a directions)`,
which differentiates the new direction `a` innermost.

This module builds the missing bridge. It is the eigenvector/tensor mirror of
the scalar campaign's weakened Nirenberg interior module
(`iteratedChartBilinearH1ComplData_weak`,
`iteratedDerivedChartBilinear_memWkp_two_two_interior_weakened`).

## The bridge

`eigenvectorIteratedTensorChartBilinearData_toData` converts the iterated
carrier `D_m` into a genuine `TensorChartBilinearH1ComplData`, under the single
regularity hypothesis chart-`H^{m+1}` of the eigenvector chart component. Its
chart component `u_chart` is the `m`-fold mixed weak partial
`eigenvectorChartIteratedPartial … m D_m.directions`, its right-hand side
`f_chart` is the carrier's effective `L²` source `D_m.fChartEff`, and its weak
partials `weak_partial j` are the canonical chosen weak `j`-partials of the
`m`-fold mixed weak partial. The level-`(m+1)` principal block of the carrier's
variational identity is re-expressed as those chosen weak partials via the
polymorphic Schwarz reindexing
`eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae`.

## Main definitions

* `eigenvectorIteratedTensorChartBilinearData_toData` — the bridge: an iterated
  carrier `D_m`, together with chart-`H^{m+1}` of the chart component, becomes a
  `TensorChartBilinearH1ComplData` for the `m`-fold mixed weak partial.

## Main theorems

* `eigenvectorChartIteratedPartial_memWkp_two_two` — the global `W^{2,2}` of the
  `m`-fold mixed weak partial: the order-2 interior elliptic engine applied to
  `eigenvectorIteratedTensorChartBilinearData_toData D_m h_parent` delivers
  interior `W^{2,2}` on a precompact subdomain, which the support-aware
  promotion `MemWkp_of_memWkp_precompact_of_ae_zero_off_compact` raises to
  global `W^{2,2}` of the chart target.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The bridge from the iterated carrier to a `TensorChartBilinearH1ComplData`

The order-2 interior elliptic engine consumes a per-component scalar
divergence-form datum `TensorChartBilinearH1ComplData g r s α P₀` — a thin
wrapper whose single field `toChartData` is the scalar `ChartBilinearH1ComplData`.
The iterated carrier `eigenvectorIteratedTensorChartBilinearData g r s h_atlas
i α P₀ m` is not such a datum: it carries the level index `m` and its principal
block is the level-`(m+1)` mixed weak partial. The definition below performs the
conversion, under chart-`H^{m+1}` of the eigenvector chart component. -/

/-- The underlying scalar `ChartBilinearH1ComplData` of
`eigenvectorIteratedTensorChartBilinearData_toData`: the per-component scalar
divergence-form datum for the `m`-fold mixed weak partial. The five data fields
are discharged exactly as described in the documentation of
`eigenvectorIteratedTensorChartBilinearData_toData`. -/
private def eigenvectorIteratedChartBilinearH1ComplData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart :=
    eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s h_atlas i α P₀ m D_m.directions
  f_chart := D_m.fChartEff
  weak_partial := fun j =>
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m D_m.directions)
      (chartTargetEuclid (I := I) (M := M) α)
  u_chart_memLp_weighted := by
      -- Weighted `MemLp 2` of the `m`-fold mixed weak partial: from the
      -- unconditional plain-volume membership, upgraded via the compact-support
      -- weighted-`L²` lemma. The `m`-fold mixed partial is a.e. zero off the
      -- compact partition-of-unity kernel.
      set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
      have hK_compact : IsCompact K :=
        chartPouKernel_isCompact (I := I) (M := M) α
      have hK_meas : MeasurableSet K :=
        chartPouKernel_measurableSet (I := I) (M := M) α
      have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
      -- The `m`-fold mixed weak partial is `MemLp 2` of the plain volume
      -- restricted to the chart target (unconditional).
      have h_plain : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m D_m.directions) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        eigenvectorChartIteratedPartial_memLp_volume
          (I := I) (M := M) g r s h_atlas i α P₀ m D_m.directions
      -- The `m`-fold mixed weak partial is a.e. zero off the kernel.
      have h_off : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ K → eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m D_m.directions y = 0 := by
        -- `_ae_zero_off_chartPouKernel` is an a.e. equality on the open
        -- complement `chartTargetEuclid α \ K`; rephrase it as an a.e.
        -- implication on the chart target.
        have h_ae := eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ m D_m.directions
        have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
        have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \ K) :=
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff hK_meas
        rw [ae_restrict_iff' hΩ_meas]
        rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at h_ae
        filter_upwards [h_ae] with y hy
        intro hy_chart hy_off
        exact hy ⟨hy_chart, hy_off⟩
      exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
        (I := I) (M := M) g α hK_compact hK_meas hK_in h_off h_plain
  f_chart_memLp_weighted := D_m.fChartEff_memLp_weighted
  weak_partial_locally_memLp := by
      -- Local `MemLp 2` of `chosenWeakPartial' 2 j (m-fold mixed partial)`:
      -- from `MemWkp 1 2` of the `m`-fold mixed partial (the polymorphic
      -- regularity bridge at `k = 1`) via `chosenWeakPartial'_memLp_of_mem`.
      intro j K hK_compact hK_in
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (1 + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [Nat.add_comm 1 m]
        exact h_parent
      have h_memWkp_one :=
        eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s h_atlas i α P₀ m 1 h_parent' D_m.directions
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_memWkp_one
      have h_chosen_memLp :=
        chosenWeakPartial'_memLp_of_mem h_memWkp_one j
      -- Restrict the chart-target `L²` membership to the compact subset `K`.
      have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
      have h_eq : ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K =
          (volume : Measure EuclN).restrict K := by
        rw [Measure.restrict_restrict hK_meas]
        congr 1
        exact Set.inter_eq_self_of_subset_left hK_in
      rw [← h_eq]
      exact h_chosen_memLp.restrict K
  weak_partial_isWeakPartial := by
      -- Each chosen weak `j`-partial is a genuine weak `j`-partial of the
      -- `m`-fold mixed partial, which lies in `W^{1,2}` of the chart target.
      intro j
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (1 + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [Nat.add_comm 1 m]
        exact h_parent
      have h_memWkp_one :=
        eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s h_atlas i α P₀ m 1 h_parent' D_m.directions
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_memWkp_one
      exact chosenWeakPartial'_isWeakPartial_of_mem h_memWkp_one j
  variational_identity := by
      -- The carrier's `m`-fold-differentiated variational identity, with the
      -- level-`(m+1)` principal block re-expressed via the polymorphic Schwarz
      -- reindexing as chosen weak partials of the `m`-fold mixed partial.
      classical
      intro ψ hψ hψ_cs hψ_supp
      have h_in := D_m.m_diff_variational_identity ψ hψ hψ_cs hψ_supp
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      -- The polymorphic Schwarz reindexing in every new direction `a`.
      have h_schwarz : ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) (Fin.cons a D_m.directions)
            =ᵐ[(volume : Measure EuclN).restrict Ω]
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m D_m.directions) Ω := fun a =>
        eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae
          (I := I) (M := M) g r s h_atlas i α P₀ m D_m.directions a h_parent
      -- Re-express the principal integral via the Schwarz reindexing.
      have h_principal_eq :
          (∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a b y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s h_atlas i α P₀ (m + 1)
                    (Fin.cons a D_m.directions) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
            ∂(volume : Measure EuclN)) =
          ∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a b y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s h_atlas i α P₀ m D_m.directions) Ω y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
            ∂(volume : Measure EuclN) := by
        refine MeasureTheory.integral_congr_ae ?_
        have h_combined : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (m + 1)
                (Fin.cons a D_m.directions) y =
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_atlas i α P₀ m D_m.directions) Ω y := by
          rw [ae_all_iff]
          intro a
          filter_upwards [h_schwarz a] with y hy
          exact hy
        filter_upwards [h_combined] with y hy
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [hy a]
      rw [h_principal_eq] at h_in
      exact h_in

/-- **The iterated carrier as a `TensorChartBilinearH1ComplData`.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, a
component multi-index `P₀`, a level `m : ℕ`, an iterated carrier
`D_m : eigenvectorIteratedTensorChartBilinearData g r s h_atlas i α P₀ m`, and
chart-`H^{m+1}` regularity `h_parent` of the eigenvector chart component, this is
the per-component scalar divergence-form datum
`TensorChartBilinearH1ComplData g r s α P₀` whose

* chart component `u_chart` is the `m`-fold mixed weak partial
  `eigenvectorChartIteratedPartial g r s h_atlas i α P₀ m D_m.directions`;
* right-hand side `f_chart` is the carrier's effective `L²` source `D_m.fChartEff`;
* weak partials `weak_partial j` are the canonical chosen weak `j`-partials of
  the `m`-fold mixed weak partial.

The five data fields are discharged as in the scalar campaign's
`iteratedChartBilinearH1ComplData_weak`: the weighted `L²` of `u_chart` from the
unconditional plain-volume `eigenvectorChartIteratedPartial_memLp_volume`
upgraded via the compact-support weighted-`L²` lemma; the weighted `L²` of
`f_chart` is the carrier field; the local `L²` of every weak partial and the
weak-partial-derivative data follow from the polymorphic regularity bridge
`eigenvectorChartIteratedPartial_memWkp_of_memWkp` at `k = 1`; the variational
identity is the carrier's `m_diff_variational_identity` with the level-`(m+1)`
principal block re-expressed via the polymorphic Schwarz reindexing
`eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae`.

This is the eigenvector/tensor mirror of the scalar campaign's
`iteratedChartBilinearH1ComplData_weak`. -/
def eigenvectorIteratedTensorChartBilinearData_toData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ where
  toChartData :=
    eigenvectorIteratedChartBilinearH1ComplData
      (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent

/-! ## Global `W^{2,2}` of the iterated mixed weak partial

Running the order-2 interior elliptic engine on the bridged datum
`eigenvectorIteratedTensorChartBilinearData_toData D_m h_parent` delivers
interior `W^{2,2}` of the `m`-fold mixed weak partial on a precompact subdomain.
The support-aware promotion raises that interior regularity to global `W^{2,2}`
of the chart target, because the `m`-fold mixed weak partial vanishes almost
everywhere off the compact partition-of-unity kernel. -/

/-- **Global `W^{2,2}` of the iterated mixed weak partial.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, an eigenbasis index `i`, a chart center `α : M`, a
component multi-index `P₀`, a level `m : ℕ`, a direction multi-index
`directions`, an iterated carrier `D_m` whose direction multi-index is
`directions`, and chart-`H^{m+1}` regularity of the eigenvector chart component,
the `m`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s h_atlas
i α P₀ m directions` lies in `MemWkp 2 2 … (chartTargetEuclid α)` — it has global
`W^{2,2}` regularity on the chart target.

The proof bridges the iterated carrier `D_m` into a genuine
`TensorChartBilinearH1ComplData` via `eigenvectorIteratedTensorChartBilinearData_toData`,
applies the order-2 interior elliptic engine
`tensorChartBilinear_chartComponent_regularity_of_data` for interior `W^{2,2}` on
a precompact subdomain `Ω''` (a thickening of the compact partition-of-unity
kernel inside the chart target), and promotes that interior regularity to global
`W^{2,2}` of the chart target via the support-aware promotion
`MemWkp_of_memWkp_precompact_of_ae_zero_off_compact` — the `m`-fold mixed weak
partial vanishes almost everywhere off the compact kernel.

This is the eigenvector/tensor mirror of the scalar campaign's
`iteratedDerivedChartBilinear_memWkp_two_two_interior_weakened` (followed by the
support-aware global promotion). -/
theorem eigenvectorChartIteratedPartial_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_dir : D_m.directions = directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m directions)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The bridged per-component scalar divergence-form datum.
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorIteratedTensorChartBilinearData_toData
      (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent
    with hD_def
  -- `D.u_chart` is, definitionally, the `m`-fold mixed weak partial along
  -- `D_m.directions`.
  have hD_u_chart : D.u_chart =
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m D_m.directions := rfl
  -- The compact partition-of-unity kernel and its enclosing open chart target.
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- A closed thickening of `K` of radius `R_α` inside the chart target.
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  -- The precompact interior subdomain `Ω'' := thickening (R_α / 2) K`.
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  -- `closure Ω'' ⊆ cthickening (R_α / 2) K ⊆ cthickening R_α K ⊆ chart target`.
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (R_α / 2) K :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_half_in_chart : Metric.cthickening (R_α / 2) K ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (R_α / 2) ≤ R_α := by linarith
    exact (Metric.cthickening_mono hle K).trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_half_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  -- The difference-quotient room radius `R₀ := R_α / 4`.
  set R₀ : ℝ := R_α / 4 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    -- `cthickening R₀ (closure Ω'') ⊆ cthickening R₀ (cthickening (R_α/2) K)`
    -- `⊆ cthickening (R₀ + R_α/2) K ⊆ cthickening R_α K ⊆ chart target`.
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) ⊆
        Metric.cthickening (R₀ + R_α / 2) K := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + R_α / 2) K ⊆
        Metric.cthickening R_α K := by
      have hle : R₀ + R_α / 2 ≤ R_α := by rw [hR₀_def]; linarith
      exact Metric.cthickening_mono hle K
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  -- The order-2 interior elliptic engine: `D.u_chart` lies in `W^{1,2}(Ω'')`
  -- and every weak partial `D.weak_partial j` lies in `W^{1,2}(Ω'')`.
  obtain ⟨h_uChart_memW1p, h_wp_memW1p⟩ :=
    tensorChartBilinear_chartComponent_regularity_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  -- Assemble `MemWkp 2 2` of `D.u_chart` on `Ω''`: `W^{1,2}` plus chart-`H¹`
  -- of every chosen weak partial (which agrees a.e. with `D.weak_partial j`).
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p, fun j => ?_⟩
    -- The canonical chosen weak `j`-partial of `D.u_chart` over `Ω''` agrees
    -- a.e. with `D.weak_partial j`, which lies in `W^{1,2}(Ω'')`.
    have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
      fun y hy => h_closureΩ''_in_chart (subset_closure hy)
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j (D.weak_partial j) D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial j)
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p j).1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
            D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_memW1p j)
  -- Rewrite the interior `W^{2,2}` to be about the `m`-fold mixed weak partial.
  rw [hD_u_chart] at h_uChart_memWkp_two_Ω''
  -- The `m`-fold mixed weak partial is `MemLp 2` of the plain volume restricted
  -- to the chart target (the global `L²` input for the promotion).
  have h_global_Lp : MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s h_atlas i α P₀ m D_m.directions) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    eigenvectorChartIteratedPartial_memLp_volume
      (I := I) (M := M) g r s h_atlas i α P₀ m D_m.directions
  -- The `m`-fold mixed weak partial is a.e. zero off the compact kernel `K`.
  have h_ae_zero : eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s h_atlas i α P₀ m D_m.directions
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K)] 0 :=
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P₀ m D_m.directions
  -- Promote the interior `W^{2,2}(Ω'')` to global `W^{2,2}` of the chart target.
  have h_global :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m D_m.directions)
        (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
      h_global_Lp h_ae_zero h_uChart_memWkp_two_Ω''
  -- Rewrite the direction multi-index `D_m.directions` to `directions`.
  rw [h_dir] at h_global
  exact h_global

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The bridge produces a genuine `TensorChartBilinearH1ComplData`. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
  eigenvectorIteratedTensorChartBilinearData_toData
    (I := I) (M := M) g r s h_atlas i α P₀ D_m h_parent

/-- The global `W^{2,2}` headline produces `MemWkp 2 2` of the `m`-fold mixed
weak partial on the chart target. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s h_atlas i α P₀ m)
    (h_dir : D_m.directions = directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m directions)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartIteratedPartial_memWkp_two_two
    g r s h_atlas i α P₀ directions D_m h_dir h_parent

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations below re-key the bridge and the global `W^{2,2}` headline onto
the intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`.
The proofs transfer verbatim with the chart-locality-free dependency twins
substituted for their originals. -/

/-- Chart-locality-free twin of `eigenvectorIteratedChartBilinearH1ComplData`. -/
private def eigenvectorIteratedChartBilinearH1ComplData_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart :=
    eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
      g r s i α P₀ m D_m.directions
  f_chart := D_m.fChartEff
  weak_partial := fun j =>
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m D_m.directions)
      (chartTargetEuclid (I := I) (M := M) α)
  u_chart_memLp_weighted := by
      -- Weighted `MemLp 2` of the `m`-fold mixed weak partial: from the
      -- unconditional plain-volume membership, upgraded via the compact-support
      -- weighted-`L²` lemma. The `m`-fold mixed partial is a.e. zero off the
      -- compact partition-of-unity kernel.
      set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
      have hK_compact : IsCompact K :=
        chartPouKernel_isCompact (I := I) (M := M) α
      have hK_meas : MeasurableSet K :=
        chartPouKernel_measurableSet (I := I) (M := M) α
      have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
      -- The `m`-fold mixed weak partial is `MemLp 2` of the plain volume
      -- restricted to the chart target (unconditional).
      have h_plain : MemLp (eigenvectorChartIteratedPartial_unconditional
          (I := I) (M := M)
          g r s i α P₀ m D_m.directions) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        eigenvectorChartIteratedPartial_unconditional_memLp_volume
          (I := I) (M := M) g r s i α P₀ m D_m.directions
      -- The `m`-fold mixed weak partial is a.e. zero off the kernel.
      have h_off : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ K → eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m D_m.directions y = 0 := by
        -- `_ae_zero_off_chartPouKernel` is an a.e. equality on the open
        -- complement `chartTargetEuclid α \ K`; rephrase it as an a.e.
        -- implication on the chart target.
        have h_ae := eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ m D_m.directions
        have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
        have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \ K) :=
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff hK_meas
        rw [ae_restrict_iff' hΩ_meas]
        rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at h_ae
        filter_upwards [h_ae] with y hy
        intro hy_chart hy_off
        exact hy ⟨hy_chart, hy_off⟩
      exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
        (I := I) (M := M) g α hK_compact hK_meas hK_in h_off h_plain
  f_chart_memLp_weighted := D_m.fChartEff_memLp_weighted
  weak_partial_locally_memLp := by
      -- Local `MemLp 2` of `chosenWeakPartial' 2 j (m-fold mixed partial)`:
      -- from `MemWkp 1 2` of the `m`-fold mixed partial (the polymorphic
      -- regularity bridge at `k = 1`) via `chosenWeakPartial'_memLp_of_mem`.
      intro j K hK_compact hK_in
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (1 + m) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [Nat.add_comm 1 m]
        exact h_parent
      have h_memWkp_one :=
        eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ m 1 h_parent' D_m.directions
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_memWkp_one
      have h_chosen_memLp :=
        chosenWeakPartial'_memLp_of_mem h_memWkp_one j
      -- Restrict the chart-target `L²` membership to the compact subset `K`.
      have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
      have h_eq : ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K =
          (volume : Measure EuclN).restrict K := by
        rw [Measure.restrict_restrict hK_meas]
        congr 1
        exact Set.inter_eq_self_of_subset_left hK_in
      rw [← h_eq]
      exact h_chosen_memLp.restrict K
  weak_partial_isWeakPartial := by
      -- Each chosen weak `j`-partial is a genuine weak `j`-partial of the
      -- `m`-fold mixed partial, which lies in `W^{1,2}` of the chart target.
      intro j
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (1 + m) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [Nat.add_comm 1 m]
        exact h_parent
      have h_memWkp_one :=
        eigenvectorChartIteratedPartial_unconditional_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ m 1 h_parent' D_m.directions
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_memWkp_one
      exact chosenWeakPartial'_isWeakPartial_of_mem h_memWkp_one j
  variational_identity := by
      -- The carrier's `m`-fold-differentiated variational identity, with the
      -- level-`(m+1)` principal block re-expressed via the polymorphic Schwarz
      -- reindexing as chosen weak partials of the `m`-fold mixed partial.
      classical
      intro ψ hψ hψ_cs hψ_supp
      have h_in := D_m.m_diff_variational_identity ψ hψ hψ_cs hψ_supp
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      -- The polymorphic Schwarz reindexing in every new direction `a`.
      have h_schwarz : ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a D_m.directions)
            =ᵐ[(volume : Measure EuclN).restrict Ω]
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m D_m.directions) Ω := fun a =>
        eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae_unconditional
          (I := I) (M := M) g r s i α P₀ m D_m.directions a h_parent
      -- Re-express the principal integral via the Schwarz reindexing.
      have h_principal_eq :
          (∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a b y *
                  eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                    g r s i α P₀ (m + 1)
                    (Fin.cons a D_m.directions) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
            ∂(volume : Measure EuclN)) =
          ∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a b y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                    (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                      g r s i α P₀ m D_m.directions) Ω y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
            ∂(volume : Measure EuclN) := by
        refine MeasureTheory.integral_congr_ae ?_
        have h_combined : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (m + 1)
                (Fin.cons a D_m.directions) y =
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                  g r s i α P₀ m D_m.directions) Ω y := by
          rw [ae_all_iff]
          intro a
          filter_upwards [h_schwarz a] with y hy
          exact hy
        filter_upwards [h_combined] with y hy
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [hy a]
      rw [h_principal_eq] at h_in
      exact h_in

/-- Chart-locality-free twin of
`eigenvectorIteratedTensorChartBilinearData_toData`. -/
def eigenvectorIteratedTensorChartBilinearData_toData_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ where
  toChartData :=
    eigenvectorIteratedChartBilinearH1ComplData_unconditional
      (I := I) (M := M) g r s i α P₀ D_m h_parent

/-- Chart-locality-free twin of
`eigenvectorChartIteratedPartial_memWkp_two_two`. -/
theorem eigenvectorChartIteratedPartial_memWkp_two_two_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData_unconditional (I := I) (M := M)
      g r s i α P₀ m)
    (h_dir : D_m.directions = directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m directions)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- The bridged per-component scalar divergence-form datum.
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorIteratedTensorChartBilinearData_toData_unconditional
      (I := I) (M := M) g r s i α P₀ D_m h_parent
    with hD_def
  -- `D.u_chart` is, definitionally, the `m`-fold mixed weak partial along
  -- `D_m.directions`.
  have hD_u_chart : D.u_chart =
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m D_m.directions := rfl
  -- The compact partition-of-unity kernel and its enclosing open chart target.
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  -- A closed thickening of `K` of radius `R_α` inside the chart target.
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  -- The precompact interior subdomain `Ω'' := thickening (R_α / 2) K`.
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  -- `closure Ω'' ⊆ cthickening (R_α / 2) K ⊆ cthickening R_α K ⊆ chart target`.
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (R_α / 2) K :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_half_in_chart : Metric.cthickening (R_α / 2) K ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (R_α / 2) ≤ R_α := by linarith
    exact (Metric.cthickening_mono hle K).trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_half_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  -- The difference-quotient room radius `R₀ := R_α / 4`.
  set R₀ : ℝ := R_α / 4 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    -- `cthickening R₀ (closure Ω'') ⊆ cthickening R₀ (cthickening (R_α/2) K)`
    -- `⊆ cthickening (R₀ + R_α/2) K ⊆ cthickening R_α K ⊆ chart target`.
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) ⊆
        Metric.cthickening (R₀ + R_α / 2) K := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + R_α / 2) K ⊆
        Metric.cthickening R_α K := by
      have hle : R₀ + R_α / 2 ≤ R_α := by rw [hR₀_def]; linarith
      exact Metric.cthickening_mono hle K
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  -- The order-2 interior elliptic engine: `D.u_chart` lies in `W^{1,2}(Ω'')`
  -- and every weak partial `D.weak_partial j` lies in `W^{1,2}(Ω'')`.
  obtain ⟨h_uChart_memW1p, h_wp_memW1p⟩ :=
    tensorChartBilinear_chartComponent_regularity_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  -- Assemble `MemWkp 2 2` of `D.u_chart` on `Ω''`: `W^{1,2}` plus chart-`H¹`
  -- of every chosen weak partial (which agrees a.e. with `D.weak_partial j`).
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p, fun j => ?_⟩
    -- The canonical chosen weak `j`-partial of `D.u_chart` over `Ω''` agrees
    -- a.e. with `D.weak_partial j`, which lies in `W^{1,2}(Ω'')`.
    have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
      fun y hy => h_closureΩ''_in_chart (subset_closure hy)
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j (D.weak_partial j) D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial j)
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p j).1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
            D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_memW1p j)
  -- Rewrite the interior `W^{2,2}` to be about the `m`-fold mixed weak partial.
  rw [hD_u_chart] at h_uChart_memWkp_two_Ω''
  -- The `m`-fold mixed weak partial is `MemLp 2` of the plain volume restricted
  -- to the chart target (the global `L²` input for the promotion).
  have h_global_Lp : MemLp (eigenvectorChartIteratedPartial_unconditional
      (I := I) (M := M)
      g r s i α P₀ m D_m.directions) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    eigenvectorChartIteratedPartial_unconditional_memLp_volume
      (I := I) (M := M) g r s i α P₀ m D_m.directions
  -- The `m`-fold mixed weak partial is a.e. zero off the compact kernel `K`.
  have h_ae_zero : eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
      g r s i α P₀ m D_m.directions
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K)] 0 :=
    eigenvectorChartIteratedPartial_unconditional_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m D_m.directions
  -- Promote the interior `W^{2,2}(Ω'')` to global `W^{2,2}` of the chart target.
  have h_global :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m D_m.directions)
        (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
      h_global_Lp h_ae_zero h_uChart_memWkp_two_Ω''
  -- Rewrite the direction multi-index `D_m.directions` to `directions`.
  rw [h_dir] at h_global
  exact h_global

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
