import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedScaffold
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.TwiceDerivedData

/-!
# Structural machinery of the arbitrary-order eigenvector chart-component bootstrap

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the eigenvector
chart component `eigenvectorChartComponentFun` and its recursive `m`-fold mixed
weak partials `eigenvectorChartIteratedPartial` carry the iterated Sobolev
structure of the resolvent eigenvector.

This module collects the **Schwarz-free structural backbone** of the
arbitrary-order interior-regularity bootstrap — the two reindexing /
order-assembly lemmas that mediate between the level-indexed iterated mixed weak
partials and the chart-`H^k` regularity of the chart component:

* `eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae` — the
  polymorphic Schwarz reindexing identity: the `(m + 1)`-fold mixed weak partial
  along `Fin.cons a dirs` (which differentiates the new direction `a` innermost)
  agrees a.e. with the chosen weak `a`-partial of the `m`-fold mixed weak
  partial along `dirs`. This is the eigenvector/tensor mirror of the scalar
  campaign's `chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae_weak`;
  it lets the `Fin.cons`-indexed principal block of the iterated
  divergence-form datum be re-expressed in genuine-chosen-weak-partial form.
* `eigenvectorChartComponent_memWkp_m_plus_two_of_iterated` — the structural
  order-assembly: from chart-`H²` of every `m`-fold mixed weak partial and
  chart-`H¹` of every `j`-fold mixed weak partial for `j ≤ m`, the eigenvector
  chart component lies in chart-`H^{m+2}`. This is the eigenvector/tensor mirror
  of the scalar `chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two`. It
  raises the Sobolev order of the chart component by two, given the per-level
  regularity that the order-2 interior engine produces.

Both lemmas are **unconditional structural facts** — pure manipulations of the
iterated `MemWkp` predicate and the recursive definition of
`eigenvectorChartIteratedPartial`, established from committed infrastructure.

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
open DifferentialGeometry.Analysis.Laplacian.TwiceDerivedChartBilinearH1ComplData
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The last entry of `Fin.cons a dirs` at length `m + 2` is the last entry of
`dirs`. -/
private lemma fin_cons_last_succ
    {a : Fin (Module.finrank ℝ E)} {m : ℕ}
    (dirs : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    (Fin.cons a dirs : Fin (m + 2) → Fin (Module.finrank ℝ E))
        (Fin.last (m + 1)) = dirs (Fin.last m) := by
  have h : (Fin.last (m + 1) : Fin (m + 2)) = (Fin.last m).succ := by
    ext; simp [Fin.last]
  rw [h, Fin.cons_succ]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The initial segment of `Fin.cons a dirs` at length `m + 2` is
`Fin.cons a (Fin.init dirs)`. -/
private lemma fin_init_cons
    {a : Fin (Module.finrank ℝ E)} {m : ℕ}
    (dirs : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    Fin.init (Fin.cons a dirs : Fin (m + 2) → Fin (Module.finrank ℝ E)) =
      Fin.cons a (Fin.init dirs) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · simp [Fin.init]
  · intro k
    simp [Fin.init, Fin.cons_succ]

/-- **Polymorphic Schwarz reindexing of the eigenvector iterated mixed weak
partial.**

Re-keyed onto the chart-locality-free eigenvector chart component
`eigenvectorChartComponentFun` — itself built from the intrinsic eigenbasis
vector `tensorResolventEigenbasisVec
(tensorResolventL2_isCompactOperator g r s) i` — via its recursive `m`-fold
mixed weak partial `eigenvectorChartIteratedPartial`.

For every level `m`, direction multi-index `dirs : Fin m → Fin n`, and new
direction `a`, given global chart-`H^{m+1}` regularity of the chart-locality-free
eigenvector chart component, the `(m + 1)`-fold mixed weak partial
`eigenvectorChartIteratedPartial g r s i α P₀ (m + 1)
(Fin.cons a dirs)` — which differentiates `a` innermost — agrees almost
everywhere on the chart target with the chosen weak `a`-partial
`chosenWeakPartial' 2 a (eigenvectorChartIteratedPartial … m dirs)`
of the `m`-fold mixed weak partial along `dirs`. -/
theorem eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E))
      (a : Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a dirs)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m
  induction m with
  | zero =>
      intro dirs a _h_parent
      have h_lhs_eq :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ 1 (Fin.cons a dirs) =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ 0 dirs)
              (chartTargetEuclid (I := I) (M := M) α) := by
        rw [eigenvectorChartIteratedPartial_succ]
        have h_last : (Fin.cons a dirs : Fin 1 → _) (Fin.last 0) = a := rfl
        have h_init : Fin.init (Fin.cons a dirs : Fin 1 → _) = dirs := by
          funext k; exact (k.elim0)
        rw [h_last, h_init]
      exact Filter.EventuallyEq.of_eq h_lhs_eq
  | succ m ih =>
      intro dirs a h_parent
      classical
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_last : (Fin.cons a dirs : Fin (m + 2) → Fin (Module.finrank ℝ E))
          (Fin.last (m + 1)) = dirs (Fin.last m) := fin_cons_last_succ dirs
      have h_init : Fin.init (Fin.cons a dirs :
          Fin (m + 2) → Fin (Module.finrank ℝ E)) = Fin.cons a (Fin.init dirs) :=
        fin_init_cons dirs
      have h_lhs_unfold :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) (Fin.cons a dirs) =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init dirs))) Ω := by
        rw [eigenvectorChartIteratedPartial_succ, h_last, h_init]
      have h_dirs_unfold :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) dirs =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init dirs)) Ω := by
        rw [eigenvectorChartIteratedPartial_succ]
      have h_parent_for_ih :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (m + 1) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            Ω :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
          (by omega) h_parent
      have h_ih := ih (Fin.init dirs) a h_parent_for_ih
      have h_propagate :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init dirs))) Ω
            =ᵐ[(volume : Measure EuclN).restrict Ω]
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init dirs)) Ω) Ω :=
        chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ih (dirs (Fin.last m))
      have h_inner_memWkp_2_2 :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m (Fin.init dirs)) Ω := by
        have h_parent_2_m :
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) (2 + m) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s i α P₀) Ω := by
          have h_eq : (2 : ℕ) + m = m + 2 := by ring
          rw [h_eq]; exact h_parent
        exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ m 2 h_parent_2_m (Fin.init dirs)
      have h_swap :=
        chosenWeakPartial'_swap_ae_of_memWkp_two
          hΩ_open h_inner_memWkp_2_2 a (dirs (Fin.last m))
      have h_final :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init dirs)) Ω) Ω =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) dirs) Ω := by
        rw [← h_dirs_unfold]
      calc eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) (Fin.cons a dirs)
          = chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init dirs))) Ω :=
            h_lhs_unfold
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init dirs)) Ω) Ω := h_propagate
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init dirs)) Ω) Ω := h_swap
        _ = chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) dirs) Ω := h_final

/-- Polymorphic per-direction-count engine for the order assembly, keyed onto the
chart-locality-free eigenvector chart component — built from the intrinsic
eigenbasis vector `tensorResolventEigenbasisVec
(tensorResolventL2_isCompactOperator g r s) i` — via its recursive mixed weak
partial `eigenvectorChartIteratedPartial`. For any `m, j : ℕ` and any
`j`-direction multi-index `dirs`, if every `(j + 1)`-fold mixed partial lies in
chart-`H^{m+1}` and every `j`-fold mixed partial lies in chart-`H¹`, then the
`j`-fold mixed weak partial in directions `dirs` lies in chart-`H^{m+2}`. -/
private theorem eigenvectorIteratedPartial_memWkp_of_chartH_at_all_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ) (j : ℕ) (dirs : Fin j → Fin (Module.finrank ℝ E)),
      (∀ idx_all : Fin j → Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx_all)
          (chartTargetEuclid (I := I) (M := M) α)) →
      (∀ idx_next : Fin (j + 1) → Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (j + 1) idx_next)
          (chartTargetEuclid (I := I) (M := M) α)) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m j dirs h_w1p_j h_memWkp_succ
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
  refine ⟨?_, fun a => ?_⟩
  · have h := h_w1p_j dirs
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h
    exact h
  · have h_succ_eq :
        eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (j + 1) (Fin.snoc dirs a) =
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) := by
      rw [eigenvectorChartIteratedPartial_succ]
      have h_last : (Fin.snoc dirs a :
          Fin (j + 1) → Fin (Module.finrank ℝ E)) (Fin.last j) = a :=
        Fin.snoc_last _ _
      have h_init : Fin.init (Fin.snoc dirs a :
          Fin (j + 1) → Fin (Module.finrank ℝ E)) = dirs := Fin.init_snoc _ _
      rw [h_last, h_init]
    have h_next := h_memWkp_succ (Fin.snoc dirs a)
    rw [h_succ_eq] at h_next
    exact h_next

/-- **Structural order-assembly: chart-`H^{m+2}` of the eigenvector chart
component.**

Keyed onto the chart-locality-free eigenvector chart component
`eigenvectorChartComponentFun` — built from the intrinsic eigenbasis vector
`tensorResolventEigenbasisVec (tensorResolventL2_isCompactOperator g r s) i` —
and its recursive mixed weak partial `eigenvectorChartIteratedPartial`.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, and an order
`m : ℕ`, the chart-locality-free eigenvector chart component lies in
chart-`H^{m+2}` on the chart target, provided:

* chart-`H¹` of every chosen `j`-fold mixed weak partial for every `j ≤ m`;
* chart-`H²` of every chosen `m`-fold mixed weak partial — the per-direction
  chart-`H²` regularity that the order-2 interior engine delivers. -/
theorem eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_general : ∀ (gap : ℕ) (j : ℕ), j + gap = m →
      ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (gap + 2) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro gap
    induction gap with
    | zero =>
        intro j hj dirs
        subst hj
        simpa using h_top_memWkp_two dirs
    | succ gap ih =>
        intro j hj dirs
        have h_engine :=
          eigenvectorIteratedPartial_memWkp_of_chartH_at_all_indices
            (I := I) (M := M) g r s i α P₀ (gap + 1) j dirs
        have hj_le : j ≤ m := by omega
        have h_w1p : ∀ idx_all : Fin j → Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx_all)
              (chartTargetEuclid (I := I) (M := M) α) :=
          fun idx_all => h_intermediate_w1p j hj_le idx_all
        have h_succ : ∀ idx_next : Fin (j + 1) → Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) ((gap + 1) + 1) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (j + 1) idx_next)
              (chartTargetEuclid (I := I) (M := M) α) := by
          intro idx_next
          have h_ih := ih (j + 1) (by omega) idx_next
          have h_eq : (gap + 1) + 1 = gap + 2 := by ring
          rw [h_eq]
          exact h_ih
        exact h_engine h_w1p h_succ
  have h_final := h_general m 0 (by omega) Fin.elim0
  rw [eigenvectorChartIteratedPartial_zero] at h_final
  exact h_final

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- Elaboration test: the Schwarz reindexing identity re-expresses the
`Fin.cons`-indexed chart-locality-free iterated mixed partial as a chosen weak
partial. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (a : Fin (Module.finrank ℝ E))
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a dirs)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae
    g r s i α P₀ m dirs a h_parent

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
