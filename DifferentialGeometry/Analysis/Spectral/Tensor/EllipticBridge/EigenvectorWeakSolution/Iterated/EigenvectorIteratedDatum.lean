import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedData

/-!
# Standalone iterated divergence-form datum for the eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the chart
`P₀`-component of a resolvent eigenvector of the connection Laplacian `Δ_∇`
satisfies a scalar divergence-form weak-elliptic identity with principal symbol
`weightedInvGramOnEuclid g α`. The arbitrary-order interior-regularity bootstrap
iterates the elliptic Leibniz-commutator step, raising the Sobolev order by one
each time it differentiates the identity.

The plain per-component datum `TensorChartBilinearH1ComplData g r s α P₀` does
not compose under iteration: it carries no level index and its principal block
is the *first* weak partial. This module ships the **standalone iterated
divergence-form datum** that does compose — the eigenvector/tensor mirror of the
scalar campaign's `IteratedDiffChartBilinearData`.

## Schematic form

The packaged identity reads, at level `m`,
```
∫_{chartTarget} ∑_{a, b} weightedInvGramOnEuclid · ∂^{m}_dir(u_chart)_{cons a dir} · ∂_bψ
  + ∫_{chartTarget} densityOnEuclid · ∂^{m}_dir(u_chart)_dir · ψ
  = ∫_{chartTarget} densityOnEuclid · fChartEff · ψ
```
where `dir : Fin m → Fin n` is the direction multi-index, `cons a dir` is the
direction multi-index used by the inner principal LHS (with the additional
direction `a` prepended innermost), and `fChartEff : EuclN → ℝ` is the effective
`L²` source at level `m`. The `m`-fold mixed weak partials are the recursive
`eigenvectorChartIteratedPartial` — chosen weak partials taken via
`chosenWeakPartial'` — which composes definitionally under `Fin.snoc`/`Fin.cons`.

## Why the standalone structure composes

The principal factor is `eigenvectorChartIteratedPartial g r s i α
P₀ (m+1) (Fin.cons a dir)`. Its `Fin.snoc`/`Fin.cons` composition is definitional:
the level-`(m+1)` mixed partial along `Fin.snoc dir l` peels — by the recursive
definition together with `Fin.snoc_last` and `Fin.init_snoc` — to the chosen
weak `l`-partial of the level-`m` mixed partial along `dir`. This is exactly the
composition that the inductive step (part 2) needs in order to build a
level-`(m+1)` datum from a level-`m` one.

## Main definitions

* `eigenvectorIteratedTensorChartBilinearData` — the standalone
  iterated divergence-form datum (a `Type`), the eigenvector/tensor mirror of
  `IteratedDiffChartBilinearData`.
* `eigenvectorChartIteratedStepNumerator` — the explicit five-layer
  differentiated numerator with `dir`/`l` separated (the standalone-step shape).
* `eigenvectorChartIteratedStep` — the indicator-of-`chartPouKernel`
  of the numerator divided by `densityOnEuclid g α`.

## Main theorems

* `eigenvectorChartIteratedPartial_memW1p_of_memWkp` — global
  `MemW1p 2` of every `m`-fold mixed weak partial from global `MemWkp (m+1) 2` of
  the chart component (the tensor analogue of
  `chosenMthMixedPartialChartPushedU_memW1p_two`).
* `eigenvector_per_pair_ibp` — the per-pair integration by parts at
  level `m` applied to the `m`-fold mixed weak partial (the tensor analogue of
  `per_pair_ibp_chosenMthMixed`).
* `eigenvectorChartIteratedStep_memLp_two_weighted` — the
  weighted-`L²` regularity of `eigenvectorChartIteratedStep`,
  *unconditional*.
* `eigenvectorIteratedTensorChartBilinearData.ofBase` — the `m = 0`
  instance.

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
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
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
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there. -/
private lemma one_div_densityOnEuclid_contDiffOn_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-- **Chart-locality-free standalone iterated divergence-form datum for the
eigenvector chart component.** Re-keyed onto the intrinsic-compactness
eigenvector, the eigenvector/tensor mirror of the scalar campaign's
`IteratedDiffChartBilinearData`. The principal factor is the chart-locality-free
recursive `m`-fold mixed weak partial `eigenvectorChartIteratedPartial`. -/
structure eigenvectorIteratedTensorChartBilinearData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) where

  directions : Fin m → Fin (Module.finrank ℝ E)

  fChartEff : EuclN → ℝ

  fChartEff_memLp_weighted :
    MemLp fChartEff 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

  m_diff_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α a b y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m directions y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * fChartEff y * ψ y
        ∂(volume : Measure EuclN)

namespace eigenvectorIteratedTensorChartBilinearData

/-- Hypothesis-bearing abstract constructor for
`eigenvectorIteratedTensorChartBilinearData`: assembles the datum from the
direction multi-index, the effective `L²` source, its weighted-`L²` membership,
and the level-`m` differentiated variational identity. -/
def mk_from_hypotheses
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {i : TensorEigenIdx (I := I) (M := M) g r s}
    {α : M} {P₀ : TensorCompIdx (E := E) r s} {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (fChartEff : EuclN → ℝ)
    (fChartEff_memLp_weighted :
      MemLp fChartEff 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
    (m_diff_variational_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m directions y * ψ y
          ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * fChartEff y * ψ y
          ∂(volume : Measure EuclN)) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m :=
  { directions := directions
    fChartEff := fChartEff
    fChartEff_memLp_weighted := fChartEff_memLp_weighted
    m_diff_variational_identity := m_diff_variational_identity }

end eigenvectorIteratedTensorChartBilinearData

/-- **Chart-locality-free polymorphic regularity bridge for the eigenvector
iterated mixed partial.** From chart-`H^{k+m}` of the chart-locality-free
eigenvector chart component, every `m`-fold mixed weak partial
`eigenvectorChartIteratedPartial g r s i α P₀ m dirs` lies in chart-`H^k`. -/
theorem eigenvectorChartIteratedPartial_memWkp_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _dirs
      simpa [eigenvectorChartIteratedPartial_zero] using h_parent
  | succ m ih =>
      intro k h_parent dirs
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      have h_inner :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (k + 1) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m (Fin.init dirs))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (k + 1) h_parent' (Fin.init dirs)
      have h_step := h_inner.chosenWeakPartial_mem (dirs (Fin.last m))
      rw [eigenvectorChartIteratedPartial_succ]
      exact h_step

/-- **Chart-locality-free global `MemW1p 2` of the eigenvector iterated mixed weak
partial.** From chart-`H^{m+1}` of the chart-locality-free eigenvector chart
component, the `m`-fold mixed weak partial
`eigenvectorChartIteratedPartial g r s i α P₀ m dirs` lies in `W^{1,2}` on the
chart target. -/
theorem eigenvectorChartIteratedPartial_memW1p_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  have h_memWkp_1 :=
    eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ m 1 h_parent' dirs
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_memWkp_1
  exact h_memWkp_1

/-- **Chart-locality-free per-pair polymorphic integration by parts for the
eigenvector iterated mixed partial.** Moves the `l`-derivative off the test
function `ψ`: the integral of `φ · (m-fold mixed partial) · ∂_l ψ` equals minus
the sum of `∫ ∂_l φ · (m-fold mixed partial) · ψ` and
`∫ φ · ((m+1)-fold mixed partial along `Fin.snoc dirs l`) · ψ`. -/
theorem eigenvector_per_pair_ibp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (l : Fin (Module.finrank ℝ E)) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        φ y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m dirs y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m dirs y *
          ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.snoc dirs l) y *
          ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  have h_v_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartIteratedPartial_memW1p_of_memWkp
      (I := I) (M := M) g r s i α P₀ m h_parent dirs
  have h_w_eq :
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.snoc dirs l) =
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
    rw [eigenvectorChartIteratedPartial_succ]
    have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs l
        (Fin.last m) = l := by simp
    have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
        dirs l) = dirs := by simp
    rw [h_last, h_init]
  have h_ibp :=
    generic_per_pair_ibp (I := I) (M := M) (α := α) h_v_memW1p hφ_chart
      hψ_smooth hψ_cs hψ_supp l
  rw [h_w_eq]
  exact h_ibp

/-- **Chart-locality-free five-layer differentiated numerator at the inductive
step.** The recursive mixed weak partials are keyed onto
`eigenvectorChartIteratedPartial`; the five summed layers carry the `l`- and
`b`-differentiations of the weighted inverse Gram, the density, and the previous
effective source. -/
def eigenvectorChartIteratedStepNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN) : ℝ :=
  (∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b l) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a dirs) y)
  + (∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b l y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a dirs))
            (chartTargetEuclid (I := I) (M := M) α) y)
  - densityDerivOnEuclid (I := I) g α l y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m dirs y
  + densityDerivOnEuclid (I := I) g α l y * fChartEffPrev y
  + densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y

/-- The standalone-step numerator at level `m` with separated extra direction `l`
coincides with the level-`m` differentiated numerator
`eigenvectorChartRHSDiffNumerator` at the snoc-extended index `Fin.snoc dirs l`. -/
theorem eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStepNumerator (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l =
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev := by
  classical
  funext y
  have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs l
      (Fin.last m) = l := by simp
  have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
      dirs l) = dirs := by simp
  unfold eigenvectorChartIteratedStepNumerator
    eigenvectorChartRHSDiffNumerator
  rw [h_last, h_init]

/-- **Chart-locality-free effective chart-pulled `L²` source at the inductive
step.** The indicator of `chartPouKernel α` of the step numerator
`eigenvectorChartIteratedStepNumerator` divided by the chart density
`densityOnEuclid g α`. -/
def eigenvectorChartIteratedStep
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Set.indicator (chartPouKernel (I := I) (M := M) α)
    (fun y => eigenvectorChartIteratedStepNumerator
        (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y)

/-- The standalone step, fed the level-`m` differentiated right-hand side
`eigenvectorChartRHSDiff` as its previous source, coincides with the
level-`(m+1)` differentiated right-hand side at the snoc-extended index
`Fin.snoc dirs l`. -/
theorem eigenvectorChartIteratedStep_eq_rhsDiff_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs
        (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m dirs) l =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.snoc dirs l) := by
  classical
  rw [eigenvectorChartRHSDiff_succ]
  unfold eigenvectorChartIteratedStep
  have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
      dirs l) = dirs := by simp
  have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
    (I := I) (M := M) g r s i α P₀ m dirs
    (eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ m dirs) l
  rw [h_num, h_init]

/-- The standalone step vanishes at any point outside `chartPouKernel α`, since
it is the indicator of that set. -/
theorem eigenvectorChartIteratedStep_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l y = 0 := by
  rw [eigenvectorChartIteratedStep, Set.indicator_of_notMem hy]

/-- The support of the standalone step is contained in `chartPouKernel α`, since
it is the indicator of that set. -/
theorem eigenvectorChartIteratedStep_support_subset_chartPouKernel
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {i : TensorEigenIdx (I := I) (M := M) g r s}
    {α : M} {P₀ : TensorCompIdx (E := E) r s} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    {fChartEffPrev : EuclN → ℝ}
    {l : Fin (Module.finrank ℝ E)} :
    Function.support
        (eigenvectorChartIteratedStep (I := I) (M := M)
          g r s i α P₀ m dirs fChartEffPrev l) ⊆
      chartPouKernel (I := I) (M := M) α := by
  unfold eigenvectorChartIteratedStep
  exact Set.support_indicator_subset

/-- **Chart-locality-free weighted-`L²` regularity of the standalone-step
effective source.** Given only the weighted-`L²` membership of the previous
effective source `fChartEffPrev`, the standalone step
`eigenvectorChartIteratedStep` is itself `MemLp 2` with respect to the
chart-pulled weighted measure restricted to the chart target. -/
theorem eigenvectorChartIteratedStep_memLp_two_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemLp fChartEffPrev 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_num : MemLp (fun y => eigenvectorChartRHSDiffNumerator
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l)
      fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict K) :=
    eigenvectorChartRHSDiffNumerator_memLp_volume_compact
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l) h_prev
  have h_div : MemLp (fun y => eigenvectorChartIteratedStepNumerator
      (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y) 2
      ((volume : Measure EuclN).restrict K) := by
    have h_eq : (fun y => eigenvectorChartIteratedStepNumerator
        (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l y /
        densityOnEuclid (I := I) g α y) =
        fun y => (1 / densityOnEuclid (I := I) g α y) *
          eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev y := by
      funext y
      rw [eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator]
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [h_eq]
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (one_div_densityOnEuclid_contDiffOn_chartTarget (I := I) (M := M) g α)
      hK_compact hK_meas hK_in h_num
  have h_plain : MemLp (eigenvectorChartIteratedStep (I := I) (M := M)
      g r s i α P₀ m dirs fChartEffPrev l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [eigenvectorChartIteratedStep, memLp_indicator_iff_restrict hK_meas]
    have h_double : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_double]
    exact h_div
  refine memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α hK_compact hK_meas hK_in
    (Filter.Eventually.of_forall (fun y hy =>
      eigenvectorChartIteratedStep_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l hy))
    h_plain

/-- The level-`1` mixed weak partial along `Fin.cons a Fin.elim0` unfolds to the
chosen weak `a`-partial `chosenWeakPartial'` of the eigenvector chart
component. -/
private lemma eigenvectorChartIteratedPartial_one_cons_elim0_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (a : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ 1 (Fin.cons a Fin.elim0) =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
  rw [eigenvectorChartIteratedPartial_succ,
    eigenvectorChartIteratedPartial_zero]
  rfl

/-- The chart-locality-free candidate weak chart partial
`eigenvectorChartWeakPartial` agrees a.e. on the chart target with the
chart-locality-free level-`1` mixed weak partial along `Fin.cons a Fin.elim0`. -/
private lemma eigenvectorChartWeakPartial_ae_eq_iteratedPartial_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (a : Fin (Module.finrank ℝ E)) :
    eigenvectorChartWeakPartial (I := I) (M := M) g r s i α P₀ a
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ 1 (Fin.cons a Fin.elim0) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_wp_isWeak : ∀ k : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P₀ k)
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        Ω :=
    fun k => eigenvectorChartWeakPartial_hasWeakPartialDeriv
      (I := I) (M := M) g r s i α P₀ k
  have h_wp_memLp : ∀ k : Fin (Module.finrank ℝ E),
      MemLp (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k) 2 ((volume : Measure EuclN).restrict Ω) :=
    fun k => Lp.memLp (eigenvectorChartPartialLp (I := I) (M := M)
      g r s i α P₀ k)
  have h_comp_memLp :
      MemLp (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀) 2 ((volume : Measure EuclN).restrict Ω) :=
    eigenvectorChartComponentFun_memLp_volume
      (I := I) (M := M) g r s i α P₀
  have h_comp_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀) Ω :=
    ⟨h_comp_memLp, fun k => ⟨_, h_wp_memLp k, h_wp_isWeak k⟩⟩
  have h_iter_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) a
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ 1 (Fin.cons a Fin.elim0))
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀) Ω := by
    rw [eigenvectorChartIteratedPartial_one_cons_elim0_eq]
    exact chosenWeakPartial'_isWeakPartial_of_mem h_comp_memW1p a
  have h_wp_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ a)
      ((volume : Measure EuclN).restrict Ω) :=
    (h_wp_memLp a).locallyIntegrable (by norm_num)
  have h_iter_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ 1 (Fin.cons a Fin.elim0))
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartIteratedPartial_one_cons_elim0_eq]
    exact (chosenWeakPartial'_memLp_of_mem h_comp_memW1p a).locallyIntegrable
      (by norm_num)
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open
    (h_wp_isWeak a) h_iter_isWeak h_wp_loc h_iter_loc

namespace eigenvectorIteratedTensorChartBilinearData

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The `m = 0` instance of
`eigenvectorIteratedTensorChartBilinearData`.**
The effective `L²` source at level `0` is the chart-locality-free seven-term
`eigenvectorChartRHS`. -/
def ofBase
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ 0 where
  directions := Fin.elim0
  fChartEff := eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
  fChartEff_memLp_weighted :=
    eigenvectorChartRHS_memLp_weighted (I := I) (M := M)
      g r s i α P₀
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_supp
    have h_id := eigenvectorChartVariationalIdentity (I := I) (M := M)
      g r s i α P₀ hψ_smooth hψ_cs hψ_supp
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ 1 (Fin.cons a Fin.elim0) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α a b y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s i α P₀ a y *
                (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_all_ae :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartWeakPartial (I := I) (M := M)
                g r s i α P₀ a y =
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ 1 (Fin.cons a Fin.elim0) y := by
        rw [Filter.eventually_all]
        intro a
        exact eigenvectorChartWeakPartial_ae_eq_iteratedPartial_one
          (I := I) (M := M) g r s i α P₀ a
      filter_upwards [h_all_ae] with y hy
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hy a]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ 0 Fin.elim0 y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i)
              α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y * ψ y
          ∂(volume : Measure EuclN) := rfl
    rw [h_principal_eq, h_mass_eq]
    exact h_id

end eigenvectorIteratedTensorChartBilinearData

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The chart-locality-free standalone iterated divergence-form datum is a `Type`. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : Type _ :=
  eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
    g r s i α P₀ m

/-- The chart-locality-free `m = 0` instance produces a level-0 datum. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ 0 :=
  eigenvectorIteratedTensorChartBilinearData.ofBase
    (I := I) (M := M) g r s i α P₀

/-- The chart-locality-free standalone-step effective source coincides
definitionally with the chart-locality-free level-`(m+1)` differentiated
right-hand side at the snoc-extended index. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs
        (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m dirs) l =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.snoc dirs l) :=
  eigenvectorChartIteratedStep_eq_rhsDiff_succ
    (I := I) (M := M) g r s i α P₀ m dirs l

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
