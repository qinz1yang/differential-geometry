import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ShiftedRicciUpperBound
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift

/-!
# Quantitative preservation of almost nonnegative sectional curvature (LFR50, part C)

Let `S` be a smooth Ricci flow on a compact boundaryless 3-manifold with `|Rm| ≤ B` on `[0, T]`.
If `sec(g(0)) ≥ -ε` with `ε ≥ 0`, then `sec(g(t)) ≥ -ε e^{6 B t}` on `[0, T]`.

In dimension three `sec ≥ -K` is equivalent to `(R / 2) g - Ric + K g ≥ 0`
(`sectionalBoundedBelowAt_iff_metricRicciAt_le`, no factor `2`). The tensor
`ricciUpperBoundSec S + ε e^{6 B t} g` is then preserved by
`ricci_upper_bound_add_smul_metric_preserved`, because `2 Ric ≤ 6 B g` when `|Rm| ≤ B`
(`metricRicciAt_le_three_mul_of_rm_bound`). The constant `6` comes only from that Ricci bound. It
multiplies `B t` in the exponent and never changes the initial `-ε`. At `ε = 0` this is exact
preservation of `sec ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Riemannian
open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- Flow form of the three-dimensional bridge: `sec(g(t)) ≥ -K` at `x` iff
`ricciUpperBoundSec S t + K g(t) ≥ 0` at `x`. -/
theorem sectionalBoundedBelowAt_iff_ricciUpperBoundSec_add_nonneg
    [CompleteSpace E] [T2Space M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D} {t : Real} {x : M}
    (hdim : Module.finrank Real (TangentSpace I x) = 3) {K : Real} :
    SectionalBoundedBelowAt (S.base.metric t) x (-K) ↔
      ∀ v : TangentSpace I x,
        0 ≤ (ricciUpperBoundSec S) t x (vec2 (I := I) v v) +
          K * (S.base.metric t).inner x v v := by
  rw [sectionalBoundedBelowAt_iff_metricRicciAt_le hdim]
  refine forall_congr' fun v => ?_
  rw [ricci_upper_bound_sec_apply (I := I) S t x v v]
  change metricRicciAt (S.base.metric t) x (vec2 (I := I) v v) ≤
      (metricScalarAt (S.base.metric t) x / 2 + K) * (S.base.metric t).inner x v v ↔
    0 ≤ 1 / 2 * metricScalarAt (S.base.metric t) x * (S.base.metric t).inner x v v -
      metricRicciAt (S.base.metric t) x (vec2 (I := I) v v) + K * (S.base.metric t).inner x v v
  constructor <;> intro h <;> linarith

private theorem hasDerivAt_exp_profile (ε c t : Real) :
    HasDerivAt (fun s : Real => ε * Real.exp (c * s)) (c * (ε * Real.exp (c * t))) t := by
  have h := (((hasDerivAt_id t).const_mul c).exp).const_mul ε
  simp only [id_eq, mul_one] at h
  convert h using 1
  ring

/-- Quantitative preservation of `sec ≥ -ε` along a Ricci flow with `|Rm| ≤ B`:
`sec(g(t)) ≥ -ε e^{6 B t}` on `[0, T]`. -/
theorem sectionalBoundedBelow_exp_preserved
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T B ε : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hRm : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ B)
    (hε : 0 ≤ ε)
    (hinit : SectionalBoundedBelow (S.base.metric 0) (-ε)) :
    ∀ t ∈ Set.Icc 0 T,
      SectionalBoundedBelow (S.base.metric t) (-ε * Real.exp (6 * B * t)) := by
  let f : Real → Real := fun s => ε * Real.exp (6 * B * s)
  have hfd (s : Real) : HasDerivAt f (6 * B * f s) s := hasDerivAt_exp_profile ε (6 * B) s
  have hf : Differentiable Real f := fun s => (hfd s).differentiableAt
  have hf0 : f 0 = ε := by simp [f]
  have hfpos (s : Real) : 0 ≤ f s := mul_nonneg hε (Real.exp_pos _).le
  have hgain : ∀ t ∈ Set.Icc 0 T, ∀ (x : M) (v : TangentSpace I x),
      2 * f t * S.ricciAt t x (vec2 (I := I) v v) ≤
        deriv f t * (S.base.metric t).inner x v v := by
    intro t ht x v
    rw [(hfd t).deriv]
    have hRic : S.ricciAt t x (vec2 (I := I) v v) ≤ 3 * B * (S.base.metric t).inner x v v :=
      metricRicciAt_le_three_mul_of_rm_bound (hdim x) (hRm t ht x) v
    have h := mul_le_mul_of_nonneg_left hRic (mul_nonneg (by norm_num : (0 : Real) ≤ 2) (hfpos t))
    linarith
  have hinit' : ∀ (x : M) (v : TangentSpace I x),
      0 ≤ (ricciUpperBoundSec S) 0 x (vec2 (I := I) v v) +
        f 0 * (S.base.metric 0).inner x v v := by
    intro x
    rw [hf0]
    exact (sectionalBoundedBelowAt_iff_ricciUpperBoundSec_add_nonneg (hdim x)).mp (hinit x)
  intro t ht x
  have h := ricci_upper_bound_add_smul_metric_preserved (I := I) hS hdim hTsub hTreg hf hgain
    hinit' t ht x
  rw [neg_mul]
  exact (sectionalBoundedBelowAt_iff_ricciUpperBoundSec_add_nonneg (hdim x)).mpr h

/-- The frozen LFR50 C contract (`design-lfr50-merged-20261004.md` §4) with `C = 6`. The frozen
hypotheses `1 ≤ B`, `0 ≤ T` and `ε e^{C B T} ≤ 1/2` are not needed and are omitted, which only
strengthens the statement. The constant `C` is chosen before the flows and `ε`, and is universal. -/
theorem exists_uniform_sectional_lower_error_constant
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    [CompleteSpace E] [CompactSpace M]
    (hdim : Module.finrank Real E = 3) (B T : Real) :
    ∃ C : Real, 0 < C ∧ ∀ (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
      (S : SolutionOn (I := I) (M := M) D), IsSmoothSolutionOn (I := I) (M := M) S →
      Set.Icc 0 T ⊆ D.carrier → Set.Ioc 0 T ⊆ D.regular →
      (∀ t ∈ Set.Icc 0 T, ∀ x : M,
        Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ B) →
      ∀ ε : Real, 0 ≤ ε →
      SectionalBoundedBelow (S.base.metric 0) (-ε) →
      ∀ t ∈ Set.Icc 0 T,
        SectionalBoundedBelow (S.base.metric t) (-ε * Real.exp (C * B * t)) :=
  ⟨6, by norm_num, fun _ _ hS hTsub hTreg hRm _ hε hinit =>
    sectionalBoundedBelow_exp_preserved hS (fun _ => hdim) hTsub hTreg hRm hε hinit⟩

end DifferentialGeometry.PDE.RicciFlow
