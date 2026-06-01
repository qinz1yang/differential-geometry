import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Analysis.Laplacian.MetricBounds
import DifferentialGeometry.Integral.Connection.CotangentExtension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Positive-definiteness of a small symmetric perturbation of a metric

On a closed Riemannian manifold `(M, g)`, a symmetric `(0,2)`-fibre field
`h` that is uniformly small relative to the metric `g` produces, when added
to `g`, an honest smooth Riemannian metric `g + h`.

The smallness condition is expressed in the **`g`-Riemannian fibre norm**: a
bilinear form `h x : TₓM →L[ℝ] TₓM →L[ℝ] ℝ` is controlled by `δ` when

  `|h x v w| ≤ δ · √(g x v v) · √(g x w w)`   for all `v, w`,

i.e. its operator norm with respect to the `g`-inner product on each tangent
space is at most `δ`. (This is *not* the model operator norm `‖h x‖`; it is
intrinsic to `g`.)

If `δ < 1` uniformly, then for `v ≠ 0`,

  `(g + h) x v v ≥ (1 - δ) · g x v v > 0`,

so `g + h` is fibrewise positive-definite, von-Neumann bounded on each fibre
(its unit ball is contained in a scaled copy of the `g`-unit ball), symmetric,
and smooth (a sum of two smooth Hom-bundle sections). It therefore assembles
into a `SmoothRiemannianMetric I M`.

## Main results

* `perturbedInner` — the fibrewise sum `g.inner x + h x`.
* `perturbedInner_pos_of_gOpBound` — fibrewise positive-definiteness under
  the `g`-operator-norm smallness bound with `δ < 1`.
* `perturbedMetric` — the assembled `SmoothRiemannianMetric`.
* `exists_posDef_perturbation_radius` — the headline existence statement:
  there is `δ > 0` (namely `δ = 1`) such that every symmetric smooth `h`
  whose `g`-operator norm is `< δ` everywhere yields a `SmoothRiemannianMetric`.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `gFibreOpBound g h δ` says the symmetric `(0,2)`-fibre field `h` is
controlled, uniformly over `M`, by `δ` in the `g`-Riemannian fibre norm:
`|h x v w| ≤ δ · √(g x v v) · √(g x w w)` for all base points `x` and all
tangent vectors `v, w`. This is the operator norm of `h x` with respect to
the inner product `g x` on `TₓM`, *not* the model operator norm. -/
def gFibreOpBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (δ : ℝ) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x),
    |h x v w| ≤ δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)

/-- The fibrewise sum `g.inner x + h x` as a continuous bilinear form on
`TₓM`. -/
noncomputable def perturbedInner
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  g.inner x + h x

@[simp] lemma perturbedInner_apply
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) (v w : TangentSpace I x) :
    perturbedInner g h x v w = g.inner x v w + h x v w := by
  simp only [perturbedInner, ContinuousLinearMap.add_apply]

/-- Symmetry of the perturbed inner product, given symmetry of `h`. -/
theorem perturbedInner_symm
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (x : M) (v w : TangentSpace I x) :
    perturbedInner g h x v w = perturbedInner g h x w v := by
  rw [perturbedInner_apply, perturbedInner_apply, g.symm x v w, hsymm x v w]

/-- Diagonal control: under the `g`-operator-norm bound `δ`, the perturbation
satisfies `|h x v v| ≤ δ · g x v v`. -/
private lemma abs_h_diag_le
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : gFibreOpBound g h δ)
    (x : M) (v : TangentSpace I x) :
    |h x v v| ≤ δ * g.inner x v v := by
  have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hbound := hδ x v v
  have hsq : Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) = g.inner x v v := by
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
  calc |h x v v|
      ≤ δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) := hbound
    _ = δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v)) := by ring
    _ = δ * g.inner x v v := by rw [hsq]

/-- The perturbed quadratic form is bounded below by `(1 - δ) · g x v v`. -/
theorem perturbedInner_self_lower_bound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : gFibreOpBound g h δ)
    (x : M) (v : TangentSpace I x) :
    (1 - δ) * g.inner x v v ≤ perturbedInner g h x v v := by
  have hdiag := abs_h_diag_le (I := I) (M := M) g h hδ x v
  have hge : -(δ * g.inner x v v) ≤ h x v v :=
    neg_le_of_abs_le hdiag
  rw [perturbedInner_apply]
  nlinarith [hge]

/-- **Fibrewise positive-definiteness of the perturbed metric** under the
`g`-operator-norm smallness bound with `δ < 1`. -/
theorem perturbedInner_pos_of_gOpBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : gFibreOpBound g h δ)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < perturbedInner g h x v v := by
  have hg_pos : 0 < g.inner x v v := g.pos x v hv
  have hcoeff : 0 < 1 - δ := by linarith
  have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g h hδ x v
  have : 0 < (1 - δ) * g.inner x v v := mul_pos hcoeff hg_pos
  linarith

/-- A scaled `g`-sublevel set `{v | g x v v < r}` (for `r > 0`) is von-Neumann
bounded: it is the image of the `g`-unit ball `{v | g x v v < 1}` (von-Neumann
bounded by the metric structure) under scalar multiplication by `√r`. -/
private lemma gSublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (x : M) {r : ℝ} (hr : 0 < r) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | g.inner x v v < r} := by
  set sr := Real.sqrt r with hsr_def
  have hsr_pos : 0 < sr := Real.sqrt_pos.mpr hr
  have hsr_sq : sr * sr = r := by
    rw [hsr_def, ← Real.sqrt_mul hr.le, Real.sqrt_mul_self hr.le]
  set L : TangentSpace I x →L[ℝ] TangentSpace I x :=
    sr • ContinuousLinearMap.id ℝ (TangentSpace I x) with hL_def
  have hL_apply : ∀ w : TangentSpace I x, L w = sr • w := by
    intro w; rw [hL_def]; simp
  have hg_unit : Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | g.inner x v v < 1} := g.isVonNBounded x
  have himg := hg_unit.image L
  have hset_eq :
      {v : TangentSpace I x | g.inner x v v < r}
        = (L : TangentSpace I x → TangentSpace I x) ''
            {w : TangentSpace I x | g.inner x w w < 1} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hv
      refine ⟨sr⁻¹ • v, ?_, ?_⟩
      · have hscale : g.inner x (sr⁻¹ • v) (sr⁻¹ • v)
            = sr⁻¹ * (sr⁻¹ * g.inner x v v) := by
          simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hscale]
        have hsr_ne : sr ≠ 0 := ne_of_gt hsr_pos
        have : sr⁻¹ * (sr⁻¹ * g.inner x v v) = g.inner x v v / r := by
          field_simp
          rw [← hsr_sq]; ring
        rw [this, div_lt_one hr]; exact hv
      · rw [hL_apply]
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hsr_pos), one_smul]
    · rintro ⟨w, hw, rfl⟩
      rw [hL_apply]
      have hscale : g.inner x (sr • w) (sr • w) = sr * (sr * g.inner x w w) := by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hscale]
      have hrw : sr * (sr * g.inner x w w) = r * g.inner x w w := by
        rw [← mul_assoc, hsr_sq]
      rw [hrw]
      calc r * g.inner x w w < r * 1 := by
              apply mul_lt_mul_of_pos_left hw hr
        _ = r := mul_one r
  rw [hset_eq]
  exact himg

/-- **von-Neumann boundedness of the perturbed unit ball.** Under the
`g`-operator-norm bound with `δ < 1`, the set `{v | (g+h) x v v < 1}` is
von-Neumann bounded. -/
theorem perturbedInner_isVonNBounded
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : gFibreOpBound g h δ)
    (x : M) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | perturbedInner g h x v v < 1} := by
  have hcoeff : 0 < 1 - δ := by linarith
  set r := (1 - δ)⁻¹ with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; exact inv_pos.mpr hcoeff
  have hsub : {v : TangentSpace I x | perturbedInner g h x v v < 1}
      ⊆ {v : TangentSpace I x | g.inner x v v < r} := by
    intro v hv
    rw [Set.mem_setOf_eq] at hv ⊢
    have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g h hδ x v
    have h1 : (1 - δ) * g.inner x v v < 1 := lt_of_le_of_lt hlb hv
    rw [hr_def, ← one_div]
    rw [lt_div_iff₀ hcoeff, mul_comm]
    exact h1
  exact (gSublevel_isVonNBounded (I := I) (M := M) g x hr_pos).subset hsub

/-- **Smoothness of the perturbed inner-product section.** If the perturbation
`h` is a smooth section of the bundle of bilinear forms, then so is
`x ↦ g.inner x + h x`. This is the `contMDiff` field of the assembled metric.

The argument descends through `cotangentCov_clmSection_smooth_aux` twice (once
per tensor slot) to a scalar statement, where the perturbed value is the sum
of two smooth scalars `g.inner x (Y x) (W x)` and `h x (Y x) (W x)`, each
obtained by applying a smooth Hom-bundle section to two smooth tangent
sections. -/
theorem perturbedInner_contMDiff
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (perturbedInner g h x)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => perturbedInner g h x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => perturbedInner g h x (Y x))
  intro W
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) := Y.contMDiff
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (W x)) := W.contMDiff
  have hg_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (Y x) (W x)) := by
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x (g.inner x (Y x) (W x))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => g.inner x)
        (v := fun x : M => Y x)
        (w := fun x : M => W x)
        g.contMDiff hY hW
    intro x
    have h_at := h_total x
    rw [contMDiffAt_totalSpace] at h_at
    exact h_at.2
  have hh_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => h x (Y x) (W x)) := by
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x (h x (Y x) (W x))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => h x)
        (v := fun x : M => Y x)
        (w := fun x : M => W x)
        hsmooth hY hW
    intro x
    have h_at := h_total x
    rw [contMDiffAt_totalSpace] at h_at
    exact h_at.2
  have h_sum_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => perturbedInner g h x (Y x) (W x)) := by
    have h_eq : (fun x : M => perturbedInner g h x (Y x) (W x))
        = fun x : M => g.inner x (Y x) (W x) + h x (Y x) (W x) := by
      funext x; rw [perturbedInner_apply]
    rw [h_eq]; exact hg_scalar.add hh_scalar
  intro x
  rw [contMDiffAt_section]
  refine (h_sum_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change perturbedInner g h y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, perturbedInner g h y (Y y) (W y)⟩).2
  rfl

/-- **The perturbed metric `g + h`.** Given a symmetric smooth perturbation
`h` whose `g`-operator norm is bounded by `δ < 1` everywhere, the fibrewise
sum `g.inner x + h x` is symmetric, fibrewise positive-definite, has a
von-Neumann bounded unit ball on every fibre, and varies smoothly, hence
assembles into an honest `SmoothRiemannianMetric I M`. -/
noncomputable def perturbedMetric
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b)))
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : gFibreOpBound g h δ) :
    SmoothRiemannianMetric I M where
  inner x := perturbedInner g h x
  symm x v w := perturbedInner_symm (I := I) (M := M) g h hsymm x v w
  pos x v hv := perturbedInner_pos_of_gOpBound (I := I) (M := M) g h hδ_lt hδ x v hv
  isVonNBounded x := perturbedInner_isVonNBounded (I := I) (M := M) g h hδ_lt hδ x
  contMDiff := perturbedInner_contMDiff (I := I) (M := M) g h hsmooth

@[simp] lemma perturbedMetric_inner
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b)))
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : gFibreOpBound g h δ) (x : M) :
    (perturbedMetric g h hsymm hsmooth hδ_lt hδ).inner x = perturbedInner g h x :=
  rfl

/-- **Positive-definiteness radius for metric perturbations.**

On a closed Riemannian manifold `(M, g)`, there is a strictly positive radius
`δ` (namely `δ = 1`) such that *every* symmetric smooth `(0,2)`-fibre field
`h` whose `g`-Riemannian fibre (operator) norm is bounded by some `δ' < δ`
uniformly over `M` produces an honest `SmoothRiemannianMetric I M`, equal
fibrewise to `g + h`.

The smallness is measured in the `g`-induced fibre norm:
`|h x v w| ≤ δ' · √(g x v v) · √(g x w w)`, i.e. the operator norm of `h x`
with respect to the inner product `g x` on `TₓM`. The resulting metric's
quadratic form is bounded below by `(1 - δ') · g x v v > 0`. -/
theorem exists_posDef_perturbation_radius
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ),
        (∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v) →
        (ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun b : M => TotalSpace.mk'
            (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
            b (h b))) →
        ∀ δ' : ℝ, δ' < δ → gFibreOpBound g h δ' →
          ∃ g' : SmoothRiemannianMetric I M,
            ∀ (x : M) (v w : TangentSpace I x),
              g'.inner x v w = g.inner x v w + h x v w := by
  refine ⟨1, one_pos, ?_⟩
  intro h hsymm hsmooth δ' hδ'_lt hδ'
  refine ⟨perturbedMetric g h hsymm hsmooth hδ'_lt hδ', ?_⟩
  intro x v w
  rw [perturbedMetric_inner, perturbedInner_apply]

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
