import DifferentialGeometry.Analysis.Sobolev.Nirenberg.Euclidean
import DifferentialGeometry.Integral.DivergenceTheorem.Family
import DifferentialGeometry.Geometry.Hessian
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Order.Compact

/-!
# Smooth global extension of the chart-pulled volume-weighted inverse Gram matrix

For a smooth Riemannian metric `g` on a smooth manifold `M` and a chart point
`α : M`, the chart-Gram-matrix-times-volume `√(det G(α)) · G(α)⁻¹` is a smooth,
symmetric, positive-definite matrix-valued function defined on the open set
`(extChartAt I α).target ⊆ E`. After identification with the standard Euclidean
space `EuclideanSpace ℝ (Fin n)` (via `toEuclidean`), it gives a smooth
matrix-valued function on the open set
`chartTargetEuclid α := toEuclidean '' (extChartAt I α).target`.

This file packages a smooth global extension of that function from a precompact
piece `K ⊆ chartTargetEuclid α` to all of `EuclideanSpace ℝ (Fin n)`. The
extension agrees with the original on `K` and equals the identity matrix
outside a slightly larger compact set. Uniform ellipticity is preserved on the
whole space, with a constructive lower bound `min(1, λ_K)` where `λ_K > 0` is
the smallest eigenvalue (equivalently, the infimum of the Rayleigh quotient on
the unit sphere) of the chart-pulled `√det · G⁻¹` over the compact support of
the cutoff function.

The end product is a `SmoothEllipticBilinearForm` (from
`NirenbergEuclidean.lean`) on `Set.univ`, ready to feed into the Nirenberg
difference-quotient interior-regularity machinery.

## Setting

Throughout this file we work in the boundaryless setting:
`[I.Boundaryless]`, `[T2Space M]`, `[SigmaCompactSpace M]`. The model fibre is
a finite-dimensional real inner-product space `E` with positive dimension.
The metric `g` is a `SmoothRiemannianMetric I M` from
`Integral.Measure.ChartDensity`.

## Strategy

1. Pull the chart Gram matrix and chart density back through
   `(extChartAt I α).symm ∘ toEuclidean.symm` to land in
   `EuclideanSpace ℝ (Fin n)`.
2. Take the inverse Gram matrix and multiply componentwise by the (positive)
   chart density. Call this `weightedInvGramOnEuclid`.
3. Pick a smooth cutoff `χ` equal to `1` on `K` and supported in a slightly
   thickened compact set inside `chartTargetEuclid α`.
4. Define
   `extendedMatrix y i j := χ y * weightedInvGramOnEuclid α y i j +
                            (1 - χ y) * δ_{ij}`.
5. Verify smoothness, symmetry, and ellipticity.
6. Package as a `SmoothEllipticBilinearForm` with `c := 0` (no zeroth-order
   term).

## Main public theorem

* `exists_smooth_metric_extension`: existence of a smooth elliptic bilinear
  form on `EuclideanSpace ℝ (Fin n)` that, on `K`, agrees pointwise with the
  chart-pulled `√det G · G⁻¹`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The chart `α` target image transferred to `EuclideanSpace ℝ (Fin n)` via
the canonical linear isomorphism `toEuclidean`. -/
def chartTargetEuclid (α : M) : Set EuclN :=
  toEuclidean '' (extChartAt I α).target

/-- The chart-target image is open under the boundaryless assumption. -/
lemma chartTargetEuclid_isOpen [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartTargetEuclid
  have hOpenE : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  exact toEuclidean.toHomeomorph.isOpenMap _ hOpenE

/-- Every point of `chartTargetEuclid α` corresponds to a point in
`(extChartAt I α).target` via `toEuclidean.symm`. -/
lemma toEuclidean_symm_mem_target {α : M} {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
  rcases hy with ⟨z, hz_target, hz_eq⟩
  have hyz : (toEuclidean (E := E)).symm y = z := by
    rw [← hz_eq]; simp
  rw [hyz]
  exact hz_target

/-- The chart-pulled Gram-matrix `(i, j)` entry: at `y ∈ EuclN`, the value is
`G(α, x_y)_{ij}` where `x_y := (extChartAt I α).symm (toEuclidean.symm y)`.
Smooth on `chartTargetEuclid α`; junk values elsewhere. -/
def gramOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartGramMatrix (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i j

/-- The chart-pulled inverse-Gram-matrix `(i, j)` entry. -/
def invGramOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartInvGramMatrix (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) i j

/-- The chart-pulled volume density `√det G(α, x_y)`. -/
def densityOnEuclid (g : SmoothRiemannianMetric I M) (α : M) (y : EuclN) : ℝ :=
  chartDensity (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

/-- The volume-weighted inverse Gram matrix `(i, j)` entry, pulled back to
`EuclideanSpace`: `√det G(α, x_y) · G(α, x_y)⁻¹_{ij}`. -/
def weightedInvGramOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y

/-- `(extChartAt I α).symm ∘ toEuclidean.symm` is smooth on
`chartTargetEuclid α` as a manifold map into `M`. -/
lemma contMDiffOn_chart_symm (α : M) :
    ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_inner_contDiff : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.contDiff
  have h_inner : ContMDiff 𝓘(ℝ, EuclN) 𝓘(ℝ, E) ∞
      (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr h_inner_contDiff
  have h_outer : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I α).symm (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    exact toEuclidean_symm_mem_target (I := I) hy
  exact h_outer.comp h_inner.contMDiffOn h_maps

/-- Helper: the chart-symm composition maps `chartTargetEuclid α` into the
chart source (which equals the trivialization base set). -/
private lemma mapsTo_chart_symm_baseSet (α : M) :
    MapsTo (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro y hy
  change (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (extChartAt I α).source :=
    (extChartAt I α).map_target h_tgt
  rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src

/-- Each entry of the chart-pulled Gram matrix is smooth on
`chartTargetEuclid α` viewed as a `ContDiffOn` statement on `EuclideanSpace`. -/
lemma gramOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (gramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_g : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartGramMatrix g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_maps := mapsTo_chart_symm_baseSet (I := I) (M := M) α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ) ∞
      (gramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_g.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

/-- Each entry of the chart-pulled inverse Gram matrix is smooth on
`chartTargetEuclid α`. -/
lemma invGramOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_g : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_maps := mapsTo_chart_symm_baseSet (I := I) (M := M) α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ) ∞
      (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_g.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

/-- The chart-pulled volume density is smooth on `chartTargetEuclid α`. -/
lemma densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  have h_dens : ContMDiffOn I 𝓘(ℝ) ∞
      (chartDensity g α)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_contMDiffOn (I := I) g α
  have h_maps := mapsTo_chart_symm_baseSet (I := I) (M := M) α
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ) ∞
      (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_dens.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

/-- Each entry of the volume-weighted inverse Gram matrix is smooth on
`chartTargetEuclid α`. -/
lemma weightedInvGramOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold weightedInvGramOnEuclid
  exact (densityOnEuclid_contDiffOn (I := I) g α).mul
    (invGramOnEuclid_contDiffOn (I := I) g α i j)

/-- The chart-pulled inverse Gram matrix is symmetric on the chart base set. -/
lemma invGramOnEuclid_symm_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    invGramOnEuclid (I := I) g α i j y =
      invGramOnEuclid (I := I) g α j i y := by
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_src : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_tgt
  have h_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x ∈ (chartAt H α).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src
  have hHerm : (chartGramMatrix (I := I) g α x).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α x
  have hHermInv : (chartInvGramMatrix (I := I) g α x).IsHermitian := by
    unfold chartInvGramMatrix
    exact hHerm.inv
  change chartInvGramMatrix (I := I) g α x i j =
    chartInvGramMatrix (I := I) g α x j i
  have h_apply := hHermInv.apply i j
  rw [star_trivial] at h_apply
  exact h_apply.symm

/-- The volume-weighted inverse Gram matrix is symmetric on the chart base set. -/
lemma weightedInvGramOnEuclid_symm_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedInvGramOnEuclid (I := I) g α i j y =
      weightedInvGramOnEuclid (I := I) g α j i y := by
  unfold weightedInvGramOnEuclid
  rw [invGramOnEuclid_symm_of_mem (I := I) g α i j hy]

/-- The chart-pulled volume density is strictly positive on the chart-target
image. -/
lemma densityOnEuclid_pos
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    0 < densityOnEuclid (I := I) g α y := by
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_src : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_tgt
  have h_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x ∈ (chartAt H α).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src
  exact chartDensity_pos (I := I) g α h_base

/-- The chart-pulled inverse Gram matrix is positive-definite on
`chartTargetEuclid α`. -/
lemma invGramOnEuclid_posDef
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        invGramOnEuclid (I := I) g α i j y)).PosDef := by
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_src : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_tgt
  have h_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change x ∈ (chartAt H α).source
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src
  have hG : (chartGramMatrix (I := I) g α x).PosDef :=
    chartGramMatrix_posDef (I := I) g α h_base
  have hGinv : (chartInvGramMatrix (I := I) g α x).PosDef := by
    unfold chartInvGramMatrix
    exact hG.inv
  have hmat_eq : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      invGramOnEuclid (I := I) g α i j y)) =
      chartInvGramMatrix (I := I) g α x := by
    ext i j
    rfl
  rw [hmat_eq]
  exact hGinv

/-- The Rayleigh-quotient lower bound from positive-definiteness: for the
weighted inverse Gram matrix at any point in `chartTargetEuclid α`, the
quadratic form is bounded below by a strictly positive multiple of `‖ξ‖²`,
where the constant is the smallest eigenvalue. -/
lemma weighted_quadForm_pos_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (ξ : EuclN) (hξ : ξ ≠ 0) :
    0 < ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
  classical
  have h_dens_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy
  have h_inv_pd := invGramOnEuclid_posDef (I := I) g α hy
  set Acoeff : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      weightedInvGramOnEuclid (I := I) g α i j y)
    with hA_def
  set Ainv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      invGramOnEuclid (I := I) g α i j y)
    with hAinv_def
  have hA_eq : Acoeff = (densityOnEuclid (I := I) g α y) • Ainv := by
    ext i j
    change weightedInvGramOnEuclid (I := I) g α i j y =
      densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y
    rfl
  have h_smul_quad : ⟪ξ, DeGiorgi.matMulE Acoeff ξ⟫_ℝ =
      densityOnEuclid (I := I) g α y * ⟪ξ, DeGiorgi.matMulE Ainv ξ⟫_ℝ := by
    rw [hA_eq]
    have h_mul : DeGiorgi.matMulE
        ((densityOnEuclid (I := I) g α y) • Ainv) ξ =
        (densityOnEuclid (I := I) g α y) • DeGiorgi.matMulE Ainv ξ := by
      apply WithLp.ofLp_injective 2
      simp only [DeGiorgi.matMulE_ofLp]
      rw [Matrix.smul_mulVec]
      rfl
    rw [h_mul]
    rw [inner_smul_right]
  have h_quad_pos : 0 < ⟪ξ, DeGiorgi.matMulE Ainv ξ⟫_ℝ := by
    have h_form : ⟪ξ, DeGiorgi.matMulE Ainv ξ⟫_ℝ =
        Ainv.mulVec ξ.ofLp ⬝ᵥ ξ.ofLp := by
      change (DeGiorgi.matMulE Ainv ξ).ofLp ⬝ᵥ star ξ.ofLp = _
      rw [DeGiorgi.matMulE_ofLp]
      have hstar : star ξ.ofLp = ξ.ofLp := by
        funext i; exact star_trivial _
      rw [hstar]
    rw [h_form]
    have hxi_ne : ξ.ofLp ≠ 0 := by
      intro h
      apply hξ
      have heq : ξ = WithLp.toLp 2 ξ.ofLp := rfl
      rw [heq, h]
      simp
    have h_dot_pos : 0 < star ξ.ofLp ⬝ᵥ Ainv.mulVec ξ.ofLp :=
      h_inv_pd.dotProduct_mulVec_pos hxi_ne
    have hstar : star ξ.ofLp = ξ.ofLp := by
      funext i; exact star_trivial _
    rw [hstar] at h_dot_pos
    rw [dotProduct_comm]
    exact h_dot_pos
  rw [h_smul_quad]
  exact mul_pos h_dens_pos h_quad_pos

/-- The continuous map `(y, ξ) ↦ ⟪ξ, A(y) ξ⟫` for `A := Matrix.of weightedInvGram`.
This is the integrand of the Rayleigh quotient. -/
private def rayleighInt
    (g : SmoothRiemannianMetric I M) (α : M) (y : EuclN) (ξ : EuclN) : ℝ :=
  ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ

/-- Pointwise sum-of-products formula for `rayleighInt`. -/
private lemma rayleighInt_eq_sum
    (g : SmoothRiemannianMetric I M) (α : M) (y ξ : EuclN) :
    rayleighInt (I := I) g α y ξ =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y * (ξ.ofLp i) * (ξ.ofLp j) := by
  classical
  unfold rayleighInt
  have h_inner : ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ =
      ((Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        weightedInvGramOnEuclid (I := I) g α i j y)).mulVec ξ.ofLp) ⬝ᵥ ξ.ofLp := by
    change (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : star ξ.ofLp = ξ.ofLp := by
      funext i; exact star_trivial _
    rw [hstar]
  rw [h_inner]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- Continuity of the Rayleigh integrand on `chartTargetEuclid α` jointly in
`(y, ξ)`. -/
private lemma rayleighInt_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (fun p : EuclN × EuclN =>
        rayleighInt (I := I) g α p.1 p.2)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) := by
  classical
  have h_eq : (fun p : EuclN × EuclN =>
      rayleighInt (I := I) g α p.1 p.2) =
      (fun p : EuclN × EuclN =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j p.1 *
            (p.2.ofLp i) * (p.2.ofLp j)) := by
    funext p
    exact rayleighInt_eq_sum (I := I) g α p.1 p.2
  rw [h_eq]
  refine continuousOn_finset_sum _ ?_
  intro i _
  refine continuousOn_finset_sum _ ?_
  intro j _
  have h_fst : ContinuousOn (fun p : EuclN × EuclN => p.1)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) :=
    continuous_fst.continuousOn
  have h_snd : ContinuousOn (fun p : EuclN × EuclN => p.2)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) :=
    continuous_snd.continuousOn
  have h_fst_in : MapsTo (fun p : EuclN × EuclN => p.1)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN))
      (chartTargetEuclid (I := I) (M := M) α) := fun _ hp => hp.1
  have h_a : ContinuousOn
      (fun p : EuclN × EuclN =>
        weightedInvGramOnEuclid (I := I) g α i j p.1)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) := by
    have h_pull : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn)
    exact h_pull.comp h_fst h_fst_in
  have h_xi_i : Continuous (fun ξ : EuclN => ξ.ofLp i) :=
    (EuclideanSpace.proj i).continuous
  have h_xi_j : Continuous (fun ξ : EuclN => ξ.ofLp j) :=
    (EuclideanSpace.proj j).continuous
  have h_xi_i_p : ContinuousOn (fun p : EuclN × EuclN => p.2.ofLp i)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) :=
    h_xi_i.continuousOn.comp h_snd (Set.mapsTo_univ _ _)
  have h_xi_j_p : ContinuousOn (fun p : EuclN × EuclN => p.2.ofLp j)
      ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) :=
    h_xi_j.continuousOn.comp h_snd (Set.mapsTo_univ _ _)
  exact (h_a.mul h_xi_i_p).mul h_xi_j_p

/-- A uniform-in-`y` Rayleigh-quotient lower bound on a compact subset `K` of
`chartTargetEuclid α`: there is `lamK > 0` such that
`lamK ‖ξ‖² ≤ ⟪ξ, A(y) ξ⟫_ℝ` for every `y ∈ K` and every `ξ ∈ EuclN`,
where `A(y) := Matrix.of (weightedInvGramOnEuclid · · y)`. -/
lemma exists_unif_lower_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ lamK : ℝ, 0 < lamK ∧
      ∀ y ∈ K, ∀ ξ : EuclN,
        lamK * ‖ξ‖ ^ 2 ≤
          ⟪ξ, DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
  classical
  set S : Set EuclN := Metric.sphere (0 : EuclN) 1 with hS_def
  have hS_compact : IsCompact S := isCompact_sphere _ _
  have hKS_compact : IsCompact (K ×ˢ S) := hK_compact.prod hS_compact
  have h_cont : ContinuousOn (fun p : EuclN × EuclN =>
      rayleighInt (I := I) g α p.1 p.2)
      (K ×ˢ S) := by
    have h_super : ContinuousOn (fun p : EuclN × EuclN =>
        rayleighInt (I := I) g α p.1 p.2)
        ((chartTargetEuclid (I := I) (M := M) α) ×ˢ (Set.univ : Set EuclN)) :=
      rayleighInt_continuousOn (I := I) g α
    apply h_super.mono
    intro p hp
    exact ⟨hK_target hp.1, Set.mem_univ _⟩
  have h_strict_pos : ∀ p ∈ K ×ˢ S, 0 < (fun p : EuclN × EuclN =>
      rayleighInt (I := I) g α p.1 p.2) p := by
    intro p hp
    obtain ⟨hpK, hpS⟩ := hp
    have h_target : p.1 ∈ chartTargetEuclid (I := I) (M := M) α :=
      hK_target hpK
    have h_xi_norm_one : ‖p.2‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hpS
      exact hpS
    have h_xi_ne : p.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h_xi_norm_one
      exact (one_ne_zero h_xi_norm_one.symm)
    exact weighted_quadForm_pos_of_mem (I := I) g α h_target p.2 h_xi_ne
  by_cases hKne : (K ×ˢ S).Nonempty
  · obtain ⟨lamK, hlamK_pos, hlamK_le⟩ :=
      hKS_compact.exists_forall_le' h_cont h_strict_pos
    refine ⟨lamK, hlamK_pos, ?_⟩
    intro y hyK ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have h_inner :
          ⟪(0 : EuclN), DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) 0⟫_ℝ = 0 := by
        rw [inner_zero_left]
      rw [h_inner]
      have h_lhs : lamK * ‖(0 : EuclN)‖ ^ 2 = 0 := by
        rw [norm_zero]; ring
      rw [h_lhs]
    · have hξ_norm_pos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      set η : EuclN := (1 / ‖ξ‖) • ξ with hη_def
      have hη_norm : ‖η‖ = 1 := by
        rw [hη_def, norm_smul]
        have hone_div : ‖(1 / ‖ξ‖ : ℝ)‖ = 1 / ‖ξ‖ := by
          rw [Real.norm_eq_abs]
          exact abs_of_pos (one_div_pos.mpr hξ_norm_pos)
        rw [hone_div]
        field_simp
      have hη_in_S : η ∈ S := by
        rw [hS_def, Metric.mem_sphere, dist_zero_right]
        exact hη_norm
      have h_yη : (y, η) ∈ K ×ˢ S := ⟨hyK, hη_in_S⟩
      have h_bound : lamK ≤ rayleighInt (I := I) g α y η := hlamK_le (y, η) h_yη
      change lamK * ‖ξ‖ ^ 2 ≤ rayleighInt (I := I) g α y ξ
      have h_scale : rayleighInt (I := I) g α y ξ =
          ‖ξ‖ ^ 2 * rayleighInt (I := I) g α y η := by
        unfold rayleighInt
        have hξ_eq_norm_smul : ξ = ‖ξ‖ • η := by
          rw [hη_def]
          rw [← smul_assoc, smul_eq_mul]
          rw [show ‖ξ‖ * (1 / ‖ξ‖) = 1 from by field_simp]
          rw [one_smul]
        conv_lhs => rw [hξ_eq_norm_smul]
        have h_matMulE_smul :
            DeGiorgi.matMulE (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) (‖ξ‖ • η) =
              ‖ξ‖ • DeGiorgi.matMulE (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
                weightedInvGramOnEuclid (I := I) g α i j y)) η := by
          apply WithLp.ofLp_injective 2
          simp only [DeGiorgi.matMulE_ofLp]
          change (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)).mulVec
                (‖ξ‖ • η.ofLp) =
            ‖ξ‖ • (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)).mulVec η.ofLp
          rw [Matrix.mulVec_smul]
        rw [h_matMulE_smul]
        rw [inner_smul_left, inner_smul_right]
        simp only [conj_trivial, sq]
        ring
      rw [h_scale]
      have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
      calc lamK * ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * lamK := by ring
        _ ≤ ‖ξ‖ ^ 2 * rayleighInt (I := I) g α y η :=
            mul_le_mul_of_nonneg_left h_bound h_norm_sq_nn
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    have hK_empty : K = ∅ := by
      by_contra h_ne
      have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr h_ne
      obtain ⟨y, hy⟩ := h_K_ne
      have hS_ne : S.Nonempty := by
        have hpos : (0 : ℕ) < Module.finrank ℝ E :=
          Nat.pos_of_ne_zero (NeZero.ne _)
        refine ⟨EuclideanSpace.single (⟨0, hpos⟩ : Fin (Module.finrank ℝ E)) 1, ?_⟩
        rw [hS_def, Metric.mem_sphere, dist_zero_right]
        rw [PiLp.norm_single]
        exact abs_one
      obtain ⟨η, hη⟩ := hS_ne
      have hyη : (y, η) ∈ K ×ˢ S := ⟨hy, hη⟩
      rw [hKne] at hyη
      exact hyη.elim
    refine ⟨1, one_pos, ?_⟩
    intro y hy ξ
    rw [hK_empty] at hy
    exact hy.elim

/-- The Kronecker-delta entry of the identity matrix on `Fin n`. -/
private def kronDelta (i j : Fin (Module.finrank ℝ E)) : ℝ := if i = j then 1 else 0

private lemma kronDelta_self (i : Fin (Module.finrank ℝ E)) :
    kronDelta (E := E) i i = 1 := by
  simp [kronDelta]

private lemma kronDelta_symm (i j : Fin (Module.finrank ℝ E)) :
    kronDelta (E := E) i j = kronDelta (E := E) j i := by
  by_cases h : i = j
  · subst h; rfl
  · simp [kronDelta, h, Ne.symm h]

/-- The globally-defined matrix entry combining the volume-weighted inverse
Gram (modulated by the cutoff `χ`) with the identity matrix.

On the support of `χ`, this is the actual chart-pulled `√det · G⁻¹`. Off the
support of `χ`, this is the identity matrix `δ_{ij}`. -/
def extendedMatrix
    (g : SmoothRiemannianMetric I M) (α : M) (χ : EuclN → ℝ)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  χ y * weightedInvGramOnEuclid (I := I) g α i j y +
    (1 - χ y) * kronDelta (E := E) i j

/-- Symmetry of the extended matrix on the support of the cutoff: relies on the
chart-pulled metric being symmetric there, plus symmetry of the Kronecker
delta. -/
lemma extendedMatrix_symm_of_mem
    (g : SmoothRiemannianMetric I M) (α : M) (χ : EuclN → ℝ)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y := by
  unfold extendedMatrix
  rw [weightedInvGramOnEuclid_symm_of_mem (I := I) g α i j hy]
  rw [kronDelta_symm (E := E) i j]

/-- Symmetry off `tsupport χ` (where `χ y = 0`): both sides reduce to
`(1) * δ_{ij}`. -/
lemma extendedMatrix_symm_off_tsupport
    (g : SmoothRiemannianMetric I M) (α : M) {χ : EuclN → ℝ}
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN} (hy : y ∉ tsupport χ) :
    extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y := by
  have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h_lhs : extendedMatrix (I := I) g α χ i j y = kronDelta (E := E) i j := by
    unfold extendedMatrix
    rw [hχ_zero]; ring
  have h_rhs : extendedMatrix (I := I) g α χ j i y = kronDelta (E := E) j i := by
    unfold extendedMatrix
    rw [hχ_zero]; ring
  rw [h_lhs, h_rhs, kronDelta_symm]

/-- Combined symmetry: the extended matrix is symmetric provided the cutoff
is supported inside the chart target. -/
lemma extendedMatrix_symm
    (g : SmoothRiemannianMetric I M) (α : M) {χ : EuclN → ℝ}
    (hχ_supp : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y := by
  by_cases hy : y ∈ tsupport χ
  · exact extendedMatrix_symm_of_mem (I := I) g α χ i j (hχ_supp hy)
  · exact extendedMatrix_symm_off_tsupport (I := I) g α i j hy

lemma extendedMatrix_contDiff
    (g : SmoothRiemannianMetric I M) (α : M) [I.Boundaryless]
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_supp : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j) := by
  set f : EuclN → ℝ := extendedMatrix (I := I) g α χ i j with hf_def
  set s : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_def
  set t : Set EuclN := (tsupport χ)ᶜ with ht_def
  have hs_open : IsOpen s := chartTargetEuclid_isOpen (I := I) (M := M) α
  have ht_open : IsOpen t := isClosed_tsupport _ |>.isOpen_compl
  have hcov : s ∪ t = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact Or.inl (hχ_supp hy)
    · exact Or.inr hy
  have hf_on_s : ContDiffOn ℝ (⊤ : ℕ∞) f s := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun y =>
      χ y * weightedInvGramOnEuclid (I := I) g α i j y +
        (1 - χ y) * kronDelta (E := E) i j) s
    refine ContDiffOn.add ?_ ?_
    · exact (hχ_smooth.contDiffOn).mul
        (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j)
    · have h_one_minus_chi : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclN => 1 - χ y) s :=
        (contDiffOn_const.sub hχ_smooth.contDiffOn)
      exact h_one_minus_chi.mul contDiffOn_const
  have hf_on_t : ContDiffOn ℝ (⊤ : ℕ∞) f t := by
    have hf_eq_const : ∀ y ∈ t, f y = kronDelta (E := E) i j := by
      intro y hy
      have hy_compl : y ∉ tsupport χ := hy
      have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy_compl
      change extendedMatrix (I := I) g α χ i j y = kronDelta (E := E) i j
      unfold extendedMatrix
      rw [hχ_zero]
      ring
    have h_const_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : EuclN => kronDelta (E := E) i j) t :=
      contDiffOn_const
    exact h_const_smooth.congr (fun y hy => hf_eq_const y hy)
  exact contDiff_of_contDiffOn_union_of_isOpen hf_on_s hf_on_t hcov hs_open ht_open

/-- Decomposition of the Rayleigh quotient of the extended matrix into a
χ-weighted weighted-inverse-Gram piece plus a (1 - χ)-weighted identity
piece. -/
lemma extendedMatrix_quad_decomp
    (g : SmoothRiemannianMetric I M) (α : M)
    (χ : EuclN → ℝ) (y : EuclN) (ξ : EuclN) :
    ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ =
      χ y * ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ +
      (1 - χ y) * ‖ξ‖ ^ 2 := by
  classical
  have h_ext : ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        extendedMatrix (I := I) g α χ i j y * ξ.ofLp i * ξ.ofLp j := by
    change (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : star ξ.ofLp = ξ.ofLp := by funext i; exact star_trivial _
    rw [hstar]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_w : ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y * ξ.ofLp i * ξ.ofLp j := by
    change (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [DeGiorgi.matMulE_ofLp]
    have hstar : star ξ.ofLp = ξ.ofLp := by funext i; exact star_trivial _
    rw [hstar]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_norm_sq : ‖ξ‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℝ E), (ξ.ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_ext, h_w, h_norm_sq]
  rw [Finset.mul_sum]
  rw [show (1 - χ y) * ∑ i : Fin (Module.finrank ℝ E), (ξ.ofLp i) ^ 2 =
      ∑ i : Fin (Module.finrank ℝ E), (1 - χ y) * (ξ.ofLp i) ^ 2 from
        (Finset.mul_sum _ _ _)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        χ y * ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y * ξ.ofLp i * ξ.ofLp j) +
      ∑ i : Fin (Module.finrank ℝ E), (1 - χ y) * (ξ.ofLp i) ^ 2 =
      ∑ i : Fin (Module.finrank ℝ E),
        (χ y * ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y * ξ.ofLp i * ξ.ofLp j +
          (1 - χ y) * (ξ.ofLp i) ^ 2) from
        (Finset.sum_add_distrib).symm]
  refine Finset.sum_congr rfl ?_
  intro i _
  unfold extendedMatrix
  rw [show ∑ j : Fin (Module.finrank ℝ E),
        (χ y * weightedInvGramOnEuclid (I := I) g α i j y +
            (1 - χ y) * kronDelta (E := E) i j) * ξ.ofLp i * ξ.ofLp j =
      ∑ j : Fin (Module.finrank ℝ E),
        ((χ y * weightedInvGramOnEuclid (I := I) g α i j y *
            ξ.ofLp i * ξ.ofLp j) +
          (1 - χ y) * kronDelta (E := E) i j * ξ.ofLp i * ξ.ofLp j) from by
    refine Finset.sum_congr rfl ?_
    intro j _
    ring]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  · rw [Finset.sum_eq_single i]
    · rw [kronDelta_self]
      ring
    · intro j _ hji
      have : kronDelta (E := E) i j = 0 := by
        unfold kronDelta
        rw [if_neg (Ne.symm hji)]
      rw [this]
      ring
    · intro h_not_mem
      exact absurd (Finset.mem_univ i) h_not_mem

/-- On the support of `χ` (where `χ y > 0` a fortiori `≥ 0`), the extended
matrix is a convex combination of the (positive-definite) chart-pulled
`√det · G⁻¹` and the (positive-definite) identity. The Rayleigh quotient
inherits a positive lower bound. -/
lemma extendedMatrix_coercive_on_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {χ : EuclN → ℝ}
    (hχ_range : Set.range χ ⊆ Set.Icc (0 : ℝ) 1)
    {y : EuclN} (_hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    {lamK : ℝ} (_hlamK_pos : 0 < lamK)
    (h_unif : ∀ ξ : EuclN,
        lamK * ‖ξ‖ ^ 2 ≤
          ⟪ξ, DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ)
    (ξ : EuclN) :
    min (1 : ℝ) lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ := by
  classical
  have hχ_in_Icc : χ y ∈ Set.Icc (0 : ℝ) 1 :=
    hχ_range (Set.mem_range_self y)
  have hχ_nn : 0 ≤ χ y := hχ_in_Icc.1
  have hχ_le_one : χ y ≤ 1 := hχ_in_Icc.2
  have h_one_minus_chi_nn : 0 ≤ 1 - χ y := by linarith
  have h_decomp := extendedMatrix_quad_decomp (I := I) g α χ y ξ
  rw [h_decomp]
  have h_unif_ξ := h_unif ξ
  have h_first : χ y * (lamK * ‖ξ‖ ^ 2) ≤
      χ y * ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ :=
    mul_le_mul_of_nonneg_left h_unif_ξ hχ_nn
  have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
  have h_min_le : min (1 : ℝ) lamK ≤ χ y * lamK + (1 - χ y) := by
    have h_min_le_lamK : min (1 : ℝ) lamK ≤ lamK := min_le_right _ _
    have h_min_le_one : min (1 : ℝ) lamK ≤ 1 := min_le_left _ _
    have h1 : χ y * min (1 : ℝ) lamK ≤ χ y * lamK :=
      mul_le_mul_of_nonneg_left h_min_le_lamK hχ_nn
    have h2 : (1 - χ y) * min (1 : ℝ) lamK ≤ (1 - χ y) * 1 :=
      mul_le_mul_of_nonneg_left h_min_le_one h_one_minus_chi_nn
    have h_factor : (χ y) * min (1 : ℝ) lamK + (1 - χ y) * min (1 : ℝ) lamK =
        min (1 : ℝ) lamK := by ring
    linarith
  have h_first_step : min (1 : ℝ) lamK * ‖ξ‖ ^ 2 ≤
      (χ y * lamK + (1 - χ y)) * ‖ξ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h_min_le h_norm_sq_nn
  have h_alg : (χ y * lamK + (1 - χ y)) * ‖ξ‖ ^ 2 =
      χ y * (lamK * ‖ξ‖ ^ 2) + (1 - χ y) * ‖ξ‖ ^ 2 := by ring
  linarith

/-- Off the support of `χ` (where `χ y = 0`), the extended matrix equals the
identity, so its Rayleigh quotient is exactly `‖ξ‖²`. -/
lemma extendedMatrix_eq_kronDelta_off_tsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {χ : EuclN → ℝ}
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) (hy : y ∉ tsupport χ) :
    extendedMatrix (I := I) g α χ i j y = kronDelta (E := E) i j := by
  have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
  unfold extendedMatrix
  rw [hχ_zero]
  ring

/-- Identity-matrix Rayleigh quotient: `⟪ξ, kronDelta-Matrix ξ⟫ = ‖ξ‖²`. -/
lemma kronDelta_quad_eq_norm_sq (ξ : EuclN) :
    ⟪ξ, DeGiorgi.matMulE
      (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        kronDelta (E := E) i j)) ξ⟫_ℝ = ‖ξ‖ ^ 2 := by
  classical
  have h_eq : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      kronDelta (E := E) i j)) =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [kronDelta]
    · simp [kronDelta, h]
  rw [h_eq]
  have hmul1 : DeGiorgi.matMulE
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) ξ = ξ := by
    apply WithLp.ofLp_injective 2
    rw [DeGiorgi.matMulE_ofLp]
    exact Matrix.one_mulVec _
  rw [hmul1]
  rw [real_inner_self_eq_norm_sq]

/-- Coercivity of the extended matrix in the universal sense: for any `y` and
any `ξ`, the Rayleigh quotient is bounded below by `min(1, lamK) ‖ξ‖²`. -/
lemma extendedMatrix_coercive
    (g : SmoothRiemannianMetric I M) (α : M)
    {χ : EuclN → ℝ}
    (hχ_range : Set.range χ ⊆ Set.Icc (0 : ℝ) 1)
    (hχ_supp : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {lamK : ℝ} (hlamK_pos : 0 < lamK) (hlamK_le : lamK ≤ 1)
    (h_unif : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
        lamK * ‖ξ‖ ^ 2 ≤
          ⟪ξ, DeGiorgi.matMulE
            (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
              weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ)
    (y : EuclN) (ξ : EuclN) :
    lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ := by
  classical
  by_cases hy : y ∈ tsupport χ
  · have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hχ_supp hy
    have h_unif_y : ∀ ξ : EuclN, lamK * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ :=
      fun ξ => h_unif y hy ξ
    have h_min_eq : min (1 : ℝ) lamK = lamK := min_eq_right hlamK_le
    have h := extendedMatrix_coercive_on_chart (I := I) g α
      (χ := χ) hχ_range (y := y) hy_target hlamK_pos h_unif_y ξ
    rw [h_min_eq] at h
    exact h
  · have h_eq : ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ = ‖ξ‖ ^ 2 := by
      have h_mat_eq : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            extendedMatrix (I := I) g α χ i j y)) =
          Matrix.of (fun i j : Fin (Module.finrank ℝ E) => kronDelta (E := E) i j) := by
        ext i j
        exact extendedMatrix_eq_kronDelta_off_tsupport (I := I) g α i j y hy
      rw [h_mat_eq]
      exact kronDelta_quad_eq_norm_sq ξ
    rw [h_eq]
    have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have : lamK * ‖ξ‖ ^ 2 ≤ 1 * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamK_le h_norm_sq_nn
    linarith

/-- **Smooth global extension of the chart-pulled volume-weighted inverse Gram
matrix.**

For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M`, a
chart point `α : M`, and any compact `K ⊆ chartTargetEuclid α` (the Euclidean
image of the chart-target via `toEuclidean`), there is:

* a smooth elliptic bilinear-form data `B : SmoothEllipticBilinearForm n univ`
  (with `c = 0`),
* a precompact open neighborhood `Ω' ⊇ K` (the open thickening that defines
  the cutoff support, contained in `chartTargetEuclid α`),

such that:
* `B.a y i j` agrees on `K` with the volume-weighted inverse Gram matrix
  entry `√(det G(α, x_y)) · G(α, x_y)⁻¹_{ij}`,
* `B` is uniformly elliptic with `B.lam = min(1, lamK0) > 0` where
  `lamK0 > 0` is the strict positive lower bound on the Rayleigh quotient
  of the volume-weighted inverse Gram matrix over a compact thickening of
  `K`,
* outside the support of the cutoff, `B.a y i j = δ_{ij}` (identity matrix).

The construction uses a smooth cutoff function `χ` to interpolate between
the chart-pulled metric data on a neighborhood of `K` and the identity matrix
elsewhere; see `extendedMatrix` for the explicit formula. -/
theorem exists_smooth_metric_extension
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN}
    (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Ω' : Set EuclN,
      IsOpen Ω' ∧ K ⊆ Ω' ∧ IsCompact (closure Ω') ∧
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α ∧
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hO : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, δ_pos, hδ_subset⟩ := hK.exists_cthickening_subset_open hO hK_target
  set Ω' : Set EuclN := Metric.thickening δ K with hΩ'_def
  set K' : Set EuclN := Metric.cthickening δ K with hK'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK'_compact : IsCompact K' := hK.cthickening (r := δ)
  have h_K_in_Ω' : K ⊆ Ω' := Metric.self_subset_thickening δ_pos K
  have h_Ω'_in_K' : Ω' ⊆ K' := Metric.thickening_subset_cthickening δ K
  have h_K'_in_chart : K' ⊆ chartTargetEuclid (I := I) (M := M) α := hδ_subset
  have h_closure_Ω'_in_K' : closure Ω' ⊆ K' :=
    Metric.closure_thickening_subset_cthickening δ K
  have h_closure_compact : IsCompact (closure Ω') :=
    hK'_compact.of_isClosed_subset isClosed_closure h_closure_Ω'_in_K'
  have h_closure_in_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closure_Ω'_in_K'.trans h_K'_in_chart
  obtain ⟨χ, hχ_smooth, hχ_supp, hχ_range, hχ_one, hχ_tsupp⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := K) (Ω' := Ω') hK hΩ'_open h_K_in_Ω'
  have hχ_tsupp_chart : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    have h1 : y ∈ Ω' := hχ_tsupp hy
    exact (h_Ω'_in_K'.trans h_K'_in_chart) h1
  have hχ_tsupp_compact : IsCompact (tsupport χ) := hχ_supp
  obtain ⟨lamK0, hlamK0_pos, hlamK0_bound⟩ :=
    exists_unif_lower_bound_on_compact (I := I) g α hχ_tsupp_compact hχ_tsupp_chart
  set lamK : ℝ := min 1 lamK0 with hlamK_def
  have hlamK_pos : 0 < lamK := lt_min one_pos hlamK0_pos
  have hlamK_le_one : lamK ≤ 1 := min_le_left _ _
  have hlamK_le_lamK0 : lamK ≤ lamK0 := min_le_right _ _
  have hlamK0_bound_for_lamK : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
    intro y hy ξ
    have h0 := hlamK0_bound y hy ξ
    have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have h_le : lamK * ‖ξ‖ ^ 2 ≤ lamK0 * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamK_le_lamK0 h_norm_sq_nn
    linarith
  let aFun : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      extendedMatrix (I := I) g α χ i j y)
  have h_a_smooth : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => aFun y i j) := by
    intro i j
    change ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j)
    exact extendedMatrix_contDiff (I := I) g α
      (χ := χ) hχ_smooth hχ_tsupp_chart i j
  have h_a_symm : ∀ y i j, aFun y i j = aFun y j i := by
    intro y i j
    change extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y
    exact extendedMatrix_symm (I := I) g α
      (χ := χ) hχ_tsupp_chart i j y
  have h_a_coercive : ∀ y ∈ (Set.univ : Set EuclN), ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (aFun y) ξ⟫_ℝ := by
    intro y _ ξ
    change lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ
    exact extendedMatrix_coercive (I := I) g α
      (χ := χ) hχ_range hχ_tsupp_chart hlamK_pos hlamK_le_one
      hlamK0_bound_for_lamK y ξ
  let B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
    { a := aFun
      c := fun _ => 0
      symm := h_a_symm
      smooth_a := h_a_smooth
      smooth_c := contDiff_const
      lam := lamK
      capLam := max lamK 1
      hlam_pos := hlamK_pos
      hlam_le_capLam := le_max_left _ _
      coercive := h_a_coercive }
  have h_agree : ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y := by
    intro y hy i j
    change extendedMatrix (I := I) g α χ i j y =
      weightedInvGramOnEuclid (I := I) g α i j y
    have hχ_y : χ y = 1 := hχ_one y hy
    unfold extendedMatrix
    rw [hχ_y]
    ring
  refine ⟨Ω', hΩ'_open, h_K_in_Ω', h_closure_compact, h_closure_in_chart, B, h_agree, rfl⟩

end MetricExtension
end Laplacian
end Analysis
end DifferentialGeometry
