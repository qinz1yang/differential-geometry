import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

/-!
# The covariant chain rule along a smooth curve

For a smooth Riemannian metric `g` on a smooth boundaryless manifold `M`, a smooth
curve `γ : ℝ → M`, and a smooth tangent vector field `X` on `M`, the intrinsic
covariant derivative along `γ` of the restricted section `r ↦ X (γ r)` agrees with
the (bundled, global) Levi-Civita covariant derivative of `X` in the direction of
the velocity `γ' = dγ_{r₀}(1)`:

`covDerivAlong g γ (fun r => X (γ r)) r₀ = (LeviCivita g) X (γ r₀) (dγ_{r₀} 1)`.

This is the first-order, curvature-free compatibility identity between the two
covariant-derivative constructions in the library:

* `covDerivAlong` (`Geometry/Connection/ParallelTransport/CovariantDerivativeAlong`),
  the chart-pinned-at-the-foot derivative of a section *along a curve*, and
* `LeviCivita` (`Geometry/Connection/LeviCivita/Defs`), the global bundled
  Levi-Civita connection.

Both are computed in the canonical chart at the foot `γ r₀`. There the Christoffel
contraction of one matches the Christoffel-correction CLM of the other
(`christoffelCorrection_eq_chartChristoffelContraction`), the chart-coordinate
velocity slots coincide via the chain-rule bridge
`chartCoord_mfderiv_along_curve_eq_fderiv`, and the derivative-of-the-representation
terms coincide by the ordinary chain rule (the chart pullback of `X` composed with
the chart-coordinate curve). The trivialisation `symmL`/`continuousLinearMapAt`
machinery of `covDerivAlong` is literally the `trivFromE`/`trivToE` machinery of
`LeviCivita`, so the two read-backs into `T_{γ(r₀)} M` agree.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

/-- **The Christoffel-correction CLM equals the chart Christoffel contraction.**
At a basepoint `α`, a foot `x`, a section value `Y : E`, and a tangent vector `v`,
the Levi-Civita-side `christoffelCorrection g α x Y v` (a CLM evaluated at `v`)
coincides with the `covDerivAlong`-side
`chartChristoffelContraction g α (trivToE α x v) Y (extChartAt I α x)`. Both
expand to `∑ᵢⱼₖ Γ^k_{ij}(φ x) · (φ-coordinate of v)ᵢ · Yⱼ • eₖ`; the only work is
to move the `k`-sum outside and the basis scalar through the `•`. -/
private lemma christoffelCorrection_eq_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α x : M) (Y : E) (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x Y v =
      chartChristoffelContraction (I := I) g α (trivToE (I := I) α x v) Y
        (extChartAt I α x) := by
  classical
  rw [christoffelCorrection_apply, chartChristoffelContraction_def]
  set F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E :=
    fun i j k =>
      (chartChristoffel (I := I) g α i j k (extChartAt I α x) *
          (chartModelBasis E).repr (trivToE (I := I) α x v) i *
          (chartModelBasis E).repr Y j) • (chartModelBasis E) k with hF
  have hLHS :
      (∑ i, ∑ j, ∑ k,
          ((chartModelBasis E).repr (trivToE (I := I) α x v) i *
                (chartModelBasis E).repr Y j *
                chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
            (chartModelBasis E) k)
        = ∑ i, ∑ j, ∑ k, F i j k := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => ?_)))
    rw [hF]; congr 1; ring
  have hRHS :
      (∑ k,
          (∑ i, ∑ j,
              chartChristoffel (I := I) g α i j k (extChartAt I α x) *
                chartCoord (E := E) i (trivToE (I := I) α x v) *
                chartCoord (E := E) j Y) •
            (chartModelBasis E) k)
        = ∑ i, ∑ j, ∑ k, F i j k := by
    have hstep1 :
        (∑ k,
            (∑ i, ∑ j,
                chartChristoffel (I := I) g α i j k (extChartAt I α x) *
                  chartCoord (E := E) i (trivToE (I := I) α x v) *
                  chartCoord (E := E) j Y) •
              (chartModelBasis E) k)
          = ∑ k, ∑ i, ∑ j, F i j k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hF, chartCoord_def, chartCoord_def]
    rw [hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  rw [hLHS, hRHS]

/-- The chart-pinned representation of the restricted section `r ↦ X (γ r)`, taken
in the foot chart at `γ r₀`, is exactly the chart-`(γ r₀)`-trivialised representation
`chartE_section_repr (γ r₀) X` of the field `X` pulled back along `γ`. Both apply the
same trivialisation `continuousLinearMapAt` at the foot `γ r₀` to the same fibre
vectors. -/
private lemma chartRepAt_restrict_eq_comp
    (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ) :
    chartRepAt (I := I) γ (fun r => X (γ r)) r₀ =
      chartE_section_repr (I := I) (γ r₀) X ∘ γ := by
  funext s
  rfl

/-- **Chain rule for the chart-representation derivative.** With `α = γ r₀`, the
`r`-derivative at `r₀` of the chart-`α`-trivialised representation of `X` pulled back
along `γ` equals the Fréchet derivative of the chart pullback
`chartE_section_repr α X ∘ (extChartAt I α).symm` at the chart image `extChartAt α (γ r₀)`,
contracted with the chart-coordinate velocity `deriv (chartCurve α γ) r₀`. This is the
ordinary chain rule applied to the eventual factorisation
`chartE_section_repr α X ∘ γ = (chartE_section_repr α X ∘ (extChartAt α).symm) ∘ (extChartAt α ∘ γ)`
near `r₀`. -/
private lemma deriv_chartE_repr_comp_curve_eq
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hX : MDiffAt (T% X) (γ r₀)) :
    deriv (chartE_section_repr (I := I) (γ r₀) X ∘ γ) r₀ =
      fderiv ℝ (chartE_section_repr (I := I) (γ r₀) X ∘ (extChartAt I (γ r₀)).symm)
          (extChartAt I (γ r₀) (γ r₀))
        (deriv (chartCurve (I := I) (γ r₀) γ) r₀) := by
  classical
  set α : M := γ r₀ with hα_def
  set f : E → E := chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm with hf_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hf_diff : DifferentiableAt ℝ f (extChartAt I α (γ r₀)) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hgood hX
  have hu_hd : HasDerivAt u (deriv u r₀) r₀ :=
    ((contDiffAt_chartCurve (I := I) hγ r₀).differentiableAt (by simp)).hasDerivAt
  have hxu : u r₀ = extChartAt I α (γ r₀) := by rw [hu_def, chartCurve_def]
  have hcomp_hd : HasDerivAt (f ∘ u) (fderiv ℝ f (extChartAt I α (γ r₀)) (deriv u r₀)) r₀ := by
    have hf_hd : HasFDerivAt f (fderiv ℝ f (extChartAt I α (γ r₀))) (u r₀) := by
      rw [hxu]; exact hf_diff.hasFDerivAt
    exact hf_hd.comp_hasDerivAt r₀ hu_hd
  have hsrc_nhds : γ ⁻¹' (extChartAt I α).source ∈ 𝓝 r₀ := by
    have hopen : IsOpen (extChartAt I α).source := isOpen_extChartAt_source (I := I) α
    have hmem : γ r₀ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact mem_chart_source H (γ r₀)
    exact hγ.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)
  have heq : (f ∘ u) =ᶠ[𝓝 r₀] chartE_section_repr (I := I) α X ∘ γ := by
    filter_upwards [hsrc_nhds] with s hs
    have hs' : γ s ∈ (extChartAt I α).source := hs
    simp only [Function.comp_apply, hf_def, hu_def, chartCurve_def]
    rw [PartialEquiv.left_inv (extChartAt I α) hs']
  rw [← heq.deriv_eq]
  exact hcomp_hd.deriv

/-- **The covariant chain rule.** For a smooth Riemannian metric `g` on a smooth
boundaryless manifold `M`, a `C^∞` curve `γ : ℝ → M`, and a tangent vector field `X`
on `M` smooth (`MDifferentiable`) at the foot `γ r₀`, the intrinsic covariant
derivative along `γ` of the restricted section `r ↦ X (γ r)` at `r₀` equals the global
Levi-Civita covariant derivative of `X` in the direction of the velocity
`γ'(r₀) = dγ_{r₀}(1)`:

`covDerivAlong g γ (fun r => X (γ r)) r₀ = (LeviCivita g) X (γ r₀) (dγ_{r₀} 1)`.

The proof reads both sides in the canonical chart at the foot `γ r₀`. The
trivialisation read-back `symmL`/`continuousLinearMapAt` of `covDerivAlong` is the
`trivFromE`/`trivToE` of `LeviCivita`, so it suffices to match the two chart-`(γ r₀)`
representatives:

* the derivative-of-representation term, via the ordinary chain rule
  (`deriv_chartE_repr_comp_curve_eq`), using that the chart-coordinate velocity slot
  `trivToE (γ r₀) (dγ_{r₀} 1)` equals `deriv (chartCurve (γ r₀) γ) r₀` (the
  manifold-to-chart velocity bridge `chartCoord_mfderiv_along_curve_eq_fderiv`), and
* the Christoffel term, via `christoffelCorrection_eq_chartChristoffelContraction`. -/
theorem covDerivAlong_restrict_eq_leviCivita
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hX : MDiffAt (T% X) (γ r₀)) :
    covDerivAlong (I := I) g γ (fun r => X (γ r)) r₀ =
      (LeviCivita (I := I) g) X (γ r₀) ((mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ)) := by
  classical
  set α : M := γ r₀ with hα_def
  set v : TangentSpace I α := (mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ) with hv_def
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hvel : trivToE (I := I) α α v = deriv (chartCurve (I := I) α γ) r₀ := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := γ) hγ α (t := r₀) hsrc
    rw [trivToE]
    rw [show v = (mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ) from rfl]
    rw [hbridge]
    rw [show (extChartAt I α ∘ γ) = chartCurve (I := I) α γ from rfl]
    exact fderiv_apply_one_eq_deriv
  have hXmd : MDiffAt (T% (fun y => X y)) α := hX
  rw [show (LeviCivita (I := I) g) X (γ r₀) ((mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ))
        = (LeviCivita (I := I) g).toFun X α v from rfl]
  rw [LeviCivita_chart_apply (I := I) g α hgood hXmd v]
  rw [chartLeviCivita_apply (I := I) g α X hgood v]
  rw [covDerivAlong_def, chartCovDerivAlong_def]
  rw [chartRepAt_restrict_eq_comp (I := I) γ X r₀]
  rw [show (trivializationAt E (TangentSpace I) α).symmL ℝ α = trivFromE (I := I) α α from rfl]
  congr 1
  have hchris :
      chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) r₀)
          ((chartE_section_repr (I := I) α X ∘ γ) r₀)
          (chartCurve (I := I) α γ r₀)
        = christoffelCorrection (I := I) g α α
            (chartE_section_repr (I := I) α X α) v := by
    rw [christoffelCorrection_eq_chartChristoffelContraction (I := I) g α α
      (chartE_section_repr (I := I) α X α) v]
    rw [hvel]
    rw [Function.comp_apply, ← hα_def, chartCurve_def, ← hα_def]
  have hderiv :
      deriv (chartE_section_repr (I := I) α X ∘ γ) r₀ =
        fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α α) (trivToE (I := I) α α v) := by
    rw [hvel]
    exact deriv_chartE_repr_comp_curve_eq (I := I) γ X r₀ hγ hX
  rw [hderiv, hchris]

end CovariantDerivativeAlong

end Riemannian
end Geometry
end DifferentialGeometry

end
