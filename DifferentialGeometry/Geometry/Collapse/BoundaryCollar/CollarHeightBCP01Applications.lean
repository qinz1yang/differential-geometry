import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightBCP01
import DifferentialGeometry.Analysis.Calculus.Taylor.TangentChord

/-!
# BCP01 discharges the chord hypothesis of BCP02.c

The BCP02.c kernel `abs_deriv_sub_chord_le` (`Analysis/Calculus/Taylor/TangentChord.lean`) takes a
bound `‖iteratedFDeriv ℝ 2 f t‖ ≤ c` on a segment. For `f = η ∘ γ`, `γ` a geodesic of `g` running
in the band `2 ≤ z ≤ 98` of a collar, `(η ∘ γ)'' = Hess_g η(γ', γ')`
(`abstractHessian_apply_velocity_of_hasGeodesicEquationAt`) and BCP01.b gives
`|Hess_g η(γ', γ')| ≤ (3/2) |γ'|_g²`.

* `CuspEmbedding.abs_iteratedDeriv_two_comp_geodesic_le`: the second-derivative bound along a
  geodesic, for any smooth `η` with the BCP01.b Hessian bound on the band.
* `CuspEmbedding.exists_smooth_height_chord` (BCP02.c with the BCP01 height): there is a smooth
  `η` (the BCP01 height, `|η − ζ| < ε` on the band) such that for every geodesic segment
  `γ : [x, x + ℓ] → e(2 ≤ z ≤ 98)` of speed `|γ'|_g ≤ s`,
  `|(η ∘ γ)'(x) − (η(γ(x + ℓ)) − η(γ x))/ℓ| ≤ (3/4) s² ℓ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- Along a geodesic through a band point, `|(η ∘ γ)''| ≤ (3/2) |γ'|_g²` when `η` has the
BCP01.b Hessian bound there. -/
theorem CuspEmbedding.abs_iteratedDeriv_two_comp_geodesic_le (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {γ : ℝ → W.Carrier} {t s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 γ t) (hgeo : HasGeodesicEquationAt g γ t)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) (hpt : e.toFun p = γ t)
    (hH : ∀ u w : TangentSpace W.model (e.toFun p),
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
          (e.toFun p) u w| ≤
        3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w))
    (hspeed : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) W.model γ t ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) W.model γ t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ s ^ 2) :
    |iteratedDeriv 2 (η ∘ γ) t| ≤ 3 / 2 * s ^ 2 := by
  have hint : W.model.IsInteriorPoint (γ t) := by
    rw [← hpt]
    refine (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mpr fun hb => ?_
    have h0 := (e.boundary_preimage hp).mp hb
    linarith
  have hη2 : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 η (γ t) := (hη _).of_le (by simp)
  have hval := abstractHessian_apply_velocity_of_hasGeodesicEquationAt g hη2 hγ hint hgeo
  dsimp only at hval
  rw [← hval]
  set v := mfderiv 𝓘(ℝ, ℝ) W.model γ t ((NormedSpace.fromTangentSpace t).symm 1) with hv
  have hhess : abstractHessian g η (γ t) v v =
      (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η (γ t) v v := by
    rw [CovariantDerivative.hessian_trivial_eq_cotangentCov _ hη2]
    rfl
  rw [hhess]
  rw [hpt] at hH
  have h := hH v v
  have hgv := metric_inner_self_nonneg g (γ t) v
  rw [mul_assoc, ← Real.sqrt_mul hgv, Real.sqrt_mul_self hgv] at h
  calc _ ≤ 3 / 2 * g.inner (γ t) v v := h
    _ ≤ 3 / 2 * s ^ 2 := by linarith

/-- **BCP02.c from BCP01.** The BCP01 height satisfies the chord estimate along every geodesic
segment in the band `2 ≤ z ≤ 98` (speed `≤ s`): the hypothesis `hM` of `abs_deriv_sub_chord_le`
is discharged with `c = (3/2) s²`. -/
theorem CuspEmbedding.exists_smooth_height_chord (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε) ∧
      ∀ (γ : ℝ → W.Carrier) (x ℓ s : ℝ), 0 < ℓ →
        (∀ t ∈ Icc x (x + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 γ t) →
        (∀ t ∈ Icc x (x + ℓ), HasGeodesicEquationAt g γ t) →
        (∀ t ∈ Icc x (x + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
          e.toFun p = γ t) →
        (∀ t ∈ Icc x (x + ℓ), g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) W.model γ t ((NormedSpace.fromTangentSpace t).symm 1))
          (mfderiv 𝓘(ℝ, ℝ) W.model γ t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ s ^ 2) →
        |deriv (η ∘ γ) x - (η (γ (x + ℓ)) - η (γ x)) / ℓ| ≤ 3 / 4 * s ^ 2 * ℓ := by
  obtain ⟨η, -, -, -, hη, -, hb, -⟩ := e.bcp01 hK hδ0 hδ hε hε1
  refine ⟨η, hη, fun p hp h2 h98 => (hb p hp h2 h98).1, ?_⟩
  intro γ x ℓ s hℓ hγ hgeo hband hspeed
  have hf : ∀ t ∈ Icc x (x + ℓ), ContDiffAt ℝ 2 (η ∘ γ) t := fun t ht =>
    contMDiffAt_iff_contDiffAt.mp (((hη _).of_le (by simp)).comp t (hγ t ht))
  have hM : ∀ t ∈ Icc x (x + ℓ), ‖iteratedFDeriv ℝ 2 (η ∘ γ) t‖ ≤ 3 / 2 * s ^ 2 := by
    intro t ht
    obtain ⟨p, hp, h2, h98, hpt⟩ := hband t ht
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact e.abs_iteratedDeriv_two_comp_geodesic_le hη (hγ t ht) (hgeo t ht) hp (by linarith) hpt
      (hb p hp h2 h98).2.2.2.2.2.1 (hspeed t ht)
  have h := DifferentialGeometry.Analysis.abs_deriv_sub_chord_le hℓ hf hM
  calc _ ≤ 3 / 2 * s ^ 2 / 2 * ℓ := h
    _ = 3 / 4 * s ^ 2 * ℓ := by ring

end DifferentialGeometry.Geometry.Collapse
