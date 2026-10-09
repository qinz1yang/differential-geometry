import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteJacobiChart

/-!
# The finite Jacobi equation of a chart geodesic variation (consumer of `FiniteJacobiChart`)

`hasDerivAt_jacobi_pairing_of_geodesic_family`: for a `C²` two-parameter family `(Y, V)` of chart
geodesics in `h` for `C²` symmetric coercive coefficients `b` (`∂ₕY = V`, `∂ₕV = −Γ(Y)(V, V)`), and a
field `W` parallel along `h ↦ Y(t₀, h)`, the variation field `J = ∂ₜY(t₀, ·)` satisfies
`(b(J, W))' = b(D_h J, W)` and `(b(D_h J, W))' = −Rm04(J, V, V, W)`, where `D_h J = ∂ₜV + Γ(V, J)`.
This is the per-chart identity used by the general-dimension transverse shift (lane CMS3-SHIFT, G3).

`coefficientRm04_jacobi_matrix_symm`: the frame matrix `Rm04(e_k, u, u, e_i)` is symmetric.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)
open DifferentialGeometry.Analysis (coefficientRm04)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance continuousDualEquiv_CMS3SHIFTa : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroup_CMS3SHIFTa : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpace_CMS3SHIFTa : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Jacobi pairing of a chart geodesic variation.** -/
theorem hasDerivAt_jacobi_pairing_of_geodesic_family {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Y V : ℝ × ℝ → E} {W : ℝ → E} {t₀ h₀ : ℝ}
    (hb : ContDiffAt ℝ 2 b (Y (t₀, h₀)))
    (hsymm : ∀ᶠ y in 𝓝 (Y (t₀, h₀)), ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b (Y (t₀, h₀))))
    (hY : ContDiffAt ℝ 2 Y (t₀, h₀)) (hV : ContDiffAt ℝ 2 V (t₀, h₀))
    (hgY : ∀ᶠ z in 𝓝 (t₀, h₀), HasDerivAt (fun s => Y (z.1, s)) (V z) z.2)
    (hgV : ∀ᶠ z in 𝓝 (t₀, h₀),
      HasDerivAt (fun s => V (z.1, s)) (-(raisedKoszulOp (b (Y z)) (fderiv ℝ b (Y z)) (V z) (V z))) z.2)
    (hW : HasDerivAt W
      (-(raisedKoszulOp (b (Y (t₀, h₀))) (fderiv ℝ b (Y (t₀, h₀))) (V (t₀, h₀)) (W h₀))) h₀) :
    HasDerivAt (fun s => b (Y (t₀, s)) (fderiv ℝ Y (t₀, s) ((1 : ℝ), (0 : ℝ))) (W s))
        (b (Y (t₀, h₀)) (fderiv ℝ V (t₀, h₀) ((1 : ℝ), (0 : ℝ)) +
          raisedKoszulOp (b (Y (t₀, h₀))) (fderiv ℝ b (Y (t₀, h₀))) (V (t₀, h₀))
            (fderiv ℝ Y (t₀, h₀) ((1 : ℝ), (0 : ℝ)))) (W h₀)) h₀ ∧
      HasDerivAt (fun s => b (Y (t₀, s)) (fderiv ℝ V (t₀, s) ((1 : ℝ), (0 : ℝ)) +
          raisedKoszulOp (b (Y (t₀, s))) (fderiv ℝ b (Y (t₀, s))) (V (t₀, s))
            (fderiv ℝ Y (t₀, s) ((1 : ℝ), (0 : ℝ)))) (W s))
        (-(coefficientRm04 b (Y (t₀, h₀)) (fderiv ℝ Y (t₀, h₀) ((1 : ℝ), (0 : ℝ))) (V (t₀, h₀))
          (V (t₀, h₀)) (W h₀))) h₀ := by
  obtain ⟨hΓsym, hΓd, -⟩ := koszul_christoffel_data hb hsymm hco
  obtain ⟨hJ, hK⟩ := hasDerivAt_chart_jacobi_of_geodesic_family
    (Γ := fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) hY hV hΓd hΓsym hgY hgV
  exact hasDerivAt_jacobi_pairing (x := fun s => Y (t₀, s)) (U := fun s => V (t₀, s))
    (J := fun s => fderiv ℝ Y (t₀, s) ((1 : ℝ), (0 : ℝ)))
    (K := fun s => fderiv ℝ V (t₀, s) ((1 : ℝ), (0 : ℝ))) hb hsymm hco hgY.self_of_nhds
    hgV.self_of_nhds hJ hK hW

/-- The frame matrix of the Jacobi operator is symmetric (consumer of the pair symmetry). -/
theorem coefficientRm04_jacobi_matrix_symm {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hb : ContDiffAt ℝ 2 b x) (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u)
    (hco : IsCoercive (b x)) {n : ℕ} (e : Fin n → E) (u : E) (i k : Fin n) :
    coefficientRm04 b x (e k) u u (e i) = coefficientRm04 b x (e i) u u (e k) :=
  coefficientRm04_jacobi_symm hb hsymm hco (e k) u (e i)

end DifferentialGeometry.Geometry.FiniteSoul
