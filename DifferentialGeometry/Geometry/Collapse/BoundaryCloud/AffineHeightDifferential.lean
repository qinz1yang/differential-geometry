import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation

/-!
# BCG02's differential clause: the saturation kernel (lane BCG-4)

Blueprint 207B, BCG02 proof (`B:8889–8958`): along the minimizing direction `v` from `x` to the
witness `y`, BCG02.b makes `DU_b(v)` close to the quotient `(U_b(y) − U_b(x))/ℓ`, the raw alignment
and the axis lift make that quotient close to `1`, and the original adapted test makes
`A_b Dη_a(v)` close to `1`; "the endpoint distortions divided by their positive separations then
give saturation errors less than `θ²/10⁵` for both covectors. Their norms are at most one plus their
prescribed small errors. FC15's pointwise Riesz estimate gives `‖DU_b − A_bDη_a‖ < θ`."

* `norm_sub_lt_of_saturation_BCG4`: FC15 with the blueprint's budget — two covectors of norm
  `≤ 1 + ε`, both `≥ 1 − ε` on one unit vector, `ε ≤ θ²/10⁵`, `θ < 1` ⟹ `‖f − g‖ < θ`;
* `norm_sub_lt_of_slopes_BCG4`: the same from slope data — `|f v − s₁| ≤ δ₁`, `|g v − s₂| ≤ δ₂`,
  `1 − δ₃ ≤ s₁, s₂`, norms `≤ 1 + δ₀`, `δ₀ + δ₁ + δ₂ + δ₃ ≤ θ²/10⁵` ⟹ `‖f − g‖ < θ` (the form in
  which BCG02.b, the raw alignment and the adapted test enter).
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **FC15 with BCG02's budget**: two covectors of norm `≤ 1 + ε` which are both `≥ 1 − ε` on one
unit vector differ by less than `θ` once `ε ≤ θ²/10⁵` and `0 < θ < 1`. -/
theorem norm_sub_lt_of_saturation_BCG4 (f g : StrongDual ℝ E) {θ ε : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hε : 0 ≤ ε) (hεθ : ε ≤ θ ^ 2 / 100000) (hf : ‖f‖ ≤ 1 + ε)
    (hg : ‖g‖ ≤ 1 + ε) (w : E) (hw : ‖w‖ = 1) (hfw : 1 - ε ≤ f w) (hgw : 1 - ε ≤ g w) :
    ‖f - g‖ < θ := by
  have h := ContinuousLinearMap.norm_sub_le_of_common_unit_saturation f g hε hf hg w hw hfw hgw
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hε1 : ε ≤ 1 := by nlinarith
  have hq : 4 * ε + ε ^ 2 < (θ / 2) ^ 2 := by nlinarith
  have hs : Real.sqrt (4 * ε + ε ^ 2) < θ / 2 :=
    (Real.sqrt_lt' (by positivity)).mpr hq
  linarith

/-- **BCG02's differential clause from slope data**: if `f v` and `g v` are within `δ₁`, `δ₂` of
slopes `s₁, s₂ ≥ 1 − δ₃` at a unit vector `v`, the norms are `≤ 1 + δ₀`, and
`δ₀ + δ₁ + δ₂ + δ₃ ≤ θ²/10⁵` with `0 < θ < 1`, then `‖f − g‖ < θ`. -/
theorem norm_sub_lt_of_slopes_BCG4 (f g : StrongDual ℝ E) {θ δ₀ δ₁ δ₂ δ₃ s₁ s₂ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (h2 : 0 ≤ δ₂) (h3 : 0 ≤ δ₃)
    (hbud : δ₀ + δ₁ + δ₂ + δ₃ ≤ θ ^ 2 / 100000) (hf : ‖f‖ ≤ 1 + δ₀) (hg : ‖g‖ ≤ 1 + δ₀)
    (v : E) (hv : ‖v‖ = 1) (hfs : |f v - s₁| ≤ δ₁) (hgs : |g v - s₂| ≤ δ₂) (hs₁ : 1 - δ₃ ≤ s₁)
    (hs₂ : 1 - δ₃ ≤ s₂) : ‖f - g‖ < θ := by
  have hfs' := (abs_le.mp hfs).1
  have hgs' := (abs_le.mp hgs).1
  exact norm_sub_lt_of_saturation_BCG4 f g hθ hθ1 (by positivity) hbud (by linarith)
    (by linarith) v hv (by linarith) (by linarith)

end DifferentialGeometry.Geometry.Collapse
