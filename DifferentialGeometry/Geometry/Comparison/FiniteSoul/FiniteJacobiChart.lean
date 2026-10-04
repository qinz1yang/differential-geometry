import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalPlane
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelChart

/-!
# The finite Jacobi equation in a chart (lane CMS3-SHIFT, group G2)

Conventions (lane CMS3-PT, `FiniteParallelDefs.lean`): `D a u v = (∂_a b)(u, v)`,
`Γ y = raisedKoszulOp (b y) (D y)`, parallel `W' = −Γ(x', W)`, geodesic `x' = U`, `U' = −Γ(U, U)`;
curvature `cFC Γ y X Y Z = DΓ[X](Y, Z) − DΓ[Y](X, Z) + Γ(X, Γ(Y, Z)) − Γ(Y, Γ(X, Z))`
(`Geometry.Connection.connectionFormCurvature`) and `coefficientRm04 b y X Y Z W = b(cFC(X, Y, Z), W)`
(`Analysis.coefficientRm04_eq_connectionFormCurvature`). These conventions were checked symbolically
(sympy, `build-logs/scratch/CMS3-SHIFT/jacobi_conventions.py`: six checks pass; the unit sphere gives
`Rm04(v, u, u, v)/area² = +1`).

* `hasDerivAt_chart_jacobi_of_geodesic_family`: for a `C²` two-parameter family `(Y, V)` of chart
  geodesics in `h` (`∂ₕY = V`, `∂ₕV = −Γ(Y)(V, V)`), `J = ∂ₜY` and `K = ∂ₜV` satisfy `J' = K` and the chart
  Jacobi equation `K' = −DΓ[J](V, V) − 2 Γ(K, V)` (mixed partials commute).
* `hasDerivAt_jacobi_covariant`: then `D_h(D_h J) = −cFC(J, V, V)` with `D_h Z = Z' + Γ(V, Z)`.
* `hasDerivAt_pairing_of_parallel`: `(b(Z, W))' = b(D_h Z, W)` for a parallel `W` (metric compatibility).
* `hasDerivAt_jacobi_pairing`: `(b(J, W))' = b(D_h J, W)` and `(b(D_h J, W))' = −Rm04(J, V, V, W)`.
* `coefficientRm04_first_bianchi`, `coefficientRm04_pair_symm`, `coefficientRm04_jacobi_symm`:
  first Bianchi identity and pair symmetry of the coefficient curvature (`C²` coefficients), so the
  Jacobi operator `Rm04(·, u, u, ·)` is symmetric.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)
open DifferentialGeometry.Analysis (coefficientRm04)
open DifferentialGeometry.Geometry.Connection (connectionFormCurvature)

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a family of operators symmetric in its two arguments is symmetric. -/
theorem fderiv_apply_symm_of_eventually_symm {Γ : E → E →L[ℝ] E →L[ℝ] E} {y : E}
    (hΓ : DifferentiableAt ℝ Γ y) (hsymm : ∀ᶠ z in 𝓝 y, ∀ u v : E, Γ z u v = Γ z v u)
    (a u v : E) : fderiv ℝ Γ y a u v = fderiv ℝ Γ y a v u := by
  have hu : HasFDerivAt (fun z => Γ z u v) ((ContinuousLinearMap.apply ℝ E v).comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) u).comp (fderiv ℝ Γ y))) y :=
    (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) u).hasFDerivAt.comp y hΓ.hasFDerivAt)
  have hv : HasFDerivAt (fun z => Γ z v u) ((ContinuousLinearMap.apply ℝ E u).comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) v).comp (fderiv ℝ Γ y))) y :=
    (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) v).hasFDerivAt.comp y hΓ.hasFDerivAt)
  have heq : (fun z => Γ z u v) =ᶠ[𝓝 y] (fun z => Γ z v u) := by
    filter_upwards [hsymm] with z hz
    exact hz u v
  have h := (hu.congr_of_eventuallyEq heq.symm).unique hv
  exact congrArg (fun L : E →L[ℝ] E => L a) h

/-- **Cyclic identity** of `cFC` for a symmetric connection form with symmetric derivative. -/
theorem connectionFormCurvature_cyclic {Γ : E → E →L[ℝ] E →L[ℝ] E} {y : E}
    (hsy : ∀ u v : E, Γ y u v = Γ y v u) (hdsy : ∀ a u v : E, fderiv ℝ Γ y a u v = fderiv ℝ Γ y a v u)
    (X Y Z : E) :
    connectionFormCurvature Γ y X Y Z + connectionFormCurvature Γ y Y Z X +
      connectionFormCurvature Γ y Z X Y = 0 := by
  unfold connectionFormCurvature
  rw [hdsy Y Z X, hdsy Z X Y, hdsy X Z Y, hsy Z X, hsy Y X, hsy Z Y]
  abel

/-- **The covariant Jacobi identity (pointwise algebra).** With `K' = −DΓ[J](U, U) − 2 Γ(K, U)` and
`U' = −Γ(U, U)`, the covariant derivative of `K + Γ(U, J)` is `−cFC(J, U, U)`. -/
theorem jacobi_covariant_eq {Γ : E → E →L[ℝ] E →L[ℝ] E} {y : E}
    (hsy : ∀ u v : E, Γ y u v = Γ y v u) (hdsy : ∀ a u v : E, fderiv ℝ Γ y a u v = fderiv ℝ Γ y a v u)
    (J U K : E) :
    (-(fderiv ℝ Γ y J U U) - (2 : ℝ) • Γ y K U) +
        ((fderiv ℝ Γ y U U + Γ y (-(Γ y U U))) J + Γ y U K) =
      -(connectionFormCurvature Γ y J U U) - Γ y U (K + Γ y U J) := by
  unfold connectionFormCurvature
  rw [add_apply, map_neg, neg_apply, map_add, two_smul, hdsy U U J, hsy K U, hsy (Γ y U U) J,
    hsy J U]
  abel

/-- **Covariant Jacobi identity, derivative form.** -/
theorem hasDerivAt_jacobi_covariant {Γ : E → E →L[ℝ] E →L[ℝ] E} {x U J K : ℝ → E} {h : ℝ}
    (hΓ : DifferentiableAt ℝ Γ (x h)) (hsym : ∀ᶠ y in 𝓝 (x h), ∀ u v : E, Γ y u v = Γ y v u)
    (hx : HasDerivAt x (U h) h) (hU : HasDerivAt U (-(Γ (x h) (U h) (U h))) h)
    (hJ : HasDerivAt J (K h) h)
    (hK : HasDerivAt K (-(fderiv ℝ Γ (x h) (J h) (U h) (U h)) - (2 : ℝ) • Γ (x h) (K h) (U h)) h) :
    HasDerivAt (fun τ => K τ + Γ (x τ) (U τ) (J τ))
      (-(connectionFormCurvature Γ (x h) (J h) (U h) (U h)) -
        Γ (x h) (U h) (K h + Γ (x h) (U h) (J h))) h := by
  have hΓx : HasDerivAt (fun τ => Γ (x τ)) (fderiv ℝ Γ (x h) (U h)) h :=
    hΓ.hasFDerivAt.comp_hasDerivAt h hx
  have h1 := (hΓx.clm_apply hU).clm_apply hJ
  have h2 := hK.add h1
  convert h2 using 1
  exact (jacobi_covariant_eq hsym.self_of_nhds
    (fderiv_apply_symm_of_eventually_symm hΓ hsym) (J h) (U h) (K h)).symm

/-- **Pairing with a parallel field.** If `b` is compatible with `Γ` at `x h`
(`Db[w](p, q) = b(Γ(w, p), q) + b(p, Γ(w, q))`) and `W' = −Γ(x', W)`, then
`(b(Z, W))' = b(Z' + Γ(x', Z), W)`. -/
theorem hasDerivAt_pairing_of_parallel {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {x Z W : ℝ → E} {h : ℝ} {u z₁ : E}
    (hb : DifferentiableAt ℝ b (x h))
    (hcompat : ∀ w p q : E, fderiv ℝ b (x h) w p q = b (x h) (Γ (x h) w p) q + b (x h) p (Γ (x h) w q))
    (hx : HasDerivAt x u h) (hZ : HasDerivAt Z z₁ h) (hW : HasDerivAt W (-(Γ (x h) u (W h))) h) :
    HasDerivAt (fun τ => b (x τ) (Z τ) (W τ)) (b (x h) (z₁ + Γ (x h) u (Z h)) (W h)) h := by
  have hbx : HasDerivAt (fun τ => b (x τ)) (fderiv ℝ b (x h) u) h :=
    hb.hasFDerivAt.comp_hasDerivAt h hx
  have h1 := (hbx.clm_apply hZ).clm_apply hW
  convert h1 using 1
  rw [add_apply, map_neg, hcompat, map_add, add_apply]
  abel

/-- **Chart Jacobi equation of a geodesic family.** If `(t, h) ↦ (Y, V)` is `C²` at `(t₀, h₀)` and
`∂ₕY = V`, `∂ₕV = −Γ(Y)(V, V)` near `(t₀, h₀)`, then `J = ∂ₜY(t₀, ·)` and `K = ∂ₜV(t₀, ·)` satisfy
`J'(h₀) = K(h₀)` and `K'(h₀) = −DΓ[J](V, V) − 2 Γ(K, V)`. -/
theorem hasDerivAt_chart_jacobi_of_geodesic_family {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {Y V : ℝ × ℝ → E} {t₀ h₀ : ℝ} (hY : ContDiffAt ℝ 2 Y (t₀, h₀)) (hV : ContDiffAt ℝ 2 V (t₀, h₀))
    (hΓ : DifferentiableAt ℝ Γ (Y (t₀, h₀)))
    (hsym : ∀ᶠ y in 𝓝 (Y (t₀, h₀)), ∀ u v : E, Γ y u v = Γ y v u)
    (hgY : ∀ᶠ z in 𝓝 (t₀, h₀), HasDerivAt (fun s => Y (z.1, s)) (V z) z.2)
    (hgV : ∀ᶠ z in 𝓝 (t₀, h₀), HasDerivAt (fun s => V (z.1, s)) (-(Γ (Y z) (V z) (V z))) z.2) :
    HasDerivAt (fun s => fderiv ℝ Y (t₀, s) ((1 : ℝ), (0 : ℝ)))
        (fderiv ℝ V (t₀, h₀) ((1 : ℝ), (0 : ℝ))) h₀ ∧
      HasDerivAt (fun s => fderiv ℝ V (t₀, s) ((1 : ℝ), (0 : ℝ)))
        (-(fderiv ℝ Γ (Y (t₀, h₀)) (fderiv ℝ Y (t₀, h₀) ((1 : ℝ), (0 : ℝ))) (V (t₀, h₀))
            (V (t₀, h₀))) -
          (2 : ℝ) • Γ (Y (t₀, h₀)) (fderiv ℝ V (t₀, h₀) ((1 : ℝ), (0 : ℝ))) (V (t₀, h₀))) h₀ := by
  set z₀ : ℝ × ℝ := (t₀, h₀) with hz₀
  set e₁ : ℝ × ℝ := ((1 : ℝ), (0 : ℝ)) with he₁
  set e₂ : ℝ × ℝ := ((0 : ℝ), (1 : ℝ)) with he₂
  have h2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- differentiability near `z₀`
  have hYev : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ Y z :=
    (hY.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  have hVev : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ V z :=
    (hV.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  have hDY : DifferentiableAt ℝ (fderiv ℝ Y) z₀ :=
    (hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hDV : DifferentiableAt ℝ (fderiv ℝ V) z₀ :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hsymY : ∀ a c, fderiv ℝ (fderiv ℝ Y) z₀ a c = fderiv ℝ (fderiv ℝ Y) z₀ c a :=
    hY.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hsymV : ∀ a c, fderiv ℝ (fderiv ℝ V) z₀ a c = fderiv ℝ (fderiv ℝ V) z₀ c a :=
    hV.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  -- slices
  have hsl : ∀ z : ℝ × ℝ, HasDerivAt (fun s : ℝ => (z.1, s)) e₂ z.2 := fun z =>
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hline : HasDerivAt (fun t : ℝ => (t, h₀)) e₁ t₀ :=
    (hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ h₀)
  -- `∂ₕY = V` and `∂ₕV = −Γ(Y)(V, V)` as identities of `fderiv … e₂` near `z₀`
  have hAY : (fun z => fderiv ℝ Y z e₂) =ᶠ[𝓝 z₀] V := by
    filter_upwards [hYev, hgY] with z hz hg
    have h := hz.hasFDerivAt.comp_hasDerivAt z.2 (hsl z)
    exact h.unique hg
  have hAV : (fun z => fderiv ℝ V z e₂) =ᶠ[𝓝 z₀] fun z => -(Γ (Y z) (V z) (V z)) := by
    filter_upwards [hVev, hgV] with z hz hg
    have h := hz.hasFDerivAt.comp_hasDerivAt z.2 (hsl z)
    exact h.unique hg
  -- derivative of `z ↦ fderiv … z e₂` in a direction
  have happ : ∀ (G : ℝ × ℝ → E), DifferentiableAt ℝ (fderiv ℝ G) z₀ → ∀ a : ℝ × ℝ,
      fderiv ℝ (fun z => fderiv ℝ G z e₂) z₀ a = fderiv ℝ (fderiv ℝ G) z₀ a e₂ := by
    intro G hG a
    have h : HasFDerivAt (fun z => fderiv ℝ G z e₂)
        ((ContinuousLinearMap.apply ℝ E e₂).comp (fderiv ℝ (fderiv ℝ G) z₀)) z₀ :=
      (ContinuousLinearMap.apply ℝ E e₂).hasFDerivAt.comp z₀ hG.hasFDerivAt
    rw [h.fderiv]
    rfl
  -- the `h`-derivative of `s ↦ fderiv G (t₀, s) e₁`
  have hslice : ∀ (G : ℝ × ℝ → E), DifferentiableAt ℝ (fderiv ℝ G) z₀ →
      HasDerivAt (fun s => fderiv ℝ G (t₀, s) e₁) (fderiv ℝ (fderiv ℝ G) z₀ e₂ e₁) h₀ := by
    intro G hG
    have h := (hG.hasFDerivAt.comp_hasDerivAt h₀ (hsl z₀)).clm_apply (hasDerivAt_const h₀ e₁)
    simpa using h
  refine ⟨?_, ?_⟩
  · have h := hslice Y hDY
    convert h using 1
    rw [hsymY e₂ e₁, ← happ Y hDY e₁, hAY.fderiv_eq]
  · have h := hslice V hDV
    convert h using 1
    rw [hsymV e₂ e₁, ← happ V hDV e₁, hAV.fderiv_eq]
    -- the directional derivative of `z ↦ −Γ(Y z)(V z, V z)` along `e₁`, through the line `t ↦ (t, h₀)`
    have hYd : DifferentiableAt ℝ Y z₀ := hYev.self_of_nhds
    have hVd : DifferentiableAt ℝ V z₀ := hVev.self_of_nhds
    have hf : DifferentiableAt ℝ (fun z => -(Γ (Y z) (V z) (V z))) z₀ :=
      (((hΓ.comp z₀ hYd).clm_apply hVd).clm_apply hVd).neg
    have hl1 := hf.hasFDerivAt.comp_hasDerivAt t₀ hline
    have hYl : HasDerivAt (fun t => Y (t, h₀)) (fderiv ℝ Y z₀ e₁) t₀ :=
      hYd.hasFDerivAt.comp_hasDerivAt t₀ hline
    have hVl : HasDerivAt (fun t => V (t, h₀)) (fderiv ℝ V z₀ e₁) t₀ :=
      hVd.hasFDerivAt.comp_hasDerivAt t₀ hline
    have hΓl : HasDerivAt (fun t => Γ (Y (t, h₀))) (fderiv ℝ Γ (Y z₀) (fderiv ℝ Y z₀ e₁)) t₀ :=
      hΓ.hasFDerivAt.comp_hasDerivAt t₀ hYl
    have hl2 := ((hΓl.clm_apply hVl).clm_apply hVl).neg
    have heq := hl1.unique hl2
    change fderiv ℝ (fun z => -(Γ (Y z) (V z) (V z))) z₀ e₁ = _ at heq
    rw [heq, add_apply, hsym.self_of_nhds (V z₀) (fderiv ℝ V z₀ e₁), two_smul]
    abel

end Algebra

section Koszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance continuousDualEquiv_CMS3SHIFT : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroup_CMS3SHIFT : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpace_CMS3SHIFT : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The Koszul Christoffel operator of `C²` symmetric coercive coefficients is symmetric near `x`,
differentiable at `x`, with symmetric derivative, and compatible with `b`. -/
theorem koszul_christoffel_data {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) :
    (∀ᶠ y in 𝓝 x, ∀ u v : E, raisedKoszulOp (b y) (fderiv ℝ b y) u v =
        raisedKoszulOp (b y) (fderiv ℝ b y) v u) ∧
      DifferentiableAt ℝ (fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) x ∧
      ∀ w p q : E, fderiv ℝ b x w p q =
        b x (raisedKoszulOp (b x) (fderiv ℝ b x) w p) q +
          b x p (raisedKoszulOp (b x) (fderiv ℝ b x) w q) := by
  have hbd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ b y :=
    (hb.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  refine ⟨?_, DifferentialGeometry.Analysis.differentiableAt_raisedKoszulOp hb hco, ?_⟩
  · filter_upwards [DifferentialGeometry.Analysis.eventually_fderiv_symm hbd hsymm] with y hy u v
    exact DifferentialGeometry.Analysis.raisedKoszulOp_symm (b y) hy u v
  · exact (DifferentialGeometry.Analysis.eventually_metric_compat_raisedKoszulOp
      (hb.of_le (by norm_num)) hsymm hco).self_of_nhds

/-- **The Jacobi pairing identities.** Along a chart curve `x` with `x' = U`, `U' = −Γ(U, U)`, for a
Jacobi pair `J' = K`, `K' = −DΓ[J](U, U) − 2 Γ(K, U)` and a parallel field `W`:
`(b(J, W))' = b(K + Γ(U, J), W)` and `(b(K + Γ(U, J), W))' = −Rm04(J, U, U, W)`. -/
theorem hasDerivAt_jacobi_pairing {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x U J K W : ℝ → E} {h : ℝ}
    (hb : ContDiffAt ℝ 2 b (x h)) (hsymm : ∀ᶠ y in 𝓝 (x h), ∀ u v : E, b y u v = b y v u)
    (hco : IsCoercive (b (x h))) (hx : HasDerivAt x (U h) h)
    (hU : HasDerivAt U (-(raisedKoszulOp (b (x h)) (fderiv ℝ b (x h)) (U h) (U h))) h)
    (hJ : HasDerivAt J (K h) h)
    (hK : HasDerivAt K
      (-(fderiv ℝ (fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) (x h) (J h)
          (U h) (U h)) -
        (2 : ℝ) • raisedKoszulOp (b (x h)) (fderiv ℝ b (x h)) (K h) (U h)) h)
    (hW : HasDerivAt W (-(raisedKoszulOp (b (x h)) (fderiv ℝ b (x h)) (U h) (W h))) h) :
    HasDerivAt (fun τ => b (x τ) (J τ) (W τ))
        (b (x h) (K h + raisedKoszulOp (b (x h)) (fderiv ℝ b (x h)) (U h) (J h)) (W h)) h ∧
      HasDerivAt
        (fun τ => b (x τ) (K τ + raisedKoszulOp (b (x τ)) (fderiv ℝ b (x τ)) (U τ) (J τ)) (W τ))
        (-(coefficientRm04 b (x h) (J h) (U h) (U h) (W h))) h := by
  obtain ⟨hΓsym, hΓd, hcompat⟩ := koszul_christoffel_data hb hsymm hco
  have hbd : DifferentiableAt ℝ b (x h) := hb.differentiableAt (by simp)
  refine ⟨hasDerivAt_pairing_of_parallel
    (Γ := fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) hbd hcompat hx hJ hW, ?_⟩
  have hcov := hasDerivAt_jacobi_covariant
    (Γ := fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) hΓd hΓsym hx hU hJ hK
  have h2 := hasDerivAt_pairing_of_parallel
    (Γ := fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) hbd hcompat hx hcov hW
  refine h2.congr_deriv ?_
  rw [sub_add_cancel, map_neg, neg_apply,
    DifferentialGeometry.Analysis.coefficientRm04_eq_connectionFormCurvature hb hsymm hco]

/-- **First Bianchi identity** for the coefficient curvature of `C²` symmetric coercive coefficients. -/
theorem coefficientRm04_first_bianchi {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) (X Y Z W : E) :
    coefficientRm04 b x X Y Z W + coefficientRm04 b x Y Z X W + coefficientRm04 b x Z X Y W = 0 := by
  obtain ⟨hΓsym, hΓd, -⟩ := koszul_christoffel_data hb hsymm hco
  have hcyc := connectionFormCurvature_cyclic hΓsym.self_of_nhds
    (fderiv_apply_symm_of_eventually_symm hΓd hΓsym) X Y Z
  rw [DifferentialGeometry.Analysis.coefficientRm04_eq_connectionFormCurvature hb hsymm hco,
    DifferentialGeometry.Analysis.coefficientRm04_eq_connectionFormCurvature hb hsymm hco,
    DifferentialGeometry.Analysis.coefficientRm04_eq_connectionFormCurvature hb hsymm hco,
    ← add_apply, ← map_add, ← add_apply, ← map_add, hcyc, map_zero, zero_apply]

/-- **Pair symmetry** of the coefficient curvature: `Rm04(X, Y, Z, W) = Rm04(Z, W, X, Y)`. -/
theorem coefficientRm04_pair_symm {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) (X Y Z W : E) :
    coefficientRm04 b x X Y Z W = coefficientRm04 b x Z W X Y := by
  have hfirst := coefficientRm04_first_bianchi hb hsymm hco
  have hinput := DifferentialGeometry.Analysis.coefficientRm04_swap_left b x
  have houtput := DifferentialGeometry.Analysis.coefficientRm04_swap_right hb hsymm hco
  have hB0 := hfirst X Y Z W
  have hB1 := hfirst Y Z W X
  have hB2 := hfirst Y W Z X
  have hB3 := hfirst X Y W Z
  have hB4 := hfirst X Z W Y
  have hO1 := houtput Y Z X W
  have hO2 := houtput X Y Z W
  have hO3 := houtput X Z Y W
  have hO4 := houtput X W Y Z
  have hO5 := houtput Y W X Z
  have hO6 := houtput Z W X Y
  have hI1 := hinput X Z Y W
  have hI2 := hinput X W Y Z
  have hI3 := hinput X W Z Y
  have hI4 := hinput Y W Z X
  linarith

/-- The Jacobi operator `Rm04(·, u, u, ·)` is symmetric. -/
theorem coefficientRm04_jacobi_symm {b : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hb : ContDiffAt ℝ 2 b x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v : E, b y u v = b y v u) (hco : IsCoercive (b x)) (X u Y : E) :
    coefficientRm04 b x X u u Y = coefficientRm04 b x Y u u X := by
  rw [coefficientRm04_pair_symm hb hsymm hco X u u Y,
    DifferentialGeometry.Analysis.coefficientRm04_swap_left b x Y u X u,
    DifferentialGeometry.Analysis.coefficientRm04_swap_right hb hsymm hco Y u u X, neg_neg]

end Koszul

end DifferentialGeometry.Geometry.FiniteSoul
