import DifferentialGeometry.Geometry.Curvature.Surface.ConnectionPotential
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.KoszulIdentification

/-!
# The divergence form of the curvature of a surface coefficient field

For a `C²` positive symmetric coefficient field `b` on a two-dimensional space `E` and a basis
`(v₁, v₂)` of `E`, the chart curvature times the area density is a divergence:

`coefficientSectional b y v₁ v₂ * √(EG − F²) = ∂₂ P − ∂₁ Q`,

with the explicit potentials `P = surfaceConnectionP b v₁ v₂`, `Q = surfaceConnectionQ b v₁ v₂`
of `ConnectionPotential.lean` (the connection form of the Gram–Schmidt coframe), and `∂ₖ` the
derivative along `vₖ`. No frame field or Gauss–Bonnet theorem is used: the curvature numerator is
computed from the tree's identification of `coefficientRm04` with the curvature of the raised
Koszul connection (`coefficientRm04_eq_connectionFormCurvature`), differentiating the Koszul
identity `b(Γ(Y,Z),W) = koszulCov` instead of the inverse Gram matrix, and the resulting rational
identity is closed by `field_simp; ring` after eliminating `G = (D + F²)/E`.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

section Algebra

/-- The rational identity behind the divergence form (`W = √(EG − F²)`; `a, c` and `a', c'` are
the coordinates of `Γ(v₂, v₂)` and `Γ(v₁, v₂)` in the basis `(v₁, v₂)`). -/
private theorem divergence_algebra
    {E F G E1 E2 F1 F2 G1 G2 E12 E22 F12 G11 W a c a' c' : ℝ}
    (hE : 0 < E) (hW : 0 < W) (hG : G = (W ^ 2 + F ^ 2) / E)
    (h1 : a * E + c * F = F2 - G1 / 2) (h2 : a * F + c * G = G2 / 2)
    (h3 : a' * E + c' * F = E2 / 2) (h4 : a' * F + c' * G = G1 / 2) :
    (F12 - G11 / 2 - E22 / 2 - a * E1 / 2 + c * (E2 / 2 - F1) + a' * E2 / 2 + c' * G1 / 2) /
        (E * G - F ^ 2) * W =
      ((2 * E2 * F1 + 2 * E * F12 - E2 * E2 - E * E22 - F2 * E1 - F * E12) * (2 * E * W) -
          (2 * E * F1 - E * E2 - F * E1) *
            (2 * E2 * W + 2 * E * ((E2 * G + E * G2 - 2 * F * F2) / (2 * W)))) /
          (2 * E * W) ^ 2 -
        ((E1 * G1 + E * G11 - F1 * E2 - F * E12) * (2 * E * W) -
          (E * G1 - F * E2) *
            (2 * E1 * W + 2 * E * ((E1 * G + E * G1 - 2 * F * F1) / (2 * W)))) /
          (2 * E * W) ^ 2 := by
  have hD : E * G - F ^ 2 = W ^ 2 := by
    rw [hG]; field_simp; ring
  have hDne : E * G - F ^ 2 ≠ 0 := by rw [hD]; positivity
  have ha : a = (G * (F2 - G1 / 2) - F * (G2 / 2)) / (E * G - F ^ 2) := by
    rw [eq_div_iff hDne]; linear_combination G * h1 - F * h2
  have hc : c = (E * (G2 / 2) - F * (F2 - G1 / 2)) / (E * G - F ^ 2) := by
    rw [eq_div_iff hDne]; linear_combination E * h2 - F * h1
  have ha' : a' = (G * (E2 / 2) - F * (G1 / 2)) / (E * G - F ^ 2) := by
    rw [eq_div_iff hDne]; linear_combination G * h3 - F * h4
  have hc' : c' = (E * (G1 / 2) - F * (E2 / 2)) / (E * G - F ^ 2) := by
    rw [eq_div_iff hDne]; linear_combination E * h4 - F * h3
  subst ha hc ha' hc'
  rw [hD]
  subst hG
  have hE' := hE.ne'
  have hW' := hW.ne'
  field_simp
  ring

end Algebra

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem fderiv_apply_const' {L : E → F →L[ℝ] G} {y : E} (hL : DifferentiableAt ℝ L y)
    (u : F) (w : E) : fderiv ℝ (fun z => L z u) y w = fderiv ℝ L y w u := by
  rw [fderiv_clm_apply hL (differentiableAt_const u)]
  simp

private theorem fderiv_apply₂ {L : E → E →L[ℝ] E →L[ℝ] G} {y : E}
    (hL : DifferentiableAt ℝ L y) (u v w : E) :
    fderiv ℝ (fun z => L z u v) y w = fderiv ℝ L y w u v := by
  rw [fderiv_apply_const' (hL.clm_apply (differentiableAt_const u)) v w,
    fderiv_apply_const' hL u w]

private theorem fderiv_apply₃ {L : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] G} {y : E}
    (hL : DifferentiableAt ℝ L y) (u v t w : E) :
    fderiv ℝ (fun z => L z u v t) y w = fderiv ℝ L y w u v t := by
  rw [fderiv_apply_const' ((hL.clm_apply (differentiableAt_const u)).clm_apply
      (differentiableAt_const v)) t w, fderiv_apply₂ hL u v w]

private theorem hasDerivAt_line {φ : E → ℝ} {y : E} (hφ : DifferentiableAt ℝ φ y) (w : E) :
    HasDerivAt (fun t : ℝ => φ (y + t • w)) (fderiv ℝ φ y w) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hφ' : HasFDerivAt φ (fderiv ℝ φ y) (y + (0 : ℝ) • w) := by
    simpa using hφ.hasFDerivAt
  exact hφ'.comp_hasDerivAt (0 : ℝ) hl

private theorem fderiv_quot_sqrt {N e f g : E → ℝ} {y : E} (hN : DifferentiableAt ℝ N y)
    (he : DifferentiableAt ℝ e y) (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (he0 : 0 < e y) (hD0 : 0 < e y * g y - f y ^ 2) (w : E) :
    fderiv ℝ (fun z => N z / (2 * e z * √(e z * g z - f z ^ 2))) y w =
      (fderiv ℝ N y w * (2 * e y * √(e y * g y - f y ^ 2)) -
          N y * (2 * fderiv ℝ e y w * √(e y * g y - f y ^ 2) +
            2 * e y * ((fderiv ℝ e y w * g y + e y * fderiv ℝ g y w -
              2 * f y * fderiv ℝ f y w) / (2 * √(e y * g y - f y ^ 2))))) /
        (2 * e y * √(e y * g y - f y ^ 2)) ^ 2 := by
  have hW := Real.sqrt_pos.mpr hD0
  have hDd : DifferentiableAt ℝ (fun z => e z * g z - f z ^ 2) y := (he.mul hg).sub (hf.pow 2)
  have hden : DifferentiableAt ℝ (fun z => 2 * e z * √(e z * g z - f z ^ 2)) y :=
    ((differentiableAt_const 2).mul he).mul (hDd.sqrt hD0.ne')
  have hd : DifferentiableAt ℝ (fun z => N z / (2 * e z * √(e z * g z - f z ^ 2))) y :=
    by simpa only [div_eq_mul_inv] using hN.fun_mul (hden.fun_inv (by positivity))
  refine (hasDerivAt_line hd w).unique ?_
  have hel := hasDerivAt_line he w
  have hDl := (hel.fun_mul (hasDerivAt_line hg w)).fun_sub
    ((hasDerivAt_line hf w).fun_mul (hasDerivAt_line hf w))
  have hsq := hDl.sqrt (by simp only [zero_smul, add_zero]; nlinarith)
  have hq := (hasDerivAt_line hN w).fun_div ((hel.const_mul 2).fun_mul hsq)
    (by simp only [zero_smul, add_zero]; rw [← sq]; positivity)
  simp only [zero_smul, add_zero] at hq
  convert hq using 1
  · funext t
    rw [sq]
  · rw [sq]
    ring

private theorem fderiv_numerator_P {e f p q r : E → ℝ} {y : E} (he : DifferentiableAt ℝ e y)
    (hf : DifferentiableAt ℝ f y) (hp : DifferentiableAt ℝ p y) (hq : DifferentiableAt ℝ q y)
    (hr : DifferentiableAt ℝ r y) (w : E) :
    fderiv ℝ (fun z => 2 * e z * p z - e z * q z - f z * r z) y w =
      2 * (fderiv ℝ e y w * p y + e y * fderiv ℝ p y w) -
        (fderiv ℝ e y w * q y + e y * fderiv ℝ q y w) -
        (fderiv ℝ f y w * r y + f y * fderiv ℝ r y w) := by
  have hd : DifferentiableAt ℝ (fun z => 2 * e z * p z - e z * q z - f z * r z) y :=
    ((((differentiableAt_const 2).mul he).mul hp).sub (he.mul hq)).sub (hf.mul hr)
  refine (hasDerivAt_line hd w).unique ?_
  have h := ((((hasDerivAt_line he w).const_mul 2).fun_mul (hasDerivAt_line hp w)).fun_sub
    ((hasDerivAt_line he w).fun_mul (hasDerivAt_line hq w))).fun_sub
    ((hasDerivAt_line hf w).fun_mul (hasDerivAt_line hr w))
  simp only [zero_smul, add_zero] at h
  convert h using 1
  ring

private theorem fderiv_numerator_Q {e f p q : E → ℝ} {y : E} (he : DifferentiableAt ℝ e y)
    (hf : DifferentiableAt ℝ f y) (hp : DifferentiableAt ℝ p y) (hq : DifferentiableAt ℝ q y)
    (w : E) :
    fderiv ℝ (fun z => e z * p z - f z * q z) y w =
      (fderiv ℝ e y w * p y + e y * fderiv ℝ p y w) -
        (fderiv ℝ f y w * q y + f y * fderiv ℝ q y w) := by
  have hd : DifferentiableAt ℝ (fun z => e z * p z - f z * q z) y := (he.mul hp).sub (hf.mul hq)
  refine (hasDerivAt_line hd w).unique ?_
  have h := ((hasDerivAt_line he w).fun_mul (hasDerivAt_line hp w)).fun_sub
    ((hasDerivAt_line hf w).fun_mul (hasDerivAt_line hq w))
  simp only [zero_smul, add_zero] at h
  exact h

end Calculus

section Divergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a two-dimensional space a linearly independent pair spans: every vector has
coordinates. -/
theorem exists_smul_add_smul_eq_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) (x : E) : ∃ a c : ℝ, a • v₁ + c • v₂ = x := by
  have htop : Submodule.span ℝ (Set.range ![v₁, v₂]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hE])
  rw [Matrix.range_cons_cons_empty] at htop
  have hx : x ∈ Submodule.span ℝ ({v₁, v₂} : Set E) := by
    rw [htop]
    exact Submodule.mem_top
  exact Submodule.mem_span_pair.mp hx

/-- The curvature numerator `R(v₁, v₂, v₂, v₁)` in terms of the first and second jets of `b`
and the coordinates of two Christoffel vectors. -/
private theorem coefficientRm04_eq_jet (hE : Module.finrank ℝ E = 2)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂])
    (y : E) :
    ∃ a c a' c' : ℝ,
      a * b y v₁ v₁ + c * b y v₁ v₂ = fderiv ℝ b y v₂ v₁ v₂ - fderiv ℝ b y v₁ v₂ v₂ / 2 ∧
      a * b y v₁ v₂ + c * b y v₂ v₂ = fderiv ℝ b y v₂ v₂ v₂ / 2 ∧
      a' * b y v₁ v₁ + c' * b y v₁ v₂ = fderiv ℝ b y v₂ v₁ v₁ / 2 ∧
      a' * b y v₁ v₂ + c' * b y v₂ v₂ = fderiv ℝ b y v₁ v₂ v₂ / 2 ∧
      coefficientRm04 b y v₁ v₂ v₂ v₁ =
        fderiv ℝ (fderiv ℝ b) y v₂ v₁ v₁ v₂ - fderiv ℝ (fderiv ℝ b) y v₁ v₁ v₂ v₂ / 2 -
          fderiv ℝ (fderiv ℝ b) y v₂ v₂ v₁ v₁ / 2 - a * fderiv ℝ b y v₁ v₁ v₁ / 2 +
          c * (fderiv ℝ b y v₂ v₁ v₁ / 2 - fderiv ℝ b y v₁ v₁ v₂) +
          a' * fderiv ℝ b y v₂ v₁ v₁ / 2 + c' * fderiv ℝ b y v₁ v₂ v₂ / 2 := by
  have hbd : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hb2d : Differentiable ℝ (fderiv ℝ b) :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hco : ∀ z, IsCoercive (b z) := fun z => (b z).isCoercive_of_posDef (hpos z)
  set Γ : E → E →L[ℝ] E →L[ℝ] E :=
    fun z => MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) with hΓdef
  have hK : ∀ z u v t, b z (Γ z u v) t =
      1 / 2 * (fderiv ℝ b z u v t + fderiv ℝ b z v u t - fderiv ℝ b z t u v) := by
    intro z u v t
    have h := DFunLike.congr_fun (apply_raisedKoszulOp (hco z) (fderiv ℝ b z) u v) t
    rw [MetricKoszul.koszul_cov_apply] at h
    exact h
  have hΓd : DifferentiableAt ℝ Γ y := differentiableAt_raisedKoszulOp hb.contDiffAt (hco y)
  have hB : ∀ u v, b y u v = b y v u := hsymm y
  have hB1 : ∀ w u v, fderiv ℝ b y w u v = fderiv ℝ b y w v u :=
    (eventually_fderiv_symm (Eventually.of_forall fun z => hbd z)
      (Eventually.of_forall hsymm)).self_of_nhds
  have hB2 : ∀ m w u v, fderiv ℝ (fderiv ℝ b) y m w u v = fderiv ℝ (fderiv ℝ b) y m w v u :=
    fderiv_fderiv_symm (Eventually.of_forall fun z => hbd z) (hb2d y)
      (Eventually.of_forall hsymm)
  have hSch : ∀ m w, fderiv ℝ (fderiv ℝ b) y m w = fderiv ℝ (fderiv ℝ b) y w m :=
    fun m w => (hb.contDiffAt.isSymmSndFDerivAt (by simp)) m w
  have hDK : ∀ X u v t, b y (fderiv ℝ Γ y X u v) t =
      1 / 2 * (fderiv ℝ (fderiv ℝ b) y X u v t + fderiv ℝ (fderiv ℝ b) y X v u t -
        fderiv ℝ (fderiv ℝ b) y X t u v) - fderiv ℝ b y X (Γ y u v) t := by
    intro X u v t
    have hfun : (fun z => b z (Γ z u v) t) = fun z =>
        1 / 2 * (fderiv ℝ b z u v t + fderiv ℝ b z v u t - fderiv ℝ b z t u v) :=
      funext fun z => hK z u v t
    have hΓuv : DifferentiableAt ℝ (fun z => Γ z u v) y :=
      (hΓd.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v)
    have hl : fderiv ℝ (fun z => b z (Γ z u v) t) y X =
        b y (fderiv ℝ Γ y X u v) t + fderiv ℝ b y X (Γ y u v) t := by
      rw [fderiv_apply_const' ((hbd y).clm_apply hΓuv) t X, fderiv_clm_apply (hbd y) hΓuv]
      simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply]
      rw [fderiv_apply₂ hΓd u v X]
    have hd3 : ∀ p q r, DifferentiableAt ℝ (fun z => fderiv ℝ b z p q r) y := fun p q r =>
      (((hb2d y).clm_apply (differentiableAt_const p)).clm_apply
        (differentiableAt_const q)).clm_apply (differentiableAt_const r)
    have hr : fderiv ℝ (fun z => 1 / 2 * (fderiv ℝ b z u v t + fderiv ℝ b z v u t -
        fderiv ℝ b z t u v)) y X = 1 / 2 * (fderiv ℝ (fderiv ℝ b) y X u v t +
          fderiv ℝ (fderiv ℝ b) y X v u t - fderiv ℝ (fderiv ℝ b) y X t u v) := by
      have hdφ : DifferentiableAt ℝ (fun z => 1 / 2 * (fderiv ℝ b z u v t +
          fderiv ℝ b z v u t - fderiv ℝ b z t u v)) y :=
        (differentiableAt_const _).mul (((hd3 u v t).add (hd3 v u t)).sub (hd3 t u v))
      have h := (((hasDerivAt_line (hd3 u v t) X).fun_add (hasDerivAt_line (hd3 v u t) X)).fun_sub
        (hasDerivAt_line (hd3 t u v) X)).const_mul (1 / 2 : ℝ)
      simp only [fderiv_apply₃ (hb2d y)] at h
      exact (hasDerivAt_line hdφ X).unique h
    have h := hl.symm.trans ((congrArg (fun φ => fderiv ℝ φ y X) hfun).trans hr)
    linarith
  obtain ⟨a, c, hac⟩ := exists_smul_add_smul_eq_of_finrank_eq_two hE hli (Γ y v₂ v₂)
  obtain ⟨a', c', hac'⟩ := exists_smul_add_smul_eq_of_finrank_eq_two hE hli (Γ y v₁ v₂)
  have hRm : coefficientRm04 b y v₁ v₂ v₂ v₁ =
      b y (Geometry.Connection.connectionFormCurvature Γ y v₁ v₂ v₂) v₁ :=
    coefficientRm04_eq_connectionFormCurvature hb.contDiffAt (Eventually.of_forall hsymm)
      (hco y) v₁ v₂ v₂ v₁
  have e1 := hK y v₂ v₂ v₁
  have e2 := hK y v₂ v₂ v₂
  have e3 := hK y v₁ v₂ v₁
  have e4 := hK y v₁ v₂ v₂
  have k11 := hK y v₁ v₁ v₁
  have k21 := hK y v₂ v₁ v₁
  rw [← hac] at e1 e2
  rw [← hac'] at e3 e4
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul] at e1 e2 e3 e4
  refine ⟨a, c, a', c', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB v₂ v₁, hB1 v₂ v₂ v₁] at e1
    linarith
  · linarith
  · rw [hB v₂ v₁, hB1 v₁ v₂ v₁] at e3
    linarith
  · linarith
  rw [hRm]
  simp only [Geometry.Connection.connectionFormCurvature, map_add, map_sub,
    _root_.add_apply, _root_.sub_apply]
  rw [hDK v₁ v₂ v₂ v₁, hDK v₂ v₁ v₂ v₁, ← hac, ← hac']
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul]
  rw [hK y v₁ v₁ v₁, hK y v₁ v₂ v₁, hK y v₂ v₁ v₁, hK y v₂ v₂ v₁]
  rw [hB1 v₁ v₂ v₁, hB1 v₂ v₂ v₁, hSch v₁ v₂, hB2 v₂ v₁ v₂ v₁]
  ring

/-- **Divergence form of the curvature (dimension two).** For a `C²` positive symmetric
coefficient field and a basis `(v₁, v₂)`, `K √(EG − F²) = ∂₂ P − ∂₁ Q` with the explicit
connection-form potentials `P = surfaceConnectionP b v₁ v₂`, `Q = surfaceConnectionQ b v₁ v₂`. -/
theorem coefficientSectional_mul_sqrt_eq_fderiv_sub (hE : Module.finrank ℝ E = 2)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂])
    (y : E) :
    coefficientSectional b y v₁ v₂ * Real.sqrt (surfaceGramDet b v₁ v₂ y) =
      fderiv ℝ (surfaceConnectionP b v₁ v₂) y v₂ - fderiv ℝ (surfaceConnectionQ b v₁ v₂) y v₁ := by
  obtain ⟨a, c, a', c', h1, h2, h3, h4, hRm⟩ := coefficientRm04_eq_jet hE hb hsymm hpos hli y
  have hbd : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hb2d : Differentiable ℝ (fderiv ℝ b) :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd2 : ∀ u v, DifferentiableAt ℝ (fun z => b z u v) y := fun u v =>
    ((hbd y).clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v)
  have hd3 : ∀ p q r, DifferentiableAt ℝ (fun z => fderiv ℝ b z p q r) y := fun p q r =>
    (((hb2d y).clm_apply (differentiableAt_const p)).clm_apply
      (differentiableAt_const q)).clm_apply (differentiableAt_const r)
  have hEpos := surfaceE_pos hpos hli y
  have hDpos := surfaceGramDet_pos hsymm hpos hli y
  have hfun : ∀ u v w, (fun z => fderiv ℝ (fun z' => b z' u v) z w) =
      fun z => fderiv ℝ b z w u v := fun u v w => funext fun z => fderiv_apply₂ (hbd z) u v w
  have hPfun : surfaceConnectionP b v₁ v₂ = fun z =>
      (2 * b z v₁ v₁ * fderiv ℝ b z v₁ v₁ v₂ - b z v₁ v₁ * fderiv ℝ b z v₂ v₁ v₁ -
          b z v₁ v₂ * fderiv ℝ b z v₁ v₁ v₁) /
        (2 * b z v₁ v₁ * √(b z v₁ v₁ * b z v₂ v₂ - b z v₁ v₂ ^ 2)) := by
    funext z
    rw [surfaceConnectionP_def, surfaceGramDet_def, fderiv_apply₂ (hbd z),
      fderiv_apply₂ (hbd z), fderiv_apply₂ (hbd z)]
  have hQfun : surfaceConnectionQ b v₁ v₂ = fun z =>
      (b z v₁ v₁ * fderiv ℝ b z v₁ v₂ v₂ - b z v₁ v₂ * fderiv ℝ b z v₂ v₁ v₁) /
        (2 * b z v₁ v₁ * √(b z v₁ v₁ * b z v₂ v₂ - b z v₁ v₂ ^ 2)) := by
    funext z
    rw [surfaceConnectionQ_def, surfaceGramDet_def, fderiv_apply₂ (hbd z),
      fderiv_apply₂ (hbd z)]
  rw [surfaceGramDet_def] at hDpos ⊢
  have hNP : DifferentiableAt ℝ (fun z => 2 * b z v₁ v₁ * fderiv ℝ b z v₁ v₁ v₂ -
      b z v₁ v₁ * fderiv ℝ b z v₂ v₁ v₁ - b z v₁ v₂ * fderiv ℝ b z v₁ v₁ v₁) y :=
    ((((differentiableAt_const 2).mul (hd2 v₁ v₁)).mul (hd3 v₁ v₁ v₂)).sub
      ((hd2 v₁ v₁).mul (hd3 v₂ v₁ v₁))).sub ((hd2 v₁ v₂).mul (hd3 v₁ v₁ v₁))
  have hNQ : DifferentiableAt ℝ (fun z => b z v₁ v₁ * fderiv ℝ b z v₁ v₂ v₂ -
      b z v₁ v₂ * fderiv ℝ b z v₂ v₁ v₁) y :=
    ((hd2 v₁ v₁).mul (hd3 v₁ v₂ v₂)).sub ((hd2 v₁ v₂).mul (hd3 v₂ v₁ v₁))
  have hPd := fderiv_quot_sqrt hNP (hd2 v₁ v₁) (hd2 v₁ v₂) (hd2 v₂ v₂) hEpos hDpos v₂
  have hQd := fderiv_quot_sqrt hNQ (hd2 v₁ v₁) (hd2 v₁ v₂) (hd2 v₂ v₂) hEpos hDpos v₁
  have hNPd := fderiv_numerator_P (hd2 v₁ v₁) (hd2 v₁ v₂) (hd3 v₁ v₁ v₂) (hd3 v₂ v₁ v₁)
    (hd3 v₁ v₁ v₁) v₂
  have hNQd := fderiv_numerator_Q (hd2 v₁ v₁) (hd2 v₁ v₂) (hd3 v₁ v₂ v₂) (hd3 v₂ v₁ v₁) v₁
  rw [hPfun, hQfun, hPd, hQd, hNPd, hNQd]
  simp only [fderiv_apply₂ (hbd y), fderiv_apply₃ (hb2d y)]
  rw [coefficientSectional_def, hRm]
  have hSch : fderiv ℝ (fderiv ℝ b) y v₁ v₂ = fderiv ℝ (fderiv ℝ b) y v₂ v₁ :=
    (hb.contDiffAt.isSymmSndFDerivAt (by simp)) v₁ v₂
  rw [hSch]
  have hW := Real.sqrt_pos.mpr hDpos
  have hG : b y v₂ v₂ =
      (√(b y v₁ v₁ * b y v₂ v₂ - b y v₁ v₂ ^ 2) ^ 2 + b y v₁ v₂ ^ 2) / b y v₁ v₁ := by
    rw [Real.sq_sqrt hDpos.le]
    field_simp
    ring
  linear_combination divergence_algebra (E1 := fderiv ℝ b y v₁ v₁ v₁)
    (F1 := fderiv ℝ b y v₁ v₁ v₂) (E12 := fderiv ℝ (fderiv ℝ b) y v₂ v₁ v₁ v₁)
    (E22 := fderiv ℝ (fderiv ℝ b) y v₂ v₂ v₁ v₁) (F12 := fderiv ℝ (fderiv ℝ b) y v₂ v₁ v₁ v₂)
    (G11 := fderiv ℝ (fderiv ℝ b) y v₁ v₁ v₂ v₂) hEpos hW hG h1 h2 h3 h4

/-- The sheet form: existence of `C¹` potentials, periodic along every period of `b`, with
`K √(EG − F²) = ∂₂ P − ∂₁ Q` (the potentials are `surfaceConnectionP`, `surfaceConnectionQ`). -/
theorem exists_divergence_form_coefficientSectional (hE : Module.finrank ℝ E = 2)
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ∃ P Q : E → ℝ, ContDiff ℝ 1 P ∧ ContDiff ℝ 1 Q ∧
      (∀ w, (∀ y, b (y + w) = b y) → (∀ y, P (y + w) = P y) ∧ ∀ y, Q (y + w) = Q y) ∧
      ∀ y, coefficientSectional b y v₁ v₂ *
          Real.sqrt (b y v₁ v₁ * b y v₂ v₂ - (b y v₁ v₂) ^ 2) =
        fderiv ℝ P y v₂ - fderiv ℝ Q y v₁ :=
  ⟨surfaceConnectionP b v₁ v₂, surfaceConnectionQ b v₁ v₂,
    contDiff_surfaceConnectionP hb hsymm hpos hli, contDiff_surfaceConnectionQ hb hsymm hpos hli,
    fun _ hper => ⟨fun y => surfaceConnectionP_add_period hper v₁ v₂ y,
      fun y => surfaceConnectionQ_add_period hper v₁ v₂ y⟩,
    fun y => coefficientSectional_mul_sqrt_eq_fderiv_sub hE hb hsymm hpos hli y⟩

end Divergence

end DifferentialGeometry.Analysis
