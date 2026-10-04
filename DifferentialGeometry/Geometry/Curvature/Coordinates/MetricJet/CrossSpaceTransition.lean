import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientTransition
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientSectional

/-!
# Coefficient curvature under a change of model space

`coefficientRm04_transition` compares the coefficient curvature of two metric coefficient
fields related by a local diffeomorphism `E → E`. Here the two coefficient fields live on
different finite-dimensional spaces `V` and `E`; the proof is the same intertwining argument,
all of whose connection-form ingredients are already stated across spaces.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
/-- The pulled-back coefficient field is as regular as the target field and the derivative. -/
theorem contDiffOn_bilinearComp_fderiv_cross {U W : Set V} {c : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Φ : V → E} {T : Set E} (hU : IsOpen U) {n : ℕ∞ω} (hc : ContDiffOn ℝ n c T)
    (hΦ : ContDiffOn ℝ (n + 1) Φ U) (hΦUT : MapsTo Φ U T) (hWU : W ⊆ U) :
    ContDiffOn ℝ n (fun y => (c (Φ y)).bilinearComp (fderiv ℝ Φ y) (fderiv ℝ Φ y)) W := by
  have hcΦ : ContDiffOn ℝ n (fun y => c (Φ y)) U :=
    hc.comp (hΦ.of_le (le_add_of_nonneg_right zero_le_one)) hΦUT
  have hdΦ : ContDiffOn ℝ n (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU le_rfl
  have hA : ContDiffOn ℝ n (fun y => (c (Φ y)).comp (fderiv ℝ Φ y)) U := hcΦ.clm_comp hdΦ
  have hB : ContDiffOn ℝ n (fun y => ((c (Φ y)).comp (fderiv ℝ Φ y)).flip) U :=
    (ContinuousLinearMap.flipₗᵢ ℝ V E ℝ).contDiff.comp_contDiffOn hA
  have hC : ContDiffOn ℝ n
      (fun y => ((c (Φ y)).comp (fderiv ℝ Φ y)).flip.comp (fderiv ℝ Φ y)) U :=
    hB.clm_comp hdΦ
  exact ((ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).contDiff.comp_contDiffOn hC).mono hWU

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in
theorem isCoercive_of_pullback_cross {U : Set V} {W : Set E} {b : V → V →L[ℝ] V →L[ℝ] ℝ}
    {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : V → E}
    (hcco : ∀ z ∈ W, IsCoercive (c z)) (hΦUW : MapsTo Φ U W)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : V, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ∀ y ∈ U, IsCoercive (b y) := by
  intro y hy
  obtain ⟨C, hC, hCu⟩ := hcco (Φ y) (hΦUW hy)
  obtain ⟨M, hM, hle⟩ : ∃ M : ℝ, 0 < M ∧ ∀ u : V, ‖u‖ ≤ M * ‖fderiv ℝ Φ y u‖ := by
    obtain ⟨e, he⟩ := hΦinv y hy
    refine ⟨‖(e.symm : E →L[ℝ] V)‖ + 1, by positivity, fun u => ?_⟩
    have h1 := (e.symm : E →L[ℝ] V).le_opNorm (e u)
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h1
    rw [← he, ContinuousLinearEquiv.coe_coe]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (norm_nonneg _))
  refine ⟨C * (M⁻¹ * M⁻¹), mul_pos hC (mul_pos (inv_pos.mpr hM) (inv_pos.mpr hM)),
    fun u => ?_⟩
  have hlow : M⁻¹ * ‖u‖ ≤ ‖fderiv ℝ Φ y u‖ :=
    (mul_le_mul_of_nonneg_left (hle u) (inv_nonneg.mpr hM.le)).trans_eq
      (inv_mul_cancel_left₀ hM.ne' _)
  rw [hpull y hy u u]
  calc C * (M⁻¹ * M⁻¹) * ‖u‖ * ‖u‖ = C * (M⁻¹ * ‖u‖) * (M⁻¹ * ‖u‖) := by ring
    _ ≤ C * ‖fderiv ℝ Φ y u‖ * ‖fderiv ℝ Φ y u‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlow hC.le) hlow
        (mul_nonneg (inv_nonneg.mpr hM.le) (norm_nonneg u)) (mul_nonneg hC.le (norm_nonneg _))
    _ ≤ c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y u) := hCu _

/-- The second derivative of a metric pullback map between different model spaces. -/
theorem fderiv_fderiv_eq_raisedKoszulOp_of_pullback_cross
    {U : Set V} {W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    {b : V → V →L[ℝ] V →L[ℝ] ℝ} {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : V → E}
    (hc : ContDiffOn ℝ 1 c W) (hcsymm : ∀ z ∈ W, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ W, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 2 Φ U) (hΦUW : MapsTo Φ U W)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : V, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {y : V} (hy : y ∈ U) (X u : V) :
    fderiv ℝ (fderiv ℝ Φ) y X u =
      fderiv ℝ Φ y (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) X u) -
        MetricKoszul.raisedKoszulOp (c (Φ y)) (fderiv ℝ c (Φ y)) (fderiv ℝ Φ y X)
          (fderiv ℝ Φ y u) := by
  have hΦy : Φ y ∈ W := hΦUW hy
  have hb1 : ContDiffOn ℝ 1 b U := by
    refine (contDiffOn_bilinearComp_fderiv_cross hU hc hΦ hΦUW subset_rfl).congr ?_
    intro z hz
    ext u v
    exact hpull z hz u v
  have hΦ2 : ContDiffAt ℝ 2 Φ y := hΦ.contDiffAt (hU.mem_nhds hy)
  have hBco : IsCoercive (b y) := isCoercive_of_pullback_cross hcco hΦUW hΦinv hpull y hy
  have hCco : IsCoercive (c (Φ y)) := hcco (Φ y) hΦy
  obtain ⟨e, he⟩ := hΦinv y hy
  have hPhi : HasFDerivAt Φ (e : V →L[ℝ] E) y := by
    rw [he]
    exact (hΦ2.differentiableAt (by norm_num)).hasFDerivAt
  have hev : ∀ v : V, e v = fderiv ℝ Φ y v := fun v => by
    rw [← he, ContinuousLinearEquiv.coe_coe]
  have h := CheegerGromovCompactness.MetricIsometry.isom_second_eq b c Φ (fderiv ℝ Φ)
    (fderiv ℝ b y) (fderiv ℝ c (Φ y)) e (fderiv ℝ (fderiv ℝ Φ) y)
    ((hb1.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
    ((hc.contDiffAt (hW.mem_nhds hΦy)).differentiableAt (by norm_num)).hasFDerivAt hPhi
    ((hΦ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    (Filter.eventually_of_mem (hU.mem_nhds hy) hpull) he.symm (hcsymm (Φ y) hΦy)
    (hΦ2.isSymmSndFDerivAt (by norm_num)).eq hBco hCco X u
  rw [MetricKoszul.raisedKoszulOp_eq hBco, MetricKoszul.raisedKoszulOp_eq hCco, ← hev X, ← hev u,
    ← hev]
  exact h

theorem bundleMapCovDeriv_raisedKoszulOp_of_pullback_cross
    {U : Set V} {W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    {b : V → V →L[ℝ] V →L[ℝ] ℝ} {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : V → E}
    (hc : ContDiffOn ℝ 1 c W) (hcsymm : ∀ z ∈ W, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ W, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 2 Φ U) (hΦUW : MapsTo Φ U W)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : V, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ∀ y ∈ U, ∀ X u : V,
      Geometry.Connection.bundleMapCovDeriv
        (fun z => (MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) : V →L[ℝ] V →L[ℝ] V))
        (Geometry.Connection.pullbackConnectionForm
          (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) Φ)
        (fderiv ℝ Φ) y X u = 0 := by
  intro y hy X u
  change fderiv ℝ (fderiv ℝ Φ) y X u +
      MetricKoszul.raisedKoszulOp (c (Φ y)) (fderiv ℝ c (Φ y)) (fderiv ℝ Φ y X)
        (fderiv ℝ Φ y u) -
      fderiv ℝ Φ y (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) X u) = 0
  rw [fderiv_fderiv_eq_raisedKoszulOp_of_pullback_cross hU hW hc hcsymm hcco hΦ hΦUW hΦinv
    hpull hy X u]
  abel

/-- **Coefficient curvature across model spaces.** -/
theorem coefficientRm04_transition_cross {U : Set V} {W : Set E} (hU : IsOpen U)
    (hW : IsOpen W) {b : V → V →L[ℝ] V →L[ℝ] ℝ} {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : V → E}
    (hc : ContDiffOn ℝ 2 c W) (hcsymm : ∀ z ∈ W, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ W, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 3 Φ U) (hΦUW : MapsTo Φ U W)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : V, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {x : V} (hx : x ∈ U) (X Y Z T : V) :
    coefficientRm04 b x X Y Z T =
      coefficientRm04 c (Φ x) (fderiv ℝ Φ x X) (fderiv ℝ Φ x Y) (fderiv ℝ Φ x Z)
        (fderiv ℝ Φ x T) := by
  have hΦx : Φ x ∈ W := hΦUW hx
  have hb2 : ContDiffOn ℝ 2 b U := by
    refine (contDiffOn_bilinearComp_fderiv_cross hU hc hΦ hΦUW subset_rfl).congr ?_
    intro z hz
    ext u v
    exact hpull z hz u v
  have hbsymm : ∀ y ∈ U, ∀ u v : V, b y u v = b y v u := fun y hy u v =>
    (hpull y hy u v).trans ((hcsymm (Φ y) (hΦUW hy) _ _).trans (hpull y hy v u).symm)
  have hbco := isCoercive_of_pullback_cross hcco hΦUW hΦinv hpull
  have hΦ3 : ContDiffAt ℝ 3 Φ x := hΦ.contDiffAt (hU.mem_nhds hx)
  have hΓc : ContDiffAt ℝ 1
      (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) (Φ x) :=
    (MetricKoszul.raisedKoszulOp_contDiffOn (n := 1) (hc.of_le (by norm_num))
      (hc.fderiv_of_isOpen hW (by norm_num)) hcco).contDiffAt (hW.mem_nhds hΦx)
  have hpar : ∀ᶠ y in 𝓝 x, ∀ X' u : V, Geometry.Connection.bundleMapCovDeriv
      (fun z => (MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) : V →L[ℝ] V →L[ℝ] V))
      (Geometry.Connection.pullbackConnectionForm
        (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) Φ)
      (fderiv ℝ Φ) y X' u = 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hx)
      (bundleMapCovDeriv_raisedKoszulOp_of_pullback_cross hU hW (hc.of_le (by norm_num)) hcsymm
        hcco (hΦ.of_le (by norm_num)) hΦUW hΦinv hpull)
  have hint := Geometry.Connection.connectionFormCurvatureCLM_intertwines_of_parallel
    (differentiableAt_raisedKoszulOp (hb2.contDiffAt (hU.mem_nhds hx)) (hbco x hx))
    ((Geometry.Connection.pullbackConnectionForm_contDiffAt (F := Φ) hΓc
      (hΦ3.of_le (by norm_num))).differentiableAt (by norm_num))
    (hΦ3.fderiv_right (m := 2) (by norm_num)) hpar X Y
  have hZ : Geometry.Connection.connectionFormCurvature
      (Geometry.Connection.pullbackConnectionForm
        (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) Φ)
      x X Y (fderiv ℝ Φ x Z) =
      fderiv ℝ Φ x (Geometry.Connection.connectionFormCurvature
        (fun z => (MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) : V →L[ℝ] V →L[ℝ] V))
        x X Y Z) :=
    DFunLike.congr_fun hint Z
  have h1 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hU hb2 hbsymm hbco hx X Y Z T
  have h2 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hW hc hcsymm hcco hΦx
    (fderiv ℝ Φ x X) (fderiv ℝ Φ x Y) (fderiv ℝ Φ x Z) (fderiv ℝ Φ x T)
  have h3 := Geometry.Connection.connectionFormCurvature_pullback (F := Φ)
    (hΓc.differentiableAt (by norm_num)) (hΦ3.of_le (by norm_num)) X Y (fderiv ℝ Φ x Z)
  rw [h1, hpull x hx]
  refine (congrArg (fun w => c (Φ x) w (fderiv ℝ Φ x T)) hZ.symm).trans ?_
  rw [h3]
  exact h2.symm

/-- **Coefficient sectional curvature across model spaces.** -/
theorem coefficientSectional_transition_cross {U : Set V} {W : Set E} (hU : IsOpen U)
    (hW : IsOpen W) {b : V → V →L[ℝ] V →L[ℝ] ℝ} {c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : V → E}
    (hc : ContDiffOn ℝ 2 c W) (hcsymm : ∀ z ∈ W, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ W, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 3 Φ U) (hΦUW : MapsTo Φ U W)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : V, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {x : V} (hx : x ∈ U) (v u : V) :
    coefficientSectional b x v u =
      coefficientSectional c (Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x u) := by
  rw [coefficientSectional_def, coefficientSectional_def,
    coefficientRm04_transition_cross hU hW hc hcsymm hcco hΦ hΦUW hΦinv hpull hx v u u v,
    hpull x hx v v, hpull x hx u u, hpull x hx v u]

end DifferentialGeometry.Analysis
