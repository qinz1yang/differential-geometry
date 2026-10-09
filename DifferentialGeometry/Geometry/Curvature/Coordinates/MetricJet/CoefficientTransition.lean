import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientPullback
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.KoszulIdentification
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalCoordinates.TransitionBounds
import DifferentialGeometry.Geometry.Connection.ConnectionForm.CurvatureNaturality

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem fderiv_fderiv_eq_raisedKoszulOp_of_pullback {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 1 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 2 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {y : E} (hy : y ∈ U) (X u : E) :
    fderiv ℝ (fderiv ℝ Φ) y X u =
      fderiv ℝ Φ y (MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) X u) -
        MetricKoszul.raisedKoszulOp (c (Φ y)) (fderiv ℝ c (Φ y)) (fderiv ℝ Φ y X)
          (fderiv ℝ Φ y u) := by
  have hΦy : Φ y ∈ V := hΦUV hy
  have hb1 : ContDiffOn ℝ 1 b U :=
    (contDiffOn_of_pullback (k := 1) hU (hc.of_le (by norm_num)) (hΦ.of_le (by norm_num))
      hΦUV hpull).of_le (by norm_num)
  have hΦ2 : ContDiffAt ℝ 2 Φ y := hΦ.contDiffAt (hU.mem_nhds hy)
  have hBco : IsCoercive (b y) := isCoercive_of_pullback hcco hΦUV hΦinv hpull y hy
  have hCco : IsCoercive (c (Φ y)) := hcco (Φ y) hΦy
  obtain ⟨e, he⟩ := hΦinv y hy
  have hPhi : HasFDerivAt Φ (e : E →L[ℝ] E) y := by
    rw [he]
    exact (hΦ2.differentiableAt (by norm_num)).hasFDerivAt
  have hev : ∀ v : E, e v = fderiv ℝ Φ y v := fun v => by
    rw [← he, ContinuousLinearEquiv.coe_coe]
  have h := CheegerGromovCompactness.MetricIsometry.isom_second_eq b c Φ (fderiv ℝ Φ)
    (fderiv ℝ b y) (fderiv ℝ c (Φ y)) e (fderiv ℝ (fderiv ℝ Φ) y)
    ((hb1.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
    ((hc.contDiffAt (hV.mem_nhds hΦy)).differentiableAt (by norm_num)).hasFDerivAt hPhi
    ((hΦ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    (Filter.eventually_of_mem (hU.mem_nhds hy) hpull) he.symm (hcsymm (Φ y) hΦy)
    (hΦ2.isSymmSndFDerivAt (by norm_num)).eq hBco hCco X u
  rw [MetricKoszul.raisedKoszulOp_eq hBco, MetricKoszul.raisedKoszulOp_eq hCco, ← hev X, ← hev u,
    ← hev]
  exact h

private theorem bundleMapCovDeriv_pullback_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A C : E → E →L[ℝ] E →L[ℝ] E) (Φ : E → E) (y X u : E) :
    Geometry.Connection.bundleMapCovDeriv A (Geometry.Connection.pullbackConnectionForm C Φ)
        (fderiv ℝ Φ) y X u =
      fderiv ℝ (fderiv ℝ Φ) y X u + C (Φ y) (fderiv ℝ Φ y X) (fderiv ℝ Φ y u) -
        fderiv ℝ Φ y (A y X u) :=
  rfl

theorem bundleMapCovDeriv_raisedKoszulOp_of_pullback {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ContinuousDualEquiv E] [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 1 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 2 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v)) :
    ∀ y ∈ U, ∀ X u : E,
      Geometry.Connection.bundleMapCovDeriv
        (fun z => (MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) : E →L[ℝ] E →L[ℝ] E))
        (Geometry.Connection.pullbackConnectionForm
          (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) Φ)
        (fderiv ℝ Φ) y X u = 0 := by
  intro y hy X u
  rw [bundleMapCovDeriv_pullback_apply,
    fderiv_fderiv_eq_raisedKoszulOp_of_pullback hU hV hc hcsymm hcco hΦ hΦUV hΦinv hpull hy X u]
  exact sub_eq_zero.mpr (sub_add_cancel _ _)

theorem coefficientRm04_transition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {b c : E → E →L[ℝ] E →L[ℝ] ℝ} {Φ : E → E}
    (hc : ContDiffOn ℝ 2 c V) (hcsymm : ∀ z ∈ V, ∀ u v : E, c z u v = c z v u)
    (hcco : ∀ z ∈ V, IsCoercive (c z)) (hΦ : ContDiffOn ℝ 3 Φ U) (hΦUV : MapsTo Φ U V)
    (hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible)
    (hpull : ∀ y ∈ U, ∀ u v : E, b y u v = c (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y v))
    {x : E} (hx : x ∈ U) (X Y Z W : E) :
    coefficientRm04 b x X Y Z W =
      coefficientRm04 c (Φ x) (fderiv ℝ Φ x X) (fderiv ℝ Φ x Y) (fderiv ℝ Φ x Z)
        (fderiv ℝ Φ x W) := by
  let _ : ContinuousDualEquiv E := IsCoercive.continuousDualEquivOfFiniteDimensional
  have hΦx : Φ x ∈ V := hΦUV hx
  have hb2 : ContDiffOn ℝ 2 b U :=
    (contDiffOn_of_pullback (k := 2) hU (hc.of_le (by norm_num)) (hΦ.of_le (by norm_num))
      hΦUV hpull).of_le (by norm_num)
  have hbsymm := symm_of_pullback hcsymm hΦUV hpull
  have hbco := isCoercive_of_pullback hcco hΦUV hΦinv hpull
  have hΦ3 : ContDiffAt ℝ 3 Φ x := hΦ.contDiffAt (hU.mem_nhds hx)
  have hΓc : ContDiffAt ℝ 1
      (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) (Φ x) :=
    (MetricKoszul.raisedKoszulOp_contDiffOn (n := 1) (hc.of_le (by norm_num))
      (hc.fderiv_of_isOpen hV (by norm_num)) hcco).contDiffAt (hV.mem_nhds hΦx)
  have hpar : ∀ᶠ y in 𝓝 x, ∀ X' u : E, Geometry.Connection.bundleMapCovDeriv
      (fun z => (MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) : E →L[ℝ] E →L[ℝ] E))
      (Geometry.Connection.pullbackConnectionForm
        (fun z => (MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z) : E →L[ℝ] E →L[ℝ] E)) Φ)
      (fderiv ℝ Φ) y X' u = 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hx)
      (bundleMapCovDeriv_raisedKoszulOp_of_pullback hU hV (hc.of_le (by norm_num)) hcsymm hcco
        (hΦ.of_le (by norm_num)) hΦUV hΦinv hpull)
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
        (fun z => (MetricKoszul.raisedKoszulOp (b z) (fderiv ℝ b z) : E →L[ℝ] E →L[ℝ] E))
        x X Y Z) :=
    DFunLike.congr_fun hint Z
  have h1 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hU hb2 hbsymm hbco hx X Y Z W
  have h2 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hV hc hcsymm hcco hΦx
    (fderiv ℝ Φ x X) (fderiv ℝ Φ x Y) (fderiv ℝ Φ x Z) (fderiv ℝ Φ x W)
  have h3 := Geometry.Connection.connectionFormCurvature_pullback (F := Φ)
    (hΓc.differentiableAt (by norm_num)) (hΦ3.of_le (by norm_num)) X Y (fderiv ℝ Φ x Z)
  rw [h1, hpull x hx]
  refine (congrArg (fun w => c (Φ x) w (fderiv ℝ Φ x W)) hZ.symm).trans ?_
  rw [h3]
  exact h2.symm

end DifferentialGeometry.Analysis
