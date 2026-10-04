import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CrossSpaceTransition
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

/-!
# The finite Gauss identity for a totally geodesic affine slice (lane CMS3-CARRIER, group G3)

EXIT-51's curvature leaf (review §14, disposition D10). For a `C²` coefficient field `c` on an open
set of `V`, an affine slice `ι z = a₀ + J z` (`J : P →L V` injective) and the restricted field
`c_A z = c (ι z) ∘ (J × J)`: if the Christoffel form of `c` maps `J`-pairs into `range J` along the
slice (vanishing second fundamental form), then
`coefficientRm04 c_A z X Y Z T = coefficientRm04 c (ι z) (J X) (J Y) (J Z) (J T)`
(`coefficientRm04_affineSliceCoeff`) and the same for the coefficient sectional curvature
(`coefficientSectional_affineSliceCoeff`).

Route (template: `ProductCurvature.lean`): by the Koszul formula the Christoffel form of `c_A` is
`J⁻¹ Γ_c (J ·, J ·)` (`raisedKoszulOp_affineSliceCoeff`), so the constant map `J` is parallel and the
connection-form curvature intertwines (`connectionFormCurvatureCLM_intertwines_of_parallel`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

local instance continuousDualEquivV_CMS3CARRIER : DifferentialGeometry.ContinuousDualEquiv V :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance continuousDualEquivP_CMS3CARRIER : DifferentialGeometry.ContinuousDualEquiv P :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- The coefficient field restricted along the affine slice `z ↦ a₀ + J z`. -/
def affineSliceCoeff (c : V → V →L[ℝ] V →L[ℝ] ℝ) (a₀ : V) (J : P →L[ℝ] V) (z : P) :
    P →L[ℝ] P →L[ℝ] ℝ :=
  ((((c (a₀ + J z)).comp J).flip.comp J).flip)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ P] in
@[simp] theorem affineSliceCoeff_apply (c : V → V →L[ℝ] V →L[ℝ] ℝ) (a₀ : V) (J : P →L[ℝ] V)
    (z X Y : P) : affineSliceCoeff c a₀ J z X Y = c (a₀ + J z) (J X) (J Y) := by
  simp [affineSliceCoeff]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ P] in
/-- The restricted field is as regular as `c`. -/
theorem contDiffOn_affineSliceCoeff {c : V → V →L[ℝ] V →L[ℝ] ℝ} {U : Set V} {n : ℕ∞ω}
    (hc : ContDiffOn ℝ n c U) (a₀ : V) (J : P →L[ℝ] V) {W : Set P}
    (hWU : MapsTo (fun z => a₀ + J z) W U) : ContDiffOn ℝ n (affineSliceCoeff c a₀ J) W := by
  have hι : ContDiffOn ℝ n (fun z : P => a₀ + J z) W :=
    (contDiff_const.add J.contDiff).contDiffOn
  have hcι : ContDiffOn ℝ n (fun z => c (a₀ + J z)) W := hc.comp hι hWU
  have hA : ContDiffOn ℝ n (fun z => (c (a₀ + J z)).comp J) W := hcι.clm_comp contDiffOn_const
  have hB : ContDiffOn ℝ n (fun z => ((c (a₀ + J z)).comp J).flip) W :=
    (ContinuousLinearMap.flipₗᵢ ℝ P V ℝ).contDiff.comp_contDiffOn hA
  have hC : ContDiffOn ℝ n (fun z => ((c (a₀ + J z)).comp J).flip.comp J) W :=
    hB.clm_comp contDiffOn_const
  exact (ContinuousLinearMap.flipₗᵢ ℝ P P ℝ).contDiff.comp_contDiffOn hC

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ P] in
/-- The derivative of the restricted field is the derivative of `c` in `J`-directions. -/
theorem fderiv_affineSliceCoeff_apply {c : V → V →L[ℝ] V →L[ℝ] ℝ} {a₀ : V} {J : P →L[ℝ] V}
    {z : P} (hc : DifferentiableAt ℝ c (a₀ + J z)) (X u w : P) :
    fderiv ℝ (affineSliceCoeff c a₀ J) z X u w = fderiv ℝ c (a₀ + J z) (J X) (J u) (J w) := by
  have hcd : HasFDerivAt c (fderiv ℝ c (a₀ + J z)) (a₀ + J z) := hc.hasFDerivAt
  have hι : HasFDerivAt (fun z : P => a₀ + J z) J z := (J.hasFDerivAt).const_add a₀
  let ev : (P →L[ℝ] P →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (P →L[ℝ] ℝ) u)
  let evV : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (J w)).comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (J u))
  have hdiff : DifferentiableAt ℝ (affineSliceCoeff c a₀ J) z := by
    have h1 : DifferentiableAt ℝ (fun z => c (a₀ + J z)) z := hc.comp z hι.differentiableAt
    have h2 : DifferentiableAt ℝ (fun z => (c (a₀ + J z)).comp J) z :=
      h1.clm_comp (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ (fun z => ((c (a₀ + J z)).comp J).flip) z :=
      (ContinuousLinearMap.flipₗᵢ ℝ P V ℝ).differentiableAt.comp z h2
    have h4 : DifferentiableAt ℝ (fun z => ((c (a₀ + J z)).comp J).flip.comp J) z :=
      h3.clm_comp (differentiableAt_const _)
    exact (ContinuousLinearMap.flipₗᵢ ℝ P P ℝ).differentiableAt.comp z h4
  have h1 : HasFDerivAt (fun z' => affineSliceCoeff c a₀ J z' u w)
      (ev.comp (fderiv ℝ (affineSliceCoeff c a₀ J) z)) z :=
    ev.hasFDerivAt.comp z hdiff.hasFDerivAt
  have h2 : HasFDerivAt (fun z' => affineSliceCoeff c a₀ J z' u w)
      ((evV.comp (fderiv ℝ c (a₀ + J z))).comp J) z := by
    have h := (evV.hasFDerivAt.comp (a₀ + J z) hcd).comp z hι
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun z' => ?_)
    simp [evV]
  have h := congrArg (fun L : P →L[ℝ] ℝ => L X) (h1.unique h2)
  simpa [ev, evV] using h

/-- **Christoffel form of the restricted field** when the slice is totally geodesic: the
Christoffel form of `c_A` is `J⁻¹ Γ_c (J ·, J ·)`. -/
theorem raisedKoszulOp_affineSliceCoeff {c : V → V →L[ℝ] V →L[ℝ] ℝ} {a₀ : V} {J : P →L[ℝ] V}
    (hJ : Function.Injective J) {z : P} (hc : DifferentiableAt ℝ c (a₀ + J z))
    (hcco : IsCoercive (c (a₀ + J z))) (X u : P) {Z : P}
    (hZ : MetricKoszul.raisedKoszulOp (c (a₀ + J z)) (fderiv ℝ c (a₀ + J z)) (J X) (J u) = J Z) :
    MetricKoszul.raisedKoszulOp (affineSliceCoeff c a₀ J z)
      (fderiv ℝ (affineSliceCoeff c a₀ J) z) X u = Z := by
  have hco : IsCoercive (affineSliceCoeff c a₀ J z) := by
    apply ContinuousLinearMap.isCoercive_of_posDef
    intro v hv
    rw [affineSliceCoeff_apply]
    obtain ⟨κ, hκ, hκu⟩ := hcco
    have hJv : J v ≠ 0 := fun h => hv (hJ (h.trans (map_zero J).symm))
    exact lt_of_lt_of_le (mul_pos (mul_pos hκ (norm_pos_iff.mpr hJv)) (norm_pos_iff.mpr hJv))
      (hκu _)
  apply hco.bilin_injective
  rw [apply_raisedKoszulOp hco]
  refine ContinuousLinearMap.ext fun t => ?_
  rw [MetricKoszul.koszul_cov_apply, fderiv_affineSliceCoeff_apply hc,
    fderiv_affineSliceCoeff_apply hc, fderiv_affineSliceCoeff_apply hc, affineSliceCoeff_apply,
    ← hZ]
  have hcy := congrArg (fun L : V →L[ℝ] ℝ => L (J t))
    (apply_raisedKoszulOp hcco (fderiv ℝ c (a₀ + J z)) (J X) (J u))
  simp only [MetricKoszul.koszul_cov_apply] at hcy
  exact hcy.symm

/-- **The finite Gauss identity with vanishing second fundamental form**, coefficient form. -/
theorem coefficientRm04_affineSliceCoeff {U : Set V} (hU : IsOpen U)
    {c : V → V →L[ℝ] V →L[ℝ] ℝ} (hc : ContDiffOn ℝ 2 c U)
    (hcsymm : ∀ y ∈ U, ∀ u v : V, c y u v = c y v u) (hcco : ∀ y ∈ U, IsCoercive (c y))
    (a₀ : V) {J : P →L[ℝ] V} (hJ : Function.Injective J) {W : Set P} (hW : IsOpen W)
    (hWU : MapsTo (fun z => a₀ + J z) W U)
    (htg : ∀ z ∈ W, ∀ X u : P, ∃ Z : P,
      MetricKoszul.raisedKoszulOp (c (a₀ + J z)) (fderiv ℝ c (a₀ + J z)) (J X) (J u) = J Z)
    {z₀ : P} (hz₀ : z₀ ∈ W) (X Y Z T : P) :
    coefficientRm04 (affineSliceCoeff c a₀ J) z₀ X Y Z T =
      coefficientRm04 c (a₀ + J z₀) (J X) (J Y) (J Z) (J T) := by
  set cA := affineSliceCoeff c a₀ J with hcA
  have hcA2 : ContDiffOn ℝ 2 cA W := contDiffOn_affineSliceCoeff hc a₀ J hWU
  have hcAsymm : ∀ z ∈ W, ∀ u v : P, cA z u v = cA z v u := fun z hz u v => by
    rw [affineSliceCoeff_apply, affineSliceCoeff_apply, hcsymm _ (hWU hz)]
  have hcAco : ∀ z ∈ W, IsCoercive (cA z) := by
    intro z hz
    apply ContinuousLinearMap.isCoercive_of_posDef
    intro v hv
    rw [affineSliceCoeff_apply]
    obtain ⟨κ, hκ, hκu⟩ := hcco _ (hWU hz)
    have hJv : J v ≠ 0 := fun h => hv (hJ (h.trans (map_zero J).symm))
    exact lt_of_lt_of_le (mul_pos (mul_pos hκ (norm_pos_iff.mpr hJv)) (norm_pos_iff.mpr hJv))
      (hκu _)
  have hy₀ : a₀ + J z₀ ∈ U := hWU hz₀
  -- the slice map and its constant derivative
  let ι : P → V := fun z => a₀ + J z
  have hιd : ∀ z, HasFDerivAt ι J z := fun z => (J.hasFDerivAt).const_add a₀
  have hfι : fderiv ℝ ι = fun _ => J := funext fun z => (hιd z).fderiv
  have hι2 : ContDiffAt ℝ 2 ι z₀ := (contDiff_const.add J.contDiff).contDiffAt
  let A : P → P →L[ℝ] P →L[ℝ] P := fun z => MetricKoszul.raisedKoszulOp (cA z) (fderiv ℝ cA z)
  let Γ : V → V →L[ℝ] V →L[ℝ] V := fun y => MetricKoszul.raisedKoszulOp (c y) (fderiv ℝ c y)
  have hA : DifferentiableAt ℝ A z₀ :=
    differentiableAt_raisedKoszulOp (hcA2.contDiffAt (hW.mem_nhds hz₀)) (hcAco z₀ hz₀)
  have hΓ1 : ContDiffAt ℝ 1 Γ (ι z₀) :=
    (MetricKoszul.raisedKoszulOp_contDiffOn (n := 1) (hc.of_le (by norm_num))
      (hc.fderiv_of_isOpen hU (by norm_num)) hcco).contDiffAt (hU.mem_nhds hy₀)
  have hC : DifferentiableAt ℝ (Geometry.Connection.pullbackConnectionForm Γ ι) z₀ :=
    (Geometry.Connection.pullbackConnectionForm_contDiffAt (n := 1) hΓ1 hι2).differentiableAt
      (by norm_num)
  have hJ2 : ContDiffAt ℝ 2 (fderiv ℝ ι) z₀ := by
    rw [hfι]
    exact contDiffAt_const
  have hpar : ∀ᶠ z in 𝓝 z₀, ∀ X' u : P,
      Geometry.Connection.bundleMapCovDeriv A (Geometry.Connection.pullbackConnectionForm Γ ι)
        (fderiv ℝ ι) z X' u = 0 := by
    filter_upwards [hW.mem_nhds hz₀] with z hz X' u
    have hcz : DifferentiableAt ℝ c (a₀ + J z) :=
      (hc.contDiffAt (hU.mem_nhds (hWU hz))).differentiableAt (by norm_num)
    obtain ⟨Z', hZ'⟩ := htg z hz X' u
    have hAz := raisedKoszulOp_affineSliceCoeff hJ hcz (hcco _ (hWU hz)) X' u hZ'
    have h0 : fderiv ℝ (fun _ : P => J) z = 0 := fderiv_const_apply J
    simp only [Geometry.Connection.bundleMapCovDeriv, Geometry.Connection.pullbackConnectionForm,
      hfι, ContinuousLinearMap.comp_apply, h0, zero_apply, zero_add]
    change Γ (ι z) (J X') (J u) - J (A z X' u) = 0
    change Γ (a₀ + J z) (J X') (J u) - J (MetricKoszul.raisedKoszulOp (cA z) (fderiv ℝ cA z) X' u)
      = 0
    rw [hAz, hZ', sub_self]
  have hint := Geometry.Connection.connectionFormCurvatureCLM_intertwines_of_parallel
    hA hC hJ2 hpar X Y
  have hZ := DFunLike.congr_fun hint Z
  simp only [ContinuousLinearMap.comp_apply,
    Geometry.Connection.connectionFormCurvatureCLM_apply] at hZ
  have h3 := Geometry.Connection.connectionFormCurvature_pullback (C := Γ) (F := ι)
    (hΓ1.differentiableAt (by norm_num)) hι2 X Y (fderiv ℝ ι z₀ Z)
  rw [hfι] at h3 hZ
  have h1 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hW hcA2 hcAsymm hcAco hz₀
    X Y Z T
  have h2 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hU hc hcsymm hcco hy₀
    (J X) (J Y) (J Z) (J T)
  rw [h1, h2, affineSliceCoeff_apply]
  change c (ι z₀) (J (Geometry.Connection.connectionFormCurvature A z₀ X Y Z)) (J T) =
    c (ι z₀) (Geometry.Connection.connectionFormCurvature Γ (ι z₀) (J X) (J Y) (J Z)) (J T)
  rw [← h3, hZ]

/-- **The finite Gauss identity, sectional form.** -/
theorem coefficientSectional_affineSliceCoeff {U : Set V} (hU : IsOpen U)
    {c : V → V →L[ℝ] V →L[ℝ] ℝ} (hc : ContDiffOn ℝ 2 c U)
    (hcsymm : ∀ y ∈ U, ∀ u v : V, c y u v = c y v u) (hcco : ∀ y ∈ U, IsCoercive (c y))
    (a₀ : V) {J : P →L[ℝ] V} (hJ : Function.Injective J) {W : Set P} (hW : IsOpen W)
    (hWU : MapsTo (fun z => a₀ + J z) W U)
    (htg : ∀ z ∈ W, ∀ X u : P, ∃ Z : P,
      MetricKoszul.raisedKoszulOp (c (a₀ + J z)) (fderiv ℝ c (a₀ + J z)) (J X) (J u) = J Z)
    {z₀ : P} (hz₀ : z₀ ∈ W) (X Y : P) :
    coefficientSectional (affineSliceCoeff c a₀ J) z₀ X Y =
      coefficientSectional c (a₀ + J z₀) (J X) (J Y) := by
  rw [coefficientSectional_def, coefficientSectional_def,
    coefficientRm04_affineSliceCoeff hU hc hcsymm hcco a₀ hJ hW hWU htg hz₀,
    affineSliceCoeff_apply, affineSliceCoeff_apply, affineSliceCoeff_apply]

end DifferentialGeometry.Analysis
