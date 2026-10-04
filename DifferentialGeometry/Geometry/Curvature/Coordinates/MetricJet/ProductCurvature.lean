import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CrossSpaceTransition

/-!
# Coefficient curvature of a product with a flat factor

For the coefficient field `⟪a.1, a'.1⟫ + c y.2 a.2 a'.2` on `F × P`, the coefficient curvature
on vectors tangent to the `P` factor is the coefficient curvature of `c`. The Christoffel form of
the product is `(0, Γ_c)`; the slice inclusion `p ↦ (u, p)` is therefore parallel, and the
cross-space intertwining lemma for connection-form curvature gives the identity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {F P : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] in
/-- Regularity of a product coefficient field, read off from its `P` factor. -/
theorem contDiffOn_prod_coefficient {W : Set P} {c : P → P →L[ℝ] P →L[ℝ] ℝ} {n : ℕ∞ω}
    (hc : ContDiffOn ℝ n c W) {b : F × P → (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ}
    (hb : ∀ y : F × P, y.2 ∈ W → ∀ a a' : F × P, b y a a' = inner ℝ a.1 a'.1 + c y.2 a.2 a'.2)
    {y₀ : F × P} (hy₀ : y₀.2 ∈ W) :
    ContDiffOn ℝ n b (Prod.snd ⁻¹' W) := by
  let S : F × P →L[ℝ] P := ContinuousLinearMap.snd ℝ F P
  have hcs : ContDiffOn ℝ n (fun y : F × P => c y.2) (Prod.snd ⁻¹' W) :=
    hc.comp contDiffOn_snd fun _ hy => hy
  have hA : ContDiffOn ℝ n (fun y : F × P => (c y.2).comp S) (Prod.snd ⁻¹' W) :=
    hcs.clm_comp contDiffOn_const
  have hB : ContDiffOn ℝ n (fun y : F × P => ((c y.2).comp S).flip) (Prod.snd ⁻¹' W) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (F × P) P ℝ).contDiff.comp_contDiffOn hA
  have hC : ContDiffOn ℝ n (fun y : F × P => ((c y.2).comp S).flip.comp S) (Prod.snd ⁻¹' W) :=
    hB.clm_comp contDiffOn_const
  have hD : ContDiffOn ℝ n
      (fun y : F × P => (((c y.2).comp S).flip.comp S).flip) (Prod.snd ⁻¹' W) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (F × P) (F × P) ℝ).contDiff.comp_contDiffOn hC
  have hE := (contDiffOn_const (c := b y₀ - (((c y₀.2).comp S).flip.comp S).flip)).add hD
  refine hE.congr fun y hy => ?_
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun a' => ?_
  simp only [add_apply, sub_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply]
  rw [hb y hy, hb y₀ hy₀]
  simp only [S, ContinuousLinearMap.coe_snd']
  ring

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] in
theorem isCoercive_prod_coefficient {C : P →L[ℝ] P →L[ℝ] ℝ} (hC : IsCoercive C)
    {B : (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ}
    (hB : ∀ a a' : F × P, B a a' = inner ℝ a.1 a'.1 + C a.2 a'.2) : IsCoercive B := by
  obtain ⟨k, hk, hku⟩ := hC
  refine ⟨min 1 k, lt_min one_pos hk, fun a => ?_⟩
  rw [hB, real_inner_self_eq_norm_mul_norm]
  have h2 := hku a.2
  have hm0 : 0 ≤ min 1 k := (lt_min one_pos hk).le
  have hm1 : min 1 k ≤ 1 := min_le_left _ _
  have hmk : min 1 k ≤ k := min_le_right _ _
  have n1 := norm_nonneg a.1
  have n2 := norm_nonneg a.2
  rcases le_total ‖a.1‖ ‖a.2‖ with h | h
  · rw [Prod.norm_def, max_eq_right h]
    nlinarith [mul_nonneg n1 n1, mul_le_mul_of_nonneg_right hmk (mul_nonneg n2 n2)]
  · rw [Prod.norm_def, max_eq_left h]
    nlinarith [mul_nonneg n2 n2, mul_le_mul_of_nonneg_right hm1 (mul_nonneg n1 n1),
      mul_nonneg hk.le (mul_nonneg n2 n2)]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] in
/-- The derivative of a product coefficient field only sees the `P` factor. -/
theorem fderiv_prod_coefficient_apply {W : Set P} (hW : IsOpen W)
    {c : P → P →L[ℝ] P →L[ℝ] ℝ} (hc : ContDiffOn ℝ 1 c W)
    {b : F × P → (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ}
    (hb : ∀ y : F × P, y.2 ∈ W → ∀ a a' : F × P, b y a a' = inner ℝ a.1 a'.1 + c y.2 a.2 a'.2)
    {y : F × P} (hy : y.2 ∈ W) (d u v : F × P) :
    fderiv ℝ b y d u v = fderiv ℝ c y.2 d.2 u.2 v.2 := by
  have hU : IsOpen (Prod.snd ⁻¹' W : Set (F × P)) := hW.preimage continuous_snd
  have hb1 : ContDiffOn ℝ 1 b (Prod.snd ⁻¹' W) := contDiffOn_prod_coefficient hc hb hy
  have hbd : HasFDerivAt b (fderiv ℝ b y) y :=
    ((hb1.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hcd : HasFDerivAt c (fderiv ℝ c y.2) y.2 :=
    ((hc.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  let ev : ((F × P) →L[ℝ] (F × P) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ ((F × P) →L[ℝ] ℝ) u)
  let evP : (P →L[ℝ] P →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v.2).comp (ContinuousLinearMap.apply ℝ (P →L[ℝ] ℝ) u.2)
  have h1 : HasFDerivAt (fun y' => b y' u v) (ev.comp (fderiv ℝ b y)) y :=
    ev.hasFDerivAt.comp y hbd
  have h2 : HasFDerivAt (fun y' : F × P => inner ℝ u.1 v.1 + c y'.2 u.2 v.2)
      ((evP.comp (fderiv ℝ c y.2)).comp (ContinuousLinearMap.snd ℝ F P)) y :=
    ((evP.hasFDerivAt.comp y.2 hcd).comp y (hasFDerivAt_snd)).const_add _
  have h2' : HasFDerivAt (fun y' => b y' u v)
      ((evP.comp (fderiv ℝ c y.2)).comp (ContinuousLinearMap.snd ℝ F P)) y := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hy] with y' hy'
    exact hb y' hy' u v
  have h := congrArg (fun L : (F × P) →L[ℝ] ℝ => L d) (h1.unique h2')
  simpa [ev, evP] using h

/-- The Christoffel form of a product with a flat factor. -/
theorem raisedKoszulOp_prod_coefficient {W : Set P} (hW : IsOpen W)
    {c : P → P →L[ℝ] P →L[ℝ] ℝ} (hc : ContDiffOn ℝ 1 c W)
    (hcco : ∀ z ∈ W, IsCoercive (c z))
    {b : F × P → (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ}
    (hb : ∀ y : F × P, y.2 ∈ W → ∀ a a' : F × P, b y a a' = inner ℝ a.1 a'.1 + c y.2 a.2 a'.2)
    {y : F × P} (hy : y.2 ∈ W) (a a' : F × P) :
    MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) a a' =
      ((0 : F), MetricKoszul.raisedKoszulOp (c y.2) (fderiv ℝ c y.2) a.2 a'.2) := by
  have hbco : IsCoercive (b y) := isCoercive_prod_coefficient (hcco y.2 hy) (hb y hy)
  apply hbco.bilin_injective
  rw [apply_raisedKoszulOp hbco]
  refine ContinuousLinearMap.ext fun t => ?_
  rw [MetricKoszul.koszul_cov_apply, hb y hy, fderiv_prod_coefficient_apply hW hc hb hy,
    fderiv_prod_coefficient_apply hW hc hb hy, fderiv_prod_coefficient_apply hW hc hb hy]
  have hcy := congrArg (fun L : P →L[ℝ] ℝ => L t.2)
    (apply_raisedKoszulOp (hcco y.2 hy) (fderiv ℝ c y.2) a.2 a'.2)
  simp only [MetricKoszul.koszul_cov_apply] at hcy
  simp only [inner_zero_left, zero_add]
  exact hcy.symm

/-- **Coefficient curvature of a product with a flat factor**, on vectors tangent to `P`. -/
theorem coefficientRm04_prod_snd {W : Set P} (hW : IsOpen W) {c : P → P →L[ℝ] P →L[ℝ] ℝ}
    (hc : ContDiffOn ℝ 2 c W) (hcsymm : ∀ z ∈ W, ∀ u v : P, c z u v = c z v u)
    (hcco : ∀ z ∈ W, IsCoercive (c z)) {b : F × P → (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ}
    (hb : ∀ y : F × P, y.2 ∈ W → ∀ a a' : F × P, b y a a' = inner ℝ a.1 a'.1 + c y.2 a.2 a'.2)
    {y : F × P} (hy : y.2 ∈ W) (X Y Z T : P) :
    coefficientRm04 b y (0, X) (0, Y) (0, Z) (0, T) = coefficientRm04 c y.2 X Y Z T := by
  obtain ⟨u₀, z₀⟩ := y
  change z₀ ∈ W at hy
  change coefficientRm04 b (u₀, z₀) (0, X) (0, Y) (0, Z) (0, T) =
    coefficientRm04 c z₀ X Y Z T
  have hU : IsOpen (Prod.snd ⁻¹' W : Set (F × P)) := hW.preimage continuous_snd
  have hb2 : ContDiffOn ℝ 2 b (Prod.snd ⁻¹' W) := contDiffOn_prod_coefficient hc hb (y₀ := (u₀, z₀)) hy
  have hbsymm : ∀ y ∈ (Prod.snd ⁻¹' W : Set (F × P)), ∀ a a' : F × P, b y a a' = b y a' a := by
    intro y hy' a a'
    rw [hb y hy', hb y hy', hcsymm y.2 hy', real_inner_comm]
  have hbco : ∀ y ∈ (Prod.snd ⁻¹' W : Set (F × P)), IsCoercive (b y) := fun y hy' =>
    isCoercive_prod_coefficient (hcco y.2 hy') (hb y hy')
  have hc1 : ContDiffOn ℝ 1 c W := hc.of_le (by norm_num)
  -- the slice inclusion and its constant derivative
  let ι : P → F × P := fun p => (u₀, p)
  let J : P →L[ℝ] F × P := (0 : P →L[ℝ] F).prod (ContinuousLinearMap.id ℝ P)
  have hιd : ∀ p, HasFDerivAt ι J p := fun p =>
    (hasFDerivAt_const u₀ p).prodMk (hasFDerivAt_id p)
  have hfι : fderiv ℝ ι = fun _ => J := funext fun p => (hιd p).fderiv
  have hι2 : ContDiffAt ℝ 2 ι z₀ := (contDiff_const.prodMk contDiff_id).contDiffAt
  let A : P → P →L[ℝ] P →L[ℝ] P := fun z => MetricKoszul.raisedKoszulOp (c z) (fderiv ℝ c z)
  let Γ : F × P → (F × P) →L[ℝ] (F × P) →L[ℝ] (F × P) := fun y =>
    MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y)
  have hA : DifferentiableAt ℝ A z₀ :=
    differentiableAt_raisedKoszulOp (hc.contDiffAt (hW.mem_nhds hy)) (hcco z₀ hy)
  have hΓ1 : ContDiffAt ℝ 1 Γ (ι z₀) :=
    (MetricKoszul.raisedKoszulOp_contDiffOn (n := 1) (hb2.of_le (by norm_num))
      (hb2.fderiv_of_isOpen hU (by norm_num)) hbco).contDiffAt (hU.mem_nhds hy)
  have hC : DifferentiableAt ℝ (Geometry.Connection.pullbackConnectionForm Γ ι) z₀ :=
    (Geometry.Connection.pullbackConnectionForm_contDiffAt (n := 1) hΓ1 hι2).differentiableAt
      (by norm_num)
  have hJ : ContDiffAt ℝ 2 (fderiv ℝ ι) z₀ := by
    rw [hfι]
    exact contDiffAt_const
  have hpar : ∀ᶠ z in 𝓝 z₀, ∀ X' u : P,
      Geometry.Connection.bundleMapCovDeriv A (Geometry.Connection.pullbackConnectionForm Γ ι)
        (fderiv ℝ ι) z X' u = 0 := by
    filter_upwards [hW.mem_nhds hy] with z hz X' u
    have hΓz := raisedKoszulOp_prod_coefficient hW hc1 hcco hb (y := ι z) hz (J X') (J u)
    have h0 : fderiv ℝ (fun _ : P => J) z = 0 := fderiv_const_apply J
    simp only [Geometry.Connection.bundleMapCovDeriv, Geometry.Connection.pullbackConnectionForm,
      hfι, ContinuousLinearMap.comp_apply, h0, zero_apply, zero_add]
    change Γ (ι z) (J X') (J u) - J (A z X' u) = 0
    rw [hΓz]
    simp [J, A, ι]
  have hint := Geometry.Connection.connectionFormCurvatureCLM_intertwines_of_parallel
    hA hC hJ hpar X Y
  have hZ := DFunLike.congr_fun hint Z
  simp only [ContinuousLinearMap.comp_apply,
    Geometry.Connection.connectionFormCurvatureCLM_apply] at hZ
  have h3 := Geometry.Connection.connectionFormCurvature_pullback (C := Γ) (F := ι)
    (hΓ1.differentiableAt (by norm_num)) hι2 X Y (fderiv ℝ ι z₀ Z)
  rw [hfι] at h3 hZ
  have hJX : J X = (0, X) := by simp [J]
  have hJY : J Y = (0, Y) := by simp [J]
  have hJZ : J Z = (0, Z) := by simp [J]
  rw [hJX, hJY, hJZ] at h3
  rw [hJZ] at hZ
  have h1 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hU hb2 hbsymm hbco
    (x := (u₀, z₀)) hy (0, X) (0, Y) (0, Z) (0, T)
  have h2 := coefficientRm04_eq_connectionFormCurvature_of_isOpen hW hc hcsymm hcco hy X Y Z T
  rw [h1, h2]
  change b (u₀, z₀) (Geometry.Connection.connectionFormCurvature Γ (ι z₀) (0, X) (0, Y) (0, Z))
    (0, T) = _
  rw [← h3, hZ, hb (u₀, z₀) hy]
  simp [J, A]

/-- **Coefficient sectional curvature of a product with a flat factor**, on `P`-planes. -/
theorem coefficientSectional_prod_snd {W : Set P} (hW : IsOpen W)
    {c : P → P →L[ℝ] P →L[ℝ] ℝ} (hc : ContDiffOn ℝ 2 c W)
    (hcsymm : ∀ z ∈ W, ∀ u v : P, c z u v = c z v u) (hcco : ∀ z ∈ W, IsCoercive (c z))
    {b : F × P → (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ}
    (hb : ∀ y : F × P, y.2 ∈ W → ∀ a a' : F × P, b y a a' = inner ℝ a.1 a'.1 + c y.2 a.2 a'.2)
    {y : F × P} (hy : y.2 ∈ W) (X Y : P) :
    coefficientSectional b y (0, X) (0, Y) = coefficientSectional c y.2 X Y := by
  rw [coefficientSectional_def, coefficientSectional_def,
    coefficientRm04_prod_snd hW hc hcsymm hcco hb hy, hb y hy, hb y hy, hb y hy]
  simp

end DifferentialGeometry.Analysis
