import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpec
import DifferentialGeometry.Geometry.Fibration.ActualSlimCloud

/-!
# BCG03: the (CS) kernel of the augmented model (lane BAUG-C, G3)

Draft 61 §1.4 (`plane_spec`: CS on the SAME plane (P)), §2.5 (BM), D61-5, D61-6. FC27's cloud test
(CS) for the augmented stage tables, reduced to INTERIOR inputs plus the boundary (BA)/(BM) slot
errors (the route of TCP06 / SGP06 / EGP07's second half, now with the augmented model):

* `cloud_test_of_graph_coverage_BAUGC` (generic, any `M E H`): FC25's coverage kernel
  (`hausdorffDist_coordinate_graph_coverage_le`) at the two radii `R = r̂/Γ`, `tR`
  (`t = 1 − Γ²/2`, `r̂ = r/c`), SGP06's parameter bookkeeping (`sgp06_parameters_SGP5`) and the
  open-ball test in actual units (`hausdorffEDist_ball_le_of_scaled_coverage_SGP5`): localization,
  approximation `≤ e`, coverage and a `C²` bound `C` of a graph model `Φ` with a `1`-Lipschitz left
  inverse give `hausdorffEDist (T ∩ B(x, r/Γ)) ((x + im DΦ(P(c⁻¹x))) ∩ B(x, r/Γ)) ≤ Γr`;
* the augmented model with at most one listed boundary component `J ⊆ {b₀}` (BCG01's `#J_∂ ≤ 1`):
  `augmentedModel_eq_two_BAUGC` (`Φ^∂ = ι_int Ψ + slot_{b₀}(block_{b₀})`), its left inverse
  `Pc ∘ pr_int` (`norm_comp_augIntProj_le_BAUGC`, `comp_augIntProj_augmentedModel_BAUGC`), its `C²` bound
  `‖D²Φ^∂‖ ≤ ‖D²Ψ‖ + 2‖D²block_{b₀}‖` (`norm_iteratedFDeriv_two_augmentedModel_le_BAUGC`), its
  approximation error `≤ e_int + e_b` (`norm_sub_augmentedModel_le_BAUGC`);
* **`augmented_cloud_test_BAUGC`**: (CS) for the augmented model from the interior localization /
  approximation / coverage / `C²` inputs, the vanishing of the unlisted slots and the listed-slot error;
* `bm_slot_error_BAUGC`: the listed-slot error from BCG-8b's (BM) value error (`≤ 2P_*θ`), and
  `bm_iteratedFDeriv_two_le_BAUGC`: the (BM) `C²` bound `R P_*` in `iteratedFDeriv` form — the two
  boundary inputs of the kernel (D61-5: `1/R_a` never enters);
* consumer `augmented_bm_cloud_test_BAUGC`: (CS) for the augmented (BM) model at a reference with
  one listed component, from the interior inputs and BCG02's (BA) value error.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Topology

open DifferentialGeometry.Analysis GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Kernel

variable {M E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

/-- **The generic graph cloud test** (TCP06 / SGP06 / EGP07 second half, abstract): in the reference
units `c > 0` of a model `Φ : E → H` with a `1`-Lipschitz left inverse `P`, with SGP06's parameters
(`Σ < Γ/200`, `Σ < Γ³/(100C)`, `e < ΓΣ/100`, `3Σ/4 ≤ r/c ≤ 5Σ/4`), the `C²` bound `C` on the
parameter ball, FC03-type localization of the scaled cloud `c⁻¹T` to source points with exact
coordinate `P y = η q`, the approximation `dist(c⁻¹F q, Φ(η q)) ≤ e` and exact coordinate coverage:
the open-ball (CS) test of `T` at `x` holds with the plane `im DΦ(P(c⁻¹x))`, radius `r/Γ` and
error `Γr`. -/
theorem cloud_test_of_graph_coverage_BAUGC (F : M → H) (η : M → E) (D : Set M) (Φ : E → H)
    (P : H →L[ℝ] E) (hP : ∀ z, ‖P z‖ ≤ ‖z‖) (hgraph : ∀ u, P (Φ u) = u) (T : Set H) {x : H}
    (hx : x ∈ T) {c r Γ sg C e : ℝ} (hc : 0 < c) (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hC : 0 < C) (hsgC : sg < Γ ^ 3 / (100 * C)) (he0 : 0 ≤ e)
    (heΓ : e < Γ * sg / 100) (hrlo : 3 * sg / 4 ≤ r / c) (hrhi : r / c ≤ 5 * sg / 4)
    (hreg : ∀ u ∈ closedBall (P (c⁻¹ • x)) (r / c / Γ), ContDiffAt ℝ 2 Φ u)
    (hsecond : ∀ u ∈ closedBall (P (c⁻¹ • x)) (r / c / Γ), ‖iteratedFDeriv ℝ 2 Φ u‖ ≤ C)
    (hlocal : ∀ y ∈ (fun z => c⁻¹ • z) '' T ∩ closedBall (c⁻¹ • x) (r / c / Γ),
      ∃ q ∈ D, c⁻¹ • F q = y ∧ P y = η q)
    (happrox : ∀ q ∈ D, dist (c⁻¹ • F q) (Φ (η q)) ≤ e)
    (hcover : ∀ u ∈ closedBall (P (c⁻¹ • x)) (r / c / Γ), ∃ q ∈ D, η q = u ∧ F q ∈ T) :
    hausdorffEDist (T ∩ ball x (r / Γ))
      ((AffineSubspace.mk' x (fderiv ℝ Φ (P (c⁻¹ • x))).range : Set H) ∩ ball x (r / Γ)) ≤
        ENNReal.ofReal (Γ * r) := by
  obtain ⟨hRh0, -, ht0, ht1, htR0, -, hbud, hbudt, hslack⟩ :=
    sgp06_parameters_SGP5 hΓ hΓ1 hsg hsgΓ hC hsgC heΓ hrlo hrhi
  have hxh : c⁻¹ • x ∈ (fun z => c⁻¹ • z) '' T := ⟨x, hx, rfl⟩
  have hsub : (1 - Γ ^ 2 / 2) * (r / c / Γ) ≤ r / c / Γ := by
    have := hRh0.le
    nlinarith
  have hcov : ∀ R', 0 < R' → R' ≤ r / c / Γ →
      hausdorffDist ((fun z => c⁻¹ • z) '' T ∩ closedBall (c⁻¹ • x) R')
        ((fun v => c⁻¹ • x + fderiv ℝ Φ (P (c⁻¹ • x)) v) '' (univ : Set E) ∩
          closedBall (c⁻¹ • x) R') ≤ 3 * (2 * e + C * R' ^ 2 / 2) := by
    intro R' hR' hR'le
    have hball : closedBall (P (c⁻¹ • x)) R' ⊆ closedBall (P (c⁻¹ • x)) (r / c / Γ) :=
      closedBall_subset_closedBall hR'le
    refine hausdorffDist_coordinate_graph_coverage_le (fun q => c⁻¹ • F q) η D Φ P hP hgraph
      ((fun z => c⁻¹ • z) '' T) (c⁻¹ • x) hxh hR' hC.le he0 (fun u hu => hreg u (hball hu))
      (fun u hu => hsecond u (hball hu)) (fun y hy => ?_) happrox (fun u hu => ?_)
    · exact hlocal y ⟨hy.1, closedBall_subset_closedBall (x := c⁻¹ • x) hR'le hy.2⟩
    · obtain ⟨q, hq, hηq, hT⟩ := hcover u (hball hu)
      exact ⟨q, hq, hηq, ⟨F q, hT, rfl⟩⟩
  have hR : c * (r / c / Γ) = r / Γ := by field_simp
  have hd : c * (Γ * (r / c)) = Γ * r := by field_simp
  exact hausdorffEDist_ball_le_of_scaled_coverage_SGP5 T ((fun z => c⁻¹ • z) '' T) x hx hc rfl
    (fderiv ℝ Φ (P (c⁻¹ • x))) hRh0 ht0 ht1
    (lt_of_le_of_lt (hcov _ hRh0 le_rfl) (by linarith))
    (lt_of_le_of_lt (hcov _ htR0 hsub) (by linarith)) (by linarith) hR hd

end Kernel

section Augmented

/-- The left inverse of the augmented model: `‖Pc(pr_int z)‖ ≤ ‖z‖` for a `1`-Lipschitz `Pc`. -/
theorem norm_comp_augIntProj_le_BAUGC {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E)
    (hPc : ∀ z, ‖Pc z‖ ≤ ‖z‖) (z : BlockSpace (fun _ : ι ⊕ κ => ℝ²)) :
    ‖Pc.comp augIntProjCLM_BAUGC z‖ ≤ ‖z‖ :=
  (hPc _).trans (norm_augIntProj_le_BAUGC z)

/-- `Pc ∘ pr_int` is a left inverse of the augmented model when `Pc` is one of `Ψ`. -/
theorem comp_augIntProj_augmentedModel_BAUGC {ι κ E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E)
    {Ψ : E → BlockSpace (fun _ : ι => ℝ²)} (hgraph : ∀ u, Pc (Ψ u) = u) (J : Set κ)
    (Φb : κ → E → ℝ × ℝ) (u : E) :
    (Pc.comp augIntProjCLM_BAUGC) (augmentedModel_BAUGC Ψ J Φb u) = u :=
  hgraph u

/-- **At most one listed component**: with `J ⊆ {b₀}`,
`Φ^∂ = ι_int ∘ Ψ + slot_{b₀} ∘ block_{b₀}`. -/
theorem augmentedModel_eq_two_BAUGC {ι κ E : Type*} [Finite κ] [DecidableEq κ]
    (Ψ : E → BlockSpace (fun _ : ι => ℝ²)) {J : Set κ} (Φb : κ → E → ℝ × ℝ) {b₀ : κ}
    (hJ : J ⊆ {b₀}) :
    augmentedModel_BAUGC Ψ J Φb = (fun u => augIntInclCLM_BAUGC (κ := κ) (Ψ u)) +
      fun u => augSlotCLM_BAUGC (ι := ι) b₀ (augmentedBlocks_BAUGC J Φb b₀ u) := by
  have := Fintype.ofFinite κ
  funext u
  rw [augmentedModel_eq_sum_BAUGC, Pi.add_apply,
    Finset.sum_eq_single b₀ (fun b _ hb => ?_) (fun h0 => absurd (Finset.mem_univ b₀) h0)]
  have hbJ : b ∉ J := fun h => hb (hJ h)
  rw [augmentedBlocks_of_notMem_BAUGC Φb hbJ, Pi.zero_apply, map_zero]

/-- `‖slot_b‖ ≤ 2` as an operator. -/
theorem norm_augSlotCLM_le_BAUGC {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (b : κ) :
    ‖augSlotCLM_BAUGC (ι := ι) b‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two fun B => norm_augSlotCLM_apply_le_BAUGC b B

/-- `‖ι_int‖ ≤ 1` as an operator. -/
theorem norm_augIntInclCLM_le_BAUGC {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ‖augIntInclCLM_BAUGC (ι := ι) (κ := κ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [norm_augIntIncl_BAUGC, one_mul]

/-- **The `C²` bound of the augmented model** (one listed component at most):
`‖D²Φ^∂(u)‖ ≤ ‖D²Ψ(u)‖ + 2‖D²block_{b₀}(u)‖`. -/
theorem norm_iteratedFDeriv_two_augmentedModel_le_BAUGC {ι κ E : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E → BlockSpace (fun _ : ι => ℝ²)} {J : Set κ} {Φb : κ → E → ℝ × ℝ} {b₀ : κ}
    (hJ : J ⊆ {b₀}) {u : E} (hΨ : ContDiffAt ℝ 2 Ψ u)
    (hb : ContDiffAt ℝ 2 (augmentedBlocks_BAUGC J Φb b₀) u) :
    ‖iteratedFDeriv ℝ 2 (augmentedModel_BAUGC Ψ J Φb) u‖ ≤
      ‖iteratedFDeriv ℝ 2 Ψ u‖ + 2 * ‖iteratedFDeriv ℝ 2 (augmentedBlocks_BAUGC J Φb b₀) u‖ := by
  classical
  rw [augmentedModel_eq_two_BAUGC Ψ Φb hJ]
  have h1 : ContDiffAt ℝ 2 (fun u => augIntInclCLM_BAUGC (κ := κ) (Ψ u)) u :=
    (augIntInclCLM_BAUGC (ι := ι) (κ := κ)).contDiff.contDiffAt.comp u hΨ
  have h2 : ContDiffAt ℝ 2 (fun u => augSlotCLM_BAUGC (ι := ι) b₀
      (augmentedBlocks_BAUGC J Φb b₀ u)) u :=
    (augSlotCLM_BAUGC (ι := ι) b₀).contDiff.contDiffAt.comp u hb
  rw [iteratedFDeriv_add_apply h1 h2]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ((augIntInclCLM_BAUGC (ι := ι) (κ := κ)).norm_iteratedFDeriv_comp_left hΨ le_rfl).trans ?_
    calc ‖augIntInclCLM_BAUGC (ι := ι) (κ := κ)‖ * ‖iteratedFDeriv ℝ 2 Ψ u‖ ≤
          1 * ‖iteratedFDeriv ℝ 2 Ψ u‖ :=
        mul_le_mul_of_nonneg_right norm_augIntInclCLM_le_BAUGC (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ 2 Ψ u‖ := one_mul _
  · exact ((augSlotCLM_BAUGC (ι := ι) b₀).norm_iteratedFDeriv_comp_left hb le_rfl).trans
      (mul_le_mul_of_nonneg_right (norm_augSlotCLM_le_BAUGC b₀) (norm_nonneg _))

/-- **The approximation error of the augmented model** (one listed component at most): if the
unlisted boundary slots of `y` vanish, the interior error is `≤ e₁` and the listed-slot error is
`≤ e₂`, then `‖y − Φ^∂(u)‖ ≤ e₁ + e₂`. -/
theorem norm_sub_augmentedModel_le_BAUGC {ι κ E : Type*} [Fintype ι] [Fintype κ]
    (y : BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (Ψ : E → BlockSpace (fun _ : ι => ℝ²)) {J : Set κ} (Φb : κ → E → ℝ × ℝ) {b₀ : κ}
    (hJ : J ⊆ {b₀}) (u : E) (hzero : ∀ b, b ≠ b₀ → y (Sum.inr b) = 0) {e₁ e₂ : ℝ}
    (hint : ‖augIntProjCLM_BAUGC y - Ψ u‖ ≤ e₁)
    (hslot : ‖y (Sum.inr b₀) - planeBlockEmbed_BAUGA (augmentedBlocks_BAUGC J Φb b₀ u)‖ ≤ e₂) :
    ‖y - augmentedModel_BAUGC Ψ J Φb u‖ ≤ e₁ + e₂ := by
  classical
  refine (norm_le_proj_add_slot_BAUGC _ b₀ fun b hb => ?_).trans (add_le_add ?_ ?_)
  · rw [PiLp.sub_apply, hzero b hb, augmentedModel_apply_inr_BAUGC,
      augmentedBlocks_of_notMem_BAUGC Φb (fun h => hb (hJ h)), Pi.zero_apply, map_zero, sub_zero]
  · rw [map_sub, augIntProj_augmentedModel_BAUGC]
    exact hint
  · rw [PiLp.sub_apply, augmentedModel_apply_inr_BAUGC]
    exact hslot

/-- **(CS) for the augmented model** (draft 61 (P) with (BM), D61-5): FC27's open-ball cloud test
for the augmented model `Φ^∂ = augmentedModel_BAUGC Ψ J Φb` (`J ⊆ {b₀}`) with the left inverse
`Pc ∘ pr_int`, from the INTERIOR inputs (graph inverse `Pc` of `Ψ`, `C²` bound `C_int`,
localization in the interior coordinate, interior approximation `e_int`, coverage) and the BOUNDARY
inputs (unlisted slots vanish on the source set, listed-slot error `e_b`, `C²` bound `C_b` of the
listed block): the test holds at `(Γ, Σ)` with `C = C_int + 2C_b`, `e = e_int + e_b`. -/
theorem augmented_cloud_test_BAUGC {M ι κ E : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] (F : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²))
    (η : M → E) (D : Set M) (Ψ : E → BlockSpace (fun _ : ι => ℝ²)) {J : Set κ}
    (Φb : κ → E → ℝ × ℝ) {b₀ : κ} (hJ : J ⊆ {b₀}) (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E)
    (hPc : ∀ z, ‖Pc z‖ ≤ ‖z‖) (hgraph : ∀ u, Pc (Ψ u) = u)
    (T : Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) {x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (hx : x ∈ T) {c r Γ sg Cint Cb eint eb : ℝ} (hc : 0 < c) (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 200) (hCint : 0 < Cint) (hCb : 0 ≤ Cb)
    (hsgC : sg < Γ ^ 3 / (100 * (Cint + 2 * Cb))) (he0 : 0 ≤ eint + eb)
    (heΓ : eint + eb < Γ * sg / 100) (hrlo : 3 * sg / 4 ≤ r / c) (hrhi : r / c ≤ 5 * sg / 4)
    (hΨreg : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ContDiffAt ℝ 2 Ψ u)
    (hbreg : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ContDiffAt ℝ 2 (augmentedBlocks_BAUGC J Φb b₀) u)
    (hΨ2 : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ‖iteratedFDeriv ℝ 2 Ψ u‖ ≤ Cint)
    (hb2 : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ‖iteratedFDeriv ℝ 2 (augmentedBlocks_BAUGC J Φb b₀) u‖ ≤ Cb)
    (hlocal : ∀ y ∈ (fun z => c⁻¹ • z) '' T ∩ closedBall (c⁻¹ • x) (r / c / Γ),
      ∃ q ∈ D, c⁻¹ • F q = y ∧ Pc (augIntProjCLM_BAUGC y) = η q)
    (hzero : ∀ q ∈ D, ∀ b, b ≠ b₀ → F q (Sum.inr b) = 0)
    (hint : ∀ q ∈ D, ‖augIntProjCLM_BAUGC (c⁻¹ • F q) - Ψ (η q)‖ ≤ eint)
    (hslot : ∀ q ∈ D, ‖(c⁻¹ • F q) (Sum.inr b₀) -
      planeBlockEmbed_BAUGA (augmentedBlocks_BAUGC J Φb b₀ (η q))‖ ≤ eb)
    (hcover : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (c⁻¹ • x))) (r / c / Γ),
      ∃ q ∈ D, η q = u ∧ F q ∈ T) :
    hausdorffEDist (T ∩ ball x (r / Γ))
      ((AffineSubspace.mk' x (fderiv ℝ (augmentedModel_BAUGC Ψ J Φb)
          (Pc (augIntProjCLM_BAUGC (c⁻¹ • x)))).range :
          Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) ∩ ball x (r / Γ)) ≤
        ENNReal.ofReal (Γ * r) := by
  classical
  have hC : 0 < Cint + 2 * Cb := by linarith
  refine cloud_test_of_graph_coverage_BAUGC F η D (augmentedModel_BAUGC Ψ J Φb)
    (Pc.comp augIntProjCLM_BAUGC) (norm_comp_augIntProj_le_BAUGC Pc hPc)
    (comp_augIntProj_augmentedModel_BAUGC Pc hgraph J Φb) T hx hc hΓ hΓ1 hsg hsgΓ hC hsgC he0 heΓ
    hrlo hrhi (fun u hu => ?_) (fun u hu => ?_) hlocal (fun q hq => ?_) hcover
  · rw [augmentedModel_eq_two_BAUGC Ψ Φb hJ]
    exact ((augIntInclCLM_BAUGC (ι := ι) (κ := κ)).contDiff.contDiffAt.comp u (hΨreg u hu)).add
      ((augSlotCLM_BAUGC (ι := ι) b₀).contDiff.contDiffAt.comp u (hbreg u hu))
  · refine (norm_iteratedFDeriv_two_augmentedModel_le_BAUGC hJ (hΨreg u hu) (hbreg u hu)).trans ?_
    have := hΨ2 u hu
    have := hb2 u hu
    linarith
  · rw [dist_eq_norm]
    refine norm_sub_augmentedModel_le_BAUGC (c⁻¹ • F q) Ψ Φb hJ (η q) (fun b hb => ?_) (hint q hq)
      (hslot q hq)
    rw [PiLp.smul_apply, hzero q hq b hb, smul_zero]

/-- The plane encoding is `2`-Lipschitz: `‖planeEmbed B − planeEmbed B'‖ ≤ 2‖B − B'‖`. -/
theorem norm_planeBlockEmbed_sub_le_BAUGC (B B' : ℝ × ℝ) :
    ‖planeBlockEmbed_BAUGA B - planeBlockEmbed_BAUGA B'‖ ≤ 2 * ‖B - B'‖ := by
  rw [← map_sub]
  exact norm_planeBlockEmbed_le_BAUGC _

/-- **The listed-slot error from (BA)** (BCG-8b's value error): if the normalized height of the
source point is `ϑ`-close to the row, the listed slot of `R⁻¹ F_∂` differs from the plane encoding
of the (BM) block by at most `2P_*ϑ` (D61-5: `1/R` never enters). -/
theorem bm_slot_error_BAUGC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) (cb : ℝ) {R : ℝ} (hR : 0 < R) (Ar : E →L[ℝ] ℝ)
    (z₀ z : E) {t ϑ : ℝ} (hval : |(t - cb) / R - Ar (z - z₀)| < ϑ) :
    ‖planeBlockEmbed_BAUGA (R⁻¹ • boundaryBlock t) -
        planeBlockEmbed_BAUGA (boundaryModel_BCG8b cb R Ar z₀ z)‖ ≤ 2 * (P * ϑ) :=
  (norm_planeBlockEmbed_sub_le_BAUGC _ _).trans (mul_le_mul_of_nonneg_left
    (boundaryModel_value_error_BCG8b hP cb hR Ar z₀ z hval) zero_le_two)

/-- **The (BM) `C²` bound in `iteratedFDeriv` form**: `‖D²Φ^∂_{a,b}‖ ≤ R P_*` (BCG03.b). -/
theorem bm_iteratedFDeriv_two_le_BAUGC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ} (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ P) (cb : ℝ) {R : ℝ} (hR : 0 < R)
    {Ar : E →L[ℝ] ℝ} (hA : ‖Ar‖ ≤ 1) (z₀ u : E) :
    ‖iteratedFDeriv ℝ 2 (boundaryModel_BCG8b cb R Ar z₀) u‖ ≤ R * P := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  exact norm_fderiv_fderiv_boundaryModel_le_BCG8b hP2 cb hR hA z₀ u

/-- The (BM) block is `C^∞`. -/
theorem contDiff_bm_BAUGC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (cb R : ℝ)
    (Ar : E →L[ℝ] ℝ) (z₀ : E) : ContDiff ℝ ∞ (boundaryModel_BCG8b cb R Ar z₀) := by
  have hh : ContDiff ℝ ∞ (boundaryModelHeight_BCG8b cb R Ar z₀) := by
    unfold boundaryModelHeight_BCG8b
    exact contDiff_const.add (contDiff_const.mul (Ar.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hB : ContDiff ℝ ∞ fun z => boundaryBlock (boundaryModelHeight_BCG8b cb R Ar z₀ z) :=
    contDiff_boundaryBlock.comp hh
  exact hB.const_smul R⁻¹

/-- **Consumer: (CS) for the augmented (BM) model at a reference with ONE listed component**
(`J = {b₀}`, reference scale `c = R = ρ(a)`, rows `‖A_b‖ ≤ 1`, BCG.0's `P_*`): the interior inputs and
BCG02's (BA) value error `< ϑ` on the source set give the cloud test with `C = C_int + 2RP_*` and
`e = e_int + 2P_*ϑ` — the boundary block enters only through `P_*` and `ϑ`, never through `1/R`. -/
theorem augmented_bm_cloud_test_BAUGC {M ι κ E : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ P)
    (F : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (η : M → E) (D : Set M)
    (Ψ : E → BlockSpace (fun _ : ι => ℝ²)) (cb : κ → ℝ) {R : ℝ} (hR : 0 < R) (Ar : κ → E →L[ℝ] ℝ)
    (z₀ : E) {b₀ : κ} (hA : ‖Ar b₀‖ ≤ 1) (Pc : BlockSpace (fun _ : ι => ℝ²) →L[ℝ] E)
    (hPc : ∀ z, ‖Pc z‖ ≤ ‖z‖) (hgraph : ∀ u, Pc (Ψ u) = u)
    (T : Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) {x : BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (hx : x ∈ T) {r Γ sg Cint eint ϑ : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hCint : 0 < Cint) (hsgC : sg < Γ ^ 3 / (100 * (Cint + 2 * (R * P))))
    (heint : 0 ≤ eint) (hϑ : 0 ≤ ϑ) (heΓ : eint + 2 * (P * ϑ) < Γ * sg / 100)
    (hrlo : 3 * sg / 4 ≤ r / R) (hrhi : r / R ≤ 5 * sg / 4)
    (hΨreg : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (R⁻¹ • x))) (r / R / Γ),
      ContDiffAt ℝ 2 Ψ u)
    (hΨ2 : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (R⁻¹ • x))) (r / R / Γ),
      ‖iteratedFDeriv ℝ 2 Ψ u‖ ≤ Cint)
    (hlocal : ∀ y ∈ (fun z => R⁻¹ • z) '' T ∩ closedBall (R⁻¹ • x) (r / R / Γ),
      ∃ q ∈ D, R⁻¹ • F q = y ∧ Pc (augIntProjCLM_BAUGC y) = η q)
    (hzero : ∀ q ∈ D, ∀ b, b ≠ b₀ → F q (Sum.inr b) = 0)
    (hint : ∀ q ∈ D, ‖augIntProjCLM_BAUGC (R⁻¹ • F q) - Ψ (η q)‖ ≤ eint)
    (t : M → ℝ) (hslotF : ∀ q ∈ D, F q (Sum.inr b₀) = planeBlockEmbed_BAUGA (boundaryBlock (t q)))
    (hval : ∀ q ∈ D, |(t q - cb b₀) / R - Ar b₀ (η q - z₀)| < ϑ)
    (hcover : ∀ u ∈ closedBall (Pc (augIntProjCLM_BAUGC (R⁻¹ • x))) (r / R / Γ),
      ∃ q ∈ D, η q = u ∧ F q ∈ T) :
    hausdorffEDist (T ∩ ball x (r / Γ))
      ((AffineSubspace.mk' x (fderiv ℝ (augmentedModel_BAUGC Ψ {b₀} (bmBlocks_BAUGC cb R Ar z₀))
          (Pc (augIntProjCLM_BAUGC (R⁻¹ • x)))).range :
          Set (BlockSpace (fun _ : ι ⊕ κ => ℝ²))) ∩ ball x (r / Γ)) ≤
        ENNReal.ofReal (Γ * r) := by
  classical
  have hmem : b₀ ∈ ({b₀} : Set κ) := rfl
  have hblk : augmentedBlocks_BAUGC {b₀} (bmBlocks_BAUGC cb R Ar z₀) b₀ =
      boundaryModel_BCG8b (cb b₀) R (Ar b₀) z₀ :=
    augmentedBlocks_of_mem_BAUGC _ hmem
  have hRP : 0 ≤ R * P := mul_nonneg hR.le (nonneg_of_boundaryBlock_bound_BCG8b hP)
  refine augmented_cloud_test_BAUGC F η D Ψ (bmBlocks_BAUGC cb R Ar z₀) subset_rfl Pc hPc hgraph T
    hx hR hΓ hΓ1 hsg hsgΓ hCint hRP hsgC (by have := nonneg_of_boundaryBlock_bound_BCG8b hP; positivity)
    heΓ hrlo hrhi hΨreg (fun u _ => ?_) hΨ2 (fun u _ => ?_) hlocal hzero hint (fun q hq => ?_) hcover
  · rw [hblk]
    exact (contDiff_bm_BAUGC _ _ _ _).contDiffAt.of_le (by norm_num)
  · rw [hblk]
    exact bm_iteratedFDeriv_two_le_BAUGC hP2 _ hR hA z₀ u
  · rw [hblk, PiLp.smul_apply, hslotF q hq, ← map_smul]
    exact bm_slot_error_BAUGC hP (cb b₀) hR (Ar b₀) z₀ (η q) (hval q hq)

end Augmented

end DifferentialGeometry.Geometry.Collapse
