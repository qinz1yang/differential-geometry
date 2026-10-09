import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightApproximation
import DifferentialGeometry.Geometry.Connection.Hessian.Scalar

/-!
# BCP01: the analytic clauses of the smoothed collar height, in `g`-norms

Let `e : CuspEmbedding W g K δ X`, `ζ = z ∘ e⁻¹` the collar height and `η` a smooth function
satisfying the `C²` contract of row E8 at a point `p` of the band `2 ≤ z ≤ 98`
(`CuspEmbedding.exists_smooth_height_C2`, and the same `η` of row E6): `|η − ζ| < ε`,
`|d(η ∘ e)(v) − dz(v)| ≤ ε |v|_H`, `|Hess_g(η − ζ)(de v, de w)| ≤ ε |v|_H |w|_H`.
`Hess_g` is the EXISTING Hessian `(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian
(LeviCivita g)`. Every derivative clause below is stated with `g`-norms (`|u|_g = √g(u,u)`,
dual and bilinear norms written out); the operator norm of the model is never used (G-II erratum).

* `CuspEmbedding.sqrt_cusp_inner_le`: `|v|_H ≤ (1 − δ)^{-1/2} |de v|_g`.
* `CuspEmbedding.abs_le_of_abs_mfderiv_le`, `CuspEmbedding.abs_hessian_le_of_abs_mfderiv_le`:
  `H`-bounds on `de`-images are `g`-bounds on all of `T_{e p} W` (`de` is invertible).
* `CuspEmbedding.mfderiv_comp_sub_height`: `d(η ∘ e)(v) − dz(v) = d(η − ζ)(de v)`.
* `CuspEmbedding.bcp01a_of_contract` (BCP01.a in `g`-norms): `|d(η − ζ)(u)| ≤ ε' |u|_g`,
  `|Hess_g(η − ζ)(u, w)| ≤ ε' |u|_g |w|_g`, `ε' = ε (1 − δ)^{-1}`.
* `CuspEmbedding.bcp01b_differential_of_contract` (BCP01.b, first and third clauses):
  for `δ ≤ 1/1000`, `ε ≤ 1/1000`: `|dη(u)| ≤ (1 + 1/200) |u|_g`, some `u` has
  `(199/200)|u|_g ≤ dη(u)` (so `.99 < ‖dη‖_g < 1.01`), and `.99 < ∂_z η < 1.01`.
* `CuspEmbedding.hessian_add_height`: `Hess_g η = Hess_g(η − ζ) + Hess_g ζ` at positive heights.
* `CuspEmbedding.bcp01b_hessian_of_contract` (BCP01.b, second clause, from any `H`-bound
  `|Hess_g ζ(de a, de b)| ≤ c |a|_H |b|_H`): `|Hess_g η(u, w)| ≤ (ε + c)(1 − δ)^{-1} |u|_g |w|_g`;
  with `c ≤ 1`: `≤ (3/2) |u|_g |w|_g < 2`. The bound on `Hess_g ζ` is the order-one metric-error
  estimate Z-H (lane FT-C); this file takes it as the explicit inequality, no new Prop.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- `|v|_H ≤ (1 − δ)^{-1/2} |de v|_g`. -/
theorem CuspEmbedding.sqrt_cusp_inner_le (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (v : TangentSpace halfCollarModel p) :
    Real.sqrt (e.cusp.metric.inner p v v) ≤
      (Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v)) := by
  have h1 := e.one_sub_mul_le_pullback_inner hp v
  have hs : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by linarith)
  rw [le_inv_mul_iff₀ hs, ← Real.sqrt_mul (by linarith)]
  exact Real.sqrt_le_sqrt h1

/-- Every tangent vector at `e p` is `de v` for some `v`. -/
theorem CuspEmbedding.exists_mfderiv_eq (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (u : TangentSpace W.model (e.toFun p)) :
    ∃ v : TangentSpace halfCollarModel p, mfderiv halfCollarModel W.model e.toFun p v = u := by
  obtain ⟨M, hM⟩ := e.isInvertible_mfderiv hp
  refine ⟨M.symm u, ?_⟩
  rw [← hM]
  exact M.apply_symm_apply u

/-- An `H`-bound for a covector on `de`-images is a `g`-bound on all of `T_{e p} W`. -/
theorem CuspEmbedding.abs_le_of_abs_mfderiv_le (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (L : TangentSpace W.model (e.toFun p) →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ v : TangentSpace halfCollarModel p,
      |L (mfderiv halfCollarModel W.model e.toFun p v)| ≤
        c * Real.sqrt (e.cusp.metric.inner p v v))
    (u : TangentSpace W.model (e.toFun p)) :
    |L u| ≤ c * (Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) := by
  obtain ⟨v, rfl⟩ := e.exists_mfderiv_eq hp u
  calc _ ≤ c * Real.sqrt (e.cusp.metric.inner p v v) := hL v
    _ ≤ c * ((Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p v))) :=
        mul_le_mul_of_nonneg_left (e.sqrt_cusp_inner_le hδ hp v) hc
    _ = _ := by ring

/-- An `H`-bound for a Hessian on `de`-images is a `g`-bound on all of `T_{e p} W`. -/
theorem CuspEmbedding.abs_hessian_le_of_abs_mfderiv_le (e : CuspEmbedding W g K δ X)
    (hδ : δ < 1) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (f : W.Carrier → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hf : ∀ v w : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) f (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p w)| ≤
        c * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w))
    (u w : TangentSpace W.model (e.toFun p)) :
    |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) f (e.toFun p)
        u w| ≤
      c * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) *
        Real.sqrt (g.inner (e.toFun p) w w) := by
  obtain ⟨v, rfl⟩ := e.exists_mfderiv_eq hp u
  obtain ⟨v', rfl⟩ := e.exists_mfderiv_eq hp w
  have hs : Real.sqrt (1 - δ) * Real.sqrt (1 - δ) = 1 - δ := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by linarith)
  calc _ ≤ c * Real.sqrt (e.cusp.metric.inner p v v) *
        Real.sqrt (e.cusp.metric.inner p v' v') := hf v v'
    _ ≤ c * ((Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p v))) *
        ((Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v')
          (mfderiv halfCollarModel W.model e.toFun p v'))) := by
        gcongr
        · exact e.sqrt_cusp_inner_le hδ hp v
        · exact e.sqrt_cusp_inner_le hδ hp v'
    _ = _ := by
        have hinv : (1 - δ)⁻¹ = (Real.sqrt (1 - δ))⁻¹ * (Real.sqrt (1 - δ))⁻¹ := by
          rw [← mul_inv, hs]
        rw [hinv]
        ring

/-- `d(η ∘ e)(v) − dz(v) = d(η − ζ)(de v)` for `η` differentiable at `e p`. -/
theorem CuspEmbedding.mfderiv_comp_sub_height (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ}
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p))
    (v : TangentSpace halfCollarModel p) :
    (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) - (show ℝ from v.2 0) =
      mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p v) := by
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
  have hζd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) :=
    (e.contMDiffOn_height_invFunOn.contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp))).mdifferentiableAt
        one_ne_zero
  have hchain : mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v =
      mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v) := by
    rw [mfderiv_comp p hηd hed]
    rfl
  have hz := e.mfderiv_height_invFunOn_mfderiv hp v
  rw [mvfderiv_fun_sub hηd hζd, sub_apply]
  change _ = (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) η (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v)) -
    (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) ζ (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v))
  rw [hz, ← hchain]

/-- **BCP01.a in `g`-norms.** The `C¹` and Hessian clauses of the E8 contract at `p`, as bounds
for the `g`-dual and `g`-bilinear norms on all of `T_{e p} W`, with `ε (1 − δ)^{-1}`. -/
theorem CuspEmbedding.bcp01a_of_contract (e : CuspEmbedding W g K δ X) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε : ℝ} (hε : 0 ≤ ε)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hC1 : ∀ v : TangentSpace halfCollarModel p,
      |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
          (show ℝ from v.2 0)| ≤ ε * Real.sqrt (e.cusp.metric.inner p v v))
    (hC2 : ∀ v w : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p w)| ≤
        ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w)) :
    (∀ u : TangentSpace W.model (e.toFun p),
      |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u| ≤
        ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u)) ∧
    ∀ u w : TangentSpace W.model (e.toFun p),
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u w| ≤
        ε * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) *
          Real.sqrt (g.inner (e.toFun p) w w) := by
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p) := (hη _).mdifferentiableAt (by simp)
  refine ⟨fun u => ?_, e.abs_hessian_le_of_abs_mfderiv_le hδ hp _ hε hC2⟩
  have h := e.abs_le_of_abs_mfderiv_le hδ hp
    (mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)) hε
    (fun v => by rw [← e.mfderiv_comp_sub_height hp hηd v]; exact hC1 v) u
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hε)
    (Real.sqrt_nonneg _))
  -- `(1 − δ)^{-1/2} ≤ (1 − δ)^{-1}` for `0 ≤ δ < 1`
  have hs0 : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - δ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hs : Real.sqrt (1 - δ) * Real.sqrt (1 - δ) = 1 - δ := Real.mul_self_sqrt (by linarith)
  have hinv : (1 - δ)⁻¹ = (Real.sqrt (1 - δ))⁻¹ * (Real.sqrt (1 - δ))⁻¹ := by
    rw [← mul_inv, hs]
  rw [hinv]
  exact le_mul_of_one_le_left (inv_nonneg.mpr hs0.le) (one_le_inv₀ hs0 |>.mpr hs1)


/-- The `C¹` clause of the E8 contract as a `g`-dual bound for `d(η − ζ)`. -/
theorem CuspEmbedding.abs_mvfderiv_sub_height_le (e : CuspEmbedding W g K δ X) (hδ : δ < 1)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε : ℝ} (hε : 0 ≤ ε)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hC1 : ∀ v : TangentSpace halfCollarModel p,
      |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
          (show ℝ from v.2 0)| ≤ ε * Real.sqrt (e.cusp.metric.inner p v v))
    (u : TangentSpace W.model (e.toFun p)) :
    |mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u| ≤
      ε * (Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) := by
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p) := (hη _).mdifferentiableAt (by simp)
  exact e.abs_le_of_abs_mfderiv_le hδ hp
    (mvfderiv W.model (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)) hε
    (fun v => by rw [← e.mfderiv_comp_sub_height hp hηd v]; exact hC1 v) u

/-- The unit vertical vector of the model, `∂_z`. -/
theorem cusp_inner_unitVertical (H : HyperbolicCusp) (p : CuspHalfSpace) :
    H.metric.inner p (((0, 0), EuclideanSpace.single 0 1) : TangentSpace halfCollarModel p)
      (((0, 0), EuclideanSpace.single 0 1) : TangentSpace halfCollarModel p) = 1 := by
  have h := cusp_inner_vertical H p
    (((0, 0), EuclideanSpace.single 0 1) : TangentSpace halfCollarModel p) rfl
  rw [h]
  simp

/-- **BCP01.b, first and third clauses.** For `δ ≤ 1/1000` and `ε ≤ 1/1000`, the E8
`C¹` contract at `p` gives `.99 < ‖dη‖_g < 1.01` (in `g`-dual form: an upper bound by
`(1 + 1/200)|u|_g` for all `u`, and some `u` with `(199/200)|u|_g ≤ dη(u)`) and
`.99 < ∂_z η < 1.01`. -/
theorem CuspEmbedding.bcp01b_differential_of_contract (e : CuspEmbedding W g K δ X)
    (hδ : δ ≤ 1 / 1000) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hC1 : ∀ v : TangentSpace halfCollarModel p,
      |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p v) -
          (show ℝ from v.2 0)| ≤ ε * Real.sqrt (e.cusp.metric.inner p v v)) :
    (∀ u : TangentSpace W.model (e.toFun p),
      |mvfderiv W.model η (e.toFun p) u| ≤ (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u)) ∧
    (∃ u : TangentSpace W.model (e.toFun p), 0 < mvfderiv W.model η (e.toFun p) u ∧
      199 / 200 * Real.sqrt (g.inner (e.toFun p) u u) ≤ mvfderiv W.model η (e.toFun p) u) ∧
    99 / 100 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
        ((0, 0), EuclideanSpace.single 0 1)) ∧
      (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
        ((0, 0), EuclideanSpace.single 0 1)) < 101 / 100 := by
  set ζ : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hζ
  have hδ1 : δ < 1 := by linarith
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p) := (hη _).mdifferentiableAt (by simp)
  have hζd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ζ (e.toFun p) :=
    (e.contMDiffOn_height_invFunOn.contMDiffAt
      (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp))).mdifferentiableAt
        one_ne_zero
  have hsplit : ∀ u : TangentSpace W.model (e.toFun p), mvfderiv W.model η (e.toFun p) u =
      mvfderiv W.model (fun y => η y - ζ y) (e.toFun p) u + mvfderiv W.model ζ (e.toFun p) u := by
    intro u
    rw [mvfderiv_fun_sub hηd hζd, sub_apply]
    ring
  have hs : (0.9994 : ℝ) ≤ Real.sqrt (1 - δ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < Real.sqrt (1 - δ) := lt_of_lt_of_le (by norm_num) hs
  have hsinv : (Real.sqrt (1 - δ))⁻¹ ≤ 1 / 0.9994 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hs
  set dz : TangentSpace halfCollarModel p := ((0, 0), EuclideanSpace.single 0 1) with hdz
  have hH1 : e.cusp.metric.inner p dz dz = 1 := cusp_inner_unitVertical e.cusp p
  have hdz2 : dz.2 0 = 1 := by simp [hdz]
  have hvert := hC1 dz
  rw [hH1, Real.sqrt_one, mul_one, hdz2] at hvert
  dsimp only at hvert
  have hv := abs_le.mp hvert
  have h3 : 99 / 100 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p dz) ∧
      (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p dz) < 101 / 100 := by
    have key : ∀ d : ℝ, |d - 1| ≤ ε → 99 / 100 < d ∧ d < 101 / 100 := fun d hd => by
      constructor <;> linarith [abs_le.mp hd]
    exact key _ hvert
  refine ⟨fun u => ?_, ?_, h3⟩
  · have h1 := e.abs_mvfderiv_sub_height_le hδ1 hη hε0 hp hC1 u
    have h2 := e.abs_mfderiv_height_invFunOn_le hδ1 hp u
    change |mvfderiv W.model ζ (e.toFun p) u| ≤ _ at h2
    have hg := Real.sqrt_nonneg (g.inner (e.toFun p) u u)
    rw [hsplit]
    calc _ ≤ |mvfderiv W.model (fun y => η y - ζ y) (e.toFun p) u| +
          |mvfderiv W.model ζ (e.toFun p) u| := abs_add_le _ _
      _ ≤ (ε * (Real.sqrt (1 - δ))⁻¹ + (Real.sqrt (1 - δ))⁻¹) *
          Real.sqrt (g.inner (e.toFun p) u u) := by nlinarith
      _ ≤ (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u) := by
          refine mul_le_mul_of_nonneg_right ?_ hg
          have hi0 : 0 ≤ (Real.sqrt (1 - δ))⁻¹ := inv_nonneg.mpr hs0.le
          nlinarith
  · set u₀ := mfderiv halfCollarModel W.model e.toFun p dz with hu₀
    have hζu : mvfderiv W.model ζ (e.toFun p) u₀ = 1 := by
      have h := e.mfderiv_height_invFunOn_mfderiv hp dz
      rw [hdz2] at h
      exact h
    have hsub := e.mfderiv_comp_sub_height hp hηd dz
    rw [hdz2] at hsub
    change _ = mvfderiv W.model (fun y => η y - ζ y) (e.toFun p) u₀ at hsub
    have hηu : mvfderiv W.model η (e.toFun p) u₀ ≥ 1 - ε := by
      rw [hsplit, hζu, ← hsub]
      have key : ∀ d : ℝ, |d - 1| ≤ ε → d - 1 + 1 ≥ 1 - ε := fun d hd => by
        linarith [abs_le.mp hd]
      exact key _ hvert
    have hgu : g.inner (e.toFun p) u₀ u₀ ≤ 1 + δ := by
      have h := e.pullback_inner_vertical_le hp dz rfl
      rwa [hdz2, one_pow, mul_one] at h
    have hsq : Real.sqrt (g.inner (e.toFun p) u₀ u₀) ≤ 1.0005 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith
    refine ⟨u₀, by linarith, ?_⟩
    nlinarith


/-- The differential of a `C²` function is a differentiable section of the cotangent bundle. -/
theorem mdiffAtCotangent_mvfderiv_of_contMDiffAt {f : W.Carrier → ℝ} {x : W.Carrier}
    (hf : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 f x) : MDiffAtCotangent (mvfderiv W.model f) x := by
  have hf_cmd1 : ContMDiffAt W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) 1
      (inTangentCoordinates W.model 𝓘(ℝ, ℝ) id f (mfderiv W.model 𝓘(ℝ, ℝ) f) x) x := by
    have := hf.mfderiv_const (m := 1) (le_refl _)
    simpa using this
  change MDifferentiableAt W.model (W.model.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))
    (fun b : W.Carrier => TotalSpace.mk' (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      (E := fun x : W.Carrier => TangentSpace W.model x →L[ℝ] ℝ) b
      (mvfderiv W.model f b)) x
  rw [mdifferentiableAt_hom_bundle]
  refine ⟨mdifferentiableAt_id, ?_⟩
  refine (hf_cmd1.mdifferentiableAt (by norm_num)).congr_of_eventuallyEq ?_
  filter_upwards with y
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    TangentBundle.continuousLinearMapAt_model_space, mvfderiv, id_eq]
  rfl

/-- **Additivity of the Hessian** for `C²` functions on a carrier (boundary allowed). -/
theorem hessian_add_apply_of_contMDiffAt {f₁ f₂ : W.Carrier → ℝ} {x : W.Carrier}
    (h₁ : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 f₁ x) (h₂ : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 f₂ x)
    (u w : TangentSpace W.model x) :
    (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
        (fun y => f₁ y + f₂ y) x u w =
      (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) f₁ x u w +
        (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) f₂ x u w := by
  have h₁₂ : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 (fun y => f₁ y + f₂ y) x := h₁.add h₂
  rw [CovariantDerivative.hessian_trivial_eq_cotangentCov _ h₁₂,
    CovariantDerivative.hessian_trivial_eq_cotangentCov _ h₁,
    CovariantDerivative.hessian_trivial_eq_cotangentCov _ h₂]
  have hθ₁ := mdiffAtCotangent_mvfderiv_of_contMDiffAt h₁
  have hθ₂ := mdiffAtCotangent_mvfderiv_of_contMDiffAt h₂
  have hθ₁₂ := mdiffAtCotangent_mvfderiv_of_contMDiffAt h₁₂
  have hev : ∀ᶠ y in 𝓝 x, mvfderiv W.model (fun y => f₁ y + f₂ y) y =
      (mvfderiv W.model f₁ + mvfderiv W.model f₂) y := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 h₁,
      (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 h₂] with y hy₁ hy₂
    exact mvfderiv_fun_add (hy₁.mdifferentiableAt (by simp)) (hy₂.mdifferentiableAt (by simp))
  have htot : (fun y => (⟨y, mvfderiv W.model (fun y => f₁ y + f₂ y) y⟩ :
      TotalSpace (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
        (fun y => TangentSpace W.model y →L[ℝ] ℝ))) =ᶠ[𝓝 x]
      (fun y => (⟨y, (mvfderiv W.model f₁ + mvfderiv W.model f₂) y⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
          (fun y => TangentSpace W.model y →L[ℝ] ℝ))) := by
    filter_upwards [hev] with y hy
    rw [hy]
  have hθs : MDiffAtCotangent (mvfderiv W.model f₁ + mvfderiv W.model f₂) x :=
    hθ₁₂.congr_of_eventuallyEq htot.symm
  have hcongr := (cotangentCov (LeviCivita g)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hθ₁₂ hθs Filter.univ_mem hev
  have hadd := (cotangentCov (LeviCivita g)).isCovariantDerivativeOnUniv.add hθ₁ hθ₂
  change (cotangentCov (LeviCivita g)).toFun (mvfderiv W.model (fun y => f₁ y + f₂ y)) x u w = _
  rw [hcongr, hadd]
  rfl

/-- `Hess_g η = Hess_g(η − ζ) + Hess_g ζ` at a point of positive height (`K ≥ 1`). -/
theorem CuspEmbedding.hessian_eq_add_height (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) (u w : TangentSpace W.model (e.toFun p)) :
    (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η (e.toFun p) u w =
      (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u w +
        (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u w := by
  have hζ : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
      (e.toFun p) :=
    (e.contMDiffAt_height_of_pos hp hz).of_le (by exact_mod_cast Nat.succ_le_succ hK)
  have hη2 : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 η (e.toFun p) :=
    (hη _).of_le (by simp)
  have h := hessian_add_apply_of_contMDiffAt (g := g) (hη2.sub hζ) hζ u w
  have hfun : (fun y => (η y - (invFunOn e.toFun cuspDomain y).2.val 0) +
      (invFunOn e.toFun cuspDomain y).2.val 0) = η := funext fun y => by ring
  rw [hfun] at h
  exact h

/-- **BCP01.b, second clause.** If the collar height has the `H`-bound
`|Hess_g ζ(de a, de b)| ≤ c |a|_H |b|_H` at `p` (the order-one metric-error estimate, lane FT-C),
the E8 Hessian contract gives `|Hess_g η(u, w)| ≤ (ε + c)(1 − δ)^{-1} |u|_g |w|_g` on all of
`T_{e p} W`. -/
theorem CuspEmbedding.bcp01b_hessian_of_contract (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ : δ < 1) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0)
    (hC2 : ∀ v w : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p w)| ≤
        ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w))
    (hζ : ∀ a b : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p a)
          (mfderiv halfCollarModel W.model e.toFun p b)| ≤
        c * Real.sqrt (e.cusp.metric.inner p a a) * Real.sqrt (e.cusp.metric.inner p b b))
    (u w : TangentSpace W.model (e.toFun p)) :
    |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η (e.toFun p) u w| ≤
      (ε + c) * (1 - δ)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) *
        Real.sqrt (g.inner (e.toFun p) w w) := by
  refine e.abs_hessian_le_of_abs_mfderiv_le hδ hp η (add_nonneg hε hc) (fun v v' => ?_) u w
  rw [e.hessian_eq_add_height hK hη hp hz]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p v' v') +
        c * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p v' v') :=
        add_le_add (hC2 v v') (hζ v v')
    _ = _ := by ring

/-- BCP01.b, second clause with the blueprint's number: for `δ, ε ≤ 1/1000` and `c ≤ 1`,
`|Hess_g η(u, w)| ≤ (3/2) |u|_g |w|_g` (so `‖∇²η‖_g < 2`). -/
theorem CuspEmbedding.bcp01b_hessian_le_of_contract (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ : δ ≤ 1 / 1000) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε c : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) (hc0 : 0 ≤ c) (hc : c ≤ 1) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0)
    (hC2 : ∀ v w : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => η y - (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p v)
          (mfderiv halfCollarModel W.model e.toFun p w)| ≤
        ε * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w))
    (hζ : ∀ a b : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p)
          (mfderiv halfCollarModel W.model e.toFun p a)
          (mfderiv halfCollarModel W.model e.toFun p b)| ≤
        c * Real.sqrt (e.cusp.metric.inner p a a) * Real.sqrt (e.cusp.metric.inner p b b))
    (u w : TangentSpace W.model (e.toFun p)) :
    |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η (e.toFun p) u w| ≤
      3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w) := by
  refine (e.bcp01b_hessian_of_contract hK (by linarith) hη hε0 hc0 hp hz hC2 hζ u w).trans ?_
  have hu := Real.sqrt_nonneg (g.inner (e.toFun p) u u)
  have hw := Real.sqrt_nonneg (g.inner (e.toFun p) w w)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hu) hw
  have h1 : (1 - δ)⁻¹ ≤ 1000 / 999 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.mpr (by linarith)
  nlinarith

end DifferentialGeometry.Geometry.Collapse
