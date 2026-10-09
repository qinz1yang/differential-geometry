import DifferentialGeometry.Geometry.Fibration.ActualModelMarkerPlanes
import DifferentialGeometry.Geometry.Fibration.ActualInnerSections

/-!
# The data layer of the enhanced stage planes (draft 59 §1.2, (PDEF))

Blueprint `master207B.tex`, FC27 / CFS27 / GAF03–GAF04 / ZSP01 (B:1658, B:3626–3686, B:5871–5970,
B:6323–6395); external review 55 §2.5 and the binding draft 59 §1 (disposition D59-2): ONE plane
witness per stage, built from DATA — a radius preimage `q̂(x)`, a model preimage `q(x)` with its
reference label `a(x)`, the whole reference-model table `a ↦ Φ_a`, the pruning `a ↦ K_a` and the
reference coordinates `a ↦ η_a` — and the plane is a DEFINITION

  `L_x := im D(K_a ∘ Φ_a)(η_a(q(x)))`, `a = a(x)`.                                   (PDEF)

This module is generic (any block space, parameter space and label type); the three actual stages
are the structures of `ActualStagePlaneTypes.lean`.

* `StagePlaneData_PLN` (point data on the clouds `S ⊆ T`), `stagePlane_PLN`,
  `StagePlaneData_PLN.plane` (PDEF), `.rsel x₀` (total radius selection), `.radius x₀ Σ ρ`
  (`Σρ(q̂ x)`, the `r` slot of `Cfs15StageOutput`).
* `stagePlane_le_ker_marker_PLN`: a marker of `K_a ∘ Φ_a` that is locally constant at the model
  parameter annihilates the plane; `stagePlane_le_ker_proj_PLN`: a whole block of `K_a ∘ Φ_a` that
  vanishes near the parameter annihilates the plane (`L ≤ ker J_t`, `J_t` the block projection).
* `scaledCutoffBlock_arg_lt_of_close_PLN`: the plateau step of (FM*): a scaled cutoff block that is
  `e`-close to the full-marker block `(sη, s)` with `‖η‖ ≤ M` has its argument in the open
  `r`-ball as soon as `M + e/s ≤ r(1 − e/s)`.
* `ratio_of_common_point_PLN`, `ratio_ge_of_common_point_PLN`: the radius ratio of two intersecting
  CONSTANT-RADIUS charts (`R = ρ(centre)`): `(1 − ΛC_a)ρ(a) ≤ (1 + ΛC_t)ρ(t)`, hence
  `ρ(t) ≥ .99ρ(a)` when `ΛC_a, ΛC_t ≤ 1/200`. Scope: the non-zero marker charts (circle / edge /
  slim); it is NOT a statement about zero blocks (radius `R₀ ≠ ρ(centre)`) or the scale / `E'`
  blocks.
* `markerLine_input_PLN`, `zeroBlock_input_PLN`: the contributor hypothesis of GAF03
  (`large_cloud_affine_marker_locality`: `K.starProjection y = c ∧ P y ≤ Kᗮ`) for the marker line
  `K = (ker v)ᗮ` and for the whole block `K = (ker J)ᗮ`, `c = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

section Data

/-- **The data of one stage's plane witness** (draft 59 §1.2) over the cloud `S` and the enlarged
cloud `T`: radius preimage over `T`, model preimage and reference label over `S`, and the whole
reference-model table (models, pruning, coordinates). The point data live on the clouds (not on
all of `H`), so the structure is inhabited also when `X` or the label type is empty. -/
structure StagePlaneData_PLN (X H E ι : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S T : Set H) where
  /-- The radius preimage `q̂(x)` over the enlarged cloud (CFS15's radius `r(x) = Σρ(q̂ x)`). -/
  rpre : T → X
  /-- The model preimage `q(x)` over the cloud, chosen in the core of the reference `ref x`. -/
  pre : S → X
  /-- The reference label `a(x)` whose model defines the plane at `x`. -/
  ref : S → ι
  /-- The reference-model table `a ↦ Φ_a` (every reference, not only the used ones). -/
  model : ι → E → H
  /-- The pruning `a ↦ K_a` (CFS27; the identity where the producer does not prune). -/
  prune : ι → H →L[ℝ] H
  /-- The reference coordinates `a ↦ η_a`. -/
  coord : ι → X → E

variable {X H E ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {S T : Set H}

/-- The plane of the reference `a` at the point `q`: `im D(K_a ∘ Φ_a)(η_a q)`. -/
def stagePlane_PLN (model : ι → E → H) (prune : ι → H →L[ℝ] H) (coord : ι → X → E) (a : ι)
    (q : X) : Submodule ℝ H :=
  LinearMap.range (fderiv ℝ (prune a ∘ model a) (coord a q) : E →ₗ[ℝ] H)

open Classical in
/-- **(PDEF)**: the plane at `x ∈ S` is `im D(K_a ∘ Φ_a)(η_a(q(x)))` with `a = a(x)` (`⊥` off
the cloud). -/
def StagePlaneData_PLN.plane (A : StagePlaneData_PLN X H E ι S T) (x : H) : Submodule ℝ H :=
  if hx : x ∈ S then stagePlane_PLN A.model A.prune A.coord (A.ref ⟨x, hx⟩) (A.pre ⟨x, hx⟩)
  else ⊥

open Classical in
/-- The total radius selection: `q̂(x)` on the enlarged cloud, the given point `x₀` elsewhere (the
form `sel : H → X` taken by the CFS15 consumers; only its values on `T` matter). -/
def StagePlaneData_PLN.rsel (A : StagePlaneData_PLN X H E ι S T) (x₀ : X) (x : H) : X :=
  if hx : x ∈ T then A.rpre ⟨x, hx⟩ else x₀

/-- The CFS15 radius `r(x) = Σρ(q̂(x))` at the radius selection (the slot `r` of
`Cfs15StageOutput`, literally `fun x => Σ * ρ (sel x)` with `sel = A.rsel x₀`). -/
def StagePlaneData_PLN.radius (A : StagePlaneData_PLN X H E ι S T) (x₀ : X) (sg : ℝ)
    (ρ : X → ℝ) (x : H) : ℝ :=
  sg * ρ (A.rsel x₀ x)

/-- (PDEF) at a cloud point. -/
theorem StagePlaneData_PLN.plane_of_mem (A : StagePlaneData_PLN X H E ι S T) {x : H}
    (hx : x ∈ S) :
    A.plane x = LinearMap.range (fderiv ℝ (A.prune (A.ref ⟨x, hx⟩) ∘ A.model (A.ref ⟨x, hx⟩))
      (A.coord (A.ref ⟨x, hx⟩) (A.pre ⟨x, hx⟩)) : E →ₗ[ℝ] H) := by
  rw [StagePlaneData_PLN.plane, dite_eq_left hx]
  rfl

/-- The radius selection at a point of the enlarged cloud. -/
theorem StagePlaneData_PLN.rsel_of_mem (A : StagePlaneData_PLN X H E ι S T) (x₀ : X) {x : H}
    (hx : x ∈ T) : A.rsel x₀ x = A.rpre ⟨x, hx⟩ := by
  rw [StagePlaneData_PLN.rsel, dite_eq_left hx]

/-- The radius at a point of the enlarged cloud. -/
theorem StagePlaneData_PLN.radius_of_mem (A : StagePlaneData_PLN X H E ι S T) (x₀ : X) (sg : ℝ)
    (ρ : X → ℝ) {x : H} (hx : x ∈ T) : A.radius x₀ sg ρ x = sg * ρ (A.rpre ⟨x, hx⟩) := by
  rw [StagePlaneData_PLN.radius, A.rsel_of_mem x₀ hx]

/-- The radius selection is a selection of preimages over `T` as soon as `q̂` is one. -/
theorem StagePlaneData_PLN.rsel_spec (A : StagePlaneData_PLN X H E ι S T) (x₀ : X) (f : X → H)
    (h : ∀ x : T, f (A.rpre x) = x.1) : ∀ x ∈ T, f (A.rsel x₀ x) = x := fun x hx => by
  rw [A.rsel_of_mem x₀ hx]
  exact h ⟨x, hx⟩

/-- (PDEF) by the chain rule: `L_x = im (K_a ∘ DΦ_a(η_a q))` when `Φ_a` is differentiable there. -/
theorem stagePlane_eq_range_comp_PLN (model : ι → E → H) (prune : ι → H →L[ℝ] H)
    (coord : ι → X → E) (a : ι) (q : X) (hd : DifferentiableAt ℝ (model a) (coord a q)) :
    stagePlane_PLN model prune coord a q =
      LinearMap.range ((prune a).comp (fderiv ℝ (model a) (coord a q)) : E →ₗ[ℝ] H) := by
  rw [stagePlane_PLN, fderiv_comp (coord a q) (prune a).differentiableAt hd,
    ContinuousLinearMap.fderiv]

end Data

section Blocks

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)] {X E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A locally constant marker annihilates the plane**: if the `t`-marker of `K_a ∘ Φ_a` is
constant near `η_a(q)` (and `K_a ∘ Φ_a` is differentiable there), then
`stagePlane a q ≤ ker v_t`. -/
theorem stagePlane_le_ker_marker_PLN (model : ι → E → BlockSpace V)
    (prune : ι → BlockSpace V →L[ℝ] BlockSpace V) (coord : ι → X → E) (a : ι) (q : X) (t : κ)
    {c : ℝ} (hd : DifferentiableAt ℝ (prune a ∘ model a) (coord a q))
    (hloc : (fun u => ((prune a ∘ model a) u t).snd) =ᶠ[𝓝 (coord a q)] fun _ => c) :
    stagePlane_PLN model prune coord a q ≤
      LinearMap.ker ((blockMarkerCLM (V := V) t : BlockSpace V →L[ℝ] ℝ) :
        BlockSpace V →ₗ[ℝ] ℝ) :=
  range_fderiv_le_ker_blockMarkerCLM_GAFS t hd hloc

/-- The projection `J_t` onto the WHOLE block `t` of the block space. -/
def blockProjCLM_PLN (t : κ) : BlockSpace V →L[ℝ] WithLp 2 (V t × ℝ) :=
  PiLp.proj (𝕜 := ℝ) 2 (fun i => WithLp 2 (V i × ℝ)) t

omit [Fintype κ] in
theorem blockProjCLM_apply_PLN (t : κ) (y : BlockSpace V) : blockProjCLM_PLN t y = y t := rfl

/-- **A vanishing whole block annihilates the plane**: if the `t`-block of `K_a ∘ Φ_a` vanishes
near `η_a(q)`, then `stagePlane a q ≤ ker J_t` (`J_t` = projection onto the whole block `t`). -/
theorem stagePlane_le_ker_proj_PLN (model : ι → E → BlockSpace V)
    (prune : ι → BlockSpace V →L[ℝ] BlockSpace V) (coord : ι → X → E) (a : ι) (q : X) (t : κ)
    (hd : DifferentiableAt ℝ (prune a ∘ model a) (coord a q))
    (hloc : (fun u => (prune a ∘ model a) u t) =ᶠ[𝓝 (coord a q)] fun _ => 0) :
    stagePlane_PLN model prune coord a q ≤
      LinearMap.ker ((blockProjCLM_PLN (V := V) t : BlockSpace V →L[ℝ] WithLp 2 (V t × ℝ)) :
        BlockSpace V →ₗ[ℝ] WithLp 2 (V t × ℝ)) := by
  rintro _ ⟨h, rfl⟩
  rw [LinearMap.mem_ker]
  have h1 : HasFDerivAt (fun u => blockProjCLM_PLN (V := V) t ((prune a ∘ model a) u))
      ((blockProjCLM_PLN (V := V) t).comp (fderiv ℝ (prune a ∘ model a) (coord a q)))
      (coord a q) :=
    (blockProjCLM_PLN (V := V) t).hasFDerivAt.comp _ hd.hasFDerivAt
  have h2 : HasFDerivAt (fun u => blockProjCLM_PLN (V := V) t ((prune a ∘ model a) u))
      (0 : E →L[ℝ] WithLp 2 (V t × ℝ)) (coord a q) :=
    (hasFDerivAt_const (0 : WithLp 2 (V t × ℝ)) (coord a q)).congr_of_eventuallyEq hloc
  have h3 := congrArg (fun L : E →L[ℝ] WithLp 2 (V t × ℝ) => L h) (h1.unique h2)
  simpa using h3

end Blocks

section Plateau

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The plateau step of (FM\*)**: if the scaled cutoff block `(φ(s⁻¹u)u, sφ(s⁻¹u))` is `e`-close
to the full-marker block `(sη, s)` with `‖η‖ ≤ M`, `0 ≤ e < s`, and `M + e/s ≤ r(1 − e/s)`, then the
cutoff argument is strictly inside the `r`-ball: `‖s⁻¹u‖ < r`. -/
theorem scaledCutoffBlock_arg_lt_of_close_PLN {φ : F → ℝ} {s e M r : ℝ} (hs : 0 < s)
    (he : e < s) {η u : F} (hη : ‖η‖ ≤ M)
    (hclose : ‖(WithLp.toLp 2 (s • η, s) : WithLp 2 (F × ℝ)) - scaledCutoffBlock s φ u‖ < e)
    (hr : M + e / s ≤ r * (1 - e / s)) : ‖s⁻¹ • u‖ < r := by
  set m := φ (s⁻¹ • u) with hm
  have hdiff : (WithLp.toLp 2 (s • η, s) : WithLp 2 (F × ℝ)) - scaledCutoffBlock s φ u =
      WithLp.toLp 2 (s • η - m • u, s - s * m) := rfl
  rw [hdiff] at hclose
  have hsnd : ‖s - s * m‖ < e :=
    lt_of_le_of_lt (WithLp.norm_snd_le (x := WithLp.toLp 2 (s • η - m • u, s - s * m))) hclose
  have hfst : ‖s • η - m • u‖ < e :=
    lt_of_le_of_lt (WithLp.norm_fst_le (x := WithLp.toLp 2 (s • η - m • u, s - s * m))) hclose
  rw [Real.norm_eq_abs] at hsnd
  have hes : e / s < 1 := (div_lt_one hs).mpr he
  have hm1 : 1 - e / s < m := by
    have h1 : s * (1 - m) < e := by
      have := (abs_lt.mp hsnd).2
      linarith
    have h2 : 1 - m < e / s := by
      rw [lt_div_iff₀ hs]
      linarith
    linarith
  have hm0 : 0 < m := by linarith
  have hsη : ‖s • η‖ ≤ s * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hη hs.le
  have hmu : m * ‖u‖ < s * M + e := by
    have h1 : ‖m • u‖ ≤ ‖s • η‖ + ‖s • η - m • u‖ := by
      have := norm_sub_le (s • η) (s • η - m • u)
      rwa [sub_sub_cancel] at this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm0] at h1
    linarith
  have hgoal : ‖s⁻¹ • u‖ = ‖u‖ / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), inv_mul_eq_div]
  rw [hgoal, div_lt_iff₀ hs]
  -- `m‖u‖ < sM + e` and `m > 1 − e/s` give `‖u‖ < s(M + e/s)/(1 − e/s) ≤ s r`.
  have hk : 0 < 1 - e / s := by linarith
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have h1 : (1 - e / s) * ‖u‖ ≤ m * ‖u‖ := mul_le_mul_of_nonneg_right hm1.le hu0
  have h2 : s * M + e = s * (M + e / s) := by field_simp
  have h3 : s * (M + e / s) ≤ s * (r * (1 - e / s)) := mul_le_mul_of_nonneg_left hr hs.le
  have h4 : (1 - e / s) * ‖u‖ < (1 - e / s) * (r * s) := by nlinarith
  exact lt_of_mul_lt_mul_left h4 hk.le

end Plateau

section Ratio

/-- **The radius ratio of two intersecting constant-radius charts**: for a `Λ`-Lipschitz `ρ` and a
common point `q` with `d(q, a) < C_aρ(a)`, `d(q, t) < C_tρ(t)`:
`(1 − ΛC_a)ρ(a) ≤ (1 + ΛC_t)ρ(t)`. (Scope: the charts whose radius is `ρ(centre)` — circle, edge,
slim; not zero blocks.) -/
theorem ratio_of_common_point_PLN {X : Type*} [MetricSpace X] {ρ : X → ℝ} {Λ Ca Ct : ℝ}
    (hρL : LipschitzWith (Real.toNNReal Λ) ρ) (hΛ : 0 ≤ Λ) {a t q : X}
    (hqa : dist q a < Ca * ρ a) (hqt : dist q t < Ct * ρ t) :
    (1 - Λ * Ca) * ρ a ≤ (1 + Λ * Ct) * ρ t := by
  have h1 := hρL.dist_le_mul q a
  have h2 := hρL.dist_le_mul q t
  rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1 h2
  have h1' : Λ * dist q a ≤ Λ * (Ca * ρ a) := mul_le_mul_of_nonneg_left hqa.le hΛ
  have h2' : Λ * dist q t ≤ Λ * (Ct * ρ t) := mul_le_mul_of_nonneg_left hqt.le hΛ
  have ha := (abs_le.mp (h1.trans h1')).1
  have ht := (abs_le.mp (h2.trans h2')).2
  nlinarith

/-- **`R_t/R_a ≥ .99` for intersecting non-zero constant-radius marker charts**: with
`ΛC_a ≤ 1/200` and `ΛC_t ≤ 1/200`, `ρ(t) ≥ (99/100)ρ(a)`. -/
theorem ratio_ge_of_common_point_PLN {X : Type*} [MetricSpace X] {ρ : X → ℝ} {Λ Ca Ct : ℝ}
    (hρL : LipschitzWith (Real.toNNReal Λ) ρ) (hΛ : 0 ≤ Λ) {a t q : X} (ha : 0 < ρ a)
    (ht : 0 < ρ t) (hqa : dist q a < Ca * ρ a) (hqt : dist q t < Ct * ρ t)
    (hCa : Λ * Ca ≤ 1 / 200) (hCt : Λ * Ct ≤ 1 / 200) : 99 / 100 * ρ a ≤ ρ t := by
  have h := ratio_of_common_point_PLN hρL hΛ hqa hqt
  have h1 : (1 - 1 / 200) * ρ a ≤ (1 - Λ * Ca) * ρ a :=
    mul_le_mul_of_nonneg_right (by linarith) ha.le
  have h2 : (1 + Λ * Ct) * ρ t ≤ (1 + 1 / 200) * ρ t :=
    mul_le_mul_of_nonneg_right (by linarith) ht.le
  nlinarith

end Ratio

section Gaf03

variable {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **GAF03's contributor hypothesis for a marker line**: with `K = (ker v)ᗮ`, a contributor `y`
with `v y = v x` and plane `P ≤ ker v` satisfies `K.starProjection y = K.starProjection x` and
`P ≤ Kᗮ` (`c = K.starProjection x`, the full-marker vector). -/
theorem markerLine_input_PLN (v : H →L[ℝ] ℝ) (P : Submodule ℝ H) {x y : H} (hv : v y = v x)
    (hP : P ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ)) :
    (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection y =
        (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ.starProjection x ∧
      P ≤ (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮᗮ := by
  rw [Submodule.orthogonal_orthogonal]
  refine ⟨?_, hP⟩
  rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.orthogonal_orthogonal, LinearMap.mem_ker]
  change v (y - x) = 0
  rw [map_sub, hv, sub_self]

/-- **GAF03's contributor hypothesis for a whole block** (ZSP01's form, `c = 0`): with
`K = (ker J)ᗮ`, a contributor `y` with `J y = 0` and plane `P ≤ ker J` satisfies
`K.starProjection y = 0` and `P ≤ Kᗮ`. -/
theorem zeroBlock_input_PLN (J : H →L[ℝ] W) (P : Submodule ℝ H) {y : H} (hy : J y = 0)
    (hP : P ≤ LinearMap.ker (J : H →ₗ[ℝ] W)) :
    (LinearMap.ker (J : H →ₗ[ℝ] W))ᗮ.starProjection y = 0 ∧
      P ≤ (LinearMap.ker (J : H →ₗ[ℝ] W))ᗮᗮ := by
  rw [Submodule.orthogonal_orthogonal]
  refine ⟨?_, hP⟩
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal,
    LinearMap.mem_ker]
  exact hy

end Gaf03

end DifferentialGeometry.Geometry.Collapse
