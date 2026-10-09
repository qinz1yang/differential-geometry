import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConormApplications

/-!
# EDP03's collar in physical units: the original pair `(η_j, t)` and the height pair `(η_j, H₀)`

Lane C14-EDP3. Blueprint `master207B.tex`, EDP03 (`lem:fibration-edge-original-buffer-and-height`,
collar clause B:6862–6865, proof B:6938–6946): "On the collar `3.9Δ < t < 4.1Δ`, the original pair
`(η_i, t)` has least singular value greater than `.9`" (in `R_i⁻²g`, after "changing to `R_i` units
divides by `q < 1.01`"). External review 53 §2.3 / §5: a DERIVED lemma of `EdgeChart`'s collar (the
`100Δ` domain and the collar to `10Δ`), not a new disk packet; "surjective" alone is not "`> .9`".

The co-norm itself is lane C14-EDP6's `EdgeFamily.collar_conorm_EDP6`, stated in the NORMALIZED
context of the chart (rescaled ball `B(j, 100Δ)`, smoothing `Fs/ρ(j)/(ρ/ρ(j))`, metric `ρ(j)⁻²g`).
Here it is transported to PHYSICAL units on EDP03's own domain
`Y_j = {p ∈ B(j, 100Δρ(j)) : |η_j| < 5Δ, t < 5Δ}`, `t = Fs/ρ`, with the scale ratio `ρ(p)/ρ(j)`
explicit and the unit sphere of `ρ(j)⁻²g` written `g(W, W) = ρ(j)²`.

* `edgeRowHeight_eq_self_EDP3`, `edgeRowHeight_le_two_EDP3`, `edgeRowHeight_eq_four_iff_EDP3`:
  LFR27's constant-core profile: `H₀ = t` where `t ≥ 2Δ`, `H₀ ≤ 2Δ` where `t ≤ 2Δ`,
  `H₀ = 4Δ ↔ t = 4Δ`.
* `mvfderiv_edgeReferenceCoordinates_congr_EDP3`: the differential of a pair only sees the germs.
* `conorm_homotopy_EDP3`: a co-norm bound `> c` of `a`, and `‖b W − a W‖ ≤ ε` on the test vectors,
  give the bound `> c − ε` for every `(1 − τ) a + τ b`, `τ ∈ [0, 1]` (EDP04's homotopy (EI)).
* `EdgeFamily.collar_conorm_phys_EDP3`: on EDP03's collar, for the ORIGINAL pair
  `J = (η_j, Fs/ρ)`: `ρ(p)/ρ(j) ∈ [99/100, 101/100]` and every unit `ξ ∈ ℝ²` has `W` with
  `g(W, W) = ρ(j)²` and `⟪DJ(p) W, ξ⟫ > (1 − (γc + βc))/(ρ(p)/ρ(j)) > 9/10`.
* `EdgeFamily.collar_height_conorm_EDP3`: the same for the height pair `J₀ = (η_j, H₀)` (the start
  of EDP04's homotopy), with `H₀ =ᶠ t` near the point, `DJ₀(p) = DJ(p)`, and `DJ₀(p)` onto.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### The constant-core profile -/

/-- LFR27's height is `t = F/ρ` where `t ≥ 2Δ`. -/
theorem edgeRowHeight_eq_self_EDP3 {Y : Type*} {Δ : ℝ} (hΔ : 0 < Δ) {F ρ : Y → ℝ} {y : Y}
    (h : 2 * Δ ≤ F y / ρ y) : edgeRowHeight Δ F ρ y = F y / ρ y := by
  unfold edgeRowHeight
  have h2 : 2 ≤ F y / ρ y / Δ := by
    rw [le_div_iff₀ hΔ]
    linarith
  rw [edgeSublevelProfile_eq_self h2]
  field_simp

/-- LFR27's height is at most `2Δ` where `t ≤ 2Δ`. -/
theorem edgeRowHeight_le_two_EDP3 {Y : Type*} {Δ : ℝ} (hΔ : 0 < Δ) {F ρ : Y → ℝ} {y : Y}
    (h : F y / ρ y ≤ 2 * Δ) : edgeRowHeight Δ F ρ y ≤ 2 * Δ := by
  unfold edgeRowHeight
  have h2 : F y / ρ y / Δ ≤ 2 := by
    rw [div_le_iff₀ hΔ]
    linarith
  have := edgeSublevelProfile_le_two h2
  nlinarith

/-- The rim of LFR27's height is the rim of `t`: `H₀ = 4Δ ↔ t = 4Δ`. -/
theorem edgeRowHeight_eq_four_iff_EDP3 {Y : Type*} {Δ : ℝ} (hΔ : 0 < Δ) {F ρ : Y → ℝ} {y : Y} :
    edgeRowHeight Δ F ρ y = 4 * Δ ↔ F y / ρ y = 4 * Δ := by
  constructor
  · intro h
    rcases le_total (F y / ρ y) (2 * Δ) with hl | hl
    · have := edgeRowHeight_le_two_EDP3 hΔ hl
      linarith
    · rwa [← edgeRowHeight_eq_self_EDP3 hΔ hl]
  · intro h
    rw [edgeRowHeight_eq_self_EDP3 hΔ (by linarith), h]

/-! ### Calculus of pairs -/

section Pairs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The differential of a pair `(f, h)` only depends on the germ of `h`. -/
theorem mvfderiv_edgeReferenceCoordinates_congr_EDP3 {f h h' : M → ℝ} {x : M}
    (hh : h =ᶠ[𝓝 x] h') :
    mvfderiv I (edgeReferenceCoordinates ![f, h]) x =
      mvfderiv I (edgeReferenceCoordinates ![f, h']) x := by
  have he : edgeReferenceCoordinates ![f, h] =ᶠ[𝓝 x] edgeReferenceCoordinates ![f, h'] := by
    filter_upwards [hh] with y hy
    unfold edgeReferenceCoordinates
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact hy
  unfold mvfderiv
  rw [he.mfderiv_eq, he.eq_of_nhds]
  rfl

end Pairs

/-- **The co-norm along a homotopy** (EDP04's (EI)): if every unit `ξ ∈ ℝ²` has a test vector
`W ∈ S` with `c < ⟪a W, ξ⟫`, and `‖b W − a W‖ ≤ ε` on `S`, then for every `τ ∈ [0, 1]` every unit
`ξ` has `W ∈ S` with `c − ε < ⟪((1 − τ) a + τ b) W, ξ⟫`. -/
theorem conorm_homotopy_EDP3 {T : Type*} (S : Set T) (a b : T → EuclideanSpace ℝ (Fin 2))
    {c ε τ : ℝ} (ha : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W ∈ S, c < inner ℝ (a W) ξ)
    (hab : ∀ W ∈ S, ‖b W - a W‖ ≤ ε) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ‖ξ‖ = 1) :
    ∃ W ∈ S, c - ε < inner ℝ ((1 - τ) • a W + τ • b W) ξ := by
  refine conorm_perturb_EDP6 S a (fun W => (1 - τ) • a W + τ • b W) ha (fun W hW => ?_) ξ hξ
  have he : (1 - τ) • a W + τ • b W - a W = τ • (b W - a W) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0]
  have h1 := hab W hW
  have h0 : 0 ≤ ‖b W - a W‖ := norm_nonneg _
  have hε : 0 ≤ ε := h0.trans h1
  calc τ * ‖b W - a W‖ ≤ 1 * ε := mul_le_mul hτ1 h1 h0 zero_le_one
    _ = ε := one_mul ε

/-! ### The collar co-norm in physical units -/

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **EDP03's collar co-norm in physical units** (B:6862–6865, B:6938–6946): at a point `x` of the
collar `3.9Δ < t < 4.1Δ` of `Y_j` (`t = Fs/ρ`), the scale ratio `ρ(x)/ρ(j)` lies in
`[99/100, 101/100]`, and every unit `ξ ∈ ℝ²` has a `ρ(j)⁻²g`-unit `W` (`g(W, W) = ρ(j)²`) with
`⟪DJ(x) W, ξ⟫ > (1 − (γc + βc))/(ρ(x)/ρ(j)) > 9/10` for the ORIGINAL pair `J = (η_j, Fs/ρ)`. -/
theorem EdgeFamily.collar_conorm_phys_EDP3
    (Fe : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) (hΔ : 0 < Δ) {j : X} (hj : j ∈ Fe.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (hη : |Fe.coord j x| < 5 * Δ)
    (ht1 : 39 / 10 * Δ < Fe.smoothing x / ρ x) (ht2 : Fe.smoothing x / ρ x < 41 / 10 * Δ) :
    (99 / 100 ≤ ρ x / ρ j ∧ ρ x / ρ j ≤ 101 / 100) ∧
    ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W : TangentSpace 𝓘(ℝ, E3) x,
      g.inner x W W = ρ j ^ 2 ∧
      (1 - (γc + βc)) / (ρ x / ρ j) < inner ℝ (mvfderiv 𝓘(ℝ, E3)
        (edgeReferenceCoordinates ![Fe.coord j, fun z => Fe.smoothing z / ρ z]) x W) ξ ∧
      9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3)
        (edgeReferenceCoordinates ![Fe.coord j, fun z => Fe.smoothing z / ρ z]) x W) ξ := by
  have hrj := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hq : ∀ y, Fe.smoothing y / ρ j / (ρ y / ρ j) = Fe.smoothing y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hF1 : Δ / 10 ≤ Fe.smoothing x / ρ j / (ρ x / ρ j) := by
    rw [hq]
    linarith
  have hF2 : Fe.smoothing x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by
    rw [hq]
    linarith
  have h := Fe.collar_conorm_EDP6 hγc hγc1 hβc1 hj
  set η := Fe.coord j with hηdef
  set Fs := Fe.smoothing with hFsdef
  let c := Fe.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc : η = c.coord := by
    rw [hηdef]
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
  have hJ : edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)] =
      edgeReferenceCoordinates ![η, fun z => Fs z / ρ z] := by
    rw [hc]
    simp_rw [hq]
  have hη' : |c.coord x| ≤ 10 * Δ := by
    rw [← hc]
    linarith
  have hxR : x ∈ ball j (100 * Δ) := hd
  obtain ⟨hratio, hco⟩ := h x hxR hη' hF1 hF2
  have hxx : x ∈ ball x (100 * (ρ x / ρ j)) :=
    mem_ball_self (mul_pos (by norm_num) (div_pos (hρ x) (hρ j)))
  refine ⟨hratio, fun ξ hξ => ?_⟩
  obtain ⟨W, hW, hlow, h9⟩ := hco x hxx ξ hξ
  refine ⟨W, ?_, ?_, ?_⟩
  · have hw' : (ρ j)⁻¹ ^ 2 * g.inner x W W = 1 := hW
    have hr2 : 0 < ρ j ^ 2 := by positivity
    field_simp at hw'
    linarith
  · rw [← hJ]
    exact hlow
  · rw [← hJ]
    exact h9

/-- **EDP03's collar co-norm for the height pair** `J₀ = (η_j, H₀)`, `H₀ = Δψ(t/Δ)` (the pair at the
start of EDP04's homotopy (EI)): on the collar `H₀ =ᶠ t` near the point, `DJ₀ = DJ` for the original
pair `J = (η_j, t)`, `DJ₀` is onto, and `J₀` has the co-norm bound of
`EdgeFamily.collar_conorm_phys_EDP3`. -/
theorem EdgeFamily.collar_height_conorm_EDP3
    (Fe : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) (hΔ : 0 < Δ) {j : X} (hj : j ∈ Fe.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (hη : |Fe.coord j x| < 5 * Δ)
    (ht1 : 39 / 10 * Δ < Fe.smoothing x / ρ x) (ht2 : Fe.smoothing x / ρ x < 41 / 10 * Δ) :
    edgeRowHeight Δ Fe.smoothing ρ =ᶠ[𝓝 x] (fun z => Fe.smoothing z / ρ z) ∧
    mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates ![Fe.coord j, edgeRowHeight Δ Fe.smoothing ρ]) x =
      mvfderiv 𝓘(ℝ, E3)
        (edgeReferenceCoordinates ![Fe.coord j, fun z => Fe.smoothing z / ρ z]) x ∧
    Function.Surjective (mvfderiv 𝓘(ℝ, E3)
      (edgeReferenceCoordinates ![Fe.coord j, edgeRowHeight Δ Fe.smoothing ρ]) x) ∧
    ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W : TangentSpace 𝓘(ℝ, E3) x,
      g.inner x W W = ρ j ^ 2 ∧
      (1 - (γc + βc)) / (ρ x / ρ j) < inner ℝ (mvfderiv 𝓘(ℝ, E3)
        (edgeReferenceCoordinates ![Fe.coord j, edgeRowHeight Δ Fe.smoothing ρ]) x W) ξ ∧
      9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3)
        (edgeReferenceCoordinates ![Fe.coord j, edgeRowHeight Δ Fe.smoothing ρ]) x W) ξ := by
  have htc : ContinuousAt (fun z => Fe.smoothing z / ρ z) x :=
    (Fe.contMDiffAt_height_of_collar hj hx (by linarith) (by linarith) (by linarith)).continuousAt
  have hev := edgeRowHeight_eventuallyEq hΔ htc (by linarith)
  have hD := mvfderiv_edgeReferenceCoordinates_congr_EDP3 (I := 𝓘(ℝ, E3)) (f := Fe.coord j) hev
  obtain ⟨-, hco⟩ := Fe.collar_conorm_phys_EDP3 hγc hγc1 hβc1 hΔ hj hx hη ht1 ht2
  refine ⟨hev, hD, ?_, ?_⟩
  · refine surjective_of_conorm_pos_EDP6 (mvfderiv 𝓘(ℝ, E3)
      (edgeReferenceCoordinates ![Fe.coord j, edgeRowHeight Δ Fe.smoothing ρ]) x).toLinearMap
      (fun ξ hξ => ?_)
    obtain ⟨W, -, -, h9⟩ := hco ξ hξ
    refine ⟨W, ?_⟩
    change 0 < inner ℝ (mvfderiv 𝓘(ℝ, E3)
      (edgeReferenceCoordinates ![Fe.coord j, edgeRowHeight Δ Fe.smoothing ρ]) x W) ξ
    rw [hD]
    linarith
  · intro ξ hξ
    rw [hD]
    exact hco ξ hξ

end DifferentialGeometry.Geometry.Collapse
