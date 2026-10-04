import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.BufferedFibreStability

/-!
# LFR28 step 4: the interpolation is transverse, and LFR03 isotopes the model fibre to the source

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223), proof step 4
(A:27399–27420). On the model domain `U` the interpolation between the model map `u₀ = (t, H_N)` and
the pulled-back source map `w = (f_i ∘ j_i, H_i ∘ j_i)` is
`F_s = (1 - s) u₀ + s w`, `0 ≤ s ≤ 1`. For a target level `c` and the sublevel value `e` (`= 4Δ`)
put `X_c = {y | y.1 = c, y.2 ≤ e}` with side boundary `∂X_c = {y.1 = c, y.2 = e}`.

* `hasMFDerivAt_edgeInterp`: `dF_s = (1 - s) du₀ + s dw`.
* `edgeInterp_surjective_fst` (interior): if some `X` has `du₀(X).1 = 1` and `|dw(X).1 - 1| ≤ 10⁻³`,
  the first covector of every `F_s` is onto.
* `edgeInterp_surjective_pair` (boundary, the blueprint's two-by-two determinant): if `X₁, X₂` give
  the model matrix `[[1, 0], [0, m]]`, `m ≥ 1/2`, and `dw` is entrywise `10⁻³`-close to it, the pair
  `(F_s.1 - c, e - F_s.2)` is a submersion at every time.
* `edgeInterp_mem_window`, `edgeInterp_mem_boundary_window`: if `|w - u₀| ≤ δ` componentwise, every
  preimage of `X_c` (resp. `∂X_c`) lies in the model window `|u₀.1 - c| ≤ δ`, `u₀.2 ≤ e + δ`
  (resp. `|u₀.2 - e| ≤ δ`).
* `exists_edgeInterp_fibre_isotopy`: with one compact `Q` containing the window, LFR03
  (`lfr03_exists_isotopy_fibre`) gives a compactly supported jointly `C^{r-1}` isotopy carrying
  the model fibre `{u₀.1 = c, u₀.2 ≤ e}` onto the pulled-back source fibre `{w.1 = c, w.2 ≤ e}` and
  boundary onto boundary.

The blueprint's inputs are (LFR28.3) (first covector within `10⁻³` of `dt`), (LFR28.4) (second
within `10⁻³` of `dH_N`, with `dH_N(∂_t) = 0`, `‖dH_N‖ > 1 - 10⁻⁸`) and (LFR28.5) (values within
`Δ/100`); here they enter as the vector hypotheses `hrow`, `hpair` and the value hypothesis
`hval`, evaluated on `∂_t` and the unit model gradient direction (`X₁ = ∂_t`, `X₂` = that
direction, `m = dH_N(X₂)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- The differential of the interpolation `F_s = (1 - s) u₀ + s w`. -/
theorem hasMFDerivAt_edgeInterp {u₀ w : M → ℝ × ℝ} {x : M} {A₀ A₁ : TangentSpace I x →L[ℝ] ℝ × ℝ}
    (hu₀ : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) u₀ x A₀) (hw : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) w x A₁) (s : ℝ) :
    HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) (fun y => (1 - s) • u₀ y + s • w y) x ((1 - s) • A₀ + s • A₁) :=
  (hu₀.const_smul (1 - s)).add (hw.const_smul s)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- **Interior transversality.** If a vector `X` has model first covector value one and source
first covector value within `10⁻³` of one, the first covector of every interpolation is onto. -/
theorem edgeInterp_surjective_fst {u₀ w : M → ℝ × ℝ} {x : M} {A₀ A₁ : TangentSpace I x →L[ℝ] ℝ × ℝ}
    (hu₀ : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) u₀ x A₀) (hw : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) w x A₁)
    {s c : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (X : TangentSpace I x)
    (h1 : (A₀ X).1 = 1) (h2 : |(A₁ X).1 - 1| ≤ 1 / 1000) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ)
      (fun y => ((1 - s) • u₀ y + s • w y).1 - c) x) := by
  have hF := hasMFDerivAt_edgeInterp hu₀ hw s
  have hP : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (fun p : ℝ × ℝ => p.1 - c)
      ((1 - s) • u₀ x + s • w x) (ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    (hasFDerivAt_fst.sub_const c).hasMFDerivAt
  have hd : mfderiv I 𝓘(ℝ, ℝ) (fun y => ((1 - s) • u₀ y + s • w y).1 - c) x =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((1 - s) • A₀ + s • A₁) :=
    (hP.comp x hF).mfderiv
  rw [hd]
  set a : ℝ := (1 - s) * (A₀ X).1 + s * (A₁ X).1 with ha
  have hval : ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((1 - s) • A₀ + s • A₁)) X = a := by
    simp [ha]
  have hapos : 0 < a := by
    rw [ha, h1]
    have h2' := (abs_le.mp h2).1
    nlinarith [hs.1, hs.2]
  intro v
  change ℝ at v
  refine ⟨(v / a) • X, ?_⟩
  change ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((1 - s) • A₀ + s • A₁) :
    TangentSpace I x →L[ℝ] ℝ) ((v / a) • X) = v
  rw [ContinuousLinearMap.map_smul, hval, smul_eq_mul]
  field_simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- **Boundary transversality (the two-by-two determinant).** If `X₁, X₂` give the model matrix
`[[1, 0], [0, m]]` with `m ≥ 1/2` and the source matrix is entrywise within `10⁻³` of it, then
`(F_s.1 - c, e - F_s.2)` is a submersion at every time `s ∈ [0, 1]`. -/
theorem edgeInterp_surjective_pair {u₀ w : M → ℝ × ℝ} {x : M}
    {A₀ A₁ : TangentSpace I x →L[ℝ] ℝ × ℝ}
    (hu₀ : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) u₀ x A₀) (hw : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) w x A₁)
    {s c e : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (X₁ X₂ : TangentSpace I x)
    (h11 : (A₀ X₁).1 = 1) (h12 : (A₀ X₂).1 = 0) (h21 : (A₀ X₁).2 = 0) (h22 : 1 / 2 ≤ (A₀ X₂).2)
    (k11 : |(A₁ X₁).1 - 1| ≤ 1 / 1000) (k12 : |(A₁ X₂).1| ≤ 1 / 1000)
    (k21 : |(A₁ X₁).2| ≤ 1 / 1000) (k22 : |(A₁ X₂).2 - (A₀ X₂).2| ≤ 1 / 1000) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ)
      (fun y => (((1 - s) • u₀ y + s • w y).1 - c, e - ((1 - s) • u₀ y + s • w y).2)) x) := by
  have hF := hasMFDerivAt_edgeInterp hu₀ hw s
  set A : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ) with hA
  have hP : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ => (p.1 - c, e - p.2))
      ((1 - s) • u₀ x + s • w x) A :=
    ((hasFDerivAt_fst.sub_const c).prodMk (hasFDerivAt_snd.const_sub e)).hasMFDerivAt
  have hd : mfderiv I 𝓘(ℝ, ℝ × ℝ)
      (fun y => (((1 - s) • u₀ y + s • w y).1 - c, e - ((1 - s) • u₀ y + s • w y).2)) x =
      A.comp ((1 - s) • A₀ + s • A₁) := (hP.comp x hF).mfderiv
  rw [hd]
  set a11 : ℝ := (1 - s) * (A₀ X₁).1 + s * (A₁ X₁).1 with ha11
  set a12 : ℝ := (1 - s) * (A₀ X₂).1 + s * (A₁ X₂).1 with ha12
  set a21 : ℝ := (1 - s) * (A₀ X₁).2 + s * (A₁ X₁).2 with ha21
  set a22 : ℝ := (1 - s) * (A₀ X₂).2 + s * (A₁ X₂).2 with ha22
  have hLX : ∀ α β : ℝ, A.comp ((1 - s) • A₀ + s • A₁) (α • X₁ + β • X₂) =
      (α * a11 + β * a12, -(α * a21 + β * a22)) := by
    intro α β
    apply Prod.ext
    · simp [hA, ha11, ha12]
      ring
    · simp [hA, ha21, ha22]
      ring
  have k11' := abs_le.mp k11
  have k12' := abs_le.mp k12
  have k21' := abs_le.mp k21
  have k22' := abs_le.mp k22
  have hs0 := hs.1
  have hs1 := hs.2
  have b11 : 999 / 1000 ≤ a11 := by rw [ha11, h11]; nlinarith
  have b12 : |a12| ≤ 1 / 1000 := by
    rw [ha12, h12, abs_le]; constructor <;> nlinarith
  have b21 : |a21| ≤ 1 / 1000 := by
    rw [ha21, h21, abs_le]; constructor <;> nlinarith
  have b22 : (A₀ X₂).2 - 1 / 1000 ≤ a22 := by rw [ha22]; nlinarith
  have hdet : 0 < a11 * a22 - a12 * a21 := by
    have h1 : |a12 * a21| ≤ 1 / 1000 * (1 / 1000) := by
      rw [abs_mul]
      exact mul_le_mul b12 b21 (abs_nonneg _) (by norm_num)
    have h2 := (abs_le.mp h1).2
    nlinarith
  intro v
  change ℝ × ℝ at v
  set D := a11 * a22 - a12 * a21 with hD
  have hD0 : D ≠ 0 := hdet.ne'
  refine ⟨((v.1 * a22 + a12 * v.2) / D) • X₁ + ((-(a11 * v.2) - a21 * v.1) / D) • X₂, ?_⟩
  refine (hLX _ _).trans ?_
  apply Prod.ext
  · change (v.1 * a22 + a12 * v.2) / D * a11 + (-(a11 * v.2) - a21 * v.1) / D * a12 = v.1
    field_simp
    ring
  · change -((v.1 * a22 + a12 * v.2) / D * a21 + (-(a11 * v.2) - a21 * v.1) / D * a22) = v.2
    field_simp
    ring

omit [FiniteDimensional ℝ E] [I.Boundaryless] [TopologicalSpace M] [IsManifold I ∞ M] in
/-- **The model window.** If `|w - u₀| ≤ δ` componentwise at `x` and the interpolation at a time
`s ∈ [0, 1]` lies in `X_c = {y.1 = c, y.2 ≤ e}`, then `|u₀.1 - c| ≤ δ` and `u₀.2 ≤ e + δ`. -/
theorem edgeInterp_mem_window {u₀ w : M → ℝ × ℝ} {x : M} {s c e δ : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hv1 : |(w x).1 - (u₀ x).1| ≤ δ) (hv2 : |(w x).2 - (u₀ x).2| ≤ δ)
    (h1 : ((1 - s) • u₀ x + s • w x).1 = c) (h2 : ((1 - s) • u₀ x + s • w x).2 ≤ e) :
    |(u₀ x).1 - c| ≤ δ ∧ (u₀ x).2 ≤ e + δ := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  have hv1' := abs_le.mp hv1
  have hv2' := abs_le.mp hv2
  have hs0 := hs.1
  have hs1 := hs.2
  refine ⟨?_, by nlinarith⟩
  rw [abs_le]
  constructor <;> nlinarith

omit [FiniteDimensional ℝ E] [I.Boundaryless] [TopologicalSpace M] [IsManifold I ∞ M] in
/-- **The boundary window.** As `edgeInterp_mem_window`, on `∂X_c`: `|u₀.2 - e| ≤ δ`. -/
theorem edgeInterp_mem_boundary_window {u₀ w : M → ℝ × ℝ} {x : M} {s e δ : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hv2 : |(w x).2 - (u₀ x).2| ≤ δ)
    (h2 : ((1 - s) • u₀ x + s • w x).2 = e) :
    |(u₀ x).2 - e| ≤ δ := by
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h2
  have hv2' := abs_le.mp hv2
  have hs0 := hs.1
  have hs1 := hs.2
  rw [abs_le]
  constructor <;> nlinarith

variable [T2Space M] [SigmaCompactSpace M]

/-- **LFR28 step 4: the LFR03 isotopy from the model fibre to the pulled-back source fibre.**
Let `u₀, w : M → ℝ × ℝ` be `C^r` (`2 ≤ r`), `|w - u₀| ≤ δ` componentwise, and on the model window
`|u₀.1 - c| ≤ δ`, `u₀.2 ≤ e + δ` (contained in one compact `Q`) let some vector have model first
covector value one and source value within `10⁻³` of one; on the boundary window
`|u₀.1 - c| ≤ δ`, `|u₀.2 - e| ≤ δ` let `X₁, X₂` give the model matrix `[[1, 0], [0, m]]`, `m ≥ 1/2`,
with the source matrix entrywise `10⁻³`-close. Then a compactly supported, jointly `C^{r-1}`
isotopy `Φ` with `Φ 0 = id` carries `{u₀.1 = c, u₀.2 ≤ e}` onto `{w.1 = c, w.2 ≤ e}` and
`{u₀.1 = c, u₀.2 = e}` onto `{w.1 = c, w.2 = e}`. -/
theorem exists_edgeInterp_fibre_isotopy {r : ℕ} (hr : 2 ≤ r) {u₀ w : M → ℝ × ℝ}
    (hu₀ : ContMDiff I 𝓘(ℝ, ℝ × ℝ) r u₀) (hw : ContMDiff I 𝓘(ℝ, ℝ × ℝ) r w) {c e δ : ℝ}
    (hval : ∀ x, |(w x).1 - (u₀ x).1| ≤ δ ∧ |(w x).2 - (u₀ x).2| ≤ δ)
    (hrow : ∀ x, |(u₀ x).1 - c| ≤ δ → (u₀ x).2 ≤ e + δ → ∃ X : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X).1 = 1 ∧ |(mfderiv I 𝓘(ℝ, ℝ × ℝ) w x X).1 - 1| ≤ 1 / 1000)
    (hpair : ∀ x, |(u₀ x).1 - c| ≤ δ → |(u₀ x).2 - e| ≤ δ → ∃ X₁ X₂ : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).1 = 1 ∧ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).1 = 0 ∧
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).2 = 0 ∧ 1 / 2 ≤ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) w x X₁).1 - 1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) w x X₂).1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) w x X₁).2| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) w x X₂).2 - (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2| ≤ 1 / 1000)
    {Q : Set M} (hQ : IsCompact Q) (hQw : ∀ x, |(u₀ x).1 - c| ≤ δ → (u₀ x).2 ≤ e + δ → x ∈ Q) :
    ∃ (K : Set M) (Φ : ℝ → M ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮I, I⟯ M),
      IsCompact K ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ((r - 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × M => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl I M ((r - 1 : ℕ) : WithTop ℕ∞) ∧
      (∀ t x, x ∉ K → Φ t x = x) ∧
      Φ 1 '' {x | (u₀ x).1 = c ∧ (u₀ x).2 ≤ e} = {x | (w x).1 = c ∧ (w x).2 ≤ e} ∧
      Φ 1 '' {x | (u₀ x).1 = c ∧ (u₀ x).2 = e} = {x | (w x).1 = c ∧ (w x).2 = e} := by
  have hr0 : ((r : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hdu₀ : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) u₀ x := fun x => (hu₀ x).mdifferentiableAt hr0
  have hdw : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) w x := fun x => (hw x).mdifferentiableAt hr0
  set F : ℝ × M → ℝ × ℝ := fun q => (1 - q.1) • u₀ q.2 + q.1 • w q.2 with hFdef
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × ℝ) r F (Icc 0 1 ×ˢ univ) := by
    have h1 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) r (fun q : ℝ × M => 1 - q.1) :=
      contMDiff_const.sub contMDiff_fst
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × ℝ) r (fun q : ℝ × M => u₀ q.2) :=
      hu₀.comp contMDiff_snd
    have h3 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × ℝ) r (fun q : ℝ × M => w q.2) :=
      hw.comp contMDiff_snd
    exact ((h1.smul h2).add (contMDiff_fst.smul h3)).contMDiffOn
  set X : Set (ℝ × ℝ) := {y | y.1 - c = 0 ∧ 0 ≤ e - y.2} with hX
  set Xb : Set (ℝ × ℝ) := {y | y.1 - c = 0 ∧ e - y.2 = 0} with hXb
  have hφ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => y.1 - c) := contDiff_fst.sub contDiff_const
  have hβ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => e - y.2) := contDiff_const.sub contDiff_snd
  have hwin : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → |(u₀ x).1 - c| ≤ δ ∧ (u₀ x).2 ≤ e + δ := by
    intro t ht x hx
    exact edgeInterp_mem_window ht (hval x).1 (hval x).2 (sub_eq_zero.mp hx.1)
      (sub_nonneg.mp hx.2)
  have htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => (fun y : ℝ × ℝ => y.1 - c) (F (t, y))) x) := by
    intro t ht x hx
    obtain ⟨hw1, hw2⟩ := hwin t ht x hx
    obtain ⟨V, hV1, hV2⟩ := hrow x hw1 hw2
    exact edgeInterp_surjective_fst (hdu₀ x).hasMFDerivAt (hdw x).hasMFDerivAt ht V hV1 hV2
  have htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ Xb →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ)
        (fun y => ((fun y : ℝ × ℝ => y.1 - c) (F (t, y)), (fun y : ℝ × ℝ => e - y.2) (F (t, y))))
        x) := by
    intro t ht x hx
    have hxX : F (t, x) ∈ X := ⟨hx.1, hx.2.ge⟩
    obtain ⟨hw1, -⟩ := hwin t ht x hxX
    have hw3 := edgeInterp_mem_boundary_window ht (hval x).2 (sub_eq_zero.mp hx.2).symm
    obtain ⟨X₁, X₂, h11, h12, h21, h22, k11, k12, k21, k22⟩ := hpair x hw1 hw3
    exact edgeInterp_surjective_pair (hdu₀ x).hasMFDerivAt (hdw x).hasMFDerivAt ht X₁ X₂ h11 h12
      h21 h22 k11 k12 k21 k22
  obtain ⟨K, Φ, hK, -, hΦ, h0, hoff, -, -, h1, h1b⟩ :=
    DifferentialGeometry.Analysis.ODE.lfr03_exists_isotopy_fibre hr hF hφ hβ hX hXb htrans
      htransb hQ (fun t ht x hx => hQw x (hwin t ht x hx).1 (hwin t ht x hx).2) isOpen_univ
      (fun _ _ _ _ => mem_univ _)
  have hS0 : {x | F (0, x) ∈ X} = {x | (u₀ x).1 = c ∧ (u₀ x).2 ≤ e} := by
    ext x
    simp [hFdef, hX, sub_eq_zero]
  have hS1 : {x | F (1, x) ∈ X} = {x | (w x).1 = c ∧ (w x).2 ≤ e} := by
    ext x
    simp [hFdef, hX, sub_eq_zero]
  have hB0 : {x | F (0, x) ∈ Xb} = {x | (u₀ x).1 = c ∧ (u₀ x).2 = e} := by
    ext x
    simp [hFdef, hXb, sub_eq_zero, eq_comm]
  have hB1 : {x | F (1, x) ∈ Xb} = {x | (w x).1 = c ∧ (w x).2 = e} := by
    ext x
    simp [hFdef, hXb, sub_eq_zero, eq_comm]
  refine ⟨K, Φ, hK, hΦ, h0, hoff, ?_, ?_⟩
  · rw [← hS0, ← hS1]
    exact h1
  · rw [← hB0, ← hB1]
    exact h1b

end DifferentialGeometry.Geometry.Collapse
