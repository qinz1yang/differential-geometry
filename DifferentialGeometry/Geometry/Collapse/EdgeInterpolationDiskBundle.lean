import DifferentialGeometry.Geometry.Collapse.EdgeInterpolationTransversality
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.PacketBundle

/-!
# LFR28.1: the source edge slab is a trivial bundle with the model fibre, boundary `H = e`

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223), statement (LFR28.1) and
proof step 4, last paragraph (A:27421–27435), in abstract form. Data: a model manifold `M` with a
smooth model map `u₀ = (t, H_N)`, a source manifold `Y` with a smooth source map `u = (f, H)`, an
actual `C^r` model-to-source diffeomorphism `j` defined on all of `M`, and the interpolation
`F_s = (1 - s) u₀ + s (u ∘ j)` of `EdgeInterpolationTransversality` with the vector hypotheses
(LFR28.3)/(LFR28.4) on the model windows of every level `|c| < b` and the value hypothesis
(LFR28.5). With the source slab in the image of `j` and the source slab proper over `(-b, b)`:

* `edgeInterp_model_regular`, `edgeInterp_model_regular_boundary`: the model fibre
  `{u₀.1 = 0, u₀.2 ≤ e}` is a regular sublevel (lane SUB-BDY's manifold with boundary);
* `edgeInterp_source_regular`, `edgeInterp_source_regular_boundary`: `f` is a submersion on the
  source slab and `(f, H)` on its side boundary `{H = e}`, at EVERY level of `(-b, b)` (through `j`);
* `edgeInterp_disk_bundle` (**LFR28.1, abstract**): the model fibre and the source fibre
  `{f = 0, H ≤ e}` are smoothly diffeomorphic (LFR03 + LFR04 through W-2c's
  `lfr05_bundle_trivial_over_interval`); `f` restricted to `{a₀ < f < b₀, H ≤ e}` is trivial with
  that fibre (smooth injective `Θ` over the identity, onto, smooth inverse data); the boundary
  points of the source fibre are exactly those with `H = e`.

In LFR28, `e = 4Δ`, `H = Δψ(η/Δ)` (so `H ≤ 4Δ ⇔ η ≤ 4Δ` and `H = η` near the level, LFR27), and the
model fibre is LFR24's disk `D_4`; identifying the model fibre with the closed disk is the
remaining model-side input (recorded in the sheet).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Manifold.RegularLevel DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Kernels

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The first component of a map to `ℝ × ℝ` is a submersion where its differential takes a vector
to a nonzero first coordinate. -/
theorem surjective_mfderiv_fst_of_apply {v : M → ℝ × ℝ} {x : M}
    {A : TangentSpace I x →L[ℝ] ℝ × ℝ} (hv : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) v x A)
    (X : TangentSpace I x) (hX : (A X).1 ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun z => (v z).1) x) := by
  have hP : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (fun p : ℝ × ℝ => p.1) (v x)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) := hasFDerivAt_fst.hasMFDerivAt
  have hd : mfderiv I 𝓘(ℝ, ℝ) (fun z => (v z).1) x = (ContinuousLinearMap.fst ℝ ℝ ℝ).comp A :=
    (hP.comp x hv).mfderiv
  rw [hd]
  intro y
  change ℝ at y
  refine ⟨(y / (A X).1) • X, ?_⟩
  change ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp A : TangentSpace I x →L[ℝ] ℝ)
    ((y / (A X).1) • X) = y
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  change y / (A X).1 * (A X).1 = y
  field_simp

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The pair `(v.1, e - v.2)` is a submersion where the differential of `v` has a nonsingular
two-by-two minor on two vectors. -/
theorem surjective_mfderiv_fst_sub_snd_of_apply {v : M → ℝ × ℝ} {x : M} {e : ℝ}
    {A : TangentSpace I x →L[ℝ] ℝ × ℝ} (hv : HasMFDerivAt I 𝓘(ℝ, ℝ × ℝ) v x A)
    (X₁ X₂ : TangentSpace I x) (hdet : (A X₁).1 * (A X₂).2 - (A X₂).1 * (A X₁).2 ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => ((v z).1, e - (v z).2)) x) := by
  set B : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ) with hB
  have hP : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ => (p.1, e - p.2)) (v x) B :=
    (hasFDerivAt_fst.prodMk (hasFDerivAt_snd.const_sub e)).hasMFDerivAt
  have hd : mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => ((v z).1, e - (v z).2)) x = B.comp A :=
    (hP.comp x hv).mfderiv
  rw [hd]
  set a11 := (A X₁).1
  set a12 := (A X₂).1
  set a21 := (A X₁).2
  set a22 := (A X₂).2
  have hLX : ∀ α β : ℝ, B.comp A (α • X₁ + β • X₂) =
      (α * a11 + β * a12, -(α * a21 + β * a22)) := by
    intro α β
    apply Prod.ext
    · simp [hB, a11, a12]
    · simp [hB, a21, a22]
  intro w
  change ℝ × ℝ at w
  set D := a11 * a22 - a12 * a21 with hD
  refine ⟨((w.1 * a22 + a12 * w.2) / D) • X₁ + ((-(a11 * w.2) - a21 * w.1) / D) • X₂, ?_⟩
  refine (hLX _ _).trans ?_
  apply Prod.ext
  · change (w.1 * a22 + a12 * w.2) / D * a11 + (-(a11 * w.2) - a21 * w.1) / D * a12 = w.1
    field_simp
    ring
  · change -((w.1 * a22 + a12 * w.2) / D * a21 + (-(a11 * w.2) - a21 * w.1) / D * a22) = w.2
    field_simp
    ring

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Determinant of the near-model two-by-two matrix (the source end `s = 1` of
`edgeInterp_surjective_pair`). -/
theorem det_ne_zero_of_near_model {p₁ p₂ q₁ q₂ : ℝ × ℝ} (h11 : p₁.1 = 1) (h12 : p₂.1 = 0)
    (h22 : 1 / 2 ≤ p₂.2) (k11 : |q₁.1 - 1| ≤ 1 / 1000) (k12 : |q₂.1| ≤ 1 / 1000)
    (k21 : |q₁.2| ≤ 1 / 1000) (k22 : |q₂.2 - p₂.2| ≤ 1 / 1000) :
    q₁.1 * q₂.2 - q₂.1 * q₁.2 ≠ 0 := by
  have k11' := abs_le.mp k11
  have k22' := abs_le.mp k22
  have h1 : |q₂.1 * q₁.2| ≤ 1 / 1000 * (1 / 1000) := by
    rw [abs_mul]
    exact mul_le_mul k12 k21 (abs_nonneg _) (by norm_num)
  have h2 := (abs_le.mp h1).2
  have hp : p₁.1 = 1 ∧ p₂.1 = 0 := ⟨h11, h12⟩
  clear hp
  apply ne_of_gt
  nlinarith

end Kernels

section Bundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- **The model fibre is a regular sublevel** (interior part). -/
theorem edgeInterp_model_regular {r : ℕ} (j : PartialDiffeomorph I I M Y r) {u₀ : M → ℝ × ℝ}
    (hu₀ : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ u₀) {u : Y → ℝ × ℝ} {b e δ : ℝ} (hb : 0 < b)
    (hval : ∀ x, |(u (j x)).1 - (u₀ x).1| ≤ δ ∧ |(u (j x)).2 - (u₀ x).2| ≤ δ)
    (hrow : ∀ x, |(u₀ x).1| ≤ b + δ → (u₀ x).2 ≤ e + δ → ∃ X : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X).1 = 1 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X).1 - 1| ≤ 1 / 1000) :
    ∀ x, (u₀ x).1 = 0 → 0 ≤ e - (u₀ x).2 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun x => (u₀ x).1) x) := by
  intro x h0 h1
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hval x).1
  obtain ⟨X, hX, -⟩ := hrow x (by rw [h0, abs_zero]; linarith) (by linarith)
  have hX' : (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X).1 ≠ 0 := by rw [hX]; norm_num
  exact surjective_mfderiv_fst_of_apply ((hu₀ x).mdifferentiableAt (by simp)).hasMFDerivAt X hX'

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- **The model fibre is a regular sublevel** (side boundary part). -/
theorem edgeInterp_model_regular_boundary {r : ℕ} (j : PartialDiffeomorph I I M Y r)
    {u₀ : M → ℝ × ℝ} (hu₀ : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ u₀) {u : Y → ℝ × ℝ} {b e δ : ℝ}
    (hb : 0 < b) (hval : ∀ x, |(u (j x)).1 - (u₀ x).1| ≤ δ ∧ |(u (j x)).2 - (u₀ x).2| ≤ δ)
    (hpair : ∀ x, |(u₀ x).1| ≤ b + δ → |(u₀ x).2 - e| ≤ δ → ∃ X₁ X₂ : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).1 = 1 ∧ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).1 = 0 ∧
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).2 = 0 ∧ 1 / 2 ≤ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).1 - 1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).2| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).2 -
        (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2| ≤ 1 / 1000) :
    ∀ x, (u₀ x).1 = 0 → e - (u₀ x).2 = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun x => ((u₀ x).1, e - (u₀ x).2)) x) := by
  intro x h0 h1
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hval x).1
  obtain ⟨X₁, X₂, h11, h12, h21, h22, -, -, -, -⟩ := hpair x (by rw [h0, abs_zero]; linarith)
    (by rw [show (u₀ x).2 - e = 0 by linarith, abs_zero]; exact hδ)
  have hdet : (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).1 * (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2 -
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).1 * (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).2 ≠ 0 := by
    rw [h11, h12, h21]
    linarith
  exact surjective_mfderiv_fst_sub_snd_of_apply ((hu₀ x).mdifferentiableAt (by simp)).hasMFDerivAt
    X₁ X₂ hdet

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- **The source slab is regular at every level of `(-b, b)`** (interior part), through `j`. -/
theorem edgeInterp_source_regular {r : ℕ} (hr : 1 ≤ r) (j : PartialDiffeomorph I I M Y r)
    (hj : j.source = univ) {u₀ : M → ℝ × ℝ} {u : Y → ℝ × ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ u) {b e δ : ℝ}
    (hval : ∀ x, |(u (j x)).1 - (u₀ x).1| ≤ δ ∧ |(u (j x)).2 - (u₀ x).2| ≤ δ)
    (hrow : ∀ x, |(u₀ x).1| ≤ b + δ → (u₀ x).2 ≤ e + δ → ∃ X : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X).1 = 1 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X).1 - 1| ≤ 1 / 1000)
    (henc : ∀ y, |(u y).1| < b → (u y).2 ≤ e → y ∈ j.target) :
    ∀ y, (u y).1 ∈ Ioo (-b) b → 0 ≤ e - (u y).2 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => (u y).1) y) := by
  intro y hy hB
  have hy' : |(u y).1| < b := abs_lt.mpr hy
  have hyt := henc y hy' (by linarith)
  have hjy : j (j.symm y) = y := j.right_inv hyt
  have hx : j.symm y ∈ j.source := by rw [hj]; exact mem_univ _
  set x := j.symm y
  have hv1 := abs_le.mp (hval x).1
  have hv2 := abs_le.mp (hval x).2
  rw [hjy] at hv1 hv2
  obtain ⟨X, -, hX⟩ := hrow x (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
    (by linarith)
  have hr0 : ((r : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hjd : MDifferentiableAt I I j x := j.mdifferentiableAt hr0 hx
  have hud : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) u (j x) := (hu (j x)).mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x := hud.comp x hjd
  have hX' : (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X).1 ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hX
    norm_num at hX
  have hs := surjective_mfderiv_fst_of_apply hw.hasMFDerivAt X hX'
  have h := surjective_mfderiv_of_surjective_mfderiv_comp hr j hx
    (contDiff_fst.contMDiff.comp hu) hs
  rwa [hjy] at h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- **The source slab is regular at every level of `(-b, b)`** (side boundary `H = e`), through
`j`. -/
theorem edgeInterp_source_regular_boundary {r : ℕ} (hr : 1 ≤ r) (j : PartialDiffeomorph I I M Y r)
    (hj : j.source = univ) {u₀ : M → ℝ × ℝ} {u : Y → ℝ × ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ u) {b e δ : ℝ}
    (hval : ∀ x, |(u (j x)).1 - (u₀ x).1| ≤ δ ∧ |(u (j x)).2 - (u₀ x).2| ≤ δ)
    (hpair : ∀ x, |(u₀ x).1| ≤ b + δ → |(u₀ x).2 - e| ≤ δ → ∃ X₁ X₂ : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).1 = 1 ∧ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).1 = 0 ∧
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).2 = 0 ∧ 1 / 2 ≤ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).1 - 1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).2| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).2 -
        (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2| ≤ 1 / 1000)
    (henc : ∀ y, |(u y).1| < b → (u y).2 ≤ e → y ∈ j.target) :
    ∀ y, (u y).1 ∈ Ioo (-b) b → e - (u y).2 = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => ((u y).1, e - (u y).2)) y) := by
  intro y hy hB
  have hy' : |(u y).1| < b := abs_lt.mpr hy
  have hyt := henc y hy' (by linarith)
  have hjy : j (j.symm y) = y := j.right_inv hyt
  have hx : j.symm y ∈ j.source := by rw [hj]; exact mem_univ _
  set x := j.symm y
  have hv1 := abs_le.mp (hval x).1
  have hv2 := abs_le.mp (hval x).2
  rw [hjy] at hv1 hv2
  obtain ⟨X₁, X₂, h11, h12, -, h22, k11, k12, k21, k22⟩ :=
    hpair x (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])
      (by rw [abs_le]; constructor <;> linarith)
  have hr0 : ((r : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hjd : MDifferentiableAt I I j x := j.mdifferentiableAt hr0 hx
  have hud : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) u (j x) := (hu (j x)).mdifferentiableAt (by simp)
  have hw : MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x := hud.comp x hjd
  have hs := surjective_mfderiv_fst_sub_snd_of_apply (e := e) hw.hasMFDerivAt X₁ X₂
    (det_ne_zero_of_near_model h11 h12 h22 k11 k12 k21 k22)
  have hg : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (fun y => ((u y).1, e - (u y).2)) :=
    (contDiff_fst.contMDiff.comp hu).prodMk_space
      ((contDiff_const.sub contDiff_snd).contMDiff.comp hu)
  have h := surjective_mfderiv_of_surjective_mfderiv_comp hr j hx hg hs
  rwa [hjy] at h

/-- Regular sublevel structures defined by equal functions give diffeomorphic sublevels. -/
theorem nonempty_diffeomorph_regularSublevel_of_eq {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ ℝ)
    {Ψ Ψ' B B' : M → ℝ} (hΨ : ContMDiff I 𝓘(ℝ, ℝ) ∞ Ψ) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B)
    (hΨ' : ContMDiff I 𝓘(ℝ, ℝ) ∞ Ψ') (hB' : ContMDiff I 𝓘(ℝ, ℝ) ∞ B')
    (hreg : ∀ x, Ψ x = 0 → 0 ≤ B x → Surjective (mfderiv I 𝓘(ℝ, ℝ) Ψ x))
    (hregb : ∀ x, Ψ x = 0 → B x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (Ψ y, B y)) x))
    (hreg' : ∀ x, Ψ' x = 0 → 0 ≤ B' x → Surjective (mfderiv I 𝓘(ℝ, ℝ) Ψ' x))
    (hregb' : ∀ x, Ψ' x = 0 → B' x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (Ψ' y, B' y)) x))
    (h₁ : Ψ' = Ψ) (h₂ : B' = B) :
    letI := regularSublevelChartedSpace hdim hΨ hB hreg hregb
    letI := regularSublevelChartedSpace hdim hΨ' hB' hreg' hregb'
    Nonempty ({x : M // Ψ x = 0 ∧ 0 ≤ B x} ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
      {x : M // Ψ' x = 0 ∧ 0 ≤ B' x}) := by
  subst h₁ h₂
  let _ := regularSublevelChartedSpace hdim hΨ hB hreg hregb
  exact ⟨Diffeomorph.refl _ _ _⟩

end Bundle

section Main

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  [T2Space Y] [SigmaCompactSpace Y]

/-- **LFR28.1 (abstract form): the source slab is a trivial bundle whose fibre is the model fibre,
with boundary exactly `H = e`.** Model `u₀ = (t, H_N)` on `M`, source `u = (f, H)` on `Y`, an actual
`C^r` diffeomorphism `j` (`3 ≤ r`) defined on all of `M`; values `|u ∘ j - u₀| ≤ δ`; on the model
windows of all levels `|c| < b` the vector hypotheses of `exists_edgeInterp_fibre_isotopy`; the level-0
window inside a compact `Q`; the source slab `{|f| < b, H ≤ e}` inside the image of `j`, and proper
over `(-b, b)`. Then for `-b < a₀ < 0 < b₀ < b`:
1. the model fibre `{t = 0, H_N ≤ e}` and the source fibre `{f = 0, H ≤ e}` (regular sublevels) are
   smoothly diffeomorphic;
2. `f` on `{a₀ < f < b₀, H ≤ e}` is trivial with that fibre: a smooth injective `Θ` over the
   identity of `(a₀, b₀)`, equal to the inclusion over `0`, onto, with smooth inverse data `R`;
3. the boundary points of the source fibre are exactly its points with `H = e`. -/
theorem edgeInterp_disk_bundle {r : ℕ} (hr : 3 ≤ r) {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ ℝ)
    (j : PartialDiffeomorph I I M Y r) (hj : j.source = univ)
    {u₀ : M → ℝ × ℝ} (hu₀ : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ u₀)
    {u : Y → ℝ × ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ u) {b e δ : ℝ}
    (hval : ∀ x, |(u (j x)).1 - (u₀ x).1| ≤ δ ∧ |(u (j x)).2 - (u₀ x).2| ≤ δ)
    (hrow : ∀ x, |(u₀ x).1| ≤ b + δ → (u₀ x).2 ≤ e + δ → ∃ X : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X).1 = 1 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X).1 - 1| ≤ 1 / 1000)
    (hpair : ∀ x, |(u₀ x).1| ≤ b + δ → |(u₀ x).2 - e| ≤ δ → ∃ X₁ X₂ : TangentSpace I x,
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).1 = 1 ∧ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).1 = 0 ∧
      (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₁).2 = 0 ∧ 1 / 2 ≤ (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).1 - 1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).1| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₁).2| ≤ 1 / 1000 ∧
      |(mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x X₂).2 -
        (mfderiv I 𝓘(ℝ, ℝ × ℝ) u₀ x X₂).2| ≤ 1 / 1000)
    {Q : Set M} (hQ : IsCompact Q) (hQw : ∀ x, |(u₀ x).1| ≤ δ → (u₀ x).2 ≤ e + δ → x ∈ Q)
    (henc : ∀ y, |(u y).1| < b → (u y).2 ≤ e → y ∈ j.target)
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-b) b →
      IsCompact ((fun y => (u y).1) ⁻¹' K ∩ {y | 0 ≤ e - (u y).2}))
    {a₀ b₀ : ℝ} (ha₀ : -b < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < b) :
    letI := regularSublevelChartedSpace (Ψ := fun x : M => (u₀ x).1)
      (B := fun x => e - (u₀ x).2) hdim (contDiff_fst.contMDiff.comp hu₀)
      ((contDiff_const.sub contDiff_snd).contMDiff.comp hu₀)
      (edgeInterp_model_regular j hu₀ (by linarith [h0.1, h0.2]) hval hrow)
      (edgeInterp_model_regular_boundary j hu₀ (by linarith [h0.1, h0.2]) hval hpair)
    letI := regularSublevelChartedSpace (Ψ := fun y : Y => (u y).1)
      (B := fun y => e - (u y).2) hdim (contDiff_fst.contMDiff.comp hu)
      ((contDiff_const.sub contDiff_snd).contMDiff.comp hu)
      (fun y hy hB => edgeInterp_source_regular (by omega) j hj hu hval hrow henc y
        (by rw [hy]; exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB)
      (fun y hy hB => edgeInterp_source_regular_boundary (by omega) j hj hu hval hpair henc y
        (by rw [hy]; exact ⟨by linarith [h0.1, h0.2], by linarith [h0.1, h0.2]⟩) hB)
    let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
    Nonempty ({x : M // (u₀ x).1 = 0 ∧ 0 ≤ e - (u₀ x).2} ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
      {y : Y // (u y).1 = 0 ∧ 0 ≤ e - (u y).2}) ∧
    (∃ Θ : {y : Y // (u y).1 = 0 ∧ 0 ≤ e - (u y).2} × Q₀ → Y,
      ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, ℝ)) I ∞ Θ ∧
      (∀ p, (u (Θ p)).1 = p.2 ∧ 0 ≤ e - (u (Θ p)).2) ∧
      (∀ x, Θ (x, ⟨0, h0⟩) = x) ∧ Injective Θ ∧
      ∃ O : Set Y, IsOpen O ∧ (∀ y, (u y).1 ∈ Ioo a₀ b₀ → 0 ≤ e - (u y).2 → y ∈ O) ∧
        ∃ R : Y → Y, ContMDiffOn I I ∞ R O ∧
          ∀ y (hy : (u y).1 ∈ Ioo a₀ b₀), 0 ≤ e - (u y).2 →
            ∃ hR : (u (R y)).1 = 0 ∧ 0 ≤ e - (u (R y)).2, Θ (⟨R y, hR⟩, ⟨(u y).1, hy⟩) = y) ∧
    ∀ y : {y : Y // (u y).1 = 0 ∧ 0 ≤ e - (u y).2},
      (𝓡∂ (d + 1)).IsBoundaryPoint y ↔ (u y).2 = e := by
  have hb : 0 < b := by linarith [h0.1, h0.2]
  have hr1 : 1 ≤ r := by omega
  have hr0 : ((r : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hjs : ContMDiff I I r j := by
    have h := j.contMDiffOn
    rw [hj] at h
    exact contMDiffOn_univ.mp h
  have hur : ContMDiff I 𝓘(ℝ, ℝ × ℝ) r u := hu.of_le (by exact_mod_cast le_top)
  have hwr : ContMDiff I 𝓘(ℝ, ℝ × ℝ) r (fun z => u (j z)) := hur.comp hjs
  have hdu₀ : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) u₀ x := fun x =>
    (hu₀ x).mdifferentiableAt (by simp)
  have hdw : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (fun z => u (j z)) x := fun x =>
    (hwr x).mdifferentiableAt hr0
  set F : ℝ × M → ℝ × ℝ := fun q => (1 - q.1) • u₀ q.2 + q.1 • u (j q.2) with hFdef
  have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × ℝ) r F (Icc 0 1 ×ˢ univ) := by
    have h1 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) r (fun q : ℝ × M => 1 - q.1) :=
      contMDiff_const.sub contMDiff_fst
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × ℝ) r (fun q : ℝ × M => u₀ q.2) :=
      (hu₀.of_le (by exact_mod_cast le_top)).comp contMDiff_snd
    have h3 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × ℝ) r (fun q : ℝ × M => u (j q.2)) :=
      hwr.comp contMDiff_snd
    exact ((h1.smul h2).add (contMDiff_fst.smul h3)).contMDiffOn
  have hF0e : (fun x => F (0, x)) = u₀ := funext fun x => by simp [hFdef]
  have hF0 : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => F (0, x)) := by rw [hF0e]; exact hu₀
  have hF1 : ∀ x, F (1, x) = u (j x) := fun x => by simp [hFdef]
  have hφ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => y.1) := contDiff_fst
  have hβ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => e - y.2) := contDiff_const.sub contDiff_snd
  have hwin : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (F (t, x)).1 = 0 → 0 ≤ e - (F (t, x)).2 →
      |(u₀ x).1| ≤ δ ∧ (u₀ x).2 ≤ e + δ := by
    intro t ht x h1 h2
    have h1' : ((1 - t) • u₀ x + t • (fun z => u (j z)) x).1 = 0 := h1
    have h2' : ((1 - t) • u₀ x + t • (fun z => u (j z)) x).2 ≤ e := by
      change 0 ≤ e - ((1 - t) • u₀ x + t • (fun z => u (j z)) x).2 at h2
      linarith
    have h := edgeInterp_mem_window (w := fun z => u (j z)) ht (hval x).1 (hval x).2 h1' h2'
    rw [sub_zero] at h
    exact h
  have htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (fun y : ℝ × ℝ => y.1) (F (t, x)) = 0 →
      0 ≤ (fun y : ℝ × ℝ => e - y.2) (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => (fun y : ℝ × ℝ => y.1) (F (t, y))) x) := by
    intro t ht x h1 h2
    obtain ⟨hw1, hw2⟩ := hwin t ht x h1 h2
    have hδ : 0 ≤ δ := (abs_nonneg _).trans (hval x).1
    obtain ⟨X, hX1, hX2⟩ := hrow x (by linarith) hw2
    have h := edgeInterp_surjective_fst (c := 0) (hdu₀ x).hasMFDerivAt (hdw x).hasMFDerivAt ht X
      hX1 hX2
    have heq : (fun y => ((1 - t) • u₀ y + t • u (j y)).1 - 0) =
        (fun y => (fun y : ℝ × ℝ => y.1) (F (t, y))) := funext fun y => sub_zero _
    rwa [heq] at h
  have htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (fun y : ℝ × ℝ => y.1) (F (t, x)) = 0 →
      (fun y : ℝ × ℝ => e - y.2) (F (t, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => ((fun y : ℝ × ℝ => y.1) (F (t, y)),
        (fun y : ℝ × ℝ => e - y.2) (F (t, y)))) x) := by
    intro t ht x h1 h2
    obtain ⟨hw1, -⟩ := hwin t ht x h1 h2.ge
    have hδ : 0 ≤ δ := (abs_nonneg _).trans (hval x).1
    have hw3 := edgeInterp_mem_boundary_window (u₀ := u₀) (w := fun z => u (j z)) ht (hval x).2
      (show ((1 - t) • u₀ x + t • (fun z => u (j z)) x).2 = e by
        change e - ((1 - t) • u₀ x + t • (fun z => u (j z)) x).2 = 0 at h2
        linarith)
    obtain ⟨X₁, X₂, h11, h12, h21, h22, k11, k12, k21, k22⟩ := hpair x (by linarith) hw3
    have h := edgeInterp_surjective_pair (c := 0) (e := e) (hdu₀ x).hasMFDerivAt
      (hdw x).hasMFDerivAt ht X₁ X₂ h11 h12 h21 h22 k11 k12 k21 k22
    have heq : (fun y => (((1 - t) • u₀ y + t • u (j y)).1 - 0,
        e - ((1 - t) • u₀ y + t • u (j y)).2)) =
        (fun y => ((fun y : ℝ × ℝ => y.1) (F (t, y)), (fun y : ℝ × ℝ => e - y.2) (F (t, y)))) :=
      funext fun y => Prod.ext (sub_zero _) rfl
    rwa [heq] at h
  have hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (fun y : ℝ × ℝ => y.1) (F (t, x)) = 0 →
      0 ≤ (fun y : ℝ × ℝ => e - y.2) (F (t, x)) → x ∈ Q := fun t ht x h1 h2 =>
    hQw x (hwin t ht x h1 h2).1 (hwin t ht x h1 h2).2
  have henc0 : ∀ y, (fun y : ℝ × ℝ => y.1) (u y) = 0 → 0 ≤ (fun y : ℝ × ℝ => e - y.2) (u y) →
      y ∈ j.target := fun y h1 h2 => henc y (by
        change (u y).1 = 0 at h1
        rw [h1, abs_zero]
        exact hb) (by change 0 ≤ e - (u y).2 at h2; linarith)
  let cU := regularSublevelChartedSpace (Ψ := fun x => (fun y : ℝ × ℝ => y.1) (F (0, x)))
    (B := fun x => (fun y : ℝ × ℝ => e - y.2) (F (0, x))) hdim (hφ.contMDiff.comp hF0)
    (hβ.contMDiff.comp hF0) (htrans 0 (left_mem_Icc.2 zero_le_one))
    (htransb 0 (left_mem_Icc.2 zero_le_one))
  have : IsManifold (𝓡∂ (d + 1)) ∞
      {x : M // (fun y : ℝ × ℝ => y.1) (F (0, x)) = 0 ∧
        0 ≤ (fun y : ℝ × ℝ => e - y.2) (F (0, x))} :=
    regularSublevel_isManifold (Ψ := fun x => (fun y : ℝ × ℝ => y.1) (F (0, x)))
      (B := fun x => (fun y : ℝ × ℝ => e - y.2) (F (0, x))) hdim (hφ.contMDiff.comp hF0)
      (hβ.contMDiff.comp hF0) _ _
  have hc : Continuous fun x => F (0, x) := hF0.continuous
  have hS : IsCompact {x : M | (fun y : ℝ × ℝ => y.1) (F (0, x)) = 0 ∧
      0 ≤ (fun y : ℝ × ℝ => e - y.2) (F (0, x))} := by
    refine hQ.of_isClosed_subset ?_ fun x hx =>
      hencl 0 (left_mem_Icc.2 zero_le_one) x hx.1 hx.2
    exact (isClosed_eq (hφ.continuous.comp hc) continuous_const).inter
      (isClosed_le continuous_const (hβ.continuous.comp hc))
  have : CompactSpace {x : M // (fun y : ℝ × ℝ => y.1) (F (0, x)) = 0 ∧
      0 ≤ (fun y : ℝ × ℝ => e - y.2) (F (0, x))} := isCompact_iff_compactSpace.mp hS
  obtain ⟨⟨e₁⟩, hΘ, -⟩ := lfr05_bundle_trivial_over_interval hr hdim j hj hu hF hF0 hφ hβ hF1
    htrans htransb hQ hencl henc0 (Diffeomorph.refl _ _ _)
    (edgeInterp_source_regular hr1 j hj hu hval hrow henc)
    (edgeInterp_source_regular_boundary hr1 j hj hu hval hpair henc) hprop ha₀ h0 hb₀
  obtain ⟨e₀⟩ := nonempty_diffeomorph_regularSublevel_of_eq hdim
    (Ψ := fun x => (u₀ x).1) (B := fun x => e - (u₀ x).2)
    (Ψ' := fun x => (fun y : ℝ × ℝ => y.1) (F (0, x)))
    (B' := fun x => (fun y : ℝ × ℝ => e - y.2) (F (0, x)))
    (contDiff_fst.contMDiff.comp hu₀) ((contDiff_const.sub contDiff_snd).contMDiff.comp hu₀)
    (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
    (edgeInterp_model_regular j hu₀ hb hval hrow)
    (edgeInterp_model_regular_boundary j hu₀ hb hval hpair)
    (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
    (funext fun x => by simp [hFdef]) (funext fun x => by simp [hFdef])
  have hregS := edgeInterp_source_regular hr1 j hj hu hval hrow henc
  have hregbS := edgeInterp_source_regular_boundary hr1 j hj hu hval hpair henc
  have hPs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => (u y).1) := contDiff_fst.contMDiff.comp hu
  have hBs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => e - (u y).2) :=
    (contDiff_const.sub contDiff_snd).contMDiff.comp hu
  have hreg0 : ∀ y, (u y).1 = 0 → 0 ≤ e - (u y).2 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => (u y).1) y) := fun y hy hB =>
    hregS y (by rw [hy]; exact ⟨by linarith, hb⟩) hB
  have hregb0 : ∀ y, (u y).1 = 0 → e - (u y).2 = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => ((u y).1, e - (u y).2)) y) := fun y hy hB =>
    hregbS y (by rw [hy]; exact ⟨by linarith, hb⟩) hB
  let _ := regularSublevelChartedSpace (Ψ := fun x : M => (u₀ x).1)
    (B := fun x => e - (u₀ x).2) hdim (contDiff_fst.contMDiff.comp hu₀)
    ((contDiff_const.sub contDiff_snd).contMDiff.comp hu₀)
    (edgeInterp_model_regular j hu₀ hb hval hrow)
    (edgeInterp_model_regular_boundary j hu₀ hb hval hpair)
  let _ := regularSublevelChartedSpace (Ψ := fun y : Y => (u y).1)
    (B := fun y => e - (u y).2) hdim hPs hBs hreg0 hregb0
  refine ⟨⟨e₀.trans e₁⟩, hΘ, fun y => ?_⟩
  refine (regularSublevel_isBoundaryPoint_iff (Ψ := fun y : Y => (u y).1)
    (B := fun y => e - (u y).2) hdim hPs hBs hreg0 hregb0).trans ?_
  change e - (u y).2 = 0 ↔ (u y).2 = e
  constructor <;> intro h <;> linarith

end Main

end DifferentialGeometry.Geometry.Collapse
