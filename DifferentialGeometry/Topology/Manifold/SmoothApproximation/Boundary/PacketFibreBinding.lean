import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.BufferedFibreStability
import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelSlice
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.EmptyBoundary

/-!
# LFR05: the interpolation on `[0, 1]` and the fibres as manifolds with boundary

Blueprint LFR05 (`master207A.tex`, label `prop:collapse-finite-packet-consumer`):

* `lfr05_exists_isotopy_image_source_fibre_Icc` — the ambient part with the interpolation `F`
  given only on `[0, 1] × M` (jointly `C^r`, `2 ≤ r`) and transversality only for `t ∈ [0, 1]`;
  this removes the deviation "`F` on `ℝ × M`" of W-2b's `lfr05_exists_isotopy_image_source_fibre`,
  using W5-FLOW2's LFR03 (`lfr03_exists_isotopy_fibre`, time reparametrised by
  `Real.smoothTransition`).
* `lfr05_nonempty_diffeomorph_source_fibre` — with the model-to-source map an actual `C^r`
  diffeomorphism `j` onto its open image (`PartialDiffeomorph` with source `univ`), a smooth source
  map `f` and a smooth model map `F (0, ·)`, the model fibre `{φ ∘ F (0, ·) = 0, β ∘ F (0, ·) ≥ 0}`
  and the ENTIRE source fibre `{φ ∘ f = 0, β ∘ f ≥ 0}` — both with the manifold-with-boundary
  structure of lane SUB-BDY (`regularSublevelChartedSpace`) — are `C^{r-1}` diffeomorphic, by the
  restriction of `j ∘ Φ`.
* `lfr05_nonempty_diffeomorph_fibre_type` — hence a compact fibre `H` that is `C^{r-1}`
  diffeomorphic to the model fibre is `C^{r-1}` diffeomorphic to the source fibre;
  `lfr05_nonempty_smooth_diffeomorph_of_boundary_eq_empty` — smoothly when `∂H = ∅` (W-2b's
  empty-boundary LFR04); the with-boundary smooth type is LFR04 with boundary (collar straightening,
  lane W-2c).
* consumer `lfr05_point_nonempty_smooth_diffeomorph` — point fibres (`β = 1`): the source fibre is
  smoothly diffeomorphic to `H`, with no boundary hypothesis.

Regularity of the source fibre is derived (`lfr05_source_regular`, `lfr05_source_regular_boundary`)
from transversality at time `1` and `F (1, ·) = f ∘ j`; it is not assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.Manifold.RegularLevel

section Ambient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SigmaCompactSpace M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **LFR05, ambient part, interpolation on `[0, 1]`.** The model-to-source map composed with the
compactly supported `C^{r-1}` isotopy of LFR03 carries the model fibre onto the entire source
fibre, side boundary onto side boundary. -/
theorem lfr05_exists_isotopy_image_source_fibre_Icc {r : ℕ} (hr : 2 ≤ r)
    {Y : Type*} (j : M → Y) {f : Y → E'} {F : ℝ × M → E'}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → β (F (t, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q)
    (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) → x ∈ Q)
    {N : Set M} (hN : IsOpen N)
    (hNsub : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) → x ∈ N)
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ range j) :
    ∃ (K : Set M) (Φ : M ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮I, I⟯ M), IsCompact K ∧ K ⊆ N ∧
      (∀ x ∉ K, Φ x = x) ∧
      (fun x => j (Φ x)) '' {x | φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} =
        {y | φ (f y) = 0 ∧ 0 ≤ β (f y)} ∧
      (fun x => j (Φ x)) '' {x | φ (F (0, x)) = 0 ∧ β (F (0, x)) = 0} =
        {y | φ (f y) = 0 ∧ β (f y) = 0} := by
  obtain ⟨K, Φ, hK, hKN, -, -, hid, -, -, himg, hbimg⟩ :=
    DifferentialGeometry.Analysis.ODE.lfr03_exists_isotopy_fibre hr hF hφ hβ
      (X := {y | φ y = 0 ∧ 0 ≤ β y}) (Xb := {y | φ y = 0 ∧ β y = 0}) rfl rfl
      (fun t ht x hx => htrans t ht x hx.1 hx.2) (fun t ht x hx => htransb t ht x hx.1 hx.2) hQ
      (fun t ht x hx => hencl t ht x hx.1 hx.2) hN (fun t ht x hx => hNsub t ht x hx.1 hx.2)
  refine ⟨K, Φ 1, hK, hKN, fun x hx => hid 1 x hx, ?_, ?_⟩
  · rw [← image_image j (Φ 1)]
    change j '' (Φ 1 '' {x | F (0, x) ∈ {y | φ y = 0 ∧ 0 ≤ β y}}) = _
    rw [himg]
    have hpre : {x | F (1, x) ∈ {y | φ y = 0 ∧ 0 ≤ β y}} =
        j ⁻¹' {y | φ (f y) = 0 ∧ 0 ≤ β (f y)} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, hF1]
    rw [hpre, image_preimage_eq_inter_range, inter_eq_left]
    exact fun y hy => henc y hy.1 hy.2
  · rw [← image_image j (Φ 1)]
    change j '' (Φ 1 '' {x | F (0, x) ∈ {y | φ y = 0 ∧ β y = 0}}) = _
    rw [hbimg]
    have hpre : {x | F (1, x) ∈ {y | φ y = 0 ∧ β y = 0}} =
        j ⁻¹' {y | φ (f y) = 0 ∧ β (f y) = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, hF1]
    rw [hpre, image_preimage_eq_inter_range, inter_eq_left]
    exact fun y hy => henc y hy.1 hy.2.ge

end Ambient

section Fibres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [FiniteDimensional ℝ G] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- Surjectivity of a derivative descends from a composite with a differentiable map. -/
theorem surjective_mfderiv_of_surjective_mfderiv_comp {G₁ : Type*} [NormedAddCommGroup G₁]
    [NormedSpace ℝ G₁] {r : ℕ} (hr : 1 ≤ r) (j : PartialDiffeomorph I I M Y r) {x : M}
    (hx : x ∈ j.source) {g : Y → G₁} (hg : ContMDiff I 𝓘(ℝ, G₁) ∞ g)
    (hs : Surjective (mfderiv I 𝓘(ℝ, G₁) (fun y => g (j y)) x)) :
    Surjective (mfderiv I 𝓘(ℝ, G₁) g (j x)) := by
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : r ≠ 0 := by omega
    exact_mod_cast this
  have hjd : MDifferentiableAt I I j x := j.mdifferentiableAt hr0 hx
  have hgd : MDifferentiableAt I 𝓘(ℝ, G₁) g (j x) := hg.mdifferentiableAt (by simp)
  have hc : mfderiv I 𝓘(ℝ, G₁) (fun y => g (j y)) x =
      (mfderiv I 𝓘(ℝ, G₁) g (j x)).comp (mfderiv I I j x) :=
    mfderiv_comp x hgd hjd
  rw [hc, ContinuousLinearMap.coe_comp] at hs
  exact hs.of_comp

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [FiniteDimensional ℝ G] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- Regularity of the source fibre, derived from transversality at time `1`. -/
theorem lfr05_source_regular {r : ℕ} (hr : 1 ≤ r) (j : PartialDiffeomorph I I M Y r)
    (hj : j.source = univ) {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans1 : ∀ x, φ (F (1, x)) = 0 → 0 ≤ β (F (1, x)) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (1, y))) x))
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ j.target) :
    ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (f y)) y) := by
  intro y h0 h1
  have hy := henc y h0 h1
  have hjy : j (j.symm y) = y := j.right_inv hy
  have hx : j.symm y ∈ j.source := by rw [hj]; exact mem_univ _
  have hfun : (fun z => φ (F (1, z))) = fun z => φ (f (j z)) := funext fun z => by rw [hF1]
  have hs := htrans1 (j.symm y) (by rw [hF1, hjy]; exact h0) (by rw [hF1, hjy]; exact h1)
  rw [hfun] at hs
  have h := surjective_mfderiv_of_surjective_mfderiv_comp hr j hx (hφ.contMDiff.comp hf) hs
  rwa [hjy] at h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [FiniteDimensional ℝ G] [IsManifold I ∞ M] [IsManifold I ∞ Y] in
/-- Regularity of the side boundary of the source fibre, derived from transversality at time `1`. -/
theorem lfr05_source_regular_boundary {r : ℕ} (hr : 1 ≤ r) (j : PartialDiffeomorph I I M Y r)
    (hj : j.source = univ) {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htransb1 : ∀ x, φ (F (1, x)) = 0 → β (F (1, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (1, y)), β (F (1, y)))) x))
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ j.target) :
    ∀ y, φ (f y) = 0 → β (f y) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (f y), β (f y))) y) := by
  intro y h0 h1
  have hy := henc y h0 h1.ge
  have hjy : j (j.symm y) = y := j.right_inv hy
  have hx : j.symm y ∈ j.source := by rw [hj]; exact mem_univ _
  have hfun : (fun z => (φ (F (1, z)), β (F (1, z)))) = fun z => (φ (f (j z)), β (f (j z))) :=
    funext fun z => by rw [hF1]
  have hs := htransb1 (j.symm y) (by rw [hF1, hjy]; exact h0) (by rw [hF1, hjy]; exact h1)
  rw [hfun] at hs
  have hg : ContMDiff I 𝓘(ℝ, G × ℝ) ∞ (fun y => (φ (f y), β (f y))) :=
    (hφ.contMDiff.comp hf).prodMk_space (hβ.contMDiff.comp hf)
  have h := surjective_mfderiv_of_surjective_mfderiv_comp hr j hx hg hs
  rwa [hjy] at h

/-- **LFR05, fibre clause in finite regularity.** For an actual `C^r` model-to-source
diffeomorphism `j` onto its open image (defined on the whole model domain), a smooth source map
`f`, a smooth model map `F (0, ·)` and a jointly `C^r` interpolation `F` on `[0, 1] × M` satisfying
LFR03, with the entire source fibre in the image of `j`, the model fibre and the source fibre
(manifolds with boundary by lane SUB-BDY's `regularSublevelChartedSpace`) are `C^{r-1}`
diffeomorphic. -/
theorem lfr05_nonempty_diffeomorph_source_fibre {r : ℕ} (hr : 2 ≤ r) {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    (j : PartialDiffeomorph I I M Y r) (hj : j.source = univ)
    {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    (hF0 : ContMDiff I 𝓘(ℝ, E') ∞ (fun x => F (0, x)))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → β (F (t, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q)
    (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) → x ∈ Q)
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ j.target) :
    letI := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x))) (B := fun x => β (F (0, x)))
      hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
      (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
    letI := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
        henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
    Nonempty ({x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮
      𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯ {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) := by
  obtain ⟨-, Φ, -, -, -, -, -, -, -, himg, -⟩ :=
    DifferentialGeometry.Analysis.ODE.lfr03_exists_isotopy_fibre hr hF hφ hβ
      (X := {y | φ y = 0 ∧ 0 ≤ β y}) (Xb := {y | φ y = 0 ∧ β y = 0}) rfl rfl
      (fun t ht x hx => htrans t ht x hx.1 hx.2) (fun t ht x hx => htransb t ht x hx.1 hx.2) hQ
      (fun t ht x hx => hencl t ht x hx.1 hx.2) isOpen_univ (fun _ _ _ _ => mem_univ _)
  set P := Φ 1 with hP
  let c₀ := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
    (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
    (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
  let c₁ := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
    hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
    (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
      henc)
    (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
      (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
  have hr1 : (((r - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast Nat.sub_le r 1
  have hjsm : ContMDiff I I ((r - 1 : ℕ) : WithTop ℕ∞) j := by
    have h : ContMDiffOn I I r j univ := by rw [← hj]; exact j.contMDiffOn
    exact (contMDiffOn_univ.mp h).of_le hr1
  have hjsymm : ContMDiffOn I I ((r - 1 : ℕ) : WithTop ℕ∞) j.symm j.target :=
    j.symm.contMDiffOn.of_le hr1
  -- membership
  have hto : ∀ x : {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))},
      φ (f (j (P x))) = 0 ∧ 0 ≤ β (f (j (P x))) := by
    intro x
    have hmem : P x.1 ∈ {x | F (1, x) ∈ {y | φ y = 0 ∧ 0 ≤ β y}} := by
      rw [hP, ← himg]
      exact mem_image_of_mem _ x.2
    have h : φ (F (1, P x.1)) = 0 ∧ 0 ≤ β (F (1, P x.1)) := hmem
    rwa [hF1] at h
  have hinvmem : ∀ y : {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)},
      φ (F (0, P.symm (j.symm y))) = 0 ∧ 0 ≤ β (F (0, P.symm (j.symm y))) := by
    intro y
    have hy := henc y.1 y.2.1 y.2.2
    have hjy : j (j.symm y) = y := j.right_inv hy
    have hmem : j.symm y.1 ∈ {x | F (1, x) ∈ {y | φ y = 0 ∧ 0 ≤ β y}} := by
      change φ (F (1, j.symm y.1)) = 0 ∧ 0 ≤ β (F (1, j.symm y.1))
      rw [hF1, hjy]
      exact y.2
    rw [← himg] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    rw [← hxe, P.symm_apply_apply]
    exact hx
  let e : {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} ≃
      {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} :=
    { toFun := fun x => ⟨j (P x), hto x⟩
      invFun := fun y => ⟨P.symm (j.symm y), hinvmem y⟩
      left_inv := fun x => by
        apply Subtype.ext
        change P.symm (j.toPartialEquiv.symm (j.toPartialEquiv (P x.1))) = x.1
        have hx : P x.1 ∈ j.source := by rw [hj]; exact mem_univ _
        rw [j.toPartialEquiv.left_inv hx, P.symm_apply_apply]
      right_inv := fun y => by
        apply Subtype.ext
        change j.toPartialEquiv (P (P.symm (j.toPartialEquiv.symm y.1))) = y.1
        rw [P.apply_symm_apply]
        exact j.toPartialEquiv.right_inv (henc y.1 y.2.1 y.2.2) }
  refine ⟨{ toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }⟩
  · apply (regularSublevel_contMDiff_iff (Ψ := fun y => φ (f y)) (B := fun y => β (f y)) hdim
      (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf) _ _ (n := ((r - 1 : ℕ) : ℕ∞))).mpr
    have hval := (regularSublevel_contMDiff_val (Ψ := fun x => φ (F (0, x)))
      (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
      (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))).of_le
      (show (((r - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast le_top)
    exact hjsm.comp (P.contMDiff.comp hval)
  · apply (regularSublevel_contMDiff_iff (Ψ := fun x => φ (F (0, x)))
      (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0) _ _
      (n := ((r - 1 : ℕ) : ℕ∞))).mpr
    have hval := (regularSublevel_contMDiff_val (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1
        (htrans 1 (right_mem_Icc.2 zero_le_one)) henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)).of_le
      (show (((r - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ∞ from by exact_mod_cast le_top)
    exact P.symm.contMDiff.comp (hjsymm.comp_contMDiff hval
      (fun y => henc y.1 y.2.1 y.2.2))

/-- **LFR05, fibre type in finite regularity.** A compact fibre `Hf` that is `C^{r-1}`
diffeomorphic to the model fibre is `C^{r-1}` diffeomorphic to the entire source fibre. -/
theorem lfr05_nonempty_diffeomorph_fibre_type {r : ℕ} (hr : 2 ≤ r) {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    (j : PartialDiffeomorph I I M Y r) (hj : j.source = univ)
    {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    (hF0 : ContMDiff I 𝓘(ℝ, E') ∞ (fun x => F (0, x)))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → β (F (t, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q)
    (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) → x ∈ Q)
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ j.target)
    {Hf : Type*} [TopologicalSpace Hf] [ChartedSpace (EuclideanHalfSpace (d + 1)) Hf]
    (ψ :
      letI := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
        (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
        (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
      Hf ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
        {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))}) :
    letI := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
        henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
    Nonempty (Hf ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
      {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) := by
  let c₀ := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
    (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
    (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
  let c₁ := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
    hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
    (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
      henc)
    (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
      (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
  obtain ⟨e⟩ := lfr05_nonempty_diffeomorph_source_fibre hr hdim j hj hf hF hF0 hφ hβ hF1 htrans
    htransb hQ hencl henc
  exact ⟨ψ.trans e⟩

/-- **LFR05, smooth fibre type when the fibre `Hf` has empty boundary** (via W-2b's
empty-boundary LFR04; the with-boundary case is LFR04 with collar straightening). -/
theorem lfr05_nonempty_smooth_diffeomorph_of_boundary_eq_empty {r : ℕ} (hr : 2 ≤ r) {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    (j : PartialDiffeomorph I I M Y r) (hj : j.source = univ)
    {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    (hF0 : ContMDiff I 𝓘(ℝ, E') ∞ (fun x => F (0, x)))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → β (F (t, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q)
    (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) → x ∈ Q)
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ j.target)
    {Hf : Type*} [TopologicalSpace Hf] [ChartedSpace (EuclideanHalfSpace (d + 1)) Hf]
    [IsManifold (𝓡∂ (d + 1)) ∞ Hf] [T2Space Hf] [CompactSpace Hf]
    (ψ :
      letI := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
        (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
        (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
      Hf ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
        {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))})
    (hHb : (𝓡∂ (d + 1)).boundary Hf = ∅) :
    letI := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
        henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
    Nonempty (Hf ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯ {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) := by
  let c₁ := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
    hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
    (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
      henc)
    (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
      (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
  have : IsManifold (𝓡∂ (d + 1)) ∞ {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} :=
    regularSublevel_isManifold (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf) _ _
  obtain ⟨e⟩ := lfr05_nonempty_diffeomorph_fibre_type hr hdim j hj hf hF hF0 hφ hβ hF1 htrans
    htransb hQ hencl henc ψ
  exact nonempty_diffeomorph_of_diffeomorph_of_boundary_eq_empty (n := d) (k := r - 1)
    (by omega) e hHb

/-- **Consumer: LFR05 with empty side boundary** (e.g. point fibres, `β = 1`). When `β > 0`, a
compact fibre `Hf` that is `C^{r-1}` diffeomorphic to the model fibre is SMOOTHLY diffeomorphic to
the entire source fibre; no boundary hypothesis on `Hf` is needed. -/
theorem lfr05_nonempty_smooth_diffeomorph_of_pos {r : ℕ} (hr : 2 ≤ r) {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ G)
    (j : PartialDiffeomorph I I M Y r) (hj : j.source = univ)
    {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    (hF0 : ContMDiff I 𝓘(ℝ, E') ∞ (fun x => F (0, x)))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβpos : ∀ v, 0 < β v) (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    {Q : Set M} (hQ : IsCompact Q)
    (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) → x ∈ Q)
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ j.target)
    {Hf : Type*} [TopologicalSpace Hf] [ChartedSpace (EuclideanHalfSpace (d + 1)) Hf]
    [IsManifold (𝓡∂ (d + 1)) ∞ Hf] [T2Space Hf] [CompactSpace Hf]
    (ψ :
      letI := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
        (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
        (htrans 0 (left_mem_Icc.2 zero_le_one))
        (fun x _ h1 => absurd h1 (hβpos (F (0, x))).ne')
      Hf ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
        {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))}) :
    letI := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
        henc)
      (fun y _ h1 => absurd h1 (hβpos (f y)).ne')
    Nonempty (Hf ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯ {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) := by
  let c₀ := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
    (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
    (htrans 0 (left_mem_Icc.2 zero_le_one)) (fun x _ h1 => absurd h1 (hβpos (F (0, x))).ne')
  have : IsManifold (𝓡∂ (d + 1)) ∞ {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} :=
    regularSublevel_isManifold (Ψ := fun x => φ (F (0, x))) (B := fun x => β (F (0, x)))
      hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0) _ _
  have hk0 : ((r - 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by
    have : r - 1 ≠ 0 := by omega
    exact_mod_cast this
  have hHb : (𝓡∂ (d + 1)).boundary Hf = ∅ := by
    ext x
    simp only [mem_empty_iff_false, iff_false]
    intro hx
    have h1 := ((ψ.isLocalDiffeomorph x).isBoundaryPoint_iff hk0).mp hx
    have h2 := (regularSublevel_isBoundaryPoint_iff (Ψ := fun x => φ (F (0, x)))
      (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
      (htrans 0 (left_mem_Icc.2 zero_le_one))
      (fun x _ h1 => absurd h1 (hβpos (F (0, x))).ne')).mp h1
    exact (hβpos _).ne' h2
  exact lfr05_nonempty_smooth_diffeomorph_of_boundary_eq_empty hr hdim j hj hf hF hF0 hφ hβ hF1
    htrans (fun t _ x _ h1 => absurd h1 (hβpos (F (t, x))).ne') hQ hencl henc ψ hHb

end Fibres

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
