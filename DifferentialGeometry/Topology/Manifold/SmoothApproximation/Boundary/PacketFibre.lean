import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.RegularSublevelIsotopy
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Applications

/-!
# LFR05, the part independent of fibre manifold structures

`lfr05_exists_isotopy_image_source_fibre` (blueprint LFR05, first sentence of the proof: "Apply
LFR03 on the model domain and then the actual embedding to the terminal fiber. The source
enclosure ensures that this image is the entire source fiber"): on the model domain `M`
(boundaryless, `σ`-compact), a time-dependent map `F : ℝ × M → G` of class `C^{r+1}` that is
transverse to `X = {φ = 0, β ≥ 0}` and to `∂X = {φ = 0, β = 0}` for every time, with all fibres
in one compact `S ⊆ N`, and with `F (1, ·) = f ∘ j` for the source map `f` and the model-to-source
map `j`, yields a `C^r` diffeomorphism `Φ` of `M`, the identity off a compact `K ⊆ N`, such that
`j ∘ Φ` maps the model fibre `F (0, ·)⁻¹ X` ONTO the entire source fibre `f⁻¹ X` and the model
side boundary onto the source side boundary, provided the source fibre lies in the range of `j`.

The isotopy is W5-FLOW2's kernel C (`exists_isotopy_regularSublevel_Cn`). The remaining LFR05
steps need (b) a manifold-with-boundary structure on the fibres (shared lane SUB-BDY; exact form in
`build-logs/resume/state-W-2b.md`) and LFR04 in the with-boundary case (collar straightening,
see `build-logs/worker-W-2b.md`).

Strengthening: no hypothesis on `j` is used (the image identity holds for any map `j`); the
regularity of `j` enters only when the fibres are compared as manifolds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SigmaCompactSpace M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G'] [FiniteDimensional ℝ G']

/-- **LFR05, ambient part.** The model-to-source map composed with the compactly supported `C^r`
isotopy of the moving fibre carries the model fibre onto the entire source fibre, side boundary
onto side boundary. -/
theorem lfr05_exists_isotopy_image_source_fibre {r : ℕ} (hr : 1 ≤ r)
    {Y : Type*} (j : M → Y) {f : Y → G} {φ : G → G'} {β : G → ℝ}
    {F : ℝ × M → G} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) (r + 1) F)
    (hφ : ContDiff ℝ (r + 1) φ) (hβ : ContDiff ℝ (r + 1) β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ q : ℝ × M, φ (F q) = 0 → 0 ≤ β (F q) →
      Surjective (mfderiv I 𝓘(ℝ, G') (fun y => φ (F (q.1, y))) q.2))
    (htransb : ∀ q : ℝ × M, φ (F q) = 0 → β (F q) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G' × ℝ) (fun y => (φ (F (q.1, y)), β (F (q.1, y)))) q.2))
    {S : Set M} (hS : IsCompact S) (hWS : ∀ q : ℝ × M, φ (F q) = 0 → 0 ≤ β (F q) → q.2 ∈ S)
    {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N)
    (henc : ∀ y, φ (f y) = 0 → 0 ≤ β (f y) → y ∈ range j) :
    ∃ (K : Set M) (Φ : M ≃ₘ^r⟮I, I⟯ M), IsCompact K ∧ K ⊆ N ∧ (∀ x ∉ K, Φ x = x) ∧
      (fun x => j (Φ x)) '' {x | φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} =
        {y | φ (f y) = 0 ∧ 0 ≤ β (f y)} ∧
      (fun x => j (Φ x)) '' {x | φ (F (0, x)) = 0 ∧ β (F (0, x)) = 0} =
        {y | φ (f y) = 0 ∧ β (f y) = 0} := by
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G') (r + 1) (fun q => φ (F q)) :=
    hφ.contMDiff.comp hF
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (r + 1) (fun q => β (F q)) :=
    hβ.contMDiff.comp hF
  obtain ⟨K, Φ, hK, hKN, -, -, hid, himg, hbimg⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_isotopy_regularSublevel_Cn hr hΨ hB htrans htransb
      hS hWS hN hSN
  refine ⟨K, Φ 0 1, hK, hKN, hid 0 1, ?_, ?_⟩
  · rw [← image_image j (Φ 0 1), himg 0 1]
    have hpre : {x | φ (F (1, x)) = 0 ∧ 0 ≤ β (F (1, x))} =
        j ⁻¹' {y | φ (f y) = 0 ∧ 0 ≤ β (f y)} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, hF1]
    rw [hpre, image_preimage_eq_inter_range, inter_eq_left]
    exact fun y hy => henc y hy.1 hy.2
  · rw [← image_image j (Φ 0 1), hbimg 0 1]
    have hpre : {x | φ (F (1, x)) = 0 ∧ β (F (1, x)) = 0} =
        j ⁻¹' {y | φ (f y) = 0 ∧ β (f y) = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, hF1]
    rw [hpre, image_preimage_eq_inter_range, inter_eq_left]
    exact fun y hy => henc y hy.1 hy.2.ge

/-- **LFR05, ambient part, point fibre** (`X = {0}`, no side boundary): consumer form of
`lfr05_exists_isotopy_image_source_fibre` with `φ = id`, `β = 1`. -/
theorem lfr05_point_exists_isotopy_image_source_fibre {r : ℕ} (hr : 1 ≤ r)
    {Y : Type*} (j : M → Y) {f : Y → G'} {F : ℝ × M → G'}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G') (r + 1) F) (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ q : ℝ × M, F q = 0 → Surjective (mfderiv I 𝓘(ℝ, G') (fun y => F (q.1, y)) q.2))
    {S : Set M} (hS : IsCompact S) (hWS : ∀ q : ℝ × M, F q = 0 → q.2 ∈ S)
    {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N) (henc : ∀ y, f y = 0 → y ∈ range j) :
    ∃ (K : Set M) (Φ : M ≃ₘ^r⟮I, I⟯ M), IsCompact K ∧ K ⊆ N ∧ (∀ x ∉ K, Φ x = x) ∧
      (fun x => j (Φ x)) '' {x | F (0, x) = 0} = {y | f y = 0} := by
  obtain ⟨K, Φ, hK, hKN, hid, himg, -⟩ :=
    lfr05_exists_isotopy_image_source_fibre (φ := id) (β := fun _ => (1 : ℝ)) hr j hF contDiff_id
      contDiff_const hF1 (fun q h0 _ => htrans q h0) (fun q _ h1 => absurd h1 one_ne_zero) hS
      (fun q h0 _ => hWS q h0) hN hSN (fun y h0 _ => henc y h0)
  refine ⟨K, Φ, hK, hKN, hid, ?_⟩
  have h1 : {x | F (0, x) = 0} = {x | id (F (0, x)) = 0 ∧ (0 : ℝ) ≤ 1} := by
    ext x
    simp
  have h2 : {y | f y = 0} = {y | id (f y) = 0 ∧ (0 : ℝ) ≤ 1} := by
    ext y
    simp
  rw [h1, h2]
  exact himg

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
