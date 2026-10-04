import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.PacketFibreBinding
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.LFR04

/-!
# LFR05: smooth type of the source fibre with boundary

Blueprint LFR05 (`master207A.tex`, label `prop:collapse-finite-packet-consumer`), fibre clause in
the smooth category, for fibres with boundary (side boundary `{β = 0}`):

* `lfr05_nonempty_smooth_diffeomorph` — for `3 ≤ r` (the blueprint's hypothesis), a compact fibre
  `Hf` that is `C^{r-1}` diffeomorphic to the model fibre `{φ ∘ F (0, ·) = 0, β ∘ F (0, ·) ≥ 0}` is
  SMOOTHLY diffeomorphic to the entire source fibre `{φ ∘ f = 0, β ∘ f ≥ 0}` (both with lane
  SUB-BDY's manifold-with-boundary structure). Proof: the `C^{r-1}` fibre diffeomorphism
  (`lfr05_nonempty_diffeomorph_fibre_type`) and LFR04 with boundary
  (`nonempty_diffeomorph_of_diffeomorph_boundary`, `2 ≤ r - 1`). This removes the hypothesis
  `∂Hf = ∅` of `lfr05_nonempty_smooth_diffeomorph_of_boundary_eq_empty`.
* consumer `lfr05_nonempty_smooth_diffeomorph_model_fibre` — the source fibre is smoothly
  diffeomorphic to the model fibre itself (`Hf` = the model fibre, compact because it lies in the
  compact set `Q`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.Manifold.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **LFR05, smooth fibre type (fibres with boundary, `3 ≤ r`).** -/
theorem lfr05_nonempty_smooth_diffeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {Y : Type} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
    {r : ℕ} (hr : 3 ≤ r) {d : ℕ}
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
    {Hf : Type} [TopologicalSpace Hf] [ChartedSpace (EuclideanHalfSpace (d + 1)) Hf]
    [IsManifold (𝓡∂ (d + 1)) ∞ Hf] [T2Space Hf] [CompactSpace Hf]
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
  obtain ⟨e⟩ := lfr05_nonempty_diffeomorph_fibre_type (by omega) hdim j hj hf hF hF0 hφ hβ hF1
    htrans htransb hQ hencl henc ψ
  exact nonempty_diffeomorph_of_diffeomorph_boundary (n := d) (k := r - 1) (by omega) e

/-- **Consumer: the source fibre has the smooth type of the model fibre** (`3 ≤ r`, fibres with
boundary allowed). -/
theorem lfr05_nonempty_smooth_diffeomorph_model_fibre
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {Y : Type} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
    {r : ℕ} (hr : 3 ≤ r) {d : ℕ}
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
    letI := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
      (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
      (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
    letI := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
        henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
    Nonempty ({x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
      {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) := by
  let c₀ := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
    (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
    (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
  have : IsManifold (𝓡∂ (d + 1)) ∞ {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} :=
    regularSublevel_isManifold (Ψ := fun x => φ (F (0, x))) (B := fun x => β (F (0, x)))
      hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0) _ _
  have hc : Continuous fun x => F (0, x) := hF0.continuous
  have hS : IsCompact {x : M | φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} := by
    refine hQ.of_isClosed_subset ?_ fun x hx =>
      hencl 0 (left_mem_Icc.2 zero_le_one) x hx.1 hx.2
    exact (isClosed_eq (hφ.continuous.comp hc) continuous_const).inter
      (isClosed_le continuous_const (hβ.continuous.comp hc))
  have : CompactSpace {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))} :=
    isCompact_iff_compactSpace.mp hS
  exact lfr05_nonempty_smooth_diffeomorph hr hdim j hj hf hF hF0 hφ hβ hF1 htrans htransb hQ
    hencl henc (Diffeomorph.refl _ _ _)

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
