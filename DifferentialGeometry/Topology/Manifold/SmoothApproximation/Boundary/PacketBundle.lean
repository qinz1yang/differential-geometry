import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.PacketFibreSmooth
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval

/-!
# LFR05 (iii): the bundle clause over an interval

Blueprint LFR05 (`master207A.tex`, A:25066, label `prop:collapse-finite-packet-consumer`), last
two sentences: "If the smooth source map has a proper submersion restriction, also on its boundary
when present, that restriction is a smooth bundle with fiber `H`. It is trivial over a ball or
interval." Here the base is an interval (`G = ℝ`): the source map is `P = φ ∘ f`, the side
boundary is `{β ∘ f = 0}`.

* `lfr05_bundle_trivial_over_interval`: with W-2c's LFR05 hypotheses (which give the smooth type
  `Hf ≅ F₀` of the source fibre `F₀ = {P = 0, β ∘ f ≥ 0}`, `lfr05_nonempty_smooth_diffeomorph`)
  and a proper submersion restriction of `P` to `{a < P < b, β ∘ f ≥ 0}`, submersive also on the
  side boundary: for every `[a₀, b₀] ⊂ (a, b)` with `0 ∈ (a₀, b₀)` there is a smooth injective
  `Θ : Hf × (a₀, b₀) → Y` over the identity of `(a₀, b₀)` whose image is
  `{a₀ < P < b₀, β ∘ f ≥ 0}`; in the fibre form (`Hf = F₀`) its inverse is `y ↦ (R y, P y)` with
  `R` smooth near that set (the generic `exists_sideBoundary_interval_trivialization`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.Manifold.RegularLevel DifferentialGeometry.Topology.Ehresmann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **LFR05 (iii), interval base.** Under W-2c's LFR05 hypotheses (`G = ℝ`, `3 ≤ r`) and a proper
submersion restriction of the source map `P = φ ∘ f` to `{a < P < b, β ∘ f ≥ 0}`, submersive also
on the side boundary `{β ∘ f = 0}`: for `0 ∈ (a₀, b₀)`, `[a₀, b₀] ⊂ (a, b)`, the restriction over
`(a₀, b₀)` is a trivial bundle with fibre `Hf`: `Hf ≅ F₀` smoothly, the source fibre `F₀` gives a
trivialization with smooth inverse data, and `Θ_H : Hf × (a₀, b₀) → Y` is smooth, injective, over
the identity, with image `{a₀ < P < b₀, β ∘ f ≥ 0}`. -/
theorem lfr05_bundle_trivial_over_interval
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {Y : Type} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
    [T2Space Y] [SigmaCompactSpace Y]
    {r : ℕ} (hr : 3 ≤ r) {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1 + Module.finrank ℝ ℝ)
    (j : PartialDiffeomorph I I M Y r) (hj : j.source = univ)
    {f : Y → E'} (hf : ContMDiff I 𝓘(ℝ, E') ∞ f) {F : ℝ × M → E'}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    (hF0 : ContMDiff I 𝓘(ℝ, E') ∞ (fun x => F (0, x)))
    {φ : E' → ℝ} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hF1 : ∀ x, F (1, x) = f (j x))
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → 0 ≤ β (F (t, x)) →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, φ (F (t, x)) = 0 → β (F (t, x)) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
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
        {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))})
    {a b : ℝ}
    (hregP : ∀ y, φ (f y) ∈ Ioo a b → 0 ≤ β (f y) →
      Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => φ (f y)) y))
    (hregPB : ∀ y, φ (f y) ∈ Ioo a b → β (f y) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (φ (f y), β (f y))) y))
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b →
      IsCompact ((fun y => φ (f y)) ⁻¹' K ∩ {y | 0 ≤ β (f y)}))
    {a₀ b₀ : ℝ} (ha₀ : a < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < b) :
    letI := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
        henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
    let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
    Nonempty (Hf ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯ {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) ∧
    (∃ Θ : {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} × Q₀ → Y,
      ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, ℝ)) I ∞ Θ ∧
      (∀ p, φ (f (Θ p)) = p.2 ∧ 0 ≤ β (f (Θ p))) ∧
      (∀ x, Θ (x, ⟨0, h0⟩) = x) ∧ Injective Θ ∧
      ∃ O : Set Y, IsOpen O ∧ (∀ y, φ (f y) ∈ Ioo a₀ b₀ → 0 ≤ β (f y) → y ∈ O) ∧
        ∃ R : Y → Y, ContMDiffOn I I ∞ R O ∧
          ∀ y (hy : φ (f y) ∈ Ioo a₀ b₀), 0 ≤ β (f y) →
            ∃ hR : φ (f (R y)) = 0 ∧ 0 ≤ β (f (R y)), Θ (⟨R y, hR⟩, ⟨φ (f y), hy⟩) = y) ∧
    ∃ ΘH : Hf × Q₀ → Y, ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, ℝ)) I ∞ ΘH ∧
      (∀ p, φ (f (ΘH p)) = p.2 ∧ 0 ≤ β (f (ΘH p))) ∧ Injective ΘH ∧
      ∀ y, φ (f y) ∈ Ioo a₀ b₀ → 0 ≤ β (f y) → ∃ p, ΘH p = y := by
  let _ := regularSublevelChartedSpace (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
    hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
    (lfr05_source_regular (by omega) j hj hf hφ hF1 (htrans 1 (right_mem_Icc.2 zero_le_one))
      henc)
    (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
      (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
  have : IsManifold (𝓡∂ (d + 1)) ∞ {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} :=
    regularSublevel_isManifold (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf) _ _
  obtain ⟨e⟩ := lfr05_nonempty_smooth_diffeomorph hr hdim j hj hf hF hF0 hφ hβ hF1 htrans htransb
    hQ hencl henc ψ
  obtain ⟨Θ, hΘs, hΘP, hΘ0, hΘi, O, hO, hΩO, R, hR, hRinv⟩ :=
    exists_sideBoundary_interval_trivialization (P := fun y => φ (f y))
      (B := fun y => β (f y)) hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf) hregP hregPB
      hprop ha₀ h0 hb₀
  refine ⟨⟨e⟩, ⟨Θ, hΘs, hΘP, hΘ0, hΘi, O, hO, hΩO, R, hR, hRinv⟩,
    fun p => Θ (e p.1, p.2), hΘs.comp ((e.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd),
    fun p => hΘP _, fun p q hpq => ?_, fun y hy hBy => ?_⟩
  · have h : ((e p.1, p.2) : {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} × _) = (e q.1, q.2) :=
      hΘi hpq
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (e.injective h1) h2
  · obtain ⟨hRy, hΘy⟩ := hRinv y hy hBy
    exact ⟨(e.symm ⟨R y, hRy⟩, ⟨φ (f y), hy⟩), by
      change Θ (e (e.symm ⟨R y, hRy⟩), ⟨φ (f y), hy⟩) = y
      rw [e.apply_symm_apply]
      exact hΘy⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
