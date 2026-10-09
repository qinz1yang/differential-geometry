import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.PacketBundle
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryBallTrivialization

/-!
The original finite packet has its specified smooth fibre type over an actual ball in any
finite-dimensional target. The binding retains the source map, its side boundary and the
original family, and composes the produced radial trivialization with the produced fibre map.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.Manifold.RegularLevel DifferentialGeometry.Topology.Ehresmann

variable {E G E' H : Type*}
  [normE : NormedAddCommGroup E] [spaceE : NormedSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  [normG : NormedAddCommGroup G] [spaceG : NormedSpace ℝ G]
  [finiteG : FiniteDimensional ℝ G]
  [normE' : NormedAddCommGroup E'] [spaceE' : NormedSpace ℝ E']
  [topH : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [boundaryI : I.Boundaryless]

theorem lfr05_bundle_trivial_over_ball
    {M : Type*} [topM : TopologicalSpace M] [chartsM : ChartedSpace H M]
    [smoothM : IsManifold I ∞ M]
    [hausdorffM : T2Space M] [sigmaM : SigmaCompactSpace M]
    {Y : Type} [topY : TopologicalSpace Y] [chartsY : ChartedSpace H Y]
    [smoothY : IsManifold I ∞ Y]
    [hausdorffY : T2Space Y] [sigmaY : SigmaCompactSpace Y]
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
    {Hf : Type} [topHf : TopologicalSpace Hf]
    [chartsHf : ChartedSpace (EuclideanHalfSpace (d + 1)) Hf]
    [smoothHf : IsManifold (𝓡∂ (d + 1)) ∞ Hf]
    [hausdorffHf : T2Space Hf] [compactHf : CompactSpace Hf]
    (ψ :
      letI := regularSublevelChartedSpace (Ψ := fun x => φ (F (0, x)))
        (B := fun x => β (F (0, x))) hdim (hφ.contMDiff.comp hF0) (hβ.contMDiff.comp hF0)
        (htrans 0 (left_mem_Icc.2 zero_le_one)) (htransb 0 (left_mem_Icc.2 zero_le_one))
      Hf ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
        {x : M // φ (F (0, x)) = 0 ∧ 0 ≤ β (F (0, x))})
    {R R₀ : ℝ} (hR : 0 < R) (hRR : R < R₀)
    (hregP : ∀ y, φ (f y) ∈ Metric.ball 0 R₀ → 0 ≤ β (f y) →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun z => φ (f z)) y))
    (hregPB : ∀ y, φ (f y) ∈ Metric.ball 0 R₀ → β (f y) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun z => (φ (f z), β (f z))) y))
    (hproper : ∀ K : Set G, IsCompact K → K ⊆ Metric.ball 0 R₀ →
      IsCompact ((fun y => φ (f y)) ⁻¹' K ∩ {y | 0 ≤ β (f y)})) :
    let sourceCharts := regularSublevelChartedSpace
      (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
      hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      (lfr05_source_regular (by omega) j hj hf hφ hF1
        (htrans 1 (right_mem_Icc.2 zero_le_one)) henc)
      (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
        (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
    let base : TopologicalSpace.Opens G := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
    Nonempty (Hf ≃ₘ⟮𝓡∂ (d + 1), 𝓡∂ (d + 1)⟯
      {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)}) ∧
    (∃ Θ : {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} × base → Y,
      ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) I ∞ Θ ∧
      (∀ p, φ (f (Θ p)) = p.2 ∧ 0 ≤ β (f (Θ p))) ∧
      (∀ x, Θ (x, ⟨0, Metric.mem_ball_self hR⟩) = x) ∧ Injective Θ ∧
      ∃ O : Set Y, IsOpen O ∧ (∀ y, φ (f y) ∈ base → 0 ≤ β (f y) → y ∈ O) ∧
        ∃ Rmap : Y → Y, ContMDiffOn I I ∞ Rmap O ∧
          ∀ y (hy : φ (f y) ∈ base), 0 ≤ β (f y) →
            ∃ hr : φ (f (Rmap y)) = 0 ∧ 0 ≤ β (f (Rmap y)),
              Θ (⟨Rmap y, hr⟩, ⟨φ (f y), hy⟩) = y) ∧
    ∃ ΘH : Hf × base → Y, ContMDiff ((𝓡∂ (d + 1)).prod 𝓘(ℝ, G)) I ∞ ΘH ∧
      (∀ p, φ (f (ΘH p)) = p.2 ∧ 0 ≤ β (f (ΘH p))) ∧ Injective ΘH ∧
      ∀ y, φ (f y) ∈ base → 0 ≤ β (f y) → ∃ p, ΘH p = y := by
  let sourceCharts := regularSublevelChartedSpace
    (Ψ := fun y => φ (f y)) (B := fun y => β (f y))
    hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
    (lfr05_source_regular (by omega) j hj hf hφ hF1
      (htrans 1 (right_mem_Icc.2 zero_le_one)) henc)
    (lfr05_source_regular_boundary (by omega) j hj hf hφ hβ hF1
      (htransb 1 (right_mem_Icc.2 zero_le_one)) henc)
  obtain ⟨e⟩ := lfr05_nonempty_smooth_diffeomorph hr hdim j hj hf hF hF0 hφ hβ hF1
    htrans htransb hQ hencl henc ψ
  obtain ⟨Θ, hΘsmooth, hΘbase, hΘzero, hΘinjective, O, hOopen,
    hOcontains, Rmap, hRmap, hRinverse⟩ :=
    exists_sideBoundary_ball_trivialization (P := fun y => φ (f y))
      (B := fun y => β (f y)) hdim (hφ.contMDiff.comp hf) (hβ.contMDiff.comp hf)
      hR hRR hregP hregPB hproper
  refine ⟨⟨e⟩, ⟨Θ, hΘsmooth, hΘbase, hΘzero, hΘinjective, O, hOopen,
    hOcontains, Rmap, hRmap, hRinverse⟩, ?_⟩
  let base : TopologicalSpace.Opens G := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
  let ΘH : Hf × base → Y :=
    fun p => Θ (e p.1, p.2)
  refine ⟨ΘH, ?_, ?_, ?_, ?_⟩
  · exact hΘsmooth.comp ((e.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  · intro p
    exact hΘbase (e p.1, p.2)
  · intro p q hpq
    have hpair := hΘinjective hpq
    have hfirst : e p.1 = e q.1 := congrArg Prod.fst hpair
    have hsecond : p.2 = q.2 := congrArg
      (fun z : {y : Y // φ (f y) = 0 ∧ 0 ≤ β (f y)} × base => z.2) hpair
    exact Prod.ext (e.injective hfirst) hsecond
  · intro y hy hβy
    obtain ⟨hzero, hinverse⟩ := hRinverse y hy hβy
    refine ⟨(e.symm ⟨Rmap y, hzero⟩, ⟨φ (f y), hy⟩), ?_⟩
    dsimp [ΘH]
    simpa only [e.apply_symm_apply] using hinverse

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
