import DifferentialGeometry.Geometry.Fibration.ActualEdgeLevelDiskEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeightApplications

/-!
# EDP04: the WHOLE time-one fibre of the actual transport is a smooth disk (chain level)

Lane S-EDP-FDC, group G3 (EDP04 whole-disk binding, step C). Blueprint `master207B.tex`, EDP04
(B:6949–7038), draft 74 D74-11. For an edge centre `j` of `L : LocalChartPacketsC14` and a chain
`C : Gaf02Chain L.toLocalChartPackets …`, with the original source
`Y_j = {p ∈ B(j, 100Δρ(j)) : |η_j| < 5Δ, t < 5Δ}`, `g = u_j(E)/R_j`, `T = A/s`
(`final_smooth_EDPE`: both smooth on all of `X`, `s > 0`) and `|a| < 4Δ`:

* **`Gaf02Chain.edp04_whole_disk_EFE`**: `{p ∈ Y_j : g_j p = a, T p ≤ 4Δ}` is the range of a smooth
  embedding `ClosedCell 2 → X`, with boundary circle onto `{p ∈ Y_j : g_j p = a, T p = 4Δ}`.
  E0 (`wholeDisk_of_compact_transverse_trace_opens_EFC`) is applied to the family (EI)
  `((1 - τ)η_j + τ g_j, (1 - τ)H₀ + τ T)` on the open source `Y_j`, starting from the ORIGINAL disk
  at level `a` (`LocalChartPacketsC14.edge_levelDisk_EFE`): the whole time trace lies in the
  compact buffer of EDP03/EDP04 (`edp04_trace_compact_C14_EDPE`), the first differential is
  nonzero (`dη_j > .99` from `edp03_buffer` and `|dg_j - dη_j| ≤ H`, `final_derivative_EDPE`), and
  the pair has rank two on the rim for every `τ` (`edge_homotopy_conorm_EDPE`, collar from
  `edge_trace_EDPE`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **EDP04: the WHOLE time-one fibre is a smooth disk (chain level).** -/
theorem Gaf02Chain.edp04_whole_disk_EFE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ L.edge.centres) {a : ℝ} (ha : |a| < 4 * Δ) :
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |L.edge.coord j p| < 5 * Δ ∧ t p < 5 * Δ}
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {p | p ∈ Y ∧ gq p = a ∧ Tq p ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {p | p ∈ Y ∧ gq p = a ∧ Tq p = 4 * Δ} := by
  intro jF t A Tq gq Y
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Δ) hΛ]
  have hYo : IsOpen Y := isOpen_edgeSource_EFE L hj
  obtain ⟨-, hηs, hHs, hdη, -⟩ := edp03_buffer L.toLocalChartFamilyE hΔ hμ hτ hlam hσc hb hj
  obtain ⟨Q, hQc, hQY, hQa⟩ := edp04_trace_compact_C14_EDPE C hcw hSΞ hc hϑ hε0 hε hμ hτ hσc hb hj
  obtain ⟨hint, -⟩ := hQa a ha
  obtain ⟨φ₀, hφ₀, hφ₀r, hφ₀b⟩ := L.edge_levelDisk_EFE hΔ hμ hτ hlam hσc hb hγc hγc1 hβc1 hj ha
  obtain ⟨-, -, hT, hg⟩ := (C.final_smooth_EDPE).2
  obtain ⟨Hd, hHd, -, -, -, hedge⟩ := C.final_derivative_EDPE
  have htr := C.edge_trace_EDPE hcw hSΞ hc hϑ hε0 hε hj
  obtain ⟨hcn, hco⟩ := C.edge_homotopy_conorm_EDPE hcw hSΞ hc hϑ hε0 hε hγc hγc1 hβc1 hj
  let O : TopologicalSpace.Opens X := ⟨Y, hYo⟩
  have hfst : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ, E3) ∞ (Prod.fst : X × ℝ → X) :=
    contMDiff_fst
  have hsnd : ContMDiff (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (Prod.snd : X × ℝ → ℝ) := contMDiff_snd
  have hgq : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ) ∞ gq := hg jF
  have hTq : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ) ∞ Tq := hT
  have hh : ContMDiffOn (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : X × ℝ => (1 - q.2) * L.edge.coord j q.1 + q.2 * gq q.1) ((O : Set X) ×ˢ univ) :=
    ((contMDiff_const.sub hsnd).contMDiffOn.mul
      (hηs.comp hfst.contMDiffOn (fun q hq => hq.1))).add
      (hsnd.contMDiffOn.mul (hgq.comp hfst).contMDiffOn)
  have hT' : ContMDiffOn (𝓘(ℝ, E3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : X × ℝ => (1 - q.2) * edgeRowHeight Δ L.edge.smoothing ρ q.1 + q.2 * Tq q.1)
      ((O : Set X) ×ˢ univ) :=
    ((contMDiff_const.sub hsnd).contMDiffOn.mul
      (hHs.comp hfst.contMDiffOn (fun q hq => hq.1))).add
      (hsnd.contMDiffOn.mul (hTq.comp hfst).contMDiffOn)
  have hηY : ∀ y ∈ Y, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ) ∞ (L.edge.coord j) y := fun y hy =>
    hηs.contMDiffAt (hYo.mem_nhds hy)
  have hHY : ∀ y ∈ Y, ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ) ∞ (edgeRowHeight Δ L.edge.smoothing ρ) y :=
    fun y hy => hHs.contMDiffAt (hYo.mem_nhds hy)
  have hreg : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set X),
      (1 - θ) * L.edge.coord j y + θ * gq y = a →
      (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ y + θ * Tq y ≤ 4 * Δ →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ) (fun z => (1 - θ) * L.edge.coord j z + θ * gq z) y) := by
    intro θ hθ y hy _ _
    obtain ⟨w, hwg, hw⟩ := hdη y hy
    have hrj := hρ j
    have hunit : (ρ j)⁻¹ ^ 2 * g.inner y w w = 1 := by
      rw [hwg]
      field_simp
    have h0 := hedge jF y hy.1 (by linarith [hy.2.1]) (by linarith [hy.2.2]) w
    rw [hunit, Real.sqrt_one, mul_one] at h0
    refine surjective_mfderiv_of_mvfderiv_ne_zero_EFE (I := 𝓘(ℝ, E3))
      (f := fun z => (1 - θ) * L.edge.coord j z + θ * gq z) (x := y) w ?_
    rw [mvfderiv_homotopy_scalar_EFE θ (hηY y hy) hgq.contMDiffAt w]
    have h1 := abs_le.mp h0
    have h2 : 0 ≤ Hd := (abs_nonneg _).trans h0
    intro hz
    nlinarith [hθ.1, hθ.2, h1.1, h1.2]
  have hface : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set X),
      (1 - θ) * L.edge.coord j y + θ * gq y = a →
      (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ y + θ * Tq y = 4 * Δ →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ × ℝ) (fun z =>
        ((1 - θ) * L.edge.coord j z + θ * gq z,
          (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ z + θ * Tq z)) y) := by
    intro θ hθ y hy hfib hH
    obtain ⟨-, -, hrim⟩ := htr θ hθ y hy.1 hy.2.1 hy.2.2 a ha hfib hH.le
    obtain ⟨-, ht1, ht2⟩ := hrim hH
    have hf' : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ) ∞
        (fun z => (1 - θ) * L.edge.coord j z + θ * gq z) y :=
      (contMDiffAt_const.mul (hηY y hy)).add (contMDiffAt_const.mul hgq.contMDiffAt)
    have hh' : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ) ∞
        (fun z => (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ z + θ * Tq z) y :=
      (contMDiffAt_const.mul (hHY y hy)).add (contMDiffAt_const.mul hTq.contMDiffAt)
    have hsurj : Surjective (mvfderiv (I := 𝓘(ℝ, E3)) (edgeReferenceCoordinates
        ![fun z => (1 - θ) * L.edge.coord j z + θ * gq z,
          fun z => (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ z + θ * Tq z]) y) := by
      refine surjective_of_conorm_pos_EDP6 (mvfderiv (I := 𝓘(ℝ, E3)) (edgeReferenceCoordinates
        ![fun z => (1 - θ) * L.edge.coord j z + θ * gq z,
          fun z => (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ z + θ * Tq z]) y).toLinearMap
        (fun ξ hξ => ?_)
      obtain ⟨W, -, hW⟩ := hco y hy.1 hy.2.1 ht1 ht2 θ hθ ξ hξ
      exact ⟨W, by
        change 0 < inner ℝ (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates
          ![fun z => (1 - θ) * L.edge.coord j z + θ * gq z,
            fun z => (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ z + θ * Tq z]) y W) ξ
        linarith⟩
    exact surjective_mfderiv_pair_EFE hf' hh'
      (pair_form_of_surjective_edgeReference_EFE hf' hh' hsurj)
  have hloc : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set X),
      (1 - θ) * L.edge.coord j y + θ * gq y = a →
      (1 - θ) * edgeRowHeight Δ L.edge.smoothing ρ y + θ * Tq y ≤ 4 * Δ → y ∈ Q :=
    fun θ hθ y hy hfib hH => interior_subset (hint θ hθ y hy hfib hH)
  have hmemY : ∀ p, p ∈ ball j (100 * Δ * ρ j) → |L.edge.coord j p| < 5 * Δ →
      edgeRowHeight Δ L.edge.smoothing ρ p ≤ 4 * Δ → p ∈ Y := fun p hp hη hH =>
    ⟨hp, hη, by have := (edgeRowHeight_le_iff hΔ0).mp hH; change _ < _; linarith⟩
  have hφ₀r' : range φ₀ = {y | y ∈ (O : Set X) ∧ (1 - 0) * L.edge.coord j y + 0 * gq y = a ∧
      (1 - 0) * edgeRowHeight Δ L.edge.smoothing ρ y + 0 * Tq y ≤ 4 * Δ} := by
    rw [hφ₀r]
    ext p
    constructor
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hmemY p hp (by rw [hη]; linarith) hH, by rw [hη]; ring, by linarith⟩
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hp.1, by linarith, by linarith⟩
  have hφ₀b' : range (φ₀ ∘ cellBoundaryInclusion 2) =
      {y | y ∈ (O : Set X) ∧ (1 - 0) * L.edge.coord j y + 0 * gq y = a ∧
        (1 - 0) * edgeRowHeight Δ L.edge.smoothing ρ y + 0 * Tq y = 4 * Δ} := by
    rw [hφ₀b]
    ext p
    constructor
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hmemY p hp (by rw [hη]; linarith) hH.le, by rw [hη]; ring, by linarith⟩
    · rintro ⟨hp, hη, hH⟩
      exact ⟨hp.1, by linarith, by linarith⟩
  obtain ⟨φ, hφ, hr, hb', -⟩ :=
    DifferentialGeometry.Topology.Ehresmann.wholeDisk_of_compact_transverse_trace_opens_EFC
      (I := 𝓘(ℝ, E3)) O
      (fun q : X × ℝ => (1 - q.2) * L.edge.coord j q.1 + q.2 * gq q.1)
      (fun q : X × ℝ => (1 - q.2) * edgeRowHeight Δ L.edge.smoothing ρ q.1 + q.2 * Tq q.1)
      hh hT' a (4 * Δ) hreg hface hQc hQY hloc hφ₀ hφ₀r' hφ₀b'
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr]
    ext p
    simp only [mem_ofPred_eq, sub_self, zero_mul, one_mul, zero_add]
    rfl
  · rw [hb']
    ext p
    simp only [mem_ofPred_eq, sub_self, zero_mul, one_mul, zero_add]
    rfl

end DifferentialGeometry.Geometry.Collapse
