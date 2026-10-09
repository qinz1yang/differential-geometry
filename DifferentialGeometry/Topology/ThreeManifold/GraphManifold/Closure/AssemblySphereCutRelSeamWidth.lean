import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeam

/-!
# Chapter-14 assembly, relative COMPARE shared seams: the width of the seam bands

Lane ASM-L2e3, shared seam group (for G5 SEP and G6 NONSEP). Finitely many tubes
`φ t : PlaneLift × Circle ⇀ M` whose closed radius-three tubes lie in their sources and whose closed
UNIT tubes are pairwise disjoint have, for all small `κ > 0`, pairwise disjoint closed tubes of
radius `1 + κ` (only the closed unit tubes are given disjoint; the tubes may overlap further out).
Proof: the equalizer `{(p, q) | ‖p‖, ‖q‖ ≤ 2, φ p = φ' q}` is compact, and the larger of the two
radii has a minimum on it, which is `> 1`.

* `isCompact_tubeDisk`, `isCompact_tubeImage`, `tubeImage_mono`.
* `exists_tubeImage_disjoint`: one pair of tubes.
* `eventually_tubeImage_pairwiseDisjoint`: finitely many tubes, for all small `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The closed disk bundle of radius `ρ` of the tube model is compact. -/
theorem isCompact_tubeDisk (ρ : ℝ) :
    IsCompact {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ ρ} := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ ρ} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ ρ} =
        (Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 ρ := by
      ext z
      rcases z with ⟨z⟩
      simp [Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) ρ).image Homeomorph.ulift.symm.continuous
  have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ ρ} =
      {z : PlaneLift.{u} | ‖z.down‖ ≤ ρ} ×ˢ univ := by
    ext p
    simp
  rw [he]
  exact hc.prod isCompact_univ

section Tubes

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A closed tube of radius at most three of a tube chart is compact. -/
theorem isCompact_tubeImage
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) {ρ : ℝ} (hρ : ρ ≤ 3) :
    IsCompact (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ ρ}) :=
  (isCompact_tubeDisk ρ).image_of_continuousOn (φ.contMDiffOn.continuousOn.mono
    fun p hp => h3 (le_trans (show ‖p.1.down‖ ≤ ρ from hp) hρ))

theorem tubeImage_mono
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ ρ} ⊆
      φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ ρ'} :=
  image_mono fun _ hp => le_trans (show _ ≤ ρ from hp) h

variable [T2Space M]

/-- **One pair of tubes.** Disjoint closed unit tubes stay disjoint up to some radius `1 + κ₀`. -/
theorem exists_tubeImage_disjoint
    (φ φ' : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (h3' : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ'.source)
    (hd : Disjoint (φ '' {p | ‖p.1.down‖ ≤ 1}) (φ' '' {p | ‖p.1.down‖ ≤ 1})) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 ∧
      Disjoint (φ '' {p | ‖p.1.down‖ ≤ 1 + κ₀}) (φ' '' {p | ‖p.1.down‖ ≤ 1 + κ₀}) := by
  let T : Set (PlaneLift.{u} × Circle) := {p | ‖p.1.down‖ ≤ 2}
  have hT3 : T ⊆ {p | ‖p.1.down‖ ≤ 3} := fun p hp => le_trans (show ‖p.1.down‖ ≤ 2 from hp)
    (by norm_num)
  let f : (PlaneLift.{u} × Circle) × (PlaneLift.{u} × Circle) → M × M := fun z => (φ z.1, φ' z.2)
  have hf : ContinuousOn f (T ×ˢ T) :=
    ((φ.contMDiffOn.continuousOn.mono (hT3.trans h3)).comp continuous_fst.continuousOn
      fun z hz => hz.1).prodMk
    ((φ'.contMDiffOn.continuousOn.mono (hT3.trans h3')).comp continuous_snd.continuousOn
      fun z hz => hz.2)
  let Z := T ×ˢ T ∩ f ⁻¹' diagonal M
  have hTT : IsCompact (T ×ˢ T) := (isCompact_tubeDisk 2).prod (isCompact_tubeDisk 2)
  have hZ : IsCompact Z :=
    hTT.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hTT.isClosed isClosed_diagonal)
      inter_subset_left
  let g : (PlaneLift.{u} × Circle) × (PlaneLift.{u} × Circle) → ℝ :=
    fun z => max ‖z.1.1.down‖ ‖z.2.1.down‖
  have hg : Continuous g :=
    (continuous_norm.comp (continuous_uliftDown.comp (continuous_fst.comp continuous_fst))).max
      (continuous_norm.comp (continuous_uliftDown.comp (continuous_fst.comp continuous_snd)))
  have hmem : ∀ {κ : ℝ}, κ ≤ 1 → ∀ x, x ∈ φ '' {p | ‖p.1.down‖ ≤ 1 + κ} →
      x ∈ φ' '' {p | ‖p.1.down‖ ≤ 1 + κ} → ∃ z ∈ Z, g z ≤ 1 + κ := by
    intro κ hκ x ⟨p, hp, hpx⟩ ⟨q, hq, hqx⟩
    have hp' : ‖p.1.down‖ ≤ 1 + κ := hp
    have hq' : ‖q.1.down‖ ≤ 1 + κ := hq
    refine ⟨(p, q), ⟨⟨?_, ?_⟩, ?_⟩, max_le hp' hq'⟩
    · change ‖p.1.down‖ ≤ 2
      linarith
    · change ‖q.1.down‖ ≤ 2
      linarith
    · change (φ p, φ' q) ∈ diagonal M
      rw [mem_diagonal_iff, hpx, hqx]
  rcases Z.eq_empty_or_nonempty with hZe | hZn
  · refine ⟨1, one_pos, le_rfl, disjoint_left.mpr fun x hx hx' => ?_⟩
    obtain ⟨z, hz, -⟩ := hmem le_rfl x hx hx'
    rw [hZe] at hz
    exact hz
  obtain ⟨z₀, hz₀, hmin⟩ := hZ.exists_isMinOn hZn hg.continuousOn
  have hg₀ : 1 < g z₀ := by
    by_contra hle
    push Not at hle
    obtain ⟨-, hdiag⟩ := hz₀
    have h1 : ‖z₀.1.1.down‖ ≤ 1 := le_trans (le_max_left _ _) hle
    have h2 : ‖z₀.2.1.down‖ ≤ 1 := le_trans (le_max_right _ _) hle
    have he : φ z₀.1 = φ' z₀.2 := hdiag
    exact disjoint_left.mp hd ⟨z₀.1, h1, rfl⟩ ⟨z₀.2, h2, he.symm⟩
  refine ⟨min 1 ((g z₀ - 1) / 2), lt_min one_pos (by linarith), min_le_left _ _,
    disjoint_left.mpr fun x hx hx' => ?_⟩
  obtain ⟨z, hz, hgz⟩ := hmem (min_le_left _ _) x hx hx'
  have h := hmin hz
  have hm : min 1 ((g z₀ - 1) / 2) ≤ (g z₀ - 1) / 2 := min_le_right _ _
  change g z₀ ≤ g z at h
  linarith

/-- **Finitely many tubes.** Pairwise disjoint closed unit tubes have pairwise disjoint closed
tubes of radius `1 + κ` for all small `κ > 0`. -/
theorem eventually_tubeImage_pairwiseDisjoint {k : ℕ}
    (φ : Fin k → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hd : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1}) (φ t' '' {p | ‖p.1.down‖ ≤ 1})) :
    ∀ᶠ κ in 𝓝[>] (0 : ℝ), Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) (φ t' '' {p | ‖p.1.down‖ ≤ 1 + κ}) := by
  have h : ∀ t t' : Fin k, ∀ᶠ κ in 𝓝[>] (0 : ℝ), t ≠ t' →
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) (φ t' '' {p | ‖p.1.down‖ ≤ 1 + κ}) := by
    intro t t'
    by_cases htt : t = t'
    · exact Eventually.of_forall fun _ hne => (hne htt).elim
    obtain ⟨κ₀, hκ₀, -, hdisj⟩ := exists_tubeImage_disjoint (φ t) (φ t') (h3 t) (h3 t') (hd htt)
    filter_upwards [Ioo_mem_nhdsGT hκ₀] with κ hκ _
    exact hdisj.mono (tubeImage_mono (φ t) (by linarith [hκ.2]))
      (tubeImage_mono (φ t') (by linarith [hκ.2]))
  have h' := eventually_all.mpr fun t => eventually_all.mpr (h t)
  filter_upwards [h'] with κ hκ t t' htt
  exact hκ t t' htt

end Tubes

end GC.GraphManifold.Assembly
