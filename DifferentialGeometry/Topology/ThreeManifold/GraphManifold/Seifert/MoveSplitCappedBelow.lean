import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModel

/-!
# The capped conditions of the split tube

Lane N2c, tier 3 (first part). For a linear split seam `j` the split tube `splitSeamTube` avoids
every seam torus other than `j` (`tubeMap_ne_seam`: its points are images of interior points of
the solid torus and of the host, or points of the seam chart of `j`), and every piece other than
the solid torus and the host (`tubeMap_ne_cutMap`). The tube is compact, so a collar of height
`ε` of each other seam torus avoids it as well (`exists_seam_avoid`, by the tube lemma), and
points off the tube lie in the interior of the core (`core_of_not_tube`). Hence the hypotheses
`CappedConditions` of the assembly hold for every small `δ₂` (`exists_cappedConditions`).

Tier 3. The cut-cap transition along the split tube (`exists_splitSeamSurgery`), the capped solid
tori (`exists_sideData`) and the assembly (`exists_cappedElementary_of_sideData`) give the two
alternatives of `FibreFillingSphereSurgery` for a linear split seam
(`fibreFillingSphereSurgery_of_isLinearSeam`): `Q ≅ A # B` with `n_A + n_B + 1 = n`, or
`Q ≅ A # S² × S¹` with `n_A + 1 = n`; hence `E.SplitsBelow` (`splitsBelow_of_isLinearSeam`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

universe u

namespace ElementaryPresentation

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)

theorem seam_zero_eq_cutMap (c : Fin E.toTorus.pairing.count) (τ : Torus) :
    E.toTorus.seam c (τ, 0) =
      E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide c true) (τ, halfZero)) := by
  have e := E.seam_eq_sideCollar_true c τ (le_refl (0 : ℝ)) one_pos
  rw [neg_zero] at e
  exact e

theorem seam_zero_mem_target (c : Fin E.toTorus.pairing.count) (τ : Torus) :
    E.toTorus.seam c (τ, 0) ∈ (E.toTorus.seam c).target :=
  (E.toTorus.seam c).map_source' (by rw [E.toTorus.seam_source]; constructor <;> norm_num)

theorem tubeMap_ne_seam {q : S2 × ℝ} (hq : |q.2| < 3) {c : Fin E.toTorus.pairing.count}
    (hc : c ≠ j) (τ : Torus) : (E.splitCharts h hlin).tubeMap q ≠ E.toTorus.seam c (τ, 0) := by
  set C := E.splitCharts h hlin
  have hy := (E.toTorus.sideCollar_zero_mem (E.seamSide c true) τ).1
  rcases lt_trichotomy (SplitTube.seamHeight (SplitTube.heightOf q.1)) 0 with h1 | h1 | h1
  · rw [C.tubeMap_of_neg h1, E.seam_zero_eq_cutMap c τ]
    have hn : ‖(SplitTube.capModel C.e₀ (SplitTube.SplitCharts.side q) q).1‖ < 3 := by
      simp only [SplitTube.capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have := (SplitTube.seamHeight_neg_iff q.1).mp h1
      linarith
    exact (E.toTorus.cutMap_ne_pieceChart _ _ _ _ hy (isLocalDiffeomorphAt_clampDisc hn)).symm
  · rw [C.tubeMap_of_zero h1, SplitTube.SplitCharts.seamModel_of_zero h1]
    intro he
    have hmem : E.seamCoord j b ((GC.GraphManifold.unitOf (SplitTube.planeOf q.1),
        SplitTube.tubeFibre C.e₀ (SplitTube.SplitCharts.side q) q.2), 0) ∈
        (E.toTorus.seam j).source := by
      rw [E.toTorus.seam_source, seamCoord_apply, neg_zero]
      change -1 < sideHeight b 0 ∧ sideHeight b 0 < 1
      cases b <;> simp [sideHeight]
    have h2 : C.seam ((GC.GraphManifold.unitOf (SplitTube.planeOf q.1),
        SplitTube.tubeFibre C.e₀ (SplitTube.SplitCharts.side q) q.2), 0) ∈
        (E.toTorus.seam j).target := (E.toTorus.seam j).map_source' hmem
    rw [he] at h2
    exact Set.disjoint_left.mp (E.toTorus.seam_disjoint (Ne.symm hc)) h2
      (E.seam_zero_mem_target c τ)
  · rw [C.tubeMap_of_pos h1, E.seam_zero_eq_cutMap c τ]
    have hmem := (SplitTube.hostChart_strip_mem C.host
      (SplitTube.abs_heightOf_lt_of_seamHeight_pos h1) h1 hq).1
    exact (E.toTorus.cutMap_ne_pieceChart _ _ _ _ hy (isLocalDiffeomorphAt_clampPants hmem)).symm

theorem exists_seam_avoid {T : SphericalTubeSystem Q.toClosedOrientedManifold}
    (c : Fin E.toTorus.pairing.count) (hdisj : ∀ a q τ, T.tube a q ≠ E.toTorus.seam c (τ, 0)) :
    ∃ ε > 0, ∀ τ s, |s| < ε → ∀ a q, T.tube a q ≠ E.toTorus.seam c (τ, s) := by
  set Z : Set Q.Carrier := ⋃ a, range (T.tube a)
  have hZ : IsClosed Z := (isCompact_iUnion fun a => isCompact_range (T.tube a).continuous).isClosed
  set n : Set (Torus × ℝ) := (E.toTorus.seam c).source ∩ (E.toTorus.seam c) ⁻¹' Zᶜ
  have hn : IsOpen n := (E.toTorus.seam c).contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    (E.toTorus.seam c).open_source hZ.isOpen_compl
  have hsub : (univ : Set Torus) ×ˢ ({0} : Set ℝ) ⊆ n := by
    rintro ⟨τ, s⟩ ⟨-, hs⟩
    simp only [mem_singleton_iff] at hs
    subst hs
    refine ⟨by rw [E.toTorus.seam_source]; constructor <;> norm_num, ?_⟩
    simp only [mem_preimage, mem_compl_iff, Z, mem_iUnion, mem_range, not_exists]
    exact fun a q => hdisj a q τ
  obtain ⟨u, v, -, hv, hu, h0, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hn hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv 0 (h0 rfl)
  refine ⟨ε, hε, fun τ s hs a q he => ?_⟩
  have hmem : (τ, s) ∈ n := huv ⟨hu (mem_univ τ), hball (by simpa [Real.dist_eq] using hs)⟩
  exact hmem.2 (mem_iUnion.mpr ⟨a, q, he⟩)

theorem core_of_not_tube {T : SphericalTubeSystem Q.toClosedOrientedManifold} {x : Q.Carrier}
    (hx : ∀ a q, T.tube a q ≠ x) : x ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ x := by
  refine ⟨?_, fun b' z => hx b'.1 (z, SphericalTubeSystem.boundaryLevel b'.2)⟩
  intro hmem
  simp only [mem_iUnion, SphericalTubeSystem.removedBand, mem_image] at hmem
  obtain ⟨a, q, -, hq⟩ := hmem
  exact hx a q hq

theorem exists_cappedConditions {T : SphericalTubeSystem Q.toClosedOrientedManifold}
    (hT : T = E.splitSeamTube j b h hlin) (a : T.Index) :
    ∃ δ₁ > 0, ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₁ → E.CappedConditions h a δ₂ := by
  subst hT
  have habs : ∀ q : S2 × Icc (-2 : ℝ) 2, |(q.1, q.2.val).2| < 3 := fun q =>
    abs_lt.mpr ⟨by linarith [q.2.2.1], by linarith [q.2.2.2]⟩
  have hdisj : ∀ c, c ≠ j → ∀ a' q τ,
      (E.splitSeamTube j b h hlin).tube a' q ≠ E.toTorus.seam c (τ, 0) :=
    fun c hc a' q τ => E.tubeMap_ne_seam h hlin (habs q) hc τ
  have hex : ∀ c : Fin E.toTorus.pairing.count, ∃ ε > (0 : ℝ), c ≠ j → ∀ τ s, |s| < ε →
      ∀ a' q, (E.splitSeamTube j b h hlin).tube a' q ≠ E.toTorus.seam c (τ, s) := by
    intro c
    by_cases hc : c = j
    · exact ⟨1, one_pos, fun hc' => absurd hc hc'⟩
    · obtain ⟨ε, hε, hav⟩ := E.exists_seam_avoid c (hdisj c hc)
      exact ⟨ε, hε, fun _ => hav⟩
  choose ε hε hav using hex
  have : Nonempty (Fin E.toTorus.pairing.count) := ⟨j⟩
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min ε
  have hsd := (E.splitData h).hδ
  refine ⟨min (min 1 ((E.splitData h).δ / 2)) (ε c₀), lt_min (lt_min one_pos (half_pos hsd))
    (hε c₀), fun δ₂ hδ hδ₁ => ?_⟩
  have h1 : δ₂ ≤ 1 := hδ₁.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : δ₂ ≤ (E.splitData h).δ / 2 := hδ₁.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : δ₂ ≤ ε c₀ := hδ₁.trans (min_le_right _ _)
  refine ⟨hδ, h1, by linarith, fun a' => Subsingleton.elim (α := Unit) a' a, ?_, ?_⟩
  · intro k hkV hkH y hy
    exact core_of_not_tube fun a' q => E.tubeMap_ne_cutMap h hlin (habs q) hkV hkH hy
  · intro c hc τ s hs
    exact core_of_not_tube (hav c hc τ s (lt_of_lt_of_le hs (h3.trans (hc₀ c))))

end ElementaryPresentation

end GC.Seifert
