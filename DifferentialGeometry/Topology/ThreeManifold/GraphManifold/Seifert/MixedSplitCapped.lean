import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSplitSideDataStatement
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSurgery

/-!
# Capping conditions of a mixed split

Lane MS, tier MS3 (design `handoffs/20261004-design-ms-mixed-split.md` §1.2, §3). For a linear split
seam `j` on side `b` of a mixed stage `σ` with split datum `S`, the split tube avoids every piece
other than the solid torus `V` and the host `H` (`tubeMap_ne_cutMap`) and the zero torus of every
seam other than `j` (`tubeMap_ne_seam`), hence a whole collar of each such seam
(`exists_seam_avoid`). `CappedConditions` collects what the capped assembly needs (the text of
lane N2c's `CappedConditions`): small positive `δ₂`, one tube, the other pieces and the
`δ₂`-collars of the other seams in the interior of the core; `exists_cappedConditions` gives them
for all small `δ₂`. `disjoint_seamTorus_surgeryRegion` is the zero-torus avoidance asked by
`MixedSplit` for the protected seams. The proofs are lane N2c's
(`Seifert/MoveSplitCappedSurgery.lean`, `Seifert/MoveSplitCappedBelow.lean`) with the elementary
presentation replaced by the mixed stage; the generic `core_of_not_tube` and `exists_seam_avoid`
are restated here so that no file depending on the side-data ledger item is imported.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (sideHeight isLocalDiffeomorphAt_clampDisc
  isLocalDiffeomorphAt_clampPants pieceChart_ne_cutMap)

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool}

theorem core_of_not_tube {T : SphericalTubeSystem Q.toClosedOrientedManifold} {x : Q.Carrier}
    (hx : ∀ a q, T.tube a q ≠ x) : x ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ x := by
  refine ⟨?_, fun b' z => hx b'.1 (z, SphericalTubeSystem.boundaryLevel b'.2)⟩
  intro hmem
  simp only [mem_iUnion, SphericalTubeSystem.removedBand, mem_image] at hmem
  obtain ⟨a, q, -, hq⟩ := hmem
  exact hx a q hq

theorem exists_seam_avoid {T : SphericalTubeSystem Q.toClosedOrientedManifold}
    (c : Fin σ.toTorus.pairing.count) (hdisj : ∀ a q τ, T.tube a q ≠ σ.toTorus.seam c (τ, 0)) :
    ∃ ε > 0, ∀ τ s, |s| < ε → ∀ a q, T.tube a q ≠ σ.toTorus.seam c (τ, s) := by
  set Z : Set Q.Carrier := ⋃ a, range (T.tube a)
  have hZ : IsClosed Z := (isCompact_iUnion fun a => isCompact_range (T.tube a).continuous).isClosed
  set n : Set (Torus × ℝ) := (σ.toTorus.seam c).source ∩ (σ.toTorus.seam c) ⁻¹' Zᶜ
  have hn : IsOpen n := (σ.toTorus.seam c).contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    (σ.toTorus.seam c).open_source hZ.isOpen_compl
  have hsub : (univ : Set Torus) ×ˢ ({0} : Set ℝ) ⊆ n := by
    rintro ⟨τ, s⟩ ⟨-, hs⟩
    simp only [mem_singleton_iff] at hs
    subst hs
    refine ⟨by rw [σ.toTorus.seam_source]; constructor <;> norm_num, ?_⟩
    simp only [mem_preimage, mem_compl_iff, Z, mem_iUnion, mem_range, not_exists]
    exact fun a q => hdisj a q τ
  obtain ⟨u, v, -, hv, hu, h0, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hn hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv 0 (h0 rfl)
  refine ⟨ε, hε, fun τ s hs a q he => ?_⟩
  have hmem : (τ, s) ∈ n := huv ⟨hu (mem_univ τ), hball (by simpa [Real.dist_eq] using hs)⟩
  exact hmem.2 (mem_iUnion.mpr ⟨a, q, he⟩)

variable {h : σ.IsSplitSeam j b} (S : σ.SplitData h) (hlin : σ.IsLinearSeam j)

include h in
theorem seamMap_zero_ne_cutMap (t : Torus) {k : Fin σ.toTorus.components.count}
    (hkV : k ≠ σ.seamPiece j b) (hkH : k ≠ σ.hostPiece j b) {y : σ.toTorus.cutCarrier.Carrier}
    (hy : y ∈ σ.toTorus.components.piece k) : σ.seamMap j b (t, 0) ≠ σ.toTorus.cutMap y := by
  intro he
  rw [σ.seamMap_zero] at he
  have hy0 := (σ.toTorus.sideCollar_zero_mem (σ.seamSide j b) t).2
  rw [σ.sidePiece_seamSide] at hy0
  rcases σ.toTorus.cutMap_eq_cases he with he' | ⟨k', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · rw [he'] at hy0
    exact hkV (TorusPresentation.eq_of_mem_piece' _ hy hy0)
  · have hV : σ.seamPiece k' true = σ.seamPiece j b :=
      TorusPresentation.eq_of_mem_piece' _ (σ.toTorus.left_owned k' h1) hy0
    obtain ⟨rfl, rfl⟩ := σ.eq_of_seamPiece_eq_of_isSplitSeam h hV
    exact hkH (TorusPresentation.eq_of_mem_piece' _ hy (σ.toTorus.right_owned _ h2))
  · have hV : σ.seamPiece k' false = σ.seamPiece j b :=
      TorusPresentation.eq_of_mem_piece' _ (σ.toTorus.right_owned k' h1) hy0
    obtain ⟨rfl, rfl⟩ := σ.eq_of_seamPiece_eq_of_isSplitSeam h hV
    exact hkH (TorusPresentation.eq_of_mem_piece' _ hy (σ.toTorus.left_owned _ h2))

theorem tubeMap_ne_cutMap {q : S2 × ℝ} (hq : |q.2| < 3) {k : Fin σ.toTorus.components.count}
    (hkV : k ≠ σ.seamPiece j b) (hkH : k ≠ σ.hostPiece j b) {y : σ.toTorus.cutCarrier.Carrier}
    (hy : y ∈ σ.toTorus.components.piece k) :
    (σ.splitCharts S hlin).tubeMap q ≠ σ.toTorus.cutMap y := by
  set C := σ.splitCharts S hlin
  rcases lt_trichotomy (SplitTube.seamHeight (SplitTube.heightOf q.1)) 0 with h1 | h1 | h1
  · rw [C.tubeMap_of_neg h1]
    have hn : ‖(SplitTube.capModel C.e₀ (SplitTube.SplitCharts.side q) q).1‖ < 3 := by
      simp only [SplitTube.capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have := (SplitTube.seamHeight_neg_iff q.1).mp h1
      linarith
    exact pieceChart_ne_cutMap _ _ _ _ _ (isLocalDiffeomorphAt_clampDisc hn) hkV hy
  · rw [C.tubeMap_of_zero h1, SplitTube.SplitCharts.seamModel_of_zero h1]
    exact σ.seamMap_zero_ne_cutMap (h := h) _ hkV hkH hy
  · rw [C.tubeMap_of_pos h1]
    have hmem := (SplitTube.hostChart_strip_mem C.host
      (SplitTube.abs_heightOf_lt_of_seamHeight_pos h1) h1 hq).1
    exact pieceChart_ne_cutMap _ _ _ _ _ (isLocalDiffeomorphAt_clampPants hmem) hkH hy

theorem seam_zero_eq_cutMap (c : Fin σ.toTorus.pairing.count) (τ : Torus) :
    σ.toTorus.seam c (τ, 0) =
      σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.seamSide c true) (τ, halfZero)) := by
  have e := (σ.cutMap_sideCollar_eq_seam c true τ 0 le_rfl one_pos).symm
  change σ.toTorus.seam c (τ, -0) = _ at e
  rw [neg_zero] at e
  exact e

theorem seam_zero_mem_target (c : Fin σ.toTorus.pairing.count) (τ : Torus) :
    σ.toTorus.seam c (τ, 0) ∈ (σ.toTorus.seam c).target :=
  (σ.toTorus.seam c).map_source' (by rw [σ.toTorus.seam_source]; constructor <;> norm_num)

theorem tubeMap_ne_seam {q : S2 × ℝ} (hq : |q.2| < 3) {c : Fin σ.toTorus.pairing.count}
    (hc : c ≠ j) (τ : Torus) : (σ.splitCharts S hlin).tubeMap q ≠ σ.toTorus.seam c (τ, 0) := by
  set C := σ.splitCharts S hlin
  have hy := (σ.toTorus.sideCollar_zero_mem (σ.seamSide c true) τ).1
  rcases lt_trichotomy (SplitTube.seamHeight (SplitTube.heightOf q.1)) 0 with h1 | h1 | h1
  · rw [C.tubeMap_of_neg h1, σ.seam_zero_eq_cutMap c τ]
    have hn : ‖(SplitTube.capModel C.e₀ (SplitTube.SplitCharts.side q) q).1‖ < 3 := by
      simp only [SplitTube.capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have := (SplitTube.seamHeight_neg_iff q.1).mp h1
      linarith
    exact (σ.toTorus.cutMap_ne_pieceChart _ _ _ _ hy (isLocalDiffeomorphAt_clampDisc hn)).symm
  · rw [C.tubeMap_of_zero h1, SplitTube.SplitCharts.seamModel_of_zero h1]
    intro he
    have hmem : σ.seamCoord j b ((GC.GraphManifold.unitOf (SplitTube.planeOf q.1),
        SplitTube.tubeFibre C.e₀ (SplitTube.SplitCharts.side q) q.2), 0) ∈
        (σ.toTorus.seam j).source := by
      rw [σ.toTorus.seam_source, seamCoord_apply, neg_zero]
      change -1 < sideHeight b 0 ∧ sideHeight b 0 < 1
      cases b <;> simp [sideHeight]
    have h2 : C.seam ((GC.GraphManifold.unitOf (SplitTube.planeOf q.1),
        SplitTube.tubeFibre C.e₀ (SplitTube.SplitCharts.side q) q.2), 0) ∈
        (σ.toTorus.seam j).target := (σ.toTorus.seam j).map_source' hmem
    rw [he] at h2
    exact Set.disjoint_left.mp (σ.toTorus.seam_disjoint (Ne.symm hc)) h2
      (σ.seam_zero_mem_target c τ)
  · rw [C.tubeMap_of_pos h1, σ.seam_zero_eq_cutMap c τ]
    have hmem := (SplitTube.hostChart_strip_mem C.host
      (SplitTube.abs_heightOf_lt_of_seamHeight_pos h1) h1 hq).1
    exact (σ.toTorus.cutMap_ne_pieceChart _ _ _ _ hy (isLocalDiffeomorphAt_clampPants hmem)).symm

theorem abs_lt_three_of_tube (q : S2 × Icc (-2 : ℝ) 2) : |(q.1, q.2.val).2| < 3 :=
  abs_lt.mpr ⟨by linarith [q.2.2.1], by linarith [q.2.2.2]⟩

theorem disjoint_seamTorus_surgeryRegion {k : Fin σ.toTorus.pairing.count} (hk : k ≠ j) :
    Disjoint (range (σ.toTorus.seamTorus k)) (σ.splitSeamTube S hlin).surgeryRegion := by
  rw [Set.disjoint_left]
  rintro _ ⟨τ, rfl⟩ hmem
  simp only [SphericalTubeSystem.surgeryRegion, mem_iUnion, mem_image] at hmem
  obtain ⟨a, z, -, hz⟩ := hmem
  exact σ.tubeMap_ne_seam S hlin (abs_lt_three_of_tube z) hk τ hz

variable {T : SphericalTubeSystem Q.toClosedOrientedManifold} (a : T.Index) {δ₂ : ℝ}

structure CappedConditions (δ₂ : ℝ) : Prop where
  pos : 0 < δ₂
  le_one : δ₂ ≤ 1
  lt_split : δ₂ < S.δ
  index : ∀ a' : T.Index, a' = a
  piece : ∀ k, k ≠ σ.seamPiece j b → k ≠ σ.hostPiece j b → ∀ y ∈ σ.toTorus.components.piece k,
    σ.toTorus.cutMap y ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ σ.toTorus.cutMap y
  seam : ∀ c, c ≠ j → ∀ τ s, |s| < δ₂ →
    σ.toTorus.seam c (τ, s) ∈ T.core ∧ ∀ b' z, T.boundarySphere b' z ≠ σ.toTorus.seam c (τ, s)

theorem exists_cappedConditions (hT : T = σ.splitSeamTube S hlin) :
    ∃ δ₁ > 0, ∀ δ₂, 0 < δ₂ → δ₂ ≤ δ₁ → σ.CappedConditions S a δ₂ := by
  subst hT
  have hdisj : ∀ c, c ≠ j → ∀ a' q τ,
      (σ.splitSeamTube S hlin).tube a' q ≠ σ.toTorus.seam c (τ, 0) :=
    fun c hc a' q τ => σ.tubeMap_ne_seam S hlin (abs_lt_three_of_tube q) hc τ
  have hex : ∀ c : Fin σ.toTorus.pairing.count, ∃ ε > (0 : ℝ), c ≠ j → ∀ τ s, |s| < ε →
      ∀ a' q, (σ.splitSeamTube S hlin).tube a' q ≠ σ.toTorus.seam c (τ, s) := by
    intro c
    by_cases hc : c = j
    · exact ⟨1, one_pos, fun hc' => absurd hc hc'⟩
    · obtain ⟨ε, hε, hav⟩ := σ.exists_seam_avoid c (hdisj c hc)
      exact ⟨ε, hε, fun _ => hav⟩
  choose ε hε hav using hex
  have : Nonempty (Fin σ.toTorus.pairing.count) := ⟨j⟩
  obtain ⟨c₀, hc₀⟩ := Finite.exists_min ε
  have hsd := S.hδ
  refine ⟨min (min 1 (S.δ / 2)) (ε c₀), lt_min (lt_min one_pos (half_pos hsd))
    (hε c₀), fun δ₂ hδ hδ₁ => ?_⟩
  have h1 : δ₂ ≤ 1 := hδ₁.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : δ₂ ≤ S.δ / 2 := hδ₁.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : δ₂ ≤ ε c₀ := hδ₁.trans (min_le_right _ _)
  refine ⟨hδ, h1, by linarith, fun a' => Subsingleton.elim (α := Unit) a' a, ?_, ?_⟩
  · intro k hkV hkH y hy
    exact core_of_not_tube fun a' q =>
      σ.tubeMap_ne_cutMap S hlin (abs_lt_three_of_tube q) hkV hkH hy
  · intro c hc τ s hs
    exact core_of_not_tube (hav c hc τ s (lt_of_lt_of_le hs (h3.trans (hc₀ c))))

end GC.Seifert.RelativeNormalization.MixedStage
