import DifferentialGeometry.Topology.Morse.Attachment.ManifoldHandle

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open DifferentialGeometry.Topology.Handle
open ManifoldCellAttachment CellAttachment
open scoped _root_.Topology Manifold ContDiff

noncomputable section

private theorem morseCapRoundedLowerRound_mem_iff {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ θ R₀ : ℝ) {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hR0 : 0 ≤ R₀) (hR0lt : R₀ < data.R)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (D : Set M) (hD : morseChartBallImage hk c data ⊆ D)
    {x : M} (hx : x ∈ sublevel f (c - ε)) :
    morseCapRoundedLowerRound hk c ε r δ θ data x ∈ D ↔ x ∈ D := by
  classical
  by_cases hb : x ∈ morseChartBallImage hk c data
  · exact iff_of_true
      (hD (morseCapRoundedLowerRound_mem_ballImage hk c ε r δ θ R₀ data
        hε hδ hθ hδr hR0 hR0lt hbig hx hb)) (hD hb)
  · simp only [morseCapRoundedLowerRound, dif_neg hb]

private def morseAttachingMapOnSet {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r : ℝ) {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (D : Set M) (hD : morseChartBallImage hk c data ⊆ D) :
    AttachingRegion k (m + 1 - k) →
      SublevelSpace (fun x : D => f x.1) (c - ε) := fun a =>
  ⟨⟨(morseAttachingEmbedding hk c ε r data hε hεr a).1, hD (by
      change data.χ (cocoreModelPoint hk ε r a) ∈ morseChartBallImage hk c data
      refine ⟨cocoreModelPoint hk ε r a, ?_, rfl⟩
      exact lt_of_le_of_lt (cocoreModelPoint_norm_le hk ε r hε.le a)
        (lt_trans hεr' (by nlinarith only [data.radius_pos])))⟩,
    (morseAttachingEmbedding hk c ε r data hε hεr a).2⟩

private theorem exists_morseHandleAdjunction_homeomorph_on_set {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ θ R₀ R₀' R₁' : ℝ) {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) (hr : 0 < r)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hR0 : 0 ≤ R₀) (hR0lt : R₀ < data.R)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hRbig : r ^ 2 + 2 * ε + δ ≤ (data.R / 2) ^ 2)
    (hR : R₀' < R₁') (hR0' : 0 ≤ R₀')
    (hbig' : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀' ^ 2)
    (hR₁big : 2 * (data.R / 2) ^ 2 - 2 * ε ≤ R₁' ^ 2)
    (hR₁₂R : R₁' ≤ data.R) (hf : Continuous f)
    (D : Set M) (hD : morseChartBallImage hk c data ⊆ D) :
    let φ := morseAttachingMapOnSet hk c ε r data hε hεr hεr' D hD
    ∃ e : Handle.AdjunctionSpace k (m + 1 - k) φ ≃ₜ
        SublevelSpace (fun x : D => morseRoundedFunction hk c ε r δ R₀' R₁' data x.1) c,
      (∀ x, (e (Handle.lower φ x)).1.1 =
        morseCapRoundedLowerRound hk c ε r δ θ data x.1.1) ∧
      (∀ d, (e (Handle.cell φ d)).1.1 = handleRoundEmbedding hk c ε r δ θ data d) ∧
      (∀ z, (e z).1.1 =
        (morseHandleAdjunctionEquivRoundedSublevel hk c ε r δ θ R₀ R₀' R₁' data
          hε hδ hθ hδr hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig'
          hR₁big hR₁₂R hf
          (Handle.adjunctionMap φ (morseAttachingEmbedding hk c ε r data hε hεr)
            (fun x => ⟨x.1.1, x.2⟩) (fun _ => rfl) z)).1) ∧
      (∀ x, x.1.1 ∉ morseChartBallImage hk c data →
        (e (Handle.lower φ x)).1.1 = x.1.1) := by
  classical
  dsimp only
  let φ := morseAttachingMapOnSet hk c ε r data hε hεr hεr' D hD
  let L : Set M := morseCapRoundedLowerSublevel hk c ε r δ θ data
  let L' : Set D := {x | x.1 ∈ L}
  let R := morseCapRoundedLowerRoundingHomeo hk c ε r δ θ R₀ data
    hε hδ hθ hδr hθr hR0 hR0lt hbig hRbig hf
  have hRD (x : SublevelSpace f (c - ε)) : (R x).1 ∈ D ↔ x.1 ∈ D :=
    morseCapRoundedLowerRound_mem_iff hk c ε r δ θ R₀ data hε hδ hθ hδr hR0 hR0lt hbig D hD x.2
  have hRDsymm (x : L) (hx : x.1 ∈ D) : (R.symm x).1 ∈ D := by
    apply (hRD (R.symm x)).mp
    simpa only [R.apply_symm_apply] using hx
  let eL : SublevelSpace (fun x : D => f x.1) (c - ε) ≃ₜ L' :=
    { toFun := fun x =>
        ⟨⟨(R ⟨x.1.1, x.2⟩).1, (hRD ⟨x.1.1, x.2⟩).mpr x.1.2⟩,
          (R ⟨x.1.1, x.2⟩).2⟩
      invFun := fun x =>
        ⟨⟨(R.symm ⟨x.1.1, x.2⟩).1, hRDsymm ⟨x.1.1, x.2⟩ x.1.2⟩,
          (R.symm ⟨x.1.1, x.2⟩).2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change (R.symm (R ⟨x.1.1, x.2⟩)).1 = x.1.1
        exact congrArg Subtype.val (R.symm_apply_apply ⟨x.1.1, x.2⟩)
      right_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change (R (R.symm ⟨x.1.1, x.2⟩)).1 = x.1.1
        exact congrArg Subtype.val (R.apply_symm_apply ⟨x.1.1, x.2⟩)
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp
          (R.continuous.comp
            ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp
          (R.symm.continuous.comp
            ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)) }
  let j : StandardHandle k (m + 1 - k) → D := fun d =>
    ⟨handleRoundEmbedding hk c ε r δ θ data d,
      hD (handleRoundEmbedding_mem_ballImage hk c ε r δ θ data hε hδ hθ hδr hθr hr hεr' d)⟩
  let ψ : AttachingRegion k (m + 1 - k) → L' := eL ∘ φ
  have hψ (a : AttachingRegion k (m + 1 - k)) :
      (ψ a).1 = j (attachingInclusion k (m + 1 - k) a) := by
    apply Subtype.ext
    change morseCapRoundedLowerRound hk c ε r δ θ data
        (morseAttachingEmbedding hk c ε r data hε hεr a).1 =
      handleRoundEmbedding hk c ε r δ θ data (attachingInclusion k (m + 1 - k) a)
    rw [morseCapRoundedLowerRound_attaching_eq hk c ε r δ θ data hε hεr hεr' a]
    exact (handleRoundEmbedding_attaching_eq_lower hk c ε r δ θ data hε hδ hθ hδr hr a).symm
  have hj : Function.Injective j := by
    intro d d' h
    exact handleRoundEmbedding_injective hk c ε r δ θ data hε hδ hθ hδr hθr hr hεr
      (congrArg Subtype.val h)
  have hcj : Continuous j :=
    (handleRoundEmbedding_continuous hk c ε r δ θ data hε hδ hθ hδr hθr hr hεr).subtype_mk _
  have hmeet : Disjoint (j '' (univ \ attachingRegion k (m + 1 - k))) L' := by
    rw [Set.disjoint_left]
    rintro x ⟨d, hd, rfl⟩ hx
    exact (Set.disjoint_left.mp
      (disjoint_handleRoundEmbedding_capRoundedLowerSublevel hk c ε r δ θ data
        hε hδ hθ hδr hθr hr hεr hεr')) ⟨d, hd, rfl⟩ hx
  have hclosed : IsClosed L' :=
    (isClosed_morseCapRoundedLowerSublevel hk c ε r δ θ data hθ hδ hδr hθr hf).preimage
      continuous_subtype_val
  let eA := Handle.adjunctionCongr φ ψ eL (fun _ => rfl)
  let eU := Handle.adjunctionHomeomorphUnionImage ψ j hψ hj hcj hmeet hclosed
  have hsets : L' ∪ range j =
      sublevel (fun x : D => morseRoundedFunction hk c ε r δ R₀' R₁' data x.1) c := by
    have hambient : L ∪ range (handleRoundEmbedding hk c ε r δ θ data) =
        sublevel (morseRoundedFunction hk c ε r δ R₀' R₁' data) c :=
      (morseCapRoundedLowerUnion_eq_roundedAttachment hk c ε r δ θ data
        hε hδ hθ hδr hθr hr hεr' hRbig).trans
        (sublevel_morseRoundedFunction_eq_roundedAttachment hk c ε r δ R₀' R₁' data
          hε hδ hR hR0' hbig' hRbig hR₁big hR₁₂R).symm
    ext x
    change x ∈ L' ∪ range j ↔ x.1 ∈ sublevel _ c
    rw [← hambient]
    constructor
    · rintro (hx | ⟨d, rfl⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨d, rfl⟩
    · rintro (hx | ⟨d, hd⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨d, Subtype.ext hd⟩
  let e := (eA.trans eU).trans (Homeomorph.setCongr hsets)
  have hlower (x : SublevelSpace (fun x : D => f x.1) (c - ε)) :
      (e (Handle.lower φ x)).1.1 = morseCapRoundedLowerRound hk c ε r δ θ data x.1.1 := by
    change (eU (eA (Handle.lower φ x))).1.1 = _
    rw [Handle.adjunctionCongr_lower, Handle.adjunctionHomeomorphUnionImage_lower]
    rfl
  have hcell (d : StandardHandle k (m + 1 - k)) :
      (e (Handle.cell φ d)).1.1 = handleRoundEmbedding hk c ε r δ θ data d := by
    change (eU (eA (Handle.cell φ d))).1.1 = _
    rw [Handle.adjunctionCongr_cell, Handle.adjunctionHomeomorphUnionImage_cell]
  refine ⟨e, hlower, hcell, ?_, ?_⟩
  · intro z
    rcases Handle.cell_lower_cover φ z with ⟨d, rfl⟩ | ⟨x, rfl⟩
    · exact (hcell d).trans
        (morseHandleAdjunctionEquivRoundedSublevel_cell hk c ε r δ θ R₀ R₀' R₁' data
          hε hδ hθ hδr hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig'
          hR₁big hR₁₂R hf d).symm
    · exact (hlower x).trans
        (morseHandleAdjunctionEquivRoundedSublevel_lower hk c ε r δ θ R₀ R₀' R₁' data
          hε hδ hθ hδr hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig'
          hR₁big hR₁₂R hf ⟨x.1.1, x.2⟩).symm
  · intro x hx
    rw [hlower]
    simp only [morseCapRoundedLowerRound, dif_neg hx]


theorem exists_morseHandleAdjunction_homeomorph_roundedSublevel_on_set
    {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ θ R₀ R₀' R₁' : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hδr : δ < r ^ 2)
    (hθr : θ < r ^ 2) (hr : 0 < r)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hR0 : 0 ≤ R₀) (hR0lt : R₀ < data.R)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2)
    (hRbig : r ^ 2 + 2 * ε + δ ≤ (data.R / 2) ^ 2)
    (hR : R₀' < R₁') (hR0' : 0 ≤ R₀')
    (hbig' : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀' ^ 2)
    (hR₁big : 2 * (data.R / 2) ^ 2 - 2 * ε ≤ R₁' ^ 2)
    (hR₁₂R : R₁' ≤ data.R) (hf : Continuous f)
    (D : Set M) (hD : morseChartBallImage hk c data ⊆ D) :
    ∃ φ : C(AttachingRegion k (m + 1 - k), SublevelSpace (fun x : D => f x.1) (c - ε)),
      ∃ hφ : ∀ a, (φ a).1.1 = (morseAttachingEmbedding hk c ε r data hε hεr a).1,
        ∃ e : Handle.AdjunctionSpace k (m + 1 - k) φ ≃ₜ
            SublevelSpace (fun x : D => morseRoundedFunction hk c ε r δ R₀' R₁' data x.1) c,
          (∀ x, (e (Handle.lower φ x)).1.1 =
            morseCapRoundedLowerRound hk c ε r δ θ data x.1.1) ∧
          (∀ d, (e (Handle.cell φ d)).1.1 = handleRoundEmbedding hk c ε r δ θ data d) ∧
          (∀ z, (e z).1.1 =
            (morseHandleAdjunctionEquivRoundedSublevel hk c ε r δ θ R₀ R₀' R₁' data
              hε hδ hθ hδr hθr hr hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig'
              hR₁big hR₁₂R hf
              (Handle.adjunctionMap φ (morseAttachingEmbedding hk c ε r data hε hεr)
                (fun x => ⟨x.1.1, x.2⟩) (fun a => Subtype.ext (hφ a)) z)).1) ∧
          (∀ x, x.1.1 ∉ morseChartBallImage hk c data →
            (e (Handle.lower φ x)).1.1 = x.1.1) := by
  let φ₀ := morseAttachingMapOnSet hk c ε r data hε hεr hεr' D hD
  have hc : Continuous (fun a => (φ₀ a).1.1) := by
    refine ((handleEmbedding_continuous hk c ε r data hε hεr).comp
      (continuous_attachingInclusion k (m + 1 - k))).congr ?_
    intro a
    exact (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε hεr a).symm
  let φ : C(AttachingRegion k (m + 1 - k), SublevelSpace (fun x : D => f x.1) (c - ε)) :=
    ⟨φ₀, (hc.subtype_mk (fun a => (φ₀ a).1.2)).subtype_mk (fun a => (φ₀ a).2)⟩
  have hφ : ∀ a, (φ a).1.1 = (morseAttachingEmbedding hk c ε r data hε hεr a).1 :=
    fun _ => rfl
  obtain ⟨e, hlower, hcell, hcomm, houtside⟩ :=
    exists_morseHandleAdjunction_homeomorph_on_set hk c ε r δ θ R₀ R₀' R₁' data hε hδ hθ hδr hθr hr
      hεr hεr' hR0 hR0lt hbig hRbig hR hR0' hbig' hR₁big hR₁₂R hf D hD
  refine ⟨φ, hφ, e, hlower, hcell, ?_, houtside⟩
  intro z
  exact hcomm z

end

end DifferentialGeometry.Topology.Morse
