import DifferentialGeometry.Topology.Ehresmann.ArcEndDefiningFunctionZSP35

/-!
# The end of an embedded arc is not a relative interior point (lane S-BD2d, suffix `_OBDd`), G10c

In a graph-atlas base `Bs`, a set `T ⊆ Bs` which near `γ 0` is the arc `γ [0, 1]` does not contain a
relative neighbourhood of `γ 0` (near `γ 0` the set is a ONE-SIDED coordinate interval:
`exists_arc_end_chart_ZSP35`):

* `arc_end_not_mem_relInterior_OBDd`: `γ 0 ∉ Subtype.val '' interior (Subtype.val ⁻¹' T)`;
* `arc_end_one_not_mem_relInterior_OBDd`: the same for `γ 1` (reversed arc).
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Filter
open scoped ContDiff
open DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}

/-- **The end `γ 0` of an arc isolated in `T` is not a relative interior point of `T`.** -/
theorem arc_end_not_mem_relInterior_OBDd (At : GraphAtlas1_BCF ι Bs) {γ : ℝ → H}
    (hγc : ContinuousOn γ (Icc 0 1)) (hinj : InjOn γ (Icc 0 1)) {T : Set H}
    (hT : γ '' Icc 0 1 ⊆ T) (hTB : T ⊆ Bs)
    (hiso : ∃ N : Set H, IsOpen N ∧ γ 0 ∈ N ∧ T ∩ N ⊆ γ '' Icc 0 1) :
    γ 0 ∉ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
  intro hint
  obtain ⟨-, O, hOo, hγO, hOT⟩ := mem_image_interior_preimage_val_iff.1 hint
  choose V hVo hV using At.piece_relOpen
  obtain ⟨i, σ, ε, V', hσ, hε, hdom, hV'o, hV'B, -, -, hγV', hside⟩ :=
    exists_arc_end_chart_ZSP35 At V hVo (fun y hy => by
      have : y ∈ ⋃ j, At.param j '' At.dom j := by rw [← At.cover]; exact hy
      obtain ⟨j, hj⟩ := mem_iUnion.1 this
      exact mem_iUnion.2 ⟨j, ((Set.ext_iff.1 (hV j) y).2 hj).1⟩)
      (fun j y hy => (Set.ext_iff.1 (hV j) y).1 hy) hγc hinj hT hTB hiso isClosed_empty
      (notMem_empty _)
  set a₀ := At.coord i (γ 0) with ha₀
  -- the chart is continuous at `a₀`
  have hpar : ContinuousAt (At.param i) a₀ :=
    (At.param_smooth i).continuousOn.continuousAt
      ((At.isOpen_dom i).mem_nhds (hdom ⟨by linarith, by linarith⟩))
  have hpa : At.param i a₀ = γ 0 := by
    have hmem : γ 0 ∈ V' ∩ Bs := ⟨hγV', hTB (hT ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)⟩
    rw [hV'B] at hmem
    obtain ⟨b, hb, hbγ⟩ := hmem
    have hbdom : b ∈ At.dom i := hdom (Ioo_subset_Icc_self hb)
    have h1 : At.coord i (At.param i b) = b := At.coord_param i b hbdom
    rw [hbγ] at h1
    have hb0 : b = a₀ := h1.symm
    rw [← hb0]
    exact hbγ
  have hO : O ∈ 𝓝 (At.param i a₀) := hOo.mem_nhds (hpa ▸ hγO)
  obtain ⟨η, hη, hηO⟩ := Metric.eventually_nhds_iff.1 (hpar.eventually hO)
  set r : ℝ := min η ε / 2 with hr
  have hrpos : 0 < r := by
    have : 0 < min η ε := lt_min hη hε
    rw [hr]; linarith
  have hrη : r < η := by
    have := min_le_left η ε
    have h2 : 0 < min η ε := lt_min hη hε
    rw [hr]; linarith
  have hrε : r < ε := by
    have := min_le_right η ε
    have h2 : 0 < min η ε := lt_min hη hε
    rw [hr]; linarith
  set b := a₀ - σ * r with hb
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hbmem : b ∈ Ioo (a₀ - ε) (a₀ + ε) := by
    rcases hσ with h | h <;> rw [hb, h] <;> constructor <;> linarith
  have hbdom : b ∈ At.dom i := hdom (Ioo_subset_Icc_self hbmem)
  have hbO : At.param i b ∈ O := hηO (by
    rw [Real.dist_eq, hb, abs_lt]
    rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith)
  have hpB : At.param i b ∈ Bs := At.param_mem_BCF hbdom
  have hpT : At.param i b ∈ T := hOT ⟨hbO, hpB⟩
  have hs := (hside b hbmem).1 hpT
  rw [hb] at hs
  have : σ * (a₀ - σ * r - a₀) = -r := by
    have : σ * (a₀ - σ * r - a₀) = -(σ * σ) * r := by ring
    rw [this, hσ2]; ring
  rw [this] at hs
  linarith

/-- The same for the end `γ 1`. -/
theorem arc_end_one_not_mem_relInterior_OBDd (At : GraphAtlas1_BCF ι Bs) {γ : ℝ → H}
    (hγc : ContinuousOn γ (Icc 0 1)) (hinj : InjOn γ (Icc 0 1)) {T : Set H}
    (hT : γ '' Icc 0 1 ⊆ T) (hTB : T ⊆ Bs)
    (hiso : ∃ N : Set H, IsOpen N ∧ γ 1 ∈ N ∧ T ∩ N ⊆ γ '' Icc 0 1) :
    γ 1 ∉ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := by
  have hrev : ∀ t ∈ Icc (0 : ℝ) 1, 1 - t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have himg : (fun t => γ (1 - t)) '' Icc (0 : ℝ) 1 = γ '' Icc 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, hrev t ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, hrev t ht, by simp⟩
  have := arc_end_not_mem_relInterior_OBDd At (γ := fun t => γ (1 - t))
    (hγc.comp (continuous_const.sub continuous_id).continuousOn (fun t ht => hrev t ht))
    (fun t ht t' ht' h => by
      have := hinj (hrev t ht) (hrev t' ht') h
      linarith)
    (himg ▸ hT) hTB (by
      obtain ⟨N, hNo, hN1, hNT⟩ := hiso
      exact ⟨N, hNo, by simpa using hN1, himg ▸ hNT⟩)
  simpa using this

end DifferentialGeometry.Topology
