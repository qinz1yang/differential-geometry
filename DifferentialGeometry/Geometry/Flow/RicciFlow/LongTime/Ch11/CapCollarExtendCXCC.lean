import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CapNeckLevelsCXCC
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Topology.Compactness.ProductChartThickening

/-!
# CX-CAPCORE G1：cap 的 core-collar 延伸（后缀 `_CXCC`）

`SpatialLocalCap L`（domain `U`）的 tube chart 是 `η`-neck `nk`（`capTubeHasNeckChart`）时，
构造 global diffeomorphism `Ψ`（collar translation：neck 坐标中把 `[0,1]` 平移 `1`，band 外恒等，
band 下端由紧性取在 `int U \ {x}` 内）：
* `Ψ x = x`，`U ⊆ Ψ U ⊆ U ∪ nk(S² × [1,2])`；
* 新 cap `L' : SpatialLocalCap g η' x (Ψ U)`：`core' = Ψ core`（`CapCore` 由 `Ψ` 搬运）、
  `tube' = nk(S² × [1,2])`，tube chart 是平移 neck `nk'`（tolerance `η' ≥ 13000 η`）。
即 core 吞进旧 tube 整段（`core' = core ∪ tube`），tube 外推一个 neck 单位。
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Metric

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps eta : ℝ} {x v : M} {U : Set M}

omit [SigmaCompactSpace M] in
/-- **collar push**：global diffeomorphism `Ψ`，`Ψ x = x`，neck 坐标中 `[0,1]` 平移 `1`，
`U ⊆ Ψ U ⊆ U ∪ nk(S² × [1,2])`。 -/
theorem SpatialLocalCap.exists_collar_push_CXCC (L : SpatialLocalCap g eps x U)
    (nk : SpatialNeck g eta v) (hnk : ∀ z, L.tubeMap z = nk.map z) (hwin : (4 : ℝ) < eta⁻¹) :
    ∃ Ψ : M ≃ₘ⟮I3, I3⟯ M, Ψ x = x ∧
      (∀ (θ : Sphere 2) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → Ψ (nk.map (θ, t)) = nk.map (θ, t + 1)) ∧
      U ⊆ Ψ '' U ∧
      ∀ y ∈ Ψ '' U, y ∈ U ∨ ∃ θ : Sphere 2, ∃ t ∈ Icc (1 : ℝ) 2, y = nk.map (θ, t) := by
  have hsrc : ∀ (θ' : Sphere 2) {s : ℝ}, s ∈ Ioo (-2 : ℝ) 4 →
      ((θ', s) : Cylinder) ∈ nk.map.source := fun θ' s hs =>
    nk.mem_source_CXCC θ' (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hxcore : x ∈ L.core.carrier := interior_subset L.center_inside
  have hxU : x ∈ U := L.core_inside hxcore |> interior_subset
  have hxtube : x ∉ L.tube := fun h => by
    have hf : x ∈ frontier L.core.carrier := by
      rw [← L.overlap_eq]
      exact ⟨hxcore, h⟩
    exact hf.2 L.center_inside
  -- band around level 0 inside `int U \ {x}`
  have hsrc0 : (univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 0 ⊆ nk.map.source := fun z hz =>
    hsrc z.1 ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hband0 : nk.map.toOpenPartialHomeomorph '' ((univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 0) ⊆
      interior U \ {x} := by
    rintro _ ⟨⟨θ, a⟩, ha, rfl⟩
    have ha0 : a = 0 := le_antisymm ha.2.2 ha.2.1
    subst a
    have hfront : nk.map (θ, 0) ∈ frontier L.core.carrier := by
      rw [L.frontier_core_eq_neck_CXCC nk hnk]
      exact ⟨(θ, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    refine ⟨L.core_inside (L.core.compact.isClosed.frontier_subset hfront), ?_⟩
    intro heq
    have heq' : nk.map (θ, 0) = x := heq
    rw [heq'] at hfront
    exact hfront.2 L.center_inside
  obtain ⟨l, u0, hl, hu0, -, himg0⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band
      nk.map.toOpenPartialHomeomorph le_rfl hsrc0
      (isOpen_interior.sdiff isClosed_singleton) hband0
  set l' := max l (-1) with hl'
  have hl'0 : l' < 0 := max_lt hl (by norm_num)
  have hl'1 : -1 ≤ l' := le_max_right _ _
  have hlow : ∀ (θ : Sphere 2) {s : ℝ}, l' < s → s < u0 → nk.map (θ, s) ∈ interior U \ {x} :=
    fun θ s h1 h2 => himg0 ⟨(θ, s), ⟨mem_univ _, (le_max_left _ _).trans_lt h1, h2⟩, rfl⟩
  have hsource : (univ : Set (Sphere 2)) ×ˢ Ioo l' 3 ⊆ nk.map.source := fun z hz =>
    hsrc z.1 ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨φ, hmove, hpos, hfixφ, F, hFe, hFie, K, -, hKsub, hFfix⟩ :=
    PartialDiffeomorph.exists_collar_translation_isotopy_CXCC nk.map (a := 0) (b := 1)
      (σ := 1) hl'0 zero_le_one (by norm_num : (1 : ℝ) + 1 < 3) hsource
  have hmono : StrictMono (φ 1 : ℝ → ℝ) := strictMono_of_deriv_pos (hpos 1)
  have hφ1 : ∀ t ∈ Icc (0 : ℝ) 1, φ 1 t = t + 1 := fun t ht => by
    simpa only [one_mul] using hmove 1 ⟨zero_le_one, le_rfl⟩ t ht
  have hφl : φ 1 l' = l' := (hfixφ 1).1 (fun h => lt_irrefl _ h.1)
  have hφ0 : φ 1 0 = 1 := by simpa using hφ1 0 ⟨le_rfl, zero_le_one⟩
  -- points of the band lie at levels `(l', 3)`
  have hK : ∀ p ∈ K, ∃ θ : Sphere 2, ∃ s ∈ Ioo l' 3, p = nk.map (θ, s) := by
    intro p hp
    obtain ⟨⟨θ, s⟩, hs, rfl⟩ := hKsub hp
    exact ⟨θ, s, hs.2, rfl⟩
  have hnotU : ∀ (θ : Sphere 2) {s : ℝ}, s ∈ Ioo (1 : ℝ) 3 → nk.map (θ, s) ∉ U :=
    fun θ s hs => L.neck_not_mem_of_one_lt_CXCC nk hnk hwin hs
  have hlevelU : ∀ (θ : Sphere 2) {s : ℝ}, l' < s → s ≤ 1 → nk.map (θ, s) ∈ U := by
    intro θ s h1 h2
    rcases lt_or_ge s u0 with h3 | h3
    · exact interior_subset (hlow θ h1 h3).1
    · exact L.tube_subset_CXCC (L.neck_mem_tube_CXCC nk hnk ⟨hu0.le.trans h3, h2⟩)
  refine ⟨F 1, ?_, ?_, ?_, ?_⟩
  · -- `Ψ x = x`
    apply (hFfix 1).1
    intro hxK
    obtain ⟨θ, s, hs, hxs⟩ := hK x hxK
    rcases lt_or_ge s u0 with h1 | h1
    · exact (hlow θ hs.1 h1).2 hxs.symm
    rcases le_or_gt s 1 with h2 | h2
    · exact hxtube (hxs ▸ L.neck_mem_tube_CXCC nk hnk ⟨hu0.le.trans h1, h2⟩)
    · exact hnotU θ ⟨h2, hs.2⟩ (hxs ▸ hxU)
  · intro θ t ht
    rw [hFe 1 (θ, t) (hsrc θ ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    change nk.map (θ, φ 1 t) = _
    rw [hφ1 t ht]
  · -- `U ⊆ Ψ U`
    intro p hp
    refine ⟨(F 1).symm p, ?_, (F 1).apply_symm_apply p⟩
    by_cases hpK : p ∈ K
    · obtain ⟨θ, s, hs, rfl⟩ := hK p hpK
      have hs1 : s ≤ 1 := by
        by_contra h
        exact hnotU θ ⟨lt_of_not_ge h, hs.2⟩ hp
      rw [hFie 1 (θ, s) (hsource ⟨mem_univ _, hs⟩)]
      change nk.map (θ, (φ 1).symm s) ∈ U
      set w := (φ 1).symm s with hw
      have hφw : φ 1 w = s := (φ 1).apply_symm_apply s
      have hw0 : w ≤ 0 := by
        rw [← hmono.le_iff_le, hφw, hφ0]
        exact hs1
      have hwl : l' < w := by
        rw [← hmono.lt_iff_lt, hφw, hφl]
        exact hs.1
      exact hlevelU θ hwl (hw0.trans zero_le_one)
    · rw [(hFfix 1).2 hpK]
      exact hp
  · -- `Ψ U ⊆ U ∪ nk(S² × [1,2])`
    rintro _ ⟨p, hp, rfl⟩
    by_cases hpK : p ∈ K
    · obtain ⟨θ, s, hs, rfl⟩ := hK p hpK
      have hs1 : s ≤ 1 := by
        by_contra h
        exact hnotU θ ⟨lt_of_not_ge h, hs.2⟩ hp
      rw [hFe 1 (θ, s) (hsource ⟨mem_univ _, hs⟩)]
      change nk.map (θ, φ 1 s) ∈ U ∨ _
      rcases le_or_gt 0 s with h0 | h0
      · right
        refine ⟨θ, s + 1, ⟨by linarith, by linarith⟩, ?_⟩
        rw [hφ1 s ⟨h0, hs1⟩]
      · left
        have h1 : l' < φ 1 s := by
          rw [← hφl]
          exact hmono hs.1
        have h2 : φ 1 s ≤ 1 := by
          calc φ 1 s ≤ φ 1 0 := (hmono h0).le
            _ = 1 := hφ0
        exact hlevelU θ h1 h2
    · left
      rw [(hFfix 1).1 hpK]
      exact hp

omit [T2Space M] [SigmaCompactSpace M] in
private theorem shift_image_Icc_CXCC {nk : SpatialNeck g eta v} {v' : M} {eta' : ℝ}
    {nk' : SpatialNeck g eta' v'}
    (hnk' : ∀ (θ : Sphere 2) (t : ℝ), nk'.map (θ, t) = nk.map (θ, 1 + t))
    (a b : ℝ) :
    nk'.map '' ((univ : Set (Sphere 2)) ×ˢ Icc a b) =
      nk.map '' ((univ : Set (Sphere 2)) ×ˢ Icc (1 + a) (1 + b)) := by
  ext y
  constructor
  · rintro ⟨⟨θ, t⟩, ht, rfl⟩
    exact ⟨(θ, 1 + t), ⟨mem_univ _, by linarith [ht.2.1], by linarith [ht.2.2]⟩,
      (hnk' θ t).symm⟩
  · rintro ⟨⟨θ, t⟩, ht, rfl⟩
    refine ⟨(θ, t - 1), ⟨mem_univ _, by linarith [ht.2.1], by linarith [ht.2.2]⟩, ?_⟩
    rw [hnk' θ (t - 1)]
    congr 2
    ring

omit [SigmaCompactSpace M] in
/-- **core-collar 延伸**：cap `L`（tube chart = `η`-neck `nk`）+ `13000 η ≤ η' < 1/11` ⇒
global diffeomorphism `Ψ`（`Ψ x = x`，`U ⊆ Ψ U ⊆ U ∪ nk(S² × [1,2])`）与新 cap
`L' : SpatialLocalCap g η' x (Ψ U)`：`tube' = nk(S² × [1,2])`、`∂(Ψ U) = nk(S² × {2})`，
tube chart 为平移 `η'`-neck。 -/
theorem SpatialLocalCap.exists_collar_extension_CXCC (L : SpatialLocalCap g eps x U)
    (hUc : IsCompact U) (nk : SpatialNeck g eta v) (hnk : ∀ z, L.tubeMap z = nk.map z)
    {eta' : ℝ} (heta : 13000 * eta ≤ eta') (heta' : eta' < 1 / 11) :
    ∃ Ψ : M ≃ₘ⟮I3, I3⟯ M, Ψ x = x ∧ U ⊆ Ψ '' U ∧
      (∀ y ∈ Ψ '' U, y ∈ U ∨ ∃ θ : Sphere 2, ∃ t ∈ Icc (1 : ℝ) 2, y = nk.map (θ, t)) ∧
      ∃ L' : SpatialLocalCap g eta' x (Ψ '' U),
        L'.tube = nk.map '' ((univ : Set (Sphere 2)) ×ˢ Icc (1 : ℝ) 2) ∧
        frontier (Ψ '' U) = nk.map '' ((univ : Set (Sphere 2)) ×ˢ ({2} : Set ℝ)) ∧
        ∃ (v' : M) (nk' : SpatialNeck g eta' v'), ∀ z, L'.tubeMap z = nk'.map z := by
  have hη := nk.eps_pos
  have hwin : (4 : ℝ) < eta⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hη]
    linarith
  obtain ⟨Ψ, hΨx, hΨt, hUsub, hΨU⟩ := L.exists_collar_push_CXCC nk hnk hwin
  obtain ⟨nk', -, hmap'⟩ := nk.exists_at_coordinate_of_tolerance heta' heta nk.center
    (a := 1) (by rw [abs_one, one_mul]; linarith)
  have hnk' : ∀ (θ : Sphere 2) (t : ℝ), nk'.map (θ, t) = nk.map (θ, 1 + t) :=
    nk.translated_map_apply nk.center nk' hmap'
  have hη'pos : 0 < eta' := nk'.eps_pos
  have h11 : (11 : ℝ) < eta'⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hη'pos]
    linarith
  have key : ∀ z ∈ (univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 1, Ψ (L.tubeMap z) = nk'.map z := by
    rintro ⟨θ, t⟩ hz
    rw [hnk (θ, t), hΨt θ t hz.2, hnk' θ t, add_comm t 1]
  have htube' : Ψ '' L.tube = nk'.map '' ((univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 1) := by
    rw [← L.tube_eq, image_image]
    exact image_congr key
  let Ψ' : PartialDiffeomorph I3 I3 M M ∞ := Ψ.toPartialDiffeomorph
  have hsrc' : ∀ z ∈ (univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 1, z ∈ nk'.map.source :=
    fun z hz => nk'.domain ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  let chain0 : SpatialOrderedNeckChain g eta' (Ψ' '' L.tube) :=
    { count := 1
      count_pos := one_pos
      centers := fun _ => nk.map (nk.center, 1)
      necks := fun _ => nk'
      lo := fun _ => 0
      hi := fun _ => 1
      lo_lt_hi := fun _ => one_pos
      inside := fun _ => hsrc'
      swept_eq := by
        change Ψ '' L.tube = ⋃ _ : Fin 1, nk'.map '' ((univ : Set (Sphere 2)) ×ˢ Icc (0 : ℝ) 1)
        rw [iUnion_const, htube']
      transition_increasing := by
        intro i j hij
        have := i.isLt
        have := j.isLt
        omega }
  let L₀ := L.pushforward Ψ' (fun y _ => mem_univ y) hUc chain0
  have hL₀tube : L₀.tube = Ψ '' L.tube := rfl
  let L' : SpatialLocalCap g eta' x (Ψ '' U) :=
    { core := L₀.core
      core_inside := L₀.core_inside
      center_inside := by
        have h := L₀.center_inside
        change Ψ x ∈ _ at h
        rwa [hΨx] at h
      coreModel := L₀.coreModel
      tube := L₀.tube
      tubeMap := nk'.map
      tube_domain := hsrc'
      tube_eq := by rw [hL₀tube, htube']
      union_eq := L₀.union_eq
      overlap_eq := L₀.overlap_eq
      inner_boundary := (image_congr fun z hz =>
          (key z ⟨hz.1, by rw [hz.2]; exact ⟨le_rfl, zero_le_one⟩⟩).symm).trans
        L₀.inner_boundary
      outer_boundary := (image_congr fun z hz =>
          (key z ⟨hz.1, by rw [hz.2]; exact ⟨zero_le_one, le_rfl⟩⟩).symm).trans
        L₀.outer_boundary
      boundary_eq := L₀.boundary_eq
      boundaries_disjoint := L₀.boundaries_disjoint
      chain := L₀.chain
      coreBoundaryMap := fun z => nk'.map (z, 0)
      core_boundary_eq := fun _ => rfl }
  refine ⟨Ψ, hΨx, hUsub, hΨU, L', ?_, ?_, _, nk', fun _ => rfl⟩
  · change L₀.tube = _
    rw [hL₀tube, htube', shift_image_Icc_CXCC hnk' 0 1]
    norm_num
  · have hout : nk'.map '' ((univ : Set (Sphere 2)) ×ˢ ({1} : Set ℝ)) = frontier (Ψ '' U) :=
      L'.outer_boundary
    rw [← hout]
    ext y
    constructor
    · rintro ⟨⟨θ, t⟩, ht, rfl⟩
      have ht' : t = 1 := ht.2
      refine ⟨(θ, 2), ⟨mem_univ _, rfl⟩, ?_⟩
      rw [hnk', ht']
      norm_num
    · rintro ⟨⟨θ, t⟩, ht, rfl⟩
      have ht' : t = 2 := ht.2
      refine ⟨(θ, 1), ⟨mem_univ _, rfl⟩, ?_⟩
      rw [hnk', ht']
      norm_num

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
