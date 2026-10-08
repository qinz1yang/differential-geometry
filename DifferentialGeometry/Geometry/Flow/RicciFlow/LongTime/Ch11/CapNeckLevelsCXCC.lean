import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CapCollarPushCXCC
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness

/-!
# CX-CAPCORE G1：cap tube 的 neck level 结构与 level 间距离（后缀 `_CXCC`）

`SpatialLocalCap L` 的 tube chart 是一个 `η`-neck `nk`（`capTubeHasNeckChart`）时：
* level 描述：`tube = nk(S² × [0,1])`、`∂core = nk(S² × {0})`、`∂U = nk(S² × {1})`；
  `nk(θ, t) ∈ core ↔ t = 0`（`t ∈ [0,1]`）；**level `(1, 3)` 在 `U` 之外**
  （`neck_not_mem_of_one_lt_CXCC`：连通性 + `∂U` 处的开映像论证）。
* 距离：level gap `≥ 1` 的两点 `d ≥ (4/5)/√R(v)`（`ofReal_le_edist_of_level_gap_CXCC`，
  在 `(θ₀, a)` 处平移 neck 后用 `ball_subset_image_slab`）；同一 fiber 上
  `d ≤ (101/100)|a − b|/√R(v)`（`edist_axial_le_CXCC`）。
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
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps eta : ℝ} {x v : M} {U : Set M}

omit [T2Space M] in
theorem SpatialNeck.mem_source_CXCC (nk : SpatialNeck g eta v) (θ : Sphere 2) {t : ℝ}
    (ht : |t| < eta⁻¹) : ((θ, t) : Cylinder) ∈ nk.map.source :=
  nk.domain ⟨mem_univ _, abs_lt.mp ht⟩

omit [T2Space M] in
theorem SpatialNeck.map_inj_CXCC (nk : SpatialNeck g eta v) {z w : Cylinder}
    (hz : z ∈ nk.map.source) (hw : w ∈ nk.map.source) (h : nk.map z = nk.map w) : z = w :=
  nk.map.toPartialEquiv.injOn hz hw h

section CapLevels

variable (L : SpatialLocalCap g eps x U) (nk : SpatialNeck g eta v)
  (hnk : ∀ z, L.tubeMap z = nk.map z)
include hnk

omit [T2Space M] in
theorem SpatialLocalCap.tube_eq_neck_CXCC :
    L.tube = nk.map '' (univ ×ˢ Icc (0 : ℝ) 1) := by
  rw [← L.tube_eq]
  exact image_congr fun z _ => hnk z

omit [T2Space M] in
theorem SpatialLocalCap.frontier_core_eq_neck_CXCC :
    frontier L.core.carrier = nk.map '' (univ ×ˢ ({0} : Set ℝ)) := by
  rw [← L.inner_boundary]
  exact image_congr fun z _ => hnk z

omit [T2Space M] in
theorem SpatialLocalCap.frontier_eq_neck_CXCC :
    frontier U = nk.map '' (univ ×ˢ ({1} : Set ℝ)) := by
  rw [← L.outer_boundary]
  exact image_congr fun z _ => hnk z

omit [T2Space M] hnk in
theorem SpatialLocalCap.tube_subset_CXCC : L.tube ⊆ U :=
  subset_union_right.trans L.union_eq.ge

omit [T2Space M] in
theorem SpatialLocalCap.neck_mem_tube_CXCC {θ : Sphere 2} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    nk.map (θ, t) ∈ L.tube := by
  rw [L.tube_eq_neck_CXCC nk hnk]
  exact ⟨(θ, t), ⟨mem_univ _, ht⟩, rfl⟩

omit [T2Space M] in
/-- `t ∈ [0,1]`：`nk(θ, t) ∈ core ↔ t = 0`。 -/
theorem SpatialLocalCap.neck_mem_core_iff_CXCC (hwin : (4 : ℝ) < eta⁻¹) {θ : Sphere 2} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : nk.map (θ, t) ∈ L.core.carrier ↔ t = 0 := by
  have hsrc : ∀ (θ' : Sphere 2) {s : ℝ}, s ∈ Icc (0 : ℝ) 1 →
      ((θ', s) : Cylinder) ∈ nk.map.source := fun θ' s hs =>
    nk.mem_source_CXCC θ' (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
  constructor
  · intro hcore
    have hb : nk.map (θ, t) ∈ frontier L.core.carrier :=
      L.overlap_eq ▸ ⟨hcore, L.neck_mem_tube_CXCC nk hnk ht⟩
    rw [L.frontier_core_eq_neck_CXCC nk hnk] at hb
    obtain ⟨⟨w, b⟩, hb0, heq⟩ := hb
    have hb0' : b = 0 := hb0.2
    have h := nk.map_inj_CXCC (hsrc w ⟨hb0'.ge, hb0'.le.trans zero_le_one⟩) (hsrc θ ht) heq
    exact (congrArg Prod.snd h).symm.trans hb0'
  · rintro rfl
    have hb : nk.map (θ, 0) ∈ frontier L.core.carrier := by
      rw [L.frontier_core_eq_neck_CXCC nk hnk]
      exact ⟨(θ, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    rw [← L.overlap_eq] at hb
    exact hb.1

omit [T2Space M] in
/-- **level `(1, 3)` 在 `U` 之外**：`S² × (1,3)` 的像连通、不碰 `∂U = nk(S² × {1})`；若落在 `int U`
则 `nk(S² × (0,3))` 是含 `∂U` 点的开集且 `⊆ U`，矛盾。 -/
theorem SpatialLocalCap.neck_not_mem_of_one_lt_CXCC (hwin : (4 : ℝ) < eta⁻¹) {θ : Sphere 2}
    {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 3) : nk.map (θ, t) ∉ U := by
  have hsrc : ∀ (θ' : Sphere 2) {s : ℝ}, s ∈ Ioo (-1 : ℝ) 4 →
      ((θ', s) : Cylinder) ∈ nk.map.source := fun θ' s hs =>
    nk.mem_source_CXCC θ' (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hSsrc : (univ : Set (Sphere 2)) ×ˢ Ioo (1 : ℝ) 3 ⊆ nk.map.source := fun z hz =>
    hsrc z.1 ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hOsrc : (univ : Set (Sphere 2)) ×ˢ Ioo (0 : ℝ) 3 ⊆ nk.map.source := fun z hz =>
    hsrc z.1 ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  set S := nk.map '' ((univ : Set (Sphere 2)) ×ˢ Ioo (1 : ℝ) 3) with hS
  have hSconn : IsPreconnected S :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (nk.map.contMDiffOn_toFun.continuousOn.mono hSsrc)
  have hfrontU := L.frontier_eq_neck_CXCC nk hnk
  have hSdisj : ∀ y ∈ S, y ∉ frontier U := by
    rintro _ ⟨⟨θ1, s⟩, hs, rfl⟩ hf
    rw [hfrontU] at hf
    obtain ⟨⟨θ2, s2⟩, hs2, heq⟩ := hf
    have hs2' : s2 = 1 := hs2.2
    have h := nk.map_inj_CXCC (hsrc θ2 ⟨by linarith, by linarith⟩) (hSsrc hs) heq
    have h2 : s2 = s := congrArg Prod.snd h
    linarith [hs.2.1]
  have hcover : S ⊆ interior U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hc : y ∈ closure U
    · left
      by_contra hi
      exact hSdisj y hy ⟨hc, hi⟩
    · exact Or.inr hc
  rcases hSconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset_closure) hcover with hin | hout
  · exfalso
    have hpf : nk.map (θ, 1) ∈ frontier U := by
      rw [hfrontU]
      exact ⟨(θ, 1), ⟨mem_univ _, rfl⟩, rfl⟩
    have hO : IsOpen (nk.map '' ((univ : Set (Sphere 2)) ×ˢ Ioo (0 : ℝ) 3)) :=
      nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (isOpen_univ.prod isOpen_Ioo) hOsrc
    have hOU : nk.map '' ((univ : Set (Sphere 2)) ×ˢ Ioo (0 : ℝ) 3) ⊆ U := by
      rintro _ ⟨⟨θ1, s⟩, hs, rfl⟩
      rcases le_or_gt s 1 with h1 | h1
      · exact L.tube_subset_CXCC (L.neck_mem_tube_CXCC nk hnk ⟨hs.2.1.le, h1⟩)
      · exact interior_subset (hin ⟨(θ1, s), ⟨mem_univ _, h1, hs.2.2⟩, rfl⟩)
    have hpint : nk.map (θ, 1) ∈ interior U :=
      interior_maximal hOU hO ⟨(θ, 1), ⟨mem_univ _, by norm_num, by norm_num⟩, rfl⟩
    exact hpf.2 hpint
  · intro hU
    exact hout ⟨(θ, t), ⟨mem_univ _, ht⟩, rfl⟩ (subset_closure hU)

end CapLevels

/-- **level gap 下界**：`|a| ≤ 1`、`a + 1 ≤ b ≤ 3`、`13000 η < 1/11` ⇒
`(4/5)/√R(v) ≤ d(nk(θ₀, a), nk(θ₁, b))`。 -/
theorem SpatialNeck.ofReal_le_edist_of_level_gap_CXCC (nk : SpatialNeck g eta v)
    (heta : 13000 * eta < 1 / 11) (θ0 θ1 : Sphere 2) {a b : ℝ} (ha : |a| ≤ 1)
    (hab : a + 1 ≤ b) (hb : b ≤ 3) :
    ENNReal.ofReal ((4 / 5) / Real.sqrt (metricScalarAt g v)) ≤
      riemannianEDistOf g (nk.map (θ0, a)) (nk.map (θ1, b)) := by
  have hη := nk.eps_pos
  have hηs : eta < 1 / 143000 := by linarith
  have hinv : (143000 : ℝ) < eta⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hη]
    linarith
  have hshift : |a| * eta ≤ 1 / 2 := by nlinarith [abs_nonneg a]
  obtain ⟨out, -, hmap⟩ := nk.exists_at_coordinate_of_tolerance heta le_rfl θ0 hshift
  have hα : 0 < 13000 * eta := by positivity
  have hαinv : (9 / 10 : ℝ) < (13000 * eta)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hα]
    linarith
  have hball := out.ball_subset_image_slab (r := 9 / 10) (by norm_num) hαinv
  have hwa : ((θ0, a) : Cylinder) ∈ univ ×ˢ Ioo (-eta⁻¹) eta⁻¹ :=
    ⟨mem_univ _, abs_lt.mp (by linarith)⟩
  have hQv := nk.Q_pos
  have hQz := out.Q_pos
  have hratio := (nk.scalar_bounds_on_image_window ⟨(θ0, a), hwa, rfl⟩).2
  -- numeric comparison
  have hsα : (19 / 20 : ℝ) ≤ Real.sqrt (1 - 13000 * eta) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hsz : Real.sqrt (metricScalarAt g (nk.map (θ0, a))) ≤
      (51 / 50) * Real.sqrt (metricScalarAt g v) := by
    have h1 : metricScalarAt g (nk.map (θ0, a)) ≤ (51 / 50) ^ 2 * metricScalarAt g v := by
      nlinarith
    calc Real.sqrt (metricScalarAt g (nk.map (θ0, a)))
        ≤ Real.sqrt ((51 / 50) ^ 2 * metricScalarAt g v) := Real.sqrt_le_sqrt h1
      _ = (51 / 50) * Real.sqrt (metricScalarAt g v) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hsv : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr hQv
  have hszp : 0 < Real.sqrt (metricScalarAt g (nk.map (θ0, a))) := Real.sqrt_pos.mpr hQz
  have hnum : (4 / 5) / Real.sqrt (metricScalarAt g v) ≤
      9 / 10 * Real.sqrt (1 - 13000 * eta) / Real.sqrt (metricScalarAt g (nk.map (θ0, a))) := by
    rw [div_le_div_iff₀ hsv hszp]
    nlinarith
  apply le_of_not_gt
  intro hlt
  have hy : nk.map (θ1, b) ∈ riemannianBallOf g (nk.map (θ0, a))
      (9 / 10 * Real.sqrt (1 - 13000 * eta) /
        Real.sqrt (metricScalarAt g (nk.map (θ0, a)))) :=
    hlt.trans_le (ENNReal.ofReal_le_ofReal hnum)
  obtain ⟨⟨θ2, s⟩, hs, heq⟩ := hball hy
  rw [nk.translated_map_apply θ0 out hmap] at heq
  have hsrc1 : ((θ2, a + s) : Cylinder) ∈ nk.map.source :=
    nk.mem_source_CXCC θ2 (by
      rw [abs_lt]
      have := abs_le.mp ha
      constructor <;> linarith [hs.2.1, hs.2.2])
  have hsrc2 : ((θ1, b) : Cylinder) ∈ nk.map.source :=
    nk.mem_source_CXCC θ1 (by
      rw [abs_lt]
      have := abs_le.mp ha
      constructor <;> linarith)
  have h := congrArg Prod.snd (nk.map_inj_CXCC hsrc1 hsrc2 heq)
  change a + s = b at h
  linarith [hs.2.2]

omit [T2Space M] in
/-- 同一 fiber 上的轴向上界：`d(nk(θ, a), nk(θ, b)) ≤ (101/100)|a − b|/√R(v)`（`η ≤ 1/50`）。 -/
theorem SpatialNeck.edist_axial_le_CXCC (nk : SpatialNeck g eta v) (heta : eta ≤ 1 / 50)
    (θ : Sphere 2) {a b : ℝ} (ha : |a| < eta⁻¹) (hb : |b| < eta⁻¹) :
    riemannianEDistOf g (nk.map (θ, a)) (nk.map (θ, b)) ≤
      ENNReal.ofReal ((101 / 100) * |a - b| / Real.sqrt (metricScalarAt g v)) := by
  have hη := nk.eps_pos
  refine (nk.edist_same_fiber_le θ (abs_lt.mp ha) (abs_lt.mp hb)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hs : Real.sqrt (1 + eta) ≤ 101 / 100 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
