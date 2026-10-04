import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollar
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarRescale

/-!
# CuttingSphereTwoSidedCollar
-/

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def cuttingTwoSidedWidth (δ : ℝ) : ℝ := min (1 / 2) (δ⁻¹ / 2)

theorem cuttingTwoSidedWidth_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < cuttingTwoSidedWidth δ :=
  lt_min (by norm_num) (half_pos (inv_pos.mpr hδ))

private def outwardRaw {δ : ℝ} (b : Bool)
    (q : S2 × Ioo (-cuttingTwoSidedWidth δ) (cuttingTwoSidedWidth δ)) : S2 × ℝ :=
  (q.1, cuttingSign b - cuttingSign b * q.2.val)

private theorem outwardRaw_mem {δ : ℝ} (hδ : 0 < δ) (b : Bool)
    (q : S2 × Ioo (-cuttingTwoSidedWidth δ) (cuttingTwoSidedWidth δ)) :
    outwardRaw b q ∈ bufferedCylinder δ := by
  have hd := inv_pos.mpr hδ
  have hw : cuttingTwoSidedWidth δ ≤ δ⁻¹ / 2 := min_le_right _ _
  have ht := q.2.property
  change -δ⁻¹ - 1 < cuttingSign b - cuttingSign b * q.2.val ∧
    cuttingSign b - cuttingSign b * q.2.val < δ⁻¹ + 1
  cases b <;> norm_num [cuttingSign] <;> constructor <;> linarith [ht.1, ht.2]

def cuttingOutwardCylinderMap {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    S2 × Ioo (-cuttingTwoSidedWidth δ) (cuttingTwoSidedWidth δ) → bufferedCylinder δ :=
  fun q => ⟨outwardRaw b q, outwardRaw_mem hδ b q⟩

theorem cuttingOutwardCylinderMap_val {δ : ℝ} (hδ : 0 < δ) (b : Bool)
    (q : S2 × Ioo (-cuttingTwoSidedWidth δ) (cuttingTwoSidedWidth δ)) :
    (cuttingOutwardCylinderMap hδ b q).val =
      (q.1, cuttingSign b - cuttingSign b * q.2.val) := rfl

theorem isOpenEmbedding_cuttingOutwardCylinderMap {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    _root_.Topology.IsOpenEmbedding (cuttingOutwardCylinderMap hδ b) := by
  have hv : _root_.Topology.IsOpenEmbedding
      (fun q : S2 × Ioo (-cuttingTwoSidedWidth δ) (cuttingTwoSidedWidth δ) =>
        (q.1, q.2.val)) :=
    _root_.Topology.IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal
  have hr : _root_.Topology.IsOpenEmbedding (outwardRaw (δ := δ) b) := by
    have he : outwardRaw (δ := δ) b = fun q =>
        (q.1, cuttingSign b + (-cuttingSign b) * q.2.val) := by
      funext q
      simp only [outwardRaw, sub_eq_add_neg, neg_mul]
    rw [he]
    exact (cylinderAxialDiffeomorph (I := 𝓡 2) (M := S2) (cuttingSign b) (-cuttingSign b)
      (by simpa only [neg_sq] using cuttingSign_sq b)).toHomeomorph.isOpenEmbedding.comp hv
  exact .of_isEmbedding_isOpenMap
    (hr.isEmbedding.codRestrict (bufferedCylinder δ) (outwardRaw_mem hδ b))
    (hr.isOpenMap.codRestrict (outwardRaw_mem hδ b))

variable {ι M : Type*} {precision : ι → ℝ} [TopologicalSpace M]

def cuttingSphereTwoSidedCollar (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (b : ι × Bool) :
    TwoSidedCollar (fun y : S2 => cuttingSphereMap hδ f ⟨b, y⟩) := by
  refine TwoSidedCollar.ofOpenInterval (cuttingTwoSidedWidth_pos (hδ b.1))
    (f b.1 ∘ cuttingOutwardCylinderMap (hδ b.1) b.2)
    ((hf b.1).comp (isOpenEmbedding_cuttingOutwardCylinderMap (hδ b.1) b.2)) ?_
  intro y
  apply congrArg (f b.1)
  apply Subtype.ext
  exact Prod.ext rfl (by simp [outwardRaw, cuttingOutwardCylinderMap])

theorem cuttingSphereTwoSidedCollar_apply (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (b : ι × Bool) (y : S2) (t : ℝ) :
    (cuttingSphereTwoSidedCollar hδ f hf b).toFun (y, t) =
      f b.1 (cuttingOutwardCylinderMap (hδ b.1) b.2 (y,
        TwoSidedCollar.realHomeomorphIoo (cuttingTwoSidedWidth (precision b.1))
          (cuttingTwoSidedWidth_pos (hδ b.1)) t)) := rfl

omit [TopologicalSpace M] in
theorem cuttingOutward_mem_cutCore_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool)
    (q : S2 × Ioo (-cuttingTwoSidedWidth (precision b.1))
      (cuttingTwoSidedWidth (precision b.1))) :
    f b.1 (cuttingOutwardCylinderMap (hδ b.1) b.2 q) ∈ cutCore f ↔ q.2.val ≤ 0 := by
  rw [cutCore_chart_iff f hf hdisj]
  change (cuttingSign b.2 - cuttingSign b.2 * q.2.val ≤ -1 ∨
    1 ≤ cuttingSign b.2 - cuttingSign b.2 * q.2.val) ↔ q.2.val ≤ 0
  have hw : cuttingTwoSidedWidth (precision b.1) ≤ 1 / 2 := min_le_left _ _
  have ht := q.2.property
  cases hb : b.2 <;> norm_num [cuttingSign, hb] <;>
    intro h <;> linarith [ht.2]

theorem cuttingSphereTwoSidedCollar_mem_cutCore_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (y : S2) (t : ℝ) :
    (cuttingSphereTwoSidedCollar hδ f hf b).toFun (y, t) ∈ cutCore f ↔ t ≤ 0 := by
  rw [cuttingSphereTwoSidedCollar_apply,
    cuttingOutward_mem_cutCore_iff hδ f (fun i => (hf i).injective) hdisj]
  exact not_lt.symm.trans ((not_congr
    (TwoSidedCollar.realHomeomorphIoo_pos_iff
      (cuttingTwoSidedWidth (precision b.1)) (cuttingTwoSidedWidth_pos (hδ b.1)) t)).trans not_lt)

omit [TopologicalSpace M] in
theorem pairwise_disjoint_cuttingOutwardCollars (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Pairwise (fun b c : ι × Bool => Disjoint
      (range (f b.1 ∘ cuttingOutwardCylinderMap (hδ b.1) b.2))
      (range (f c.1 ∘ cuttingOutwardCylinderMap (hδ c.1) c.2))) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hbc
  apply disjoint_left.mpr
  rintro p ⟨q, rfl⟩ ⟨r, hr⟩
  by_cases hij : i = j
  · subst j
    have hne : b ≠ c := fun h => hbc (Prod.ext rfl h)
    have hs := congrArg (fun x : bufferedCylinder (precision i) => x.val.2) (hf i hr.symm)
    change cuttingSign b - cuttingSign b * q.2.val =
      cuttingSign c - cuttingSign c * r.2.val at hs
    have hw : cuttingTwoSidedWidth (precision i) ≤ 1 / 2 := min_le_left _ _
    have hq := q.2.property.2
    have hr' := r.2.property.2
    cases b <;> cases c
    · exact hne rfl
    · norm_num [cuttingSign] at hs
      linarith
    · norm_num [cuttingSign] at hs
      linarith
    · exact hne rfl
  · exact disjoint_left.mp (hdisj hij) ⟨_, rfl⟩ ⟨_, hr⟩

theorem pairwise_disjoint_cuttingSphereTwoSidedCollars (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Pairwise (fun b c : ι × Bool => Disjoint
      (cuttingSphereTwoSidedCollar hδ f hf b).range
      (cuttingSphereTwoSidedCollar hδ f hf c).range) := by
  intro b c hbc
  apply (pairwise_disjoint_cuttingOutwardCollars hδ f (fun i => (hf i).injective) hdisj hbc).mono
  · rintro p ⟨⟨y, t⟩, rfl⟩
    exact ⟨_, (cuttingSphereTwoSidedCollar_apply hδ f hf b y t).symm⟩
  · rintro p ⟨⟨y, t⟩, rfl⟩
    exact ⟨_, (cuttingSphereTwoSidedCollar_apply hδ f hf c y t).symm⟩

end DifferentialGeometry.Topology.ThreeManifold.Surgery
