import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingSphereAttachment

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
variable {ι M : Type*} {precision : ι → ℝ}

theorem cutCore_chart_iff (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (i : ι) (q : bufferedCylinder (precision i)) :
    f i q ∈ cutCore f ↔ q.val.2 ≤ -1 ∨ 1 ≤ q.val.2 := by
  have he : f i q ∈ cutCore f ↔ q ∉ centralDomain (precision i) := by
    constructor
    · intro hx hq
      exact hx (mem_iUnion.mpr ⟨i, ⟨q, hq, rfl⟩⟩)
    · intro hq hx
      obtain ⟨j, r, hr, he⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · subst j
        exact hq ((hf i he) ▸ hr)
      · exact disjoint_left.mp (hdisj hji) ⟨r, he⟩ ⟨q, rfl⟩
  simpa only [centralDomain, mem_preimage, mem_ofPred_eq, mem_Ioo, not_and_or, not_lt] using he

def cuttingCollarWidth (δ : ℝ) : ℝ := δ⁻¹ / 2

theorem cuttingCollarWidth_pos {δ : ℝ} (hδ : 0 < δ) : 0 < cuttingCollarWidth δ :=
  half_pos (inv_pos.mpr hδ)

private def collarRaw {δ : ℝ} (b : Bool) (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)) : S2 × ℝ :=
  (q.1, cuttingSign b + cuttingSign b * q.2.val)
private theorem collarRaw_mem {δ : ℝ} (hδ : 0 < δ) (b : Bool)
    (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)) : collarRaw b q ∈ bufferedCylinder δ := by
  have hd := inv_pos.mpr hδ
  have ht := q.2.property
  change 0 ≤ q.2.val ∧ q.2.val < δ⁻¹ / 2 at ht
  change -δ⁻¹ - 1 < cuttingSign b + cuttingSign b * q.2.val ∧
    cuttingSign b + cuttingSign b * q.2.val < δ⁻¹ + 1
  cases b <;> norm_num [cuttingSign] <;> constructor <;> linarith [ht.1, ht.2]

def cuttingCollarCylinderMap {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    S2 × Ico (0 : ℝ) (cuttingCollarWidth δ) → bufferedCylinder δ :=
  fun q => ⟨collarRaw b q, collarRaw_mem hδ b q⟩

theorem cuttingCollarCylinderMap_val {δ : ℝ} (hδ : 0 < δ) (b : Bool)
    (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)) :
    (cuttingCollarCylinderMap hδ b q).val = (q.1, cuttingSign b + cuttingSign b * q.2.val) := rfl

theorem cuttingCollar_mem_cutCore (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 q) ∈ cutCore f := by
  rw [cutCore_chart_iff f hf hdisj]
  change cuttingSign b.2 + cuttingSign b.2 * q.2.val ≤ -1 ∨
    1 ≤ cuttingSign b.2 + cuttingSign b.2 * q.2.val
  have ht := q.2.property.1
  rcases b with ⟨i, b⟩
  cases b
  · apply Or.inl
    change -1 + -1 * q.2.val ≤ -1
    linarith
  · apply Or.inr
    change 1 ≤ 1 + 1 * q.2.val
    linarith

def cuttingCollarMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) → cutCore f :=
  fun q => ⟨f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 q), cuttingCollar_mem_cutCore hδ f hf hdisj b q⟩

theorem cuttingCollarMap_zero (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (y : S2) :
    cuttingCollarMap hδ f hf hdisj b (y, ⟨0, ⟨le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩⟩) =
      cuttingSphereAttachment hδ f hf hdisj ⟨b, y⟩ := by
  apply Subtype.ext
  apply congrArg (f b.1)
  apply Subtype.ext
  exact Prod.ext rfl (by simp [collarRaw, cuttingCollarCylinderMap])

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem isEmbedding_cuttingCollarCylinderMap {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    _root_.Topology.IsEmbedding (cuttingCollarCylinderMap hδ b) := by
  have hv : _root_.Topology.IsEmbedding
      (fun q : S2 × Ico (0 : ℝ) (cuttingCollarWidth δ) => (q.1, q.2.val)) :=
    _root_.Topology.IsEmbedding.id.prodMap _root_.Topology.IsEmbedding.subtypeVal
  have hr : _root_.Topology.IsEmbedding (collarRaw (δ := δ) b) :=
    (cylinderAxialDiffeomorph (I := 𝓡 2) (M := S2) (cuttingSign b) (cuttingSign b)
      (cuttingSign_sq b)).toHomeomorph.isEmbedding.comp hv
  exact hr.codRestrict (bufferedCylinder δ) (collarRaw_mem hδ b)

variable [TopologicalSpace M]

theorem isEmbedding_cuttingCollarMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    _root_.Topology.IsEmbedding (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) :=
  ((hf b.1).isEmbedding.comp (isEmbedding_cuttingCollarCylinderMap (hδ b.1) b.2)).codRestrict
    (cutCore f) (cuttingCollar_mem_cutCore hδ f (fun i => (hf i).injective) hdisj b)

def cuttingCollarBand (δ : ℝ) (b : Bool) : Set (bufferedCylinder δ) :=
  {q | 0 < cuttingSign b * q.val.2 ∧ cuttingSign b * q.val.2 < 1 + cuttingCollarWidth δ}

theorem isOpen_cuttingCollarBand (δ : ℝ) (b : Bool) : IsOpen (cuttingCollarBand δ b) := by
  have hc : Continuous (fun q : bufferedCylinder δ => cuttingSign b * q.val.2) :=
    continuous_const.fun_mul (continuous_snd.comp continuous_subtype_val)
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

omit [TopologicalSpace M] in
theorem range_cuttingCollarMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    range (cuttingCollarMap hδ f hf hdisj b) =
      Subtype.val ⁻¹' (f b.1 '' cuttingCollarBand (precision b.1) b.2) := by
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨cuttingCollarCylinderMap (hδ b.1) b.2 r, ?_, rfl⟩
    change 0 < cuttingSign b.2 * (cuttingSign b.2 + cuttingSign b.2 * r.2.val) ∧
      cuttingSign b.2 * (cuttingSign b.2 + cuttingSign b.2 * r.2.val) <
        1 + cuttingCollarWidth (precision b.1)
    have he : cuttingSign b.2 * (cuttingSign b.2 + cuttingSign b.2 * r.2.val) = 1 + r.2.val := by
      calc
        _ = cuttingSign b.2 ^ 2 * (1 + r.2.val) := by ring
        _ = _ := by rw [cuttingSign_sq, one_mul]
    rw [he]
    constructor <;> linarith [r.2.property.1, r.2.property.2]
  · rintro ⟨q, hq, he⟩
    have hcore : q.val.2 ≤ -1 ∨ 1 ≤ q.val.2 :=
      (cutCore_chart_iff f hf hdisj b.1 q).mp (he.symm ▸ p.property)
    have hband : 0 < cuttingSign b.2 * q.val.2 ∧
        cuttingSign b.2 * q.val.2 < 1 + cuttingCollarWidth (precision b.1) := hq
    have ht : 0 ≤ cuttingSign b.2 * q.val.2 - 1 := by
      cases hb : b.2 <;> norm_num [cuttingSign, hb] at hband ⊢
      all_goals rcases hcore with hcore | hcore <;> linarith
    let r : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)) :=
      (q.val.1, ⟨cuttingSign b.2 * q.val.2 - 1, ⟨ht, by linarith [hband.2]⟩⟩)
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change f b.1 (cuttingCollarCylinderMap (hδ b.1) b.2 r) = p.val
    rw [← he]
    apply congrArg (f b.1)
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change cuttingSign b.2 + cuttingSign b.2 * (cuttingSign b.2 * q.val.2 - 1) = q.val.2
    calc
      _ = cuttingSign b.2 ^ 2 * q.val.2 := by ring
      _ = _ := by rw [cuttingSign_sq, one_mul]

theorem isOpenEmbedding_cuttingCollarMap (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool) :
    _root_.Topology.IsOpenEmbedding (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) := by
  refine ⟨isEmbedding_cuttingCollarMap hδ f hf hdisj b, ?_⟩
  rw [range_cuttingCollarMap]
  exact ((hf b.1).isOpenMap _ (isOpen_cuttingCollarBand (precision b.1) b.2)).preimage continuous_subtype_val

omit [TopologicalSpace M] in
theorem pairwise_disjoint_cuttingCollars (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Pairwise (fun b c : ι × Bool => Disjoint
      (range (cuttingCollarMap hδ f hf hdisj b)) (range (cuttingCollarMap hδ f hf hdisj c))) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hbc
  apply disjoint_left.mpr
  rintro p ⟨q, rfl⟩ ⟨r, hr⟩
  have he := congrArg Subtype.val hr
  by_cases hij : i = j
  · subst j
    have hb : b ≠ c := fun h => hbc (congrArg (Prod.mk i) h)
    have hz := congrArg (fun q : bufferedCylinder (precision i) => q.val.2) (hf i he)
    change cuttingSign c + cuttingSign c * r.2.val = cuttingSign b + cuttingSign b * q.2.val at hz
    cases b <;> cases c <;> simp only [cuttingSign, Bool.false_eq_true, if_false, if_true,
      neg_one_mul, one_mul] at hb hz
    all_goals first | contradiction | linarith [q.2.property.1, r.2.property.1]
  · exact disjoint_left.mp (hdisj hij) ⟨cuttingCollarCylinderMap (hδ i) b q, rfl⟩
      ⟨cuttingCollarCylinderMap (hδ j) c r, he⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
