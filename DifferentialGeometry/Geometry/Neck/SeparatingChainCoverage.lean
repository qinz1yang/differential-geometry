import DifferentialGeometry.Geometry.Neck.SeparatingChainGraphs
import DifferentialGeometry.Geometry.Neck.GraphControlledRegion

noncomputable section
open Set Topology
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Geometry.Affine Poincare.Geometry.Boundary

namespace Poincare.Geometry.Neck

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E H W F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric J M} {Cₒ ε : ℝ} {n : ℕ} [NeZero n]

private theorem sign_unit (D : separatingNeckChain I g Cₒ ε n (W := W)) (i : Fin (n + 1)) :
    (D.alignment i).1 = 1 ∨ (D.alignment i).1 = -1 :=
  finiteLineAffineAlignment_sign D.sign D.edgeTranslation D.sign_unit i

private theorem sign_square (D : separatingNeckChain I g Cₒ ε n (W := W)) (i : Fin (n + 1)) :
    (D.alignment i).1 * (D.alignment i).1 = 1 := by
  rcases sign_unit D i with h | h <;> rw [h] <;> norm_num

private theorem collar_closed (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    IsClosed (D.collarRegion j) :=
  (isCompact_range (D.collar j).continuous_map).isClosed.preimage D.smooth_inclusion.continuous

private theorem collar_inside (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    range (D.collar j).map ⊆ range D.inclusion := by
  rintro y ⟨x, rfl⟩
  exact interior_subset (D.collar_internal j x)

private theorem collar_image (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    D.inclusion '' D.collarRegion j = range (D.collar j).map :=
  image_preimage_eq_of_subset (collar_inside D j)

private theorem lower_face_subset (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    range (D.collar j).lowerFace ⊆ range (D.collar j).map := by
  rintro y ⟨p, rfl⟩
  exact ⟨(p, ⟨(D.collar j).lower, le_rfl, by linarith only [(D.collar j).width]⟩), rfl⟩

private theorem upper_face_subset (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    range (D.collar j).upperFace ⊆ range (D.collar j).map := by
  rintro y ⟨p, rfl⟩
  exact ⟨(p, ⟨(D.collar j).upper, by linarith only [(D.collar j).width], le_rfl⟩), rfl⟩

private theorem lower_attachment_image (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    D.inclusion '' (D.lowerSide j ∩ D.collarRegion j) = range (D.collar j).lowerFace := by
  change D.inclusion '' (D.lowerSide j ∩ D.inclusion ⁻¹' range (D.collar j).map) = _
  rw [D.lowerFace_attach]
  exact image_preimage_eq_of_subset ((lower_face_subset D j).trans (collar_inside D j))

private theorem upper_attachment_image (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) :
    D.inclusion '' (D.collarRegion j ∩ D.upperSide j) = range (D.collar j).upperFace := by
  rw [inter_comm]
  change D.inclusion '' (D.upperSide j ∩ D.inclusion ⁻¹' range (D.collar j).map) = _
  rw [D.upperFace_attach]
  exact image_preimage_eq_of_subset ((upper_face_subset D j).trans (collar_inside D j))

private theorem chart_height_controlled
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (i : Fin (n + 1))
    (x : (D.charts i).domain) (hx : ((D.charts i).chart x : M) ∈
      (D.charts i).heightRegion (Ioo (D.controlLower i) (D.controlUpper i))) :
    (x : S² × ℝ).2 ∈ Ioo (D.controlLower i) (D.controlUpper i) := by
  obtain ⟨y, ⟨z, hz, rfl⟩, he⟩ := hx
  have hzx : z = x := (D.charts i).chart.injective (Subtype.ext he)
  exact hzx ▸ hz

private theorem collar_controlled
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) (i : Fin (n + 1))
    (hi : i = j.castSucc ∨ i = j.succ) :
    range (D.collar j).map ⊆ (D.charts i).heightRegion
      (Ioo (D.controlLower i) (D.controlUpper i)) := by
  intro y hy
  have h := D.overlap_controlled j (D.collar_overlap j hy)
  rcases hi with rfl | rfl
  · exact h.1
  · exact h.2

private theorem graph_lower_controlled
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) (i : Fin (n + 1))
    (hi : i = j.castSucc ∨ i = j.succ) (A : D.collarGraph j i) (p : S²) :
    (D.alignment i).1 * A.lower p ∈ Ioo (D.controlLower i) (D.controlUpper i) := by
  apply chart_height_controlled D i ⟨(p, (D.alignment i).1 * A.lower p), A.lower_mem p⟩
  apply collar_controlled D j i hi
  apply lower_face_subset D j
  rw [← A.lowerFace_image]
  exact ⟨p, rfl⟩

private theorem graph_upper_controlled
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) (i : Fin (n + 1))
    (hi : i = j.castSucc ∨ i = j.succ) (A : D.collarGraph j i) (p : S²) :
    (D.alignment i).1 * A.upper p ∈ Ioo (D.controlLower i) (D.controlUpper i) := by
  apply chart_height_controlled D i ⟨(p, (D.alignment i).1 * A.upper p), A.upper_mem p⟩
  apply collar_controlled D j i hi
  apply upper_face_subset D j
  rw [← A.upperFace_image]
  exact ⟨p, rfl⟩

omit [FiniteDimensional ℝ F] [IsManifold J ∞ M] [T2Space M] in
private theorem signed_face_region_eq_range
    (C : cylindricalChart J (M := M)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (a : S² → ℝ) (ha : ∀ p, (p, σ * a p) ∈ C.domain) :
    C.region {x | σ * (x : S² × ℝ).2 = a (x : S² × ℝ).1} =
      range (fun p ↦ (C.chart ⟨(p, σ * a p), ha p⟩ : M)) := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [cylindricalChart.region, image_image]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : S² × ℝ).1, ?_⟩
    apply congrArg (fun z : C.domain ↦ (C.chart z : M))
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change σ * a (x : S² × ℝ).1 = (x : S² × ℝ).2
    rw [← hx, ← mul_assoc, hσσ, one_mul]
  · rintro ⟨p, rfl⟩
    refine ⟨⟨(p, σ * a p), ha p⟩, ?_, rfl⟩
    change σ * (σ * a p) = a p
    rw [← mul_assoc, hσσ, one_mul]

private theorem graph_lower_region
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) (i : Fin (n + 1))
    (A : D.collarGraph j i) :
    (D.charts i).region {x | (D.alignment i).1 * (x : S² × ℝ).2 = A.lower (x : S² × ℝ).1} =
      D.inclusion '' (D.lowerSide j ∩ D.collarRegion j) :=
  (signed_face_region_eq_range (D.charts i) _ (sign_unit D i) A.lower A.lower_mem).trans
    (A.lowerFace_image.trans (lower_attachment_image D j).symm)

private theorem graph_upper_region
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) (i : Fin (n + 1))
    (A : D.collarGraph j i) :
    (D.charts i).region {x | (D.alignment i).1 * (x : S² × ℝ).2 = A.upper (x : S² × ℝ).1} =
      D.inclusion '' (D.collarRegion j ∩ D.upperSide j) :=
  (signed_face_region_eq_range (D.charts i) _ (sign_unit D i) A.upper A.upper_mem).trans
    (A.upperFace_image.trans (upper_attachment_image D j).symm)

variable [PreconnectedSpace W]

private theorem middle_wedge
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j k : Fin n)
    (hjk : j.succ = k.castSucc) (A : D.collarGraph j j.succ) (B : D.collarGraph k j.succ) :
    (interior (D.lowerSide j))ᶜ ∩ (interior (D.upperSide k))ᶜ ⊆ D.controlledRegion j.succ := by
  have horder (p : S²) : A.upper p < B.lower p := by
    have h := D.middle_face_order j k hjk
      ⟨(p, (D.alignment j.succ).1 * A.upper p), A.upper_mem p⟩
      ⟨(p, (D.alignment j.succ).1 * B.lower p), B.lower_mem p⟩ rfl
      (by rw [← A.upperFace_image]; exact ⟨p, rfl⟩)
      (by rw [← B.lowerFace_image]; exact ⟨p, rfl⟩)
    change (D.alignment j.succ).1 * ((D.alignment j.succ).1 * A.upper p) <
      (D.alignment j.succ).1 * ((D.alignment j.succ).1 * B.lower p) at h
    simpa only [← mul_assoc, sign_square, one_mul] using h
  exact (D.charts j.succ).between_subset_controlled_of_signed_graph_collars
    D.inclusion D.smooth_inclusion.continuous D.embedding.injective
    (D.lowerSide j) (D.collarRegion j) (D.upperSide j)
    (D.lowerSide k) (D.collarRegion k) (D.upperSide k)
    (D.lowerSide_closed j) (collar_closed D j) (D.upperSide_closed j)
    (D.lowerSide_closed k) (collar_closed D k) (D.upperSide_closed k)
    (D.sides_cover j) (D.sides_cover k) (D.sides_disjoint j) (D.sides_disjoint k)
    (D.alignment j.succ).1 (sign_unit D j.succ) A.lower A.upper B.lower B.upper
    A.lower.continuous B.upper.continuous A.ordered horder B.ordered
    (Ioo (D.controlLower j.succ) (D.controlUpper j.succ)) ordConnected_Ioo
    (graph_lower_controlled D j j.succ (Or.inr rfl) A)
    (graph_upper_controlled D k j.succ (Or.inl hjk) B)
    (fun p t ht ↦ D.control_domain j.succ ⟨mem_univ p, ht⟩)
    ((collar_image D j).trans A.band_image.symm) ((collar_image D k).trans B.band_image.symm)
    (graph_lower_region D j j.succ A).le (graph_upper_region D k j.succ B).le

variable [FiniteDimensional ℝ E] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
  [CompactSpace W] [BoundarylessManifold J M]

private theorem range_geometry
    (D : separatingNeckChain I g Cₒ ε n (W := W)) :
    IsClosedEmbedding D.inclusion ∧
      closure (interior (range D.inclusion)) = range D.inclusion ∧
      IsPreconnected (interior (range D.inclusion)) ∧
      frontier (range D.inclusion) = D.inclusion '' D.lowerEnd ∪ D.inclusion '' D.upperEnd := by
  have hc : IsClosedEmbedding D.inclusion :=
    D.smooth_inclusion.continuous.isClosedEmbedding D.embedding.injective
  refine ⟨hc, closure_interior_range_of_fullRank_closedEmbedding D.inclusion D.smooth_inclusion hc
    D.fullRank D.dimension,
    isPreconnected_interior_range_of_fullRank_embedding D.inclusion D.smooth_inclusion
      D.embedding D.fullRank D.dimension, ?_⟩
  rw [← image_boundary_eq_frontier_of_fullRank_closedEmbedding
    D.inclusion D.smooth_inclusion hc D.fullRank D.dimension, D.boundary, image_union]

private theorem first_wedge_and_inward
    (D : separatingNeckChain I g Cₒ ε n (W := W))
    (A : D.collarGraph ⟨0, NeZero.pos n⟩ 0) :
    (interior (D.upperSide ⟨0, NeZero.pos n⟩))ᶜ ⊆ D.controlledRegion 0 ∧
      ∃ d : ℝ, 0 < d ∧
        ∃ hsegment : ∀ p : S², ∀ t ∈ Icc (0 : ℝ) d, (p, t) ∈ (D.charts 0).domain,
          ∀ p t (ht : t ∈ Icc (0 : ℝ) d),
            ((D.charts 0).chart ⟨(p, t), hsegment p t ht⟩ : M) ∈ range D.inclusion := by
  let j : Fin n := ⟨0, NeZero.pos n⟩
  have hτ : (D.alignment 0).1 = 1 :=
    congrArg Prod.fst (finiteLineAffineAlignment_zero D.sign D.edgeTranslation)
  have hj : (0 : Fin (n + 1)) = j.castSucc := Fin.ext rfl
  have horder (p : S²) : 0 < A.lower p := by
    have h := D.first_face_order
      ⟨(p, (D.alignment 0).1 * A.lower p), A.lower_mem p⟩
      (by rw [← A.lowerFace_image]; exact ⟨p, rfl⟩)
    change 0 < (D.alignment 0).1 * A.lower p at h
    simpa only [hτ, one_mul] using h
  have hc (p : S²) : (p, (D.alignment 0).1 * 0) ∈ (D.charts 0).domain := by
    rw [mul_zero]
    exact D.control_domain 0 ⟨mem_univ _, D.control_center 0⟩
  have hminus : D.inclusion '' D.lowerEnd =
      (D.charts 0).region {x | (D.alignment 0).1 * (x : S² × ℝ).2 = 0} := by
    rw [D.lowerEnd_image, signed_face_region_eq_range (D.charts 0) _ (sign_unit D 0) (fun _ ↦ 0) hc]
    simp only [mul_zero]
  obtain ⟨hemb, hregular, hconnected, hboundary⟩ := range_geometry D
  obtain ⟨hwedge, d, hd, hseg, hin⟩ :=
    (D.charts 0).endpoint_subset_controlled_and_inward_of_signed_graph_collar
      D.inclusion hemb hregular hconnected (D.lowerSide j) (D.collarRegion j) (D.upperSide j)
      (D.lowerSide_closed j) (collar_closed D j) (D.upperSide_closed j) (D.sides_cover j)
      (D.sides_disjoint j) D.lowerEnd D.upperEnd hboundary (D.upperEnd_side j)
      (by rintro y ⟨w, ⟨x, hx⟩, rfl⟩; exact hx ▸ D.collar_internal j x)
      (D.alignment 0).1 (sign_unit D 0) 0 A.lower A.upper A.lower.continuous A.upper.continuous
      horder A.ordered (Ioo (D.controlLower 0) (D.controlUpper 0)) ordConnected_Ioo
      (by rw [mul_zero]; exact D.control_center 0)
      (graph_upper_controlled D j 0 (Or.inl hj) A)
      (fun p t ht ↦ D.control_domain 0 ⟨mem_univ p, ht⟩)
      hminus ((collar_image D j).trans A.band_image.symm) (graph_upper_region D j 0 A).symm
  have hseg' (p : S²) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) d) : (p, t) ∈ (D.charts 0).domain := by
    simpa only [hτ, zero_add, one_mul] using hseg p t ht
  refine ⟨hwedge, d, hd, hseg', ?_⟩
  intro p t ht
  simpa only [hτ, zero_add, one_mul] using hin p t ht

private theorem last_wedge
    (D : separatingNeckChain I g Cₒ ε n (W := W))
    (A : D.collarGraph ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩ (Fin.last n)) :
    (interior (D.lowerSide ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩))ᶜ ⊆
      D.controlledRegion (Fin.last n) := by
  let j : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩
  let τ := (D.alignment (Fin.last n)).1
  have hτ : -τ = 1 ∨ -τ = -1 := by
    rcases sign_unit D (Fin.last n) with h | h
    · exact Or.inr (congrArg Neg.neg h)
    · exact Or.inl (by change -(D.alignment (Fin.last n)).1 = 1; rw [h]; norm_num)
  have hj : Fin.last n = j.succ := by
    apply Fin.ext
    change n = n - 1 + 1
    have := NeZero.pos n
    omega
  have horder (p : S²) : 0 < -A.upper p := by
    have h := D.last_face_order
      ⟨(p, (D.alignment (Fin.last n)).1 * A.upper p), A.upper_mem p⟩
      (by rw [← A.upperFace_image]; exact ⟨p, rfl⟩)
    change (D.alignment (Fin.last n)).1 * ((D.alignment (Fin.last n)).1 * A.upper p) < 0 at h
    rw [← mul_assoc, sign_square, one_mul] at h
    linarith
  have hc (p : S²) : (p, -τ * 0) ∈ (D.charts (Fin.last n)).domain := by
    rw [mul_zero]
    exact D.control_domain _ ⟨mem_univ _, D.control_center _⟩
  have hminus : D.inclusion '' D.upperEnd =
      (D.charts (Fin.last n)).region {x | -τ * (x : S² × ℝ).2 = 0} := by
    rw [D.upperEnd_image, signed_face_region_eq_range (D.charts (Fin.last n)) (-τ) hτ (fun _ ↦ 0) hc]
    simp only [mul_zero]
  have hband : {x : (D.charts (Fin.last n)).domain |
      -A.upper (x : S² × ℝ).1 ≤ -τ * (x : S² × ℝ).2 ∧
      -τ * (x : S² × ℝ).2 ≤ -A.lower (x : S² × ℝ).1} =
        {x : (D.charts (Fin.last n)).domain | A.lower (x : S² × ℝ).1 ≤ τ * (x : S² × ℝ).2 ∧
          τ * (x : S² × ℝ).2 ≤ A.upper (x : S² × ℝ).1} := by
    ext x
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hfar : D.inclusion '' (D.collarRegion j ∩ D.lowerSide j) =
      (D.charts (Fin.last n)).region {x | -τ * (x : S² × ℝ).2 = -A.lower (x : S² × ℝ).1} := by
    have he : {x : (D.charts (Fin.last n)).domain | -τ * (x : S² × ℝ).2 = -A.lower (x : S² × ℝ).1} =
        {x : (D.charts (Fin.last n)).domain | τ * (x : S² × ℝ).2 = A.lower (x : S² × ℝ).1} := by
      ext x
      change -τ * (x : S² × ℝ).2 = -A.lower (x : S² × ℝ).1 ↔
        τ * (x : S² × ℝ).2 = A.lower (x : S² × ℝ).1
      rw [neg_mul, neg_inj]
    rw [he, inter_comm]
    exact (graph_lower_region D j (Fin.last n) A).symm
  obtain ⟨hemb, hregular, hconnected, hboundary⟩ := range_geometry D
  have h := (D.charts (Fin.last n)).endpoint_subset_controlled_and_inward_of_signed_graph_collar
    D.inclusion hemb hregular hconnected (D.upperSide j) (D.collarRegion j) (D.lowerSide j)
    (D.upperSide_closed j) (collar_closed D j) (D.lowerSide_closed j)
    (by rw [union_comm (D.upperSide j ∪ _) (D.lowerSide j), union_comm (D.upperSide j) _, ← union_assoc]
        exact D.sides_cover j)
    (D.sides_disjoint j).symm D.upperEnd D.lowerEnd (hboundary.trans (union_comm _ _))
    (D.lowerEnd_side j)
    (by rintro y ⟨w, ⟨x, hx⟩, rfl⟩; exact hx ▸ D.collar_internal j x)
    (-τ) hτ 0 (fun p ↦ -A.upper p) (fun p ↦ -A.lower p)
    A.upper.continuous.neg A.lower.continuous.neg horder (fun p ↦ by linarith [A.ordered p])
    (Ioo (D.controlLower (Fin.last n)) (D.controlUpper (Fin.last n))) ordConnected_Ioo
    (by rw [mul_zero]; exact D.control_center (Fin.last n))
    (by intro p; simpa only [neg_mul_neg] using graph_lower_controlled D j (Fin.last n) (Or.inr hj) A p)
    (fun p t ht ↦ D.control_domain _ ⟨mem_univ p, ht⟩) hminus
    (by rw [hband]; exact (collar_image D j).trans A.band_image.symm) hfar
  exact h.1

theorem separatingNeckChain.controlled_regions_and_inward_segment
    (D : separatingNeckChain I g Cₒ ε n (W := W))
    (graphs : ∀ j i, i = j.castSucc ∨ i = j.succ → D.collarGraph j i) :
    (∀ (i : Fin (n + 1)) (w : W),
      (∀ j : Fin n, i = j.castSucc → w ∉ interior (D.upperSide j)) →
      (∀ j : Fin n, i = j.succ → w ∉ interior (D.lowerSide j)) → w ∈ D.controlledRegion i) ∧
      ∃ d : ℝ, 0 < d ∧
        ∃ hsegment : ∀ p : S², ∀ t ∈ Icc (0 : ℝ) d, (p, t) ∈ (D.charts 0).domain,
          ∀ p t (ht : t ∈ Icc (0 : ℝ) d),
            ((D.charts 0).chart ⟨(p, t), hsegment p t ht⟩ : M) ∈ range D.inclusion := by
  let j₀ : Fin n := ⟨0, NeZero.pos n⟩
  let j₁ : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) (by decide)⟩
  have hj₀ : (0 : Fin (n + 1)) = j₀.castSucc := Fin.ext rfl
  have hj₁ : Fin.last n = j₁.succ := by
    apply Fin.ext
    change n = n - 1 + 1
    have := NeZero.pos n
    omega
  obtain ⟨hfirst, hinward⟩ := first_wedge_and_inward D (graphs j₀ 0 (Or.inl hj₀))
  have hlast := last_wedge D (graphs j₁ (Fin.last n) (Or.inr hj₁))
  refine ⟨?_, hinward⟩
  intro i w hQ hP
  by_cases hi₀ : i = 0
  · subst i
    exact hfirst (hQ j₀ hj₀)
  by_cases hi₁ : i = Fin.last n
  · subst i
    exact hlast (hP j₁ hj₁)
  have hi : 0 < i.val ∧ i.val < n := by
    constructor
    · have hne : i.val ≠ 0 := fun h ↦ hi₀ (Fin.ext h)
      omega
    · have hne : i.val ≠ n := fun h ↦ hi₁ (Fin.ext h)
      omega
  let j : Fin n := ⟨i.val - 1, by omega⟩
  let k : Fin n := ⟨i.val, hi.2⟩
  have hj : j.succ = i := by apply Fin.ext; change i.val - 1 + 1 = i.val; omega
  have hk : k.castSucc = i := Fin.ext rfl
  have hjk : j.succ = k.castSucc := hj.trans hk.symm
  have hm := middle_wedge D j k hjk (graphs j j.succ (Or.inr rfl))
    (graphs k j.succ (Or.inl hjk))
  have hw := hm ⟨hP j hj.symm, hQ k hk.symm⟩
  exact hj ▸ hw

end Poincare.Geometry.Neck
