import DifferentialGeometry.Geometry.Neck.SeparatingChain

noncomputable section
open Set Topology
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Geometry.Affine Poincare.Geometry.Boundary

namespace Poincare.Geometry.Neck

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private instance : ConnectedSpace S² := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  exact isConnected_iff_connectedSpace.mp (isConnected_sphere hdim _ zero_le_one)

variable {E H W F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric J M} {Cₒ ε : ℝ} {n : ℕ} [NeZero n]

def separatingNeckChain.edgeTranslation (D : separatingNeckChain I g Cₒ ε n (W := W))
    (j : Fin n) : ℝ := -D.sign j * D.sourceTranslation j

def separatingNeckChain.alignment (D : separatingNeckChain I g Cₒ ε n (W := W)) :
    Fin (n + 1) → ℝ × ℝ := finiteLineAffineAlignment D.sign D.edgeTranslation

def separatingNeckChain.controlledDomain (D : separatingNeckChain I g Cₒ ε n (W := W))
    (i : Fin (n + 1)) : Set (D.charts i).domain :=
  {x | (x : S² × ℝ).2 ∈ Ioo (D.controlLower i) (D.controlUpper i)}

def separatingNeckChain.controlledRegion (D : separatingNeckChain I g Cₒ ε n (W := W))
    (i : Fin (n + 1)) : Set W := D.inclusion ⁻¹' (D.charts i).region (D.controlledDomain i)

def separatingNeckChain.truncation (D : separatingNeckChain I g Cₒ ε n (W := W))
    (i : Fin (n + 1)) : Set M :=
  (D.charts i).heightRegion (Icc (D.truncationLower i) (D.truncationUpper i))

def separatingNeckChain.collarRegion (D : separatingNeckChain I g Cₒ ε n (W := W))
    (j : Fin n) : Set W := D.inclusion ⁻¹' range (D.collar j).map

theorem separatingNeckChain.ordered_exteriors
    [FiniteDimensional ℝ E] [HasSmoothBoundary E H I] [IsManifold I ∞ W]
    [CompactSpace W] [PreconnectedSpace W]
    [BoundarylessManifold J M] (D : separatingNeckChain I g Cₒ ε n (W := W)) :
    ∀ i j : Fin n, i < j →
      D.lowerSide i ∪ D.collarRegion i ⊆ interior (D.lowerSide j) ∧
      D.collarRegion j ∪ D.upperSide j ⊆ interior (D.upperSide i) ∧
      interior (D.upperSide i) ∪ interior (D.lowerSide j) = univ := by
  have hc : IsClosedEmbedding D.inclusion :=
    D.smooth_inclusion.continuous.isClosedEmbedding D.embedding.injective
  have hT (i : Fin (n + 1)) : IsPreconnected (D.truncation i) := by
    let l := D.truncationLower i
    let r := D.truncationUpper i
    let f : S² × Icc l r → M := fun x ↦
      (D.charts i).chart ⟨(x.1, (x.2 : ℝ)), D.truncation_domain i ⟨mem_univ _, x.2.property⟩⟩
    have hf : Continuous f := continuous_subtype_val.comp ((D.charts i).chart.continuous.comp
      ((continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _))
    let : PreconnectedSpace (Icc l r) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hset : range f = D.truncation i := by
      rw [truncation, cylindricalChart.heightRegion, cylindricalChart.region, image_image]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨⟨(x.1, (x.2 : ℝ)), D.truncation_domain i ⟨mem_univ _, x.2.property⟩⟩,
          x.2.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨((x : S² × ℝ).1, ⟨(x : S² × ℝ).2, hx⟩), rfl⟩
    exact hset ▸ isPreconnected_range hf
  have hKclosed (j : Fin n) : IsClosed (D.collarRegion j) :=
    (isCompact_range (D.collar j).continuous_map).isClosed.preimage D.smooth_inclusion.continuous
  have hKconn (j : Fin n) : IsPreconnected (D.collarRegion j) := by
    let : PreconnectedSpace (Icc (D.collar j).lower (D.collar j).upper) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    exact (isPreconnected_range (D.collar j).continuous_map).preimage_of_isClosedMap
      hc.injective hc.isClosedMap (by rintro _ ⟨x, rfl⟩; exact interior_subset (D.collar_internal j x))
  have hmeet (j : Fin n) : (D.truncation j.castSucc ∩ D.truncation j.succ).Nonempty := by
    let p : S² := ⟨EuclideanSpace.single 0 1, by simp⟩
    exact ⟨(D.collar j).lowerFace p,
      D.collar_truncation j ⟨(p, ⟨(D.collar j).lower, le_rfl, by linarith only [(D.collar j).width]⟩), rfl⟩⟩
  have hboundary : frontier (range D.inclusion) = D.inclusion '' D.lowerEnd ∪ D.inclusion '' D.upperEnd := by
    rw [← image_boundary_eq_frontier_of_fullRank_closedEmbedding
      D.inclusion D.smooth_inclusion hc D.fullRank D.dimension, D.boundary, image_union]
  have hm : D.lowerEnd.Nonempty := by
    have h : (D.inclusion '' D.lowerEnd).Nonempty := by
      rw [D.lowerEnd_image]
      exact range_nonempty _
    exact h.of_image
  have hp : D.upperEnd.Nonempty := by
    have h : (D.inclusion '' D.upperEnd).Nonempty := by
      rw [D.upperEnd_image]
      exact range_nonempty _
    exact h.of_image
  exact Poincare.Topology.ordered_exteriors_of_finite_chain D.inclusion hc
    D.truncation hT hmeet D.truncation_disjoint D.lowerSide D.collarRegion D.upperSide
    D.lowerSide_closed hKclosed D.upperSide_closed D.sides_cover D.sides_disjoint
    (by rintro j _ ⟨w, hw, rfl⟩; exact D.collar_truncation j hw)
    D.lowerEnd D.upperEnd hboundary.subset D.lowerEnd_side D.upperEnd_side
    D.lowerEnd_truncation D.upperEnd_truncation hm hp hKconn D.upperSide_preconnected

theorem separatingNeckChain.recorded_collar_errors
    (D : separatingNeckChain I g Cₒ ε n (W := W)) (j : Fin n) {y : M}
    (hy : y ∈ range (D.collar j).map) :
    |(D.charts j.succ).axial y - (D.sign j * (D.charts j.castSucc).axial y + D.edgeTranslation j)| ≤
      Cₒ * ε / Real.sqrt (D.charts j.castSucc).scale ∧
    Real.sqrt (g.inner y
      (gradFun g (D.charts j.succ).axial y - D.sign j • gradFun g (D.charts j.castSucc).axial y)
      (gradFun g (D.charts j.succ).axial y - D.sign j • gradFun g (D.charts j.castSucc).axial y)) ≤ Cₒ * ε := by
  have h := D.overlap_error j y (D.collar_overlap j hy)
  have hv : Real.sqrt (D.charts j.castSucc).scale *
      |(D.charts j.castSucc).axial y - D.sign j * (D.charts j.succ).axial y - D.sourceTranslation j| ≤ Cₒ * ε :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans h
  have hg : Real.sqrt (g.inner y
      (gradFun g (D.charts j.castSucc).axial y - D.sign j • gradFun g (D.charts j.succ).axial y)
      (gradFun g (D.charts j.castSucc).axial y - D.sign j • gradFun g (D.charts j.succ).axial y)) ≤ Cₒ * ε :=
    (le_add_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).trans h
  have hscale := Real.sqrt_pos.mpr (D.charts j.castSucc).scale_pos
  have hv' : |(D.charts j.castSucc).axial y - D.sign j * (D.charts j.succ).axial y - D.sourceTranslation j| ≤
      Cₒ * ε / Real.sqrt (D.charts j.castSucc).scale :=
    (le_div_iff₀ hscale).mpr (by rw [mul_comm]; exact hv)
  have heq : |(D.charts j.succ).axial y -
      (D.sign j * (D.charts j.castSucc).axial y + D.edgeTranslation j)| =
      |(D.charts j.castSucc).axial y - D.sign j * (D.charts j.succ).axial y - D.sourceTranslation j| := by
    rcases D.sign_unit j with hs | hs
    · rw [edgeTranslation, hs]
      have hneg : (D.charts j.succ).axial y -
          (1 * (D.charts j.castSucc).axial y + -1 * D.sourceTranslation j) =
          -((D.charts j.castSucc).axial y - 1 * (D.charts j.succ).axial y - D.sourceTranslation j) := by ring
      rw [hneg, abs_neg]
    · rw [edgeTranslation, hs]
      congr 1
      ring
  refine ⟨by rw [heq]; exact hv', ?_⟩
  rcases D.sign_unit j with hs | hs
  · simp only [hs, one_smul] at hg ⊢
    have heq : gradFun g (D.charts j.succ).axial y - gradFun g (D.charts j.castSucc).axial y =
        -(gradFun g (D.charts j.castSucc).axial y - gradFun g (D.charts j.succ).axial y) := by abel
    simpa only [heq, map_neg, neg_apply, neg_neg] using hg
  · simpa only [hs, neg_one_smul, sub_neg_eq_add, add_comm] using hg

end Poincare.Geometry.Neck
