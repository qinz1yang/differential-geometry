import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateCutAssemblyReal_S31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleMain

set_option autoImplicit false

/-!
# CH12-O17 (G1): the thin side of the A09 assembly on the real cut

* `hasThinVolumeGeometry_of_piece_O17`: the S27 reduction (T2 interior scale + ambient
  `w`-collapse ⇒ `hasThinVolumeGeometry`) for ONE piece of an arbitrary torus decomposition with an
  induced metric, without a finished `LateCutFamily` (the T2 core argument is pointwise:
  `collarNegativePlane_S16` + `curvatureRadius_le_sub_one_of_negative_planes_T2`).
* `exists_late_cut_family_thin_O17`: `exists_late_cut_family_assembly_S31` with `thin / hfin / halt`
  supplied from two eventual leaves on the non-core blocks of the real cut: a nearly cuspidal
  boundary of every accuracy `w` (`hNCB`) and ambient `w`-collapse at interior points (`hAmbS`).
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology GC.LongTime
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-- **Thin geometry of one piece (generic S27).**  For a piece of a torus decomposition with an
induced metric `h`: finite curvature scales, a nearly cuspidal boundary of accuracy `1/10000`
(for T2) and of accuracy `w` when the boundary is nonempty, and ambient `w`-collapse at the images
of points at boundary distance `> 10`, give `hasThinVolumeGeometry`. -/
theorem hasThinVolumeGeometry_of_piece_O17 {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (K : ℕ) (w : ℝ)
    (hG2 : CollarNegativePlane.{u} K) (hfin : ∀ p, curvatureRadius h p ≠ ⊤)
    (hbd : (D.component i).model.boundary (D.component i).Carrier ≠ ∅ →
      Nonempty (NearlyCuspidalBoundary (D.component i) h (K + 4) (1 / 10000)))
    (hB : (D.component i).model.boundary (D.component i).Carrier ≠ ∅ →
      Nonempty (NearlyCuspidalBoundary (D.component i) h (K + 4) w))
    (hAmb : ∀ p, ENNReal.ofReal 10 < distanceToBoundary (D.component i) h p →
      volumeCollapsedAtCurvatureScale g w (cutPieceMap D i p)) :
    hasThinVolumeGeometry (D.component i) h K w := by
  -- T2 core: below the boundary distance
  have hlt : ∀ p, ENNReal.ofReal 10 < distanceToBoundary (D.component i) h p →
      curvatureRadius h p < distanceToBoundary (D.component i) h p := by
    intro p hD
    by_cases ht : distanceToBoundary (D.component i) h p = ⊤
    · rw [ht]; exact lt_top_iff_ne_top.mpr (hfin p)
    · have hb : (D.component i).model.boundary (D.component i).Carrier ≠ ∅ := fun hb =>
        ht (distanceToBoundary_eq_top_of_boundary_empty _ _ hb p)
      obtain ⟨B₀⟩ := hbd hb
      have hneg := hG2 _ _ B₀ p hD (lt_top_iff_ne_top.mpr ht)
      have hle := curvatureRadius_le_sub_one_of_negative_planes_T2 _ p hD (fun η hη => by
        obtain ⟨q, _, hq1, hq2⟩ := hneg η hη
        exact ⟨q, hq1, hq2⟩)
      exact hle.trans_lt (ENNReal.sub_lt_self ht (by
        intro h0; rw [h0] at hD; simp at hD) (by simp))
  -- volume collapse at interior points
  have hv : ∀ p, ENNReal.ofReal 10 < distanceToBoundary (D.component i) h p →
      volumeCollapsedAtCurvatureScale h w p := by
    intro p hD r hr0 hcr
    have hl := hlt p hD
    have heq : curvatureRadius g (cutPieceMap D i p) = curvatureRadius h p :=
      curvatureRadius_cutPieceMap_eq_of_lt g D i h hind hl
    have hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p := by
      rw [← hcr]; exact hl.le
    rw [ballVolume_cutPieceMap_of_le g D i h hind hd]
    exact hAmb p hD r hr0 (heq.trans hcr)
  by_cases hb : (D.component i).model.boundary (D.component i).Carrier = ∅
  · refine Or.inl ⟨hb, fun p => hv p ?_⟩
    rw [distanceToBoundary_eq_top_of_boundary_empty _ _ hb p]
    exact ENNReal.ofReal_lt_top
  · exact Or.inr ⟨hB hb, fun p hp => hv p hp⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **A09 on the real cut, thin side discharged (O17 G1).**  The binders of
`exists_late_cut_family_assembly_S31` without `thin / hfin / halt`; instead two eventual leaves on
the non-core blocks of the real cut: `hNCB` (nearly cuspidal boundary of every accuracy `w`) and
`hAmbS` (ambient `w`-collapse of the slice component at images of points at boundary distance
`> 10`).  The thin predicate is `¬ (closed ∧ sec ≥ 0) ∧ finite curvature scales`. -/
theorem exists_late_cut_family_thin_O17
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (B : BufferedPersistentCores F (K + 4))
    (base : ∀ i : Fin B.count, HyperbolicTruncation (B.model i)) (level : ℕ → ℝ)
    (two_le : ∀ j, 2 ≤ level j)
    (hball : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i (q : Fin (base i).count) (p : CuspHalfSpace),
      p.2.val 0 ≤ level j + 200 →
        (base i).cuspMap q p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
          (2 * (B.accuracy (slices j).time)⁻¹))
    (hcore : ∀ j, ⌈B.start⌉₊ ≤ j → ∀ i : Fin B.count,
      Set.range (trunc_S24 B base level two_le j i).inclusion ⊆
        riemannianBallOf (B.model i).metric (B.model i).basepoint
          (B.accuracy (slices j).time)⁻¹)
    -- proved as `collarNegativePlane_S16` / `exists_negative_plane_of_nearlyCuspidal_S27`; inline only
    -- because BoundaryWiringG2_S16 cannot be imported together with S29 (duplicate
    -- `CuspEmbedding.isOpen_image`)
    (hG2 : CollarNegativePlane.{u} K)
    (hNP : ∀ (W : CompactCarrier.{u}) (h : SmoothRiemannianMetric W.model W.Carrier),
      NearlyCuspidalBoundary W h (K + 4) (1 / 10000) → ∃ q, ¬ SectionalBoundedBelowAt h q (-(1 / 81 : ℝ)))
    (hNCB : ∀ w : ℝ, 0 < w → ∃ N : ℕ, ∀ j (hj : ⌈B.start⌉₊ ≤ j), N ≤ j →
      ∀ C (i : Fin (realDec_S31 B base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin B.count,
          Disjoint
            ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj)
                  ((trunc_S24 B base level two_le j c).inclusion x))) ''
              ((trunc_S24 B base level two_le j c).core.interior : Set _))) →
        ((realDec_S31 B base level two_le slices htimes hball j C).component i).model.boundary
            ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier ≠ ∅ →
        Nonempty (NearlyCuspidalBoundary
          ((realDec_S31 B base level two_le slices htimes hball j C).component i)
          (cutMetric_S25 ((slices j).componentMetric C)
            (realDec_S31 B base level two_le slices htimes hball j C) i) (K + 4) w))
    (hAmbS : ∀ w : ℝ, 0 < w → ∃ N : ℕ, ∀ j (hj : ⌈B.start⌉₊ ≤ j), N ≤ j →
      ∀ C (i : Fin (realDec_S31 B base level two_le slices htimes hball j C).components.count),
        (∀ c : Fin B.count,
          Disjoint
            ((fun x => (((realDec_S31 B base level two_le slices htimes hball j C).reconstruction.val
                ((realDec_S31 B base level two_le slices htimes hball j C).boundary.quotientMap x)).val :
                  (slices j).stage.Carrier)) ''
              ((realDec_S31 B base level two_le slices htimes hball j C).carrier.pieceInterior
                ((realDec_S31 B base level two_le slices htimes hball j C).components.piece i) :
                  Set _))
            ((fun x => sliceCast_CX4 (slices j)
                (B.toCores.map c (slices j).time (ceil_le_time_S31 B slices htimes j hj)
                  ((trunc_S24 B base level two_le j c).inclusion x))) ''
              ((trunc_S24 B base level two_le j c).core.interior : Set _))) →
        ∀ p : ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier,
          ENNReal.ofReal 10 <
            distanceToBoundary ((realDec_S31 B base level two_le slices htimes hball j C).component i)
              (cutMetric_S25 ((slices j).componentMetric C)
                (realDec_S31 B base level two_le slices htimes hball j C) i) p →
          volumeCollapsedAtCurvatureScale ((slices j).componentMetric C) w
            (cutPieceMap (realDec_S31 B base level two_le slices htimes hball j C) i p)) :
    Nonempty (LateCutFamily F K slices) := by
  refine exists_late_cut_family_assembly_S31 F K hK δ hadm hdec slices htimes hnonempty B base level
    two_le hball hcore
    (fun j C i =>
      ¬ (((realDec_S31 B base level two_le slices htimes hball j C).component i).model.boundary
            ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier = ∅ ∧
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow
            (cutMetric_S25 ((slices j).componentMetric C)
              (realDec_S31 B base level two_le slices htimes hball j C) i) 0) ∧
        ∀ p, curvatureRadius (cutMetric_S25 ((slices j).componentMetric C)
          (realDec_S31 B base level two_le slices htimes hball j C) i) p ≠ ⊤)
    (fun _ _ _ _ hi => hi.2) ?_
  intro w hw _
  obtain ⟨N₁, h₁⟩ := hNCB (1 / 10000) (by norm_num)
  obtain ⟨N₂, h₂⟩ := hNCB w hw
  obtain ⟨N₃, h₃⟩ := hAmbS w hw
  refine ⟨max N₁ (max N₂ N₃), fun j hj hN C i hnc => ?_⟩
  have hN1 : N₁ ≤ j := (le_max_left _ _).trans hN
  have hN2 : N₂ ≤ j := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : N₃ ≤ j := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have : ConnectedSpace ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier :=
    (realDec_S31 B base level two_le slices htimes hball j C).components.connected i
  by_cases hcn : ((realDec_S31 B base level two_le slices htimes hball j C).component i).model.boundary
        ((realDec_S31 B base level two_le slices htimes hball j C).component i).Carrier = ∅ ∧
      DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow
        (cutMetric_S25 ((slices j).componentMetric C)
          (realDec_S31 B base level two_le slices htimes hball j C) i) 0
  · exact Or.inr ⟨fun h => h.1 hcn, hcn.1, hcn.2⟩
  · have hfin : ∀ p, curvatureRadius (cutMetric_S25 ((slices j).componentMetric C)
        (realDec_S31 B base level two_le slices htimes hball j C) i) p ≠ ⊤ := by
      by_cases hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow
          (cutMetric_S25 ((slices j).componentMetric C)
            (realDec_S31 B base level two_le slices htimes hball j C) i) 0
      · obtain ⟨B₀⟩ := h₁ j hj hN1 C i hnc (fun hb => hcn ⟨hb, hsec⟩)
        obtain ⟨q, hq⟩ := hNP _ _ B₀
        exact fun p htop => hq (((curvatureRadius_eq_top_iff p).mp htop q).mono (by norm_num))
      · exact fun p htop => hsec ((curvatureRadius_eq_top_iff p).mp htop)
    exact Or.inl ⟨⟨hcn, hfin⟩, hasThinVolumeGeometry_of_piece_O17 _ _ i _
      (isInducedCutMetric_cutMetric_S25 _ _ i) K w hG2 hfin (h₁ j hj hN1 C i hnc)
      (h₂ j hj hN2 C i hnc) (h₃ j hj hN3 C i hnc)⟩

end GC.LongTime.Ch12
