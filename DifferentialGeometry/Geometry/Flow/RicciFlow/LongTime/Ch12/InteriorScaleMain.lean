import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InteriorScaleTransfer

/-!
# CH12 T2 (TCF02), groups 3-4: main statement and hT2-shaped corollary (modulo G2)

G2 (collar negative plane near an interior point at distance `D - 1`) is an explicit hypothesis
`hG2` here; it is to be replaced by the sibling-based proof (`NearlyCuspidalBoundary` collar).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- G2: collar negative plane (hypothesis form). -/
def CollarNegativePlane (K : ℕ) : Prop :=
  ∀ (W : CompactCarrier.{u}) (h : SmoothRiemannianMetric W.model W.Carrier)
    (_ : NearlyCuspidalBoundary W h (K + 4) (1 / 10000)) (p : W.Carrier),
    ENNReal.ofReal 10 < distanceToBoundary W h p → distanceToBoundary W h p < ⊤ →
    ∀ η : ℝ, 0 < η → ∃ q ∈ W.model.interior W.Carrier,
      riemannianEDistOf h p q ≤ ENNReal.ofReal ((distanceToBoundary W h p).toReal - 1 + η) ∧
        ¬ SectionalBoundedBelowAt h q (-(1 / 81 : ℝ))

theorem mem_interior_of_edist_lt_distanceToBoundary {W : CompactCarrier.{u}}
    (h : SmoothRiemannianMetric W.model W.Carrier) (p q : W.Carrier)
    (hq : riemannianEDistOf h p q < distanceToBoundary W h p) :
    q ∈ W.model.interior W.Carrier := by
  rw [← W.model.compl_boundary]
  intro hqb
  exact (not_le_of_gt hq) (iInf_le (fun z : W.model.boundary W.Carrier =>
    riemannianEDistOf h p z.val) ⟨q, hqb⟩)


section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

theorem sectionalBoundedBelowAt_restrictOpen_iff_T2
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (p : U) (K : ℝ) :
    SectionalBoundedBelowAt (g.restrictOpen U) p K ↔
      SectionalBoundedBelowAt g p.val K := by
  have hRm (v w : TangentSpace I p) :
      metricRm04StandardAt (g.restrictOpen U) p v w w v =
        metricRm04StandardAt g p.val v w w v := by
    simpa only [mfderiv_subtype_val_apply] using
      metricRm04StandardAt_restrictOpen g U p v w w v
  have hGram (v w : TangentSpace I p) :
      K * ((g.restrictOpen U).inner p v v * (g.restrictOpen U).inner p w w -
        (g.restrictOpen U).inner p v w ^ 2) =
      K * (g.inner p.val v v * g.inner p.val w w - g.inner p.val v w ^ 2) := by
    simp only [SmoothRiemannianMetric.restrictOpen_inner]
  constructor
  · intro h v w
    exact (hGram v w).symm.trans_le ((h v w).trans_eq (hRm v w))
  · intro h v w
    exact (hGram v w).trans_le ((h v w).trans_eq (hRm v w).symm)

end Restrict


namespace LateCutFamily

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem cutPieceMap_val_mem_connectedComponent_T2 (L : GC.LongTime.LateCutFamily F K slices)
    (j : ℕ) (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p q : ((L.decomposition j C).component i).Carrier) :
    (cutPieceMap (L.decomposition j C) i q).val ∈
      connectedComponent (cutPieceMap (L.decomposition j C) i p).val := by
  have hp := (cutPieceMap (L.decomposition j C) i p).property
  have hq := (cutPieceMap (L.decomposition j C) i q).property
  change ConnectedComponents.mk _ = C at hp hq
  exact ConnectedComponents.coe_eq_coe'.mp (hq.trans hp.symm)

theorem not_sectionalBoundedBelowAt_normalized_of_interior_T2
    (L : GC.LongTime.LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    {q : ((L.decomposition j C).component i).Carrier}
    (hq : q ∈ ((L.decomposition j C).component i).model.interior
      ((L.decomposition j C).component i).Carrier) {κ : ℝ}
    (hb : ¬ SectionalBoundedBelowAt (L.metric j C i) q κ) :
    ¬ SectionalBoundedBelowAt (slices j).normalizedMetric
      (cutPieceMap (L.decomposition j C) i q).val κ := by
  intro h
  apply hb
  rw [sectionalBoundedBelowAt_cutPieceMap_iff_of_mem_interior ((slices j).componentMetric C)
    (L.metric j C i) (L.induced j C i) hq]
  exact (sectionalBoundedBelowAt_restrictOpen_iff_T2 (slices j).normalizedMetric _
    (cutPieceMap (L.decomposition j C) i q) κ).mpr h

end LateCutFamily

/-- If the boundary distance is infinite and the curvature scale is finite, some interior point
has a negative plane (sectional bound `0` fails). -/
theorem exists_interior_negative_of_finite_scale_T2 {W : CompactCarrier.{u}}
    (h : SmoothRiemannianMetric W.model W.Carrier) (p : W.Carrier)
    (hD : distanceToBoundary W h p = ⊤) (hR : curvatureRadius h p ≠ ⊤) :
    ∃ q ∈ W.model.interior W.Carrier, ¬ SectionalBoundedBelowAt h q 0 := by
  by_contra hno
  push Not at hno
  apply hR
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  by_cases hr : (r : ℝ) = 0
  · have : r = 0 := by exact_mod_cast hr
    simp [this]
  have hrpos : (0 : ℝ) < r := lt_of_le_of_ne r.2 (Ne.symm hr)
  unfold curvatureRadius
  refine le_iSup_of_le (r : ℝ) (le_iSup_of_le hrpos (le_iSup_of_le ?_ ?_))
  · intro q hq
    have hqint : q ∈ W.model.interior W.Carrier :=
      mem_interior_of_edist_lt_distanceToBoundary h p q (by rw [hD]; exact hq.trans_le le_top)
    exact (hno q hqint).mono (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _)))
  · simp


namespace LateCutFamily

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- Core of TCF02 for an arbitrary late cut family (modulo `hG2`): at thin interior points
the curvature scale is below `D - 1`, finite, and a negative plane exists in the interior. -/
theorem eventually_interior_scale_core_T2 (L : GC.LongTime.LateCutFamily F K slices)
    (hG2 : CollarNegativePlane.{u} K) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p →
        curvatureRadius (L.metric j C i) p ≤
            distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p - 1 ∧
          curvatureRadius (L.metric j C i) p <
            distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ∧
          ∃ q ∈ ((L.decomposition j C).component i).model.interior
              ((L.decomposition j C).component i).Carrier,
            ¬ SectionalBoundedBelowAt (L.metric j C i) q 0 := by
  obtain ⟨N, hN⟩ := L.alternatives (1 / 10000) (by norm_num) (by
    dsimp only [euclideanThreeUnitBallVolume]
    nlinarith [Real.pi_gt_three])
  refine ⟨N, fun j hj C i hi p hD => ?_⟩
  obtain ⟨A⟩ := hN j hj C
  have hfin : curvatureRadius (L.metric j C i) p ≠ ⊤ := L.finite_scales j C i hi p
  have htop : distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p = ⊤ →
      curvatureRadius (L.metric j C i) p ≤
          distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p - 1 ∧
        curvatureRadius (L.metric j C i) p <
          distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ∧
        ∃ q ∈ ((L.decomposition j C).component i).model.interior
            ((L.decomposition j C).component i).Carrier,
          ¬ SectionalBoundedBelowAt (L.metric j C i) q 0 := by
    intro ht
    refine ⟨by rw [ht]; simp, by rw [ht]; exact lt_top_iff_ne_top.mpr hfin, ?_⟩
    exact exists_interior_negative_of_finite_scale_T2 _ p ht hfin
  cases A i with
  | hyperbolic hnot _ _ => exact (hnot hi).elim
  | nonnegative hnot _ _ => exact (hnot hi).elim
  | thin _ hgeometry =>
    rcases hgeometry with ⟨hclosed, _⟩ | ⟨⟨B⟩, _⟩
    · exact htop (distanceToBoundary_eq_top_of_boundary_empty _ _ hclosed p)
    · by_cases ht : distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p = ⊤
      · exact htop ht
      · have hlt := lt_top_iff_ne_top.mpr ht
        have hneg := hG2 _ _ B p hD hlt
        have hle := curvatureRadius_le_sub_one_of_negative_planes_T2 _ p hD (fun η hη => by
          obtain ⟨q, _, hq1, hq2⟩ := hneg η hη
          exact ⟨q, hq1, hq2⟩)
        refine ⟨hle, hle.trans_lt (ENNReal.sub_lt_self ht (by
          intro h0; rw [h0] at hD; simp at hD) (by simp)), ?_⟩
        obtain ⟨q, hq, -, hq2⟩ := hneg 1 one_pos
        exact ⟨q, hq, fun hb => hq2 (hb.mono (by norm_num))⟩


/-- TCF02, frozen statement (modulo `hG2`). -/
theorem eventually_interior_scale_ambient_T2 (L : GC.LongTime.LateCutFamily F K slices)
    (hG2 : CollarNegativePlane.{u} K) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p →
        curvatureRadius (L.metric j C i) p ≤
            distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p - 1 ∧
          curvatureRadius (L.metric j C i) p <
            distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ∧
          curvatureRadius ((slices j).componentMetric C) (cutPieceMap (L.decomposition j C) i p) =
            curvatureRadius (L.metric j C i) p ∧
          ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ curvatureRadius (L.metric j C i) p →
            cutPieceMap (L.decomposition j C) i '' riemannianBallOf (L.metric j C i) p r =
                riemannianBallOf ((slices j).componentMetric C)
                  (cutPieceMap (L.decomposition j C) i p) r ∧
              ballVolume (L.metric j C i) p r =
                ballVolume ((slices j).componentMetric C)
                  (cutPieceMap (L.decomposition j C) i p) r ∧
              ∀ k : ℕ, ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
                curvatureDerivativeNorm (L.metric j C i) k q =
                  curvatureDerivativeNorm ((slices j).componentMetric C) k
                    (cutPieceMap (L.decomposition j C) i q) := by
  obtain ⟨N, hN⟩ := eventually_interior_scale_core_T2 L hG2
  refine ⟨N, fun j hj C i hi p hD => ?_⟩
  obtain ⟨h1, h2, -⟩ := hN j hj C i hi p hD
  obtain ⟨h3, h4⟩ := cutPiece_interior_scale_ambient_T2 L j C i p h2
  exact ⟨h1, h2, h3, h4⟩

/-- The exact shape of S5's `hT2` (`DerivativeAssembly.lean`), modulo `hG2`. -/
theorem hT2_shape_T2 (L : GC.LongTime.LateCutFamily F K slices)
    (hG2 : CollarNegativePlane.{u} K) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ c i, L.thin j c i →
      ∀ p : ((L.decomposition j c).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j c).component i) (L.metric j c i) p →
      ∃ p' : (slices j).stage.Carrier,
        (curvatureRadius (L.metric j c i) p ≠ ⊤ →
          ∃ z ∈ connectedComponent p',
            ¬ SectionalBoundedBelowAt (slices j).normalizedMetric z 0) ∧
        ∀ r : ℝ, 0 < r → r ≤ 9 →
          (ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
            ∀ q ∈ riemannianBallOf (slices j).normalizedMetric p' r,
              SectionalBoundedBelowAt (slices j).normalizedMetric q (-(r ^ 2)⁻¹)) ∧
          (∀ w : ℝ, 0 < w →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r →
            ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (slices j).normalizedMetric p' r) ∧
          (∀ k : ℕ, ∀ q ∈ riemannianBallOf (L.metric j c i) p r,
            ∃ q' ∈ riemannianBallOf (slices j).normalizedMetric p' r,
              curvatureDerivativeNorm (L.metric j c i) k q =
                curvatureDerivativeNorm (slices j).normalizedMetric k q') := by
  obtain ⟨N, hN⟩ := eventually_interior_scale_core_T2 L hG2
  refine ⟨N, fun j hj c i hi p hD => ?_⟩
  obtain ⟨-, -, q, hq, hqb⟩ := hN j hj c i hi p hD
  refine ⟨(cutPieceMap (L.decomposition j c) i p).val, fun _ => ?_, fun r hr hr9 => ?_⟩
  · exact ⟨_, cutPieceMap_val_mem_connectedComponent_T2 L j c i p q,
      not_sectionalBoundedBelowAt_normalized_of_interior_T2 L j c i hq hqb⟩
  · obtain ⟨h1, h2, h3⟩ := cutPiece_normalized_transfer_T2 L j c i p hD r hr hr9
    exact ⟨h1, fun w _ hv => h2 ▸ hv, h3⟩

end LateCutFamily

end GC.LongTime.Ch12
