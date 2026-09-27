import DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit
import DifferentialGeometry.Geometry.Exponential.LocalAddition.Coordinates.Target

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

private theorem targetCoordinates_contDiffAt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 2 (targetCoordinates (I := I) g p)
      (zeroCoordinates (I := I) p) := by
  have hmd := connectedComponentDiagonalExponential_contMDiffAt_zero (I := I) g p 2
  rw [contMDiffAt_iff] at hmd
  obtain ⟨_, hcd⟩ := hmd
  have hrange : range I.tangent = (univ : Set (E × E)) :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange] at hcd
  have hchart : ContDiffAt ℝ 2 (localAdditionCoordinateMap (I := I) g p)
      (zeroCoordinates (I := I) p) := by
    have hraw := (contDiffWithinAt_univ.mp hcd).of_le
      (show (2 : WithTop ℕ∞) ≤ (↑(↑(2 : ℕ) : ℕ∞) : WithTop ℕ∞) by norm_num)
    simpa only [localAdditionCoordinateMap, zeroCoordinates] using hraw
  change ContDiffAt ℝ 2 (fun z => (localAdditionCoordinateMap (I := I) g p z).2)
    (zeroCoordinates (I := I) p)
  exact hchart.snd

theorem partialFDeriv₂_targetCoordinates_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    partialFDeriv₂ (targetCoordinates (I := I) g p)
        (zeroCoordinates (I := I) p).1
        (zeroCoordinates (I := I) p).2 =
      ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [partialFDeriv₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.id_apply] using
    targetCoordinates_fderiv_vertical (I := I) g p 1 le_rfl v

theorem partialFDeriv₂_targetCoordinates_contDiffAt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1
      (fun z : E × E =>
        partialFDeriv₂ (targetCoordinates (I := I) g p) z.1 z.2)
      (zeroCoordinates (I := I) p) := by
  let restrictVert : ((E × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E × E) E).flip
      (ContinuousLinearMap.inr ℝ E E)
  have hdf : ContDiffAt ℝ 1
      (fderiv ℝ (targetCoordinates (I := I) g p))
      (zeroCoordinates (I := I) p) :=
    (targetCoordinates_contDiffAt (I := I) g p).fderiv_right (by norm_num)
  have hcomp : ContDiffAt ℝ 1
      (fun z => restrictVert
        (fderiv ℝ (targetCoordinates (I := I) g p) z))
      (zeroCoordinates (I := I) p) :=
    restrictVert.contDiff.contDiffAt.comp
      (zeroCoordinates (I := I) p) hdf
  change ContDiffAt ℝ 1
    (fun z : E × E => restrictVert
      (fderiv ℝ (targetCoordinates (I := I) g p) (z.1, z.2)))
    (zeroCoordinates (I := I) p)
  rw [show (fun z : E × E => restrictVert
      (fderiv ℝ (targetCoordinates (I := I) g p) (z.1, z.2))) =
      fun z => restrictVert (fderiv ℝ (targetCoordinates (I := I) g p) z) by
    funext z
    rw [Prod.eta]]
  exact hcomp

theorem inverse_partialFDeriv₂_targetCoordinates_contDiffAt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1
      (fun z : E × E =>
        (partialFDeriv₂ (targetCoordinates (I := I) g p) z.1 z.2).inverse)
      (zeroCoordinates (I := I) p) := by
  have hinv :
      (partialFDeriv₂ (targetCoordinates (I := I) g p)
        (zeroCoordinates (I := I) p).1
        (zeroCoordinates (I := I) p).2).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.refl ℝ E, ?_⟩
    simpa only [ContinuousLinearEquiv.coe_refl] using
      (partialFDeriv₂_targetCoordinates_zero (I := I) g p).symm
  have hmap : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
      (partialFDeriv₂ (targetCoordinates (I := I) g p)
        (zeroCoordinates (I := I) p).1
        (zeroCoordinates (I := I) p).2) :=
    hinv.contDiffAt_map_inverse
  exact (hmap.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).comp
    (zeroCoordinates (I := I) p)
    (partialFDeriv₂_targetCoordinates_contDiffAt (I := I) g p)

theorem exists_partialFDeriv₂_targetCoordinates_inverse_on_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r > 0,
      IsCompact (Metric.closedBall (zeroCoordinates (I := I) p) r) ∧
      (∀ z ∈ Metric.closedBall (zeroCoordinates (I := I) p) r,
        (partialFDeriv₂ (targetCoordinates (I := I) g p) z.1 z.2).IsInvertible) ∧
      ContinuousOn
        (fun z : E × E =>
          (partialFDeriv₂ (targetCoordinates (I := I) g p) z.1 z.2).inverse)
        (Metric.closedBall (zeroCoordinates (I := I) p) r) := by
  let A : E × E → E →L[ℝ] E := fun z =>
    partialFDeriv₂ (targetCoordinates (I := I) g p) z.1 z.2
  let invSet : Set (E →L[ℝ] E) :=
    Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)
  have hinvOpen : IsOpen invSet := ContinuousLinearEquiv.isOpen
  have hA0 : A (zeroCoordinates (I := I) p) ∈ invSet := by
    refine ⟨ContinuousLinearEquiv.refl ℝ E, ?_⟩
    simpa only [A, ContinuousLinearEquiv.coe_refl] using
      (partialFDeriv₂_targetCoordinates_zero (I := I) g p).symm
  have hinvNhd : A ⁻¹' invSet ∈ 𝓝 (zeroCoordinates (I := I) p) :=
    (partialFDeriv₂_targetCoordinates_contDiffAt (I := I) g p).continuousAt.preimage_mem_nhds
      (hinvOpen.mem_nhds hA0)
  obtain ⟨U, hU, hInvU⟩ :=
    (inverse_partialFDeriv₂_targetCoordinates_contDiffAt (I := I) g p).contDiffOn le_rfl (by simp)
  have hgood : U ∩ A ⁻¹' invSet ∈ 𝓝 (zeroCoordinates (I := I) p) :=
    Filter.inter_mem hU hinvNhd
  obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp hgood
  let r : ℝ := q / 2
  have hr : 0 < r := div_pos hq (by norm_num)
  have hrq : r < q := by
    dsimp only [r]
    linarith
  have hball : Metric.closedBall (zeroCoordinates (I := I) p) r ⊆
      U ∩ A ⁻¹' invSet :=
    (Metric.closedBall_subset_ball hrq).trans hqsub
  refine ⟨r, hr, isCompact_closedBall _ _, ?_, ?_⟩
  · intro z hz
    rcases (hball hz).2 with ⟨e, he⟩
    exact ⟨e, he⟩
  · exact hInvU.continuousOn.mono (fun z hz => (hball hz).1)

end DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

end
