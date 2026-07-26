import DifferentialGeometry.Analysis.Calculus.MovingImplicit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ConnAddTarget

/-!
# Vertical invertibility of the harmonic-map local addition

The target coordinate of the component-local exponential addition has identity
vertical derivative at the zero section.  Its `C²` regularity therefore keeps
that vertical derivative invertible on a small closed coordinate ball, and the
totalized inverse operator varies continuously there.

This is a fixed-chart, fixed-basepoint statement.  It does not claim that the
radius is uniform as the chart center ranges over the compact manifold.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

private theorem connAddTarget_cd
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 2 (localAddTarget (I := I) g p)
      (localAddZeroCoord (I := I) p) := by
  have hmd := connAdd_cd (I := I) g p 2 (by norm_num)
  rw [contMDiffAt_iff] at hmd
  obtain ⟨_, hcd⟩ := hmd
  have hrange : range I.tangent = (univ : Set (E × E)) :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange] at hcd
  have hchart : ContDiffAt ℝ 2 (connAddChart (I := I) g p)
      (localAddZeroCoord (I := I) p) := by
    simpa only [connAddChart, localAddZeroCoord] using
      (contDiffWithinAt_univ.mp hcd)
  simpa only [localAddTarget] using hchart.snd

/-- At the zero section, the partial derivative of the local-addition target
with respect to its vertical coordinate is the identity operator. -/
theorem connAdd_part_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    partialFDeriv₂ (localAddTarget (I := I) g p)
        (localAddZeroCoord (I := I) p).1
        (localAddZeroCoord (I := I) p).2 =
      ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [partialFDeriv₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.id_apply] using
    localAddTarget_vert (I := I) g p 1 le_rfl v

/-- The vertical derivative field of the local-addition target is `C¹` at the
zero section. -/
theorem connAdd_part_cd
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1
      (fun z : E × E =>
        partialFDeriv₂ (localAddTarget (I := I) g p) z.1 z.2)
      (localAddZeroCoord (I := I) p) := by
  let restrictVert : ((E × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E × E) E).flip
      (ContinuousLinearMap.inr ℝ E E)
  have hdf : ContDiffAt ℝ 1
      (fderiv ℝ (localAddTarget (I := I) g p))
      (localAddZeroCoord (I := I) p) :=
    (connAddTarget_cd (I := I) g p).fderiv_right (by norm_num)
  have hcomp : ContDiffAt ℝ 1
      (fun z => restrictVert
        (fderiv ℝ (localAddTarget (I := I) g p) z))
      (localAddZeroCoord (I := I) p) :=
    restrictVert.contDiff.contDiffAt.comp
      (localAddZeroCoord (I := I) p) hdf
  simpa only [partialFDeriv₂, restrictVert,
    ContinuousLinearMap.compL_apply] using hcomp

/-- The inverse vertical derivative is `C¹` at the zero section.  The inverse
is Mathlib's totalized operator inverse; local invertibility follows from the
identity value at the center. -/
theorem connAdd_inv_cd
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1
      (fun z : E × E =>
        (partialFDeriv₂ (localAddTarget (I := I) g p) z.1 z.2).inverse)
      (localAddZeroCoord (I := I) p) := by
  have hinv :
      (partialFDeriv₂ (localAddTarget (I := I) g p)
        (localAddZeroCoord (I := I) p).1
        (localAddZeroCoord (I := I) p).2).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.refl ℝ E, ?_⟩
    simpa only [ContinuousLinearEquiv.coe_refl] using
      (connAdd_part_zero (I := I) g p).symm
  have hmap : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
      (partialFDeriv₂ (localAddTarget (I := I) g p)
        (localAddZeroCoord (I := I) p).1
        (localAddZeroCoord (I := I) p).2) :=
    hinv.contDiffAt_map_inverse
  exact (hmap.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).comp
    (localAddZeroCoord (I := I) p)
    (connAdd_part_cd (I := I) g p)

/-- A fixed basepoint admits a positive compact coordinate tube on which the
vertical derivative is invertible and its inverse varies continuously. -/
theorem exists_connAdd_tube
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r > 0,
      IsCompact (Metric.closedBall (localAddZeroCoord (I := I) p) r) ∧
      (∀ z ∈ Metric.closedBall (localAddZeroCoord (I := I) p) r,
        (partialFDeriv₂ (localAddTarget (I := I) g p) z.1 z.2).IsInvertible) ∧
      ContinuousOn
        (fun z : E × E =>
          (partialFDeriv₂ (localAddTarget (I := I) g p) z.1 z.2).inverse)
        (Metric.closedBall (localAddZeroCoord (I := I) p) r) := by
  let A : E × E → E →L[ℝ] E := fun z =>
    partialFDeriv₂ (localAddTarget (I := I) g p) z.1 z.2
  let invSet : Set (E →L[ℝ] E) :=
    Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)
  have hinvOpen : IsOpen invSet := ContinuousLinearEquiv.isOpen
  have hA0 : A (localAddZeroCoord (I := I) p) ∈ invSet := by
    refine ⟨ContinuousLinearEquiv.refl ℝ E, ?_⟩
    simpa only [A, ContinuousLinearEquiv.coe_refl] using
      (connAdd_part_zero (I := I) g p).symm
  have hinvNhd : A ⁻¹' invSet ∈ 𝓝 (localAddZeroCoord (I := I) p) :=
    (connAdd_part_cd (I := I) g p).continuousAt.preimage_mem_nhds
      (hinvOpen.mem_nhds hA0)
  obtain ⟨U, hU, hInvU⟩ :=
    (connAdd_inv_cd (I := I) g p).contDiffOn le_rfl (by simp)
  have hgood : U ∩ A ⁻¹' invSet ∈ 𝓝 (localAddZeroCoord (I := I) p) :=
    Filter.inter_mem hU hinvNhd
  obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp hgood
  let r : ℝ := q / 2
  have hr : 0 < r := div_pos hq (by norm_num)
  have hrq : r < q := by
    dsimp only [r]
    linarith
  have hball : Metric.closedBall (localAddZeroCoord (I := I) p) r ⊆
      U ∩ A ⁻¹' invSet :=
    (Metric.closedBall_subset_ball hrq).trans hqsub
  refine ⟨r, hr, isCompact_closedBall _ _, ?_, ?_⟩
  · intro z hz
    rcases (hball hz).2 with ⟨e, he⟩
    exact ⟨e, he⟩
  · exact hInvU.continuousOn.mono (fun z hz => (hball hz).1)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
