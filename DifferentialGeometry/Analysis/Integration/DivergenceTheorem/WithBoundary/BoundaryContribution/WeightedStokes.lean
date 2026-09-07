import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.ChartLocalFlux
import DifferentialGeometry.Topology.PartitionOfUnity
import DifferentialGeometry.Topology.Manifold.PartitionOfUnity
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Integral.Measure

variable {n : Nat} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local notation "J" => modelWithCornersEuclideanHalfSpace n
local notation "V" => EuclideanSpace Real (Fin n)

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (BoundaryManifold J M) := borel _
private local instance : BorelSpace (BoundaryManifold J M) := ⟨rfl⟩

private theorem integrable_weighted_divergence
    (g : SmoothRiemannianMetric J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : ContMDiff J 𝓘(Real) ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x => f x * divergenceGWithBoundary g X x + tangentSectionAction X f x)
      (riemannianVolumeMeasure (I := J) (M := M) g) := by
  have hm : Integrable (fun x => f x * divergenceGWithBoundary g X x)
      (riemannianVolumeMeasure (I := J) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
      (hf.continuous.mul (divergence_g_with_boundary_contMDiff g X).continuous) hc.mul_right
  have hactc : HasCompactSupport (tangentSectionAction X f) := by
    apply HasCompactSupport.intro hc
    intro x hx
    change mfderiv J 𝓘(Real) f x (X x) = 0
    rw [(notMem_tsupport_iff_eventuallyEq.mp hx).mfderiv_eq]
    change mfderiv J 𝓘(Real) (fun _ : M => (0 : Real)) x (X x) = 0
    rw [mfderiv_const]
    rfl
  exact hm.add (Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
    (tangentSectionAction_contMDiff X hf).continuous hactc)

private theorem integrable_weighted_surface_flux
    (g : SmoothRiemannianMetric J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x : BoundaryManifold J M =>
      f (x : M) * g.inner (x : M) (outwardNormal g x) (X (x : M))) (surfaceMeasure g) := by
  have : IsFiniteMeasureOnCompacts (surfaceMeasure g) := surfaceMeasure_isFiniteMeasureOnCompacts g
  have hcont : Continuous (fun x : BoundaryManifold J M =>
      f (x : M) * g.inner (x : M) (outwardNormal g x) (X (x : M))) :=
    (hf.comp (continuous_subtype_val :
      Continuous (fun x : BoundaryManifold J M => (x : M)))).mul
        (continuous_outwardNormal_inner_smoothSection g X)
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_comp_boundaryInclusion hc).mul_right

private theorem integral_weighted_divergence_eq_zero_of_interior_support
    (g : SmoothRiemannianMetric J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : ContMDiff J 𝓘(Real) ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (modelWithCornersEuclideanHalfSpace n).interior M) :
    ∫ x, f x * divergenceGWithBoundary g X x + tangentSectionAction X f x
        ∂riemannianVolumeMeasure (I := J) (M := M) g =
      ∫ x, f (x : M) * g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g := by
  have hm : Integrable (fun x => f x * divergenceGWithBoundary g X x)
      (riemannianVolumeMeasure (I := J) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
      (hf.continuous.mul (divergence_g_with_boundary_contMDiff g X).continuous) hc.mul_right
  have hsum := integrable_weighted_divergence g X hf hc
  have ha := hsum.sub hm
  have ha' : Integrable (tangentSectionAction X f)
      (riemannianVolumeMeasure (I := J) (M := M) g) := by
    convert ha using 1
    funext x
    exact (add_sub_cancel_left _ _).symm
  rw [integral_add hm ha',
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary_of_hasCompactSupport
      g hf hc hs X, add_neg_cancel]
  symm
  apply integral_eq_zero_of_ae
  filter_upwards with x
  have hfx : f (x : M) = 0 := by
    by_contra hx
    exact Set.disjoint_left.mp (modelWithCornersEuclideanHalfSpace n).disjoint_interior_boundary
      (hs (subset_tsupport f hx)) x.property
  rw [hfx, zero_mul]
  rfl

theorem integral_mul_divergence_g_with_boundary_add_tangentSectionAction_eq_surfaceMeasure_flux
    (g : SmoothRiemannianMetric J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : ContMDiff J 𝓘(Real) ∞ f) (hc : HasCompactSupport f) :
    ∫ x, f x * divergenceGWithBoundary g X x + tangentSectionAction X f x
        ∂riemannianVolumeMeasure (I := J) (M := M) g =
      ∫ x, f (x : M) * g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g := by
  classical
  obtain ⟨rho, hrho, hrhoint⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source_inter_interior (I := J) (M := M)
  obtain ⟨s, hsum⟩ := rho.toPartitionOfUnity.exists_finset_sum_smul_eq hc (subset_univ _)
  let w : M → M → Real := fun i x => rho i x * f x
  have hw (i : M) : ContMDiff J 𝓘(Real) ∞ (w i) := (rho i).contMDiff.mul hf
  have hwc (i : M) : HasCompactSupport (w i) := hc.mul_left
  have hweq : f = ∑ i ∈ s, w i := by
    funext x
    have h := (hsum x).symm
    change f x = ∑ i ∈ s, rho i x * f x at h
    simpa only [Finset.sum_apply, w] using h
  have haction (x : M) : tangentSectionAction X f x =
      ∑ i ∈ s, tangentSectionAction X (w i) x := by
    conv_lhs => rw [hweq]
    exact tangentSectionAction_finset_sum X s w x
      (fun i _ => (hw i).mdifferentiableAt (by simp))
  have hlocal (i : M) :
      (∫ x, w i x * divergenceGWithBoundary g X x + tangentSectionAction X (w i) x
        ∂riemannianVolumeMeasure (I := J) (M := M) g) =
      ∫ x, w i (x : M) * g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g := by
    rcases (modelWithCornersEuclideanHalfSpace n).isInteriorPoint_or_isBoundaryPoint i with hi | hi
    · exact integral_weighted_divergence_eq_zero_of_interior_support g X (hw i) (hwc i)
        (tsupport_mul_subset_left.trans (hrhoint i hi))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      exact integral_mul_divergence_g_with_boundary_add_tangentSectionAction_eq_surfaceMeasure_flux_of_tsupport_subset
        g ⟨i, hi⟩ X (hw i) (hwc i)
        (tsupport_mul_subset_left.trans (hrho i))
  have hleft : (fun x => f x * divergenceGWithBoundary g X x + tangentSectionAction X f x) =
      fun x => ∑ i ∈ s, (w i x * divergenceGWithBoundary g X x + tangentSectionAction X (w i) x) := by
    funext x
    rw [haction, Finset.sum_add_distrib, ← Finset.sum_mul]
    congr 1
    exact congrArg (fun t : Real => t * divergenceGWithBoundary g X x) (hsum x).symm
  have hright : (fun x : BoundaryManifold J M =>
      f (x : M) * g.inner (x : M) (outwardNormal g x) (X (x : M))) =
      fun x : BoundaryManifold J M =>
        ∑ i ∈ s, w i (x : M) * g.inner (x : M) (outwardNormal g x) (X (x : M)) := by
    funext x
    rw [← Finset.sum_mul]
    exact congrArg (fun t : Real => t * g.inner (x : M) (outwardNormal g x) (X (x : M)))
      (hsum (x : M)).symm
  rw [hleft, hright, integral_finsetSum s (fun i _ => integrable_weighted_divergence g X (hw i) (hwc i)),
    integral_finsetSum s (fun i _ => integrable_weighted_surface_flux g X (hw i).continuous (hwc i))]
  exact Finset.sum_congr rfl (fun i _ => hlocal i)

theorem integral_divergence_g_with_boundary_eq_surfaceMeasure_flux [CompactSpace M]
    (g : SmoothRiemannianMetric J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯) :
    ∫ x, divergenceGWithBoundary g X x ∂riemannianVolumeMeasure (I := J) (M := M) g =
      ∫ x, g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g := by
  simpa only [one_mul, tangentSectionAction_const, add_zero] using
    integral_mul_divergence_g_with_boundary_add_tangentSectionAction_eq_surfaceMeasure_flux
      g X (f := fun _ => 1) contMDiff_const (HasCompactSupport.of_compactSpace _)

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
