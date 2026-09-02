import DifferentialGeometry.Geometry.Connection.GlobalParallelLine
import DifferentialGeometry.Tensor.Exterior.GlobalPoincare

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

theorem exists_global_gradient_potential_of_parallel_section
    [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hparallel : ∀ x, ∀ v : TangentSpace I x,
      (LeviCivita (I := I) g) X x v = 0) :
    ∃ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      ∀ x, ∀ v : TangentSpace I x,
        mvfderiv (I := I) f x v = g.inner x (X x) v := by
  let theta := metricFlat g fun x => X x
  have htheta : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] ℝ) x (theta x)) := by
    exact ContMDiff.clm_bundle_apply (b := id) g.contMDiff X.contMDiff
  let alpha : DifferentialGeometry.DifferentialForm I M 1 :=
    DifferentialGeometry.DifferentialForm.ofCotangent theta htheta
  have hcovtheta :
      (cotangentCov (LeviCivita (I := I) g)).toFun theta = 0 := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro y
    rw [cotangentCov_metricDuality g
      (X.contMDiff.mdifferentiableAt (by simp)) v y]
    rw [hparallel x v]
    simp
  have halpha : DifferentialGeometry.DifferentialForm.isClosed alpha := by
    exact DifferentialGeometry.DifferentialForm.isClosed_of_cotangentCov_eq_zero_of_torsion_eq_zero
      (LeviCivita (I := I) g) theta htheta hcovtheta
      (LeviCivita_torsion_eq_zero (I := I) g)
  obtain ⟨f, hf, hdf⟩ :=
    DifferentialGeometry.DifferentialForm.exists_global_potential alpha halpha
  refine ⟨f, hf, ?_⟩
  intro x v
  rw [hdf x v]
  rw [DifferentialGeometry.DifferentialForm.ofCotangent_apply]
  rfl

end DifferentialGeometry.Geometry.Connection
