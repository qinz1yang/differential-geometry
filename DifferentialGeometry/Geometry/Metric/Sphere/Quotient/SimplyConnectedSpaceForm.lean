import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveSpaceForm
import DifferentialGeometry.Topology.Covering.SimplyConnected

set_option autoImplicit false

noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private instance simplyConnectedSpaceFormFinFact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]⟩

theorem exists_isometry_round_sphere_of_constant_positive_sectional_curvature
    [CompactSpace M] [SimplyConnectedSpace M] [I.Boundaryless]
    {n : ℕ} (hn : 1 < n) (hdim : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    ∃ Φ : M ≃ₘ⟮I, 𝓡 n⟯ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ (x : M) (v w : TangentSpace I x),
        (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)).inner (Φ x)
            (mfderiv I (𝓡 n) Φ x v) (mfderiv I (𝓡 n) Φ x w) =
          c * g.inner x v w := by
  obtain ⟨cover, hlocal, -, hcovering, hmetric⟩ :=
    exists_round_sphere_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) hn inferInstance inferInstance inferInstance hdim g c hc hsec
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  let _ : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  let e := hcovering.diffeomorphSc hlocal
  refine ⟨e.symm, fun x v w => ?_⟩
  have hcomp (u : TangentSpace I x) :
      mfderiv (𝓡 n) I cover (e.symm x) (mfderiv I (𝓡 n) e.symm x u) = u := by
    have hce : cover ∘ e.symm = id := by
      funext y
      exact e.apply_symm_apply y
    have h := mfderiv_comp_apply (I := I) (I' := 𝓡 n) (I'' := I) (f := e.symm) (g := cover) x
      (e.contMDiff.mdifferentiableAt (by simp)) (e.symm.contMDiff.mdifferentiableAt (by simp)) u
    rw [hce, mfderiv_id] at h
    exact h.symm
  have hx : cover (e.symm x) = x := e.apply_symm_apply x
  have h := hmetric (e.symm x) (mfderiv I (𝓡 n) e.symm x v) (mfderiv I (𝓡 n) e.symm x w)
  rw [scaleMetric_inner, hcomp v, hcomp w, hx] at h
  exact h.symm

end Geometry
end DifferentialGeometry
