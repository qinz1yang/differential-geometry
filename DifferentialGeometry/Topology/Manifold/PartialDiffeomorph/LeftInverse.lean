import DifferentialGeometry.Topology.Manifold.InverseFunction
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Set Manifold Filter
open scoped Manifold ContDiff Topology

namespace Set.LeftInvOn

theorem exists_partialDiffeomorph
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {f : M → N} {g : N → M} {U : Set M}
    (hgf : LeftInvOn g f U) (hU : IsOpen U)
    (hf : ContMDiffOn I J ∞ f U)
    (hg : ∀ x ∈ U, ContMDiffAt J I ∞ g (f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ χ : PartialDiffeomorph I J M N ∞,
      χ.source = U ∧ χ.target = f '' U ∧ (χ : M → N) = f ∧ (χ.symm : N → M) = g := by
  have hlocal : IsLocalDiffeomorphOn I J ∞ f U := by
    rintro ⟨x, hx⟩
    have hdf := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hdg := (hg x hx).mdifferentiableAt (by simp)
    have heq : g ∘ f =ᶠ[𝓝 x] id := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hgf hy
    let D : E →L[ℝ] F := mfderiv I J f x
    have hcomp : (mfderiv J I g (f x)).comp (mfderiv I J f x) =
        ContinuousLinearMap.id ℝ E := by
      have h := (mfderiv_comp x hdg hdf).symm.trans heq.mfderiv_eq
      rw [mfderiv_id] at h
      exact h
    have hinj : Function.Injective D := (ContinuousLinearMap.leftInverse_of_comp hcomp).injective
    let A : E ≃L[ℝ] F :=
      (D.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    exact DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      hU hx hf ⟨A, rfl⟩
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    have hmap := Filter.image_mem_map (m := f) (hU.mem_nhds hx)
    rwa [hlocal.isLocalHomeomorphOn.map_nhds_eq hx] at hmap
  refine ⟨{
    toFun := f
    invFun := g
    source := U
    target := f '' U
    map_source' := fun x hx => mem_image_of_mem f hx
    map_target' := ?_
    left_inv' := fun x hx => hgf hx
    right_inv' := ?_
    open_source := hU
    open_target := hopen
    contMDiffOn_toFun := hf
    contMDiffOn_invFun := ?_ }, rfl, rfl, rfl, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [hgf hx]
    exact hx
  · rintro y ⟨x, hx, rfl⟩
    rw [hgf hx]
  · rintro y ⟨x, hx, rfl⟩
    exact (hg x hx).contMDiffWithinAt

end Set.LeftInvOn
