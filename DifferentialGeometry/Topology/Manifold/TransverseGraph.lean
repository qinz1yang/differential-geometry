import DifferentialGeometry.Topology.Covering.OrderedFiber
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Covering.SimplyConnected
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_diffeomorph_graph_of_transverse_embedding
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [I.Boundaryless] [J.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [PathConnectedSpace M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [T2Space N] [ConnectedSpace N]
    (e : M → N × ℝ) (he : ContMDiff I (J.prod 𝓘(ℝ)) ∞ e)
    (hinj : Function.Injective e)
    (himm : ∀ p, Function.Injective (mfderiv I (J.prod 𝓘(ℝ)) e p))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (htransverse : ∀ p, (0, 1) ∉ range (mfderiv I (J.prod 𝓘(ℝ)) e p)) :
    ∃ (η : N ≃ₘ⟮J, I⟯ M) (h : N → ℝ), ContMDiff J 𝓘(ℝ) ∞ h ∧
      ∀ p, e (η p) = (p, h p) := by
  let q : M → N := fun p ↦ (e p).1
  have hq : ContMDiff I J ∞ q := contMDiff_fst.comp he
  have hdq (p : M) (v : E) : mfderiv I J q p v =
      (mfderiv I (J.prod 𝓘(ℝ)) e p v : F × ℝ).1 := by
    change mfderiv I J (Prod.fst ∘ e) p v = _
    rw [mfderiv_comp p mdifferentiableAt_fst (he.mdifferentiable (by decide) p), mfderiv_fst]
    rfl
  have hqinj (p : M) : Function.Injective (mfderiv I J q p) := by
    intro v w hvw
    change (mfderiv I J q p : E →L[ℝ] F) v = (mfderiv I J q p : E →L[ℝ] F) w at hvw
    suffices hzero : ∀ v : E, mfderiv I J q p v = 0 → v = 0 by
      have hz := hzero (v - w) (by rw [map_sub, hvw, sub_self])
      exact sub_eq_zero.mp hz
    intro z hz
    let A : E →L[ℝ] F × ℝ := mfderiv I (J.prod 𝓘(ℝ)) e p
    have hfst : (A z).1 = 0 := (hdq p z).symm.trans hz
    have hsnd : (A z).2 = 0 := by
      by_contra hn
      apply htransverse p
      refine ⟨((A z).2)⁻¹ • z, ?_⟩
      change A (((A z).2)⁻¹ • z) = (0, 1)
      rw [map_smul]
      ext
      · simp [hfst]
      · simp [hn]
    apply himm p
    change A z = A 0
    rw [map_zero]
    exact Prod.ext hfst hsnd
  have hloc : IsLocalDiffeomorph I J ∞ q := by
    intro p
    let D : E →L[ℝ] F := mfderiv I J q p
    let A : E ≃L[ℝ] F :=
      (D.toLinearMap.linearEquivOfInjective (hqinj p) hdim).toContinuousLinearEquiv
    exact isLocalDiffeomorphAt_of_hasMFDerivAt_equiv q hq p A
      ((hq.mdifferentiable (by decide) p).hasMFDerivAt)
  let : T2Space M := T2Space.of_injective_continuous hinj he.continuous
  have hcover := hloc.isLocalHomeomorph.covering_compact
  have hbij : Function.Bijective q :=
    ⟨DifferentialGeometry.Topology.Covering.injective_of_continuous_fiber_separating_map hcover
      (fun p ↦ (e p).2) (continuous_snd.comp he.continuous)
      (by simpa [q] using hinj), hloc.isLocalHomeomorph.surjective_compact⟩
  let φ := hloc.diffeomorphOfBijective hbij
  refine ⟨φ.symm, (fun p ↦ (e (φ.symm p)).2),
    contMDiff_snd.comp (he.comp φ.symm.contMDiff), ?_⟩
  intro p
  exact Prod.ext (φ.apply_symm_apply p) rfl

end DifferentialGeometry.Topology.Manifold
