import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
    (f : M → N) (hf : ContMDiff I J ∞ f) (x₀ : M)
    (A : E ≃L[ℝ] F) (hdf : HasMFDerivAt I J f x₀ (A : E →L[ℝ] F)) :
    IsLocalDiffeomorphAt I J ∞ f x₀ := by
  exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    f (U := Set.univ) hf.contMDiffOn isOpen_univ x₀ (Set.mem_univ x₀) A hdf

end DifferentialGeometry.Topology.Manifold

open Manifold Set Topology

namespace DifferentialGeometry.Topology

theorem isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    {f : M → N} {U : Set M} {x : M} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U) (hinv : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  have hmd : MDifferentiableAt I J f x :=
    (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcoord : (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible := by
    rwa [hmd.mfderiv, I.range_eq_univ, fderivWithin_univ] at hinv
  obtain ⟨Φ, hxΦ, hΦU, heq⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn
      (n := 1) le_rfl (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      hU hx (hf.of_le (by simp)) hcoord
  have hregular : ∀ y ∈ Φ.source,
      (fderiv ℝ (writtenInExtChartAt I J y f) (extChartAt I y y)).IsInvertible := by
    intro y hy
    have hd : IsLocalDiffeomorphAt I J 1 f y := ⟨Φ, hy, heq⟩
    have hinv' : (mfderiv I J f y).IsInvertible :=
      ⟨hd.mfderivToContinuousLinearEquiv one_ne_zero, rfl⟩
    rwa [(hd.mdifferentiableAt one_ne_zero).mfderiv, I.range_eq_univ,
      fderivWithin_univ] at hinv'
  obtain ⟨Ψ, hxΨ, _, hΨ⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      Φ.open_source hxΦ (hf.mono hΦU) hregular
  exact ⟨Ψ, hxΨ, hΨ⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_partialDiffeomorph_of_contDiffAt {f : E → F} {p : E}
    (A : E ≃L[ℝ] F) (hf : ContDiffAt ℝ 1 f p)
    (hD : HasFDerivAt f A.toContinuousLinearMap p) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1,
      p ∈ Φ.source ∧ (Φ : E → F) = f := by
  let e := hf.toOpenPartialHomeomorph f hD (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hp : p ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD (by norm_num)
  obtain ⟨U, hU, hcU⟩ := hf.contDiffOn (m := 1) le_rfl (by norm_num)
  have hi : ContDiffAt ℝ 1 e.symm (e p) := hf.to_localInverse hD (by norm_num)
  obtain ⟨V, hV, hcV⟩ := hi.contDiffOn (m := 1) le_rfl (by norm_num)
  let s : Set E := U ∩ e ⁻¹' V
  have hs : s ∈ 𝓝 p := Filter.inter_mem hU ((e.continuousAt hp).preimage_mem_nhds hV)
  let e' := e.restr s
  have hsub : e'.source ⊆ U := fun x hx ↦ (interior_subset hx.2).1
  have ht : e'.target ⊆ V := by
    intro y hy
    have hh := e'.map_target hy
    have hv : e (e'.symm y) ∈ V := (interior_subset hh.2).2
    exact (e'.right_inv hy) ▸ hv
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1 := {
    toPartialEquiv := e'.toPartialEquiv
    open_source := e'.open_source
    open_target := e'.open_target
    contMDiffOn_toFun := (hcU.mono hsub).contMDiffOn
    contMDiffOn_invFun := (hcV.mono ht).contMDiffOn }
  refine ⟨Φ, ⟨hp, mem_interior_iff_mem_nhds.mpr hs⟩, rfl⟩

end DifferentialGeometry.Manifold
