import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem contMDiffOn_extend_from_open
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (U : TopologicalSpace.Opens M) (f : U → N) (d : M → N)
    {A : Set U} (hA : IsOpen A) (hf : ContMDiffOn I J ∞ f A) :
    ContMDiffOn I J ∞ (Subtype.val.extend f d) (Subtype.val '' A) := by
  rintro x ⟨y, hy, rfl⟩
  have hlocal : ContMDiffAt I J ∞ (fun z : U ↦ Subtype.val.extend f d (z : M)) y := by
    change ContMDiffAt I J ∞ ((Subtype.val.extend f d) ∘ Subtype.val) y
    rw [Function.extend_comp Subtype.val_injective]
    exact (hf y hy).contMDiffAt (hA.mem_nhds hy)
  exact (contMDiffAt_subtype_iff.mp hlocal).contMDiffWithinAt

theorem mvfderiv_extend_from_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (f : U → ℝ) (d : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : U) (v : TangentSpace I x) :
    mvfderiv I (Subtype.val.extend f d) (x : M) (mfderiv I I (Subtype.val : U → M) x v) =
      mvfderiv I f x v := by
  have hlocal : ContMDiffAt I 𝓘(ℝ) ∞ (Subtype.val.extend f d) (x : M) := by
    rw [← contMDiffAt_subtype_iff (x := x)]
    change ContMDiffAt I 𝓘(ℝ) ∞ ((Subtype.val.extend f d) ∘ Subtype.val) x
    rw [Function.extend_comp Subtype.val_injective]
    exact hf.contMDiffAt
  have h := mvfderiv_comp_apply x (hlocal.mdifferentiableAt (by decide))
    ((contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiable (by decide) x) v
  rw [Function.extend_comp Subtype.val_injective] at h
  exact h.symm

end DifferentialGeometry.Topology.Manifold
