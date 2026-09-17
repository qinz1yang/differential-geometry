import DifferentialGeometry.Topology.Manifold.SphereDirection
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Embedding.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : ℕ} [Fact (Module.finrank ℝ F = n + 1)]

theorem isLocalDiffeomorphOn_sphereDirection_comp_of_norm_eq_one
    (v : sphere (0 : F) 1) {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hnorm : ∀ x ∈ U, ‖f x‖ = 1)
    (hder : ∀ x ∈ U, Function.Injective (fderiv ℝ f x))
    (hdim : Module.finrank ℝ E = n) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) (𝓡 n) ∞ (sphereDirection v ∘ f) U := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let g := sphereDirection v ∘ f
  have hne (x : E) (hx : x ∈ U) : f x ≠ 0 :=
    norm_ne_zero_iff.mp ((hnorm x hx).trans_ne one_ne_zero)
  have hg : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ g U :=
    (contMDiffOn_sphereDirection v).comp hf.contMDiffOn (fun x hx => hne x hx)
  have hgf : EqOn (fun x => (g x : F)) f U := by
    intro x hx
    change (sphereDirection v (f x) : F) = f x
    rw [coe_sphereDirection v (hne x hx), hnorm x hx, inv_one, one_smul]
  intro x
  have hgx := (hg.contMDiffAt (hU.mem_nhds x.property)).mdifferentiableAt (by simp)
  have hcoe := (isSmoothEmbedding_coe_sphere (E := F) (n := n)).contMDiff
  have heq : (fun y => (g y : F)) =ᶠ[𝓝 x.val] f := by
    filter_upwards [hU.mem_nhds x.property] with y hy
    exact hgf hy
  have hmf : mfderiv (𝓘(ℝ, E)) 𝓘(ℝ, F) (fun y => (g y : F)) x.val = fderiv ℝ f x.val := by
    rw [heq.mfderiv_eq, mfderiv_eq_fderiv]
  have hinj : Function.Injective (mfderiv 𝓘(ℝ, E) (𝓡 n) g x.val) := by
    have hinj' := hmf ▸ hder x.val x.property
    change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (Subtype.val ∘ g) x.val) at hinj'
    rw [mfderiv_comp x.val (hcoe.mdifferentiableAt (by simp)) hgx] at hinj'
    exact Function.Injective.of_comp hinj'
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, E) (𝓡 n) g x.val
  let A : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (L.toLinearMap.linearEquivOfInjective hinj
      (by simpa using hdim)).toContinuousLinearEquiv
  exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv g hg hU x.val
    x.property A hgx.hasMFDerivAt

end DifferentialGeometry.Topology.Manifold
