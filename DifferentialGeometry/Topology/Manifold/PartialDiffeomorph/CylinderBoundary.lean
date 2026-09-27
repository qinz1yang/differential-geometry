import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_sphere_diffeomorph_of_sphere_chart_and_cylinder_boundary
    (A : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (T : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ)) I
      (Metric.sphere (0 : E) 1 × ℝ) M ∞)
    (hA : Metric.sphere (0 : E) 1 ⊆ A.source)
    (hT : ∀ q : Metric.sphere (0 : E) 1, (q, (0 : ℝ)) ∈ T.source)
    (hrange : A '' Metric.sphere (0 : E) 1 =
      range (fun q : Metric.sphere (0 : E) 1 => T (q, 0))) :
    ∃ e : Metric.sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : E) 1,
      (∀ q, A (e q) = T (q, 0)) ∧ (∀ q, T (e.symm q, 0) = A q) := by
  have himage (q : Metric.sphere (0 : E) 1) :
      T (q, 0) ∈ A '' Metric.sphere (0 : E) 1 :=
    hrange.symm ▸ mem_range_self q
  have htarget (q : Metric.sphere (0 : E) 1) : T (q, 0) ∈ A.target := by
    obtain ⟨z, hz, heq⟩ := himage q
    exact heq ▸ A.map_source (hA hz)
  have hinverse (q : Metric.sphere (0 : E) 1) :
      A.symm (T (q, 0)) ∈ Metric.sphere (0 : E) 1 := by
    obtain ⟨z, hz, heq⟩ := himage q
    have hleft : A.symm (A z) = z := A.left_inv' (hA hz)
    rw [← heq, hleft]
    exact hz
  have hTtarget (q : Metric.sphere (0 : E) 1) : A q ∈ T.target := by
    obtain ⟨z, hz⟩ := hrange ▸ mem_image_of_mem A q.property
    exact hz ▸ T.map_source (hT z)
  have hheight (q : Metric.sphere (0 : E) 1) : (T.symm (A q)).2 = 0 := by
    obtain ⟨z, hz⟩ := hrange ▸ mem_image_of_mem A q.property
    have hleft : T.symm (T (z, 0)) = (z, 0) := T.left_inv' (hT z)
    rw [← hz, hleft]
  let f : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1 :=
    fun q => ⟨A.symm (T (q, 0)), hinverse q⟩
  let g : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1 :=
    fun q => (T.symm (A q)).1
  have hf (q : Metric.sphere (0 : E) 1) : A (f q) = T (q, 0) :=
    A.right_inv (htarget q)
  have hg (q : Metric.sphere (0 : E) 1) : T (g q, 0) = A q := by
    change T ((T.symm (A q)).1, 0) = A q
    rw [← hheight q]
    exact T.right_inv (hTtarget q)
  have hTsm : ContMDiff (𝓡 n) I ∞ (fun q : Metric.sphere (0 : E) 1 => T (q, 0)) :=
    contMDiffOn_univ.mp (T.contMDiffOn_toFun.comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun q _ => hT q))
  have hAsm : ContMDiff (𝓡 n) I ∞ (fun q : Metric.sphere (0 : E) 1 => A q) :=
    contMDiffOn_univ.mp (A.contMDiffOn_toFun.comp contMDiff_coe_sphere.contMDiffOn
      (fun q _ => hA q.property))
  have hfsm : ContMDiff (𝓡 n) (𝓡 n) ∞ f := by
    apply ContMDiff.codRestrict_sphere
    exact contMDiffOn_univ.mp (A.contMDiffOn_invFun.comp hTsm.contMDiffOn
      (fun q _ => htarget q))
  have hgsm : ContMDiff (𝓡 n) (𝓡 n) ∞ g := by
    have hcomp : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ)) ∞
        (fun q : Metric.sphere (0 : E) 1 => T.symm (A q)) :=
      contMDiffOn_univ.mp (T.contMDiffOn_invFun.comp hAsm.contMDiffOn
        (fun q _ => hTtarget q))
    exact hcomp.fst
  let e : Metric.sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : E) 1 := {
    toFun := f
    invFun := g
    left_inv := fun q => by
      change (T.symm (A (f q))).1 = q
      rw [hf]
      exact congrArg Prod.fst (T.left_inv' (hT q))
    right_inv := fun q => by
      apply Subtype.ext
      change A.symm (T (g q, 0)) = q.val
      rw [hg]
      exact A.left_inv' (hA q.property)
    contMDiff_toFun := hfsm
    contMDiff_invFun := hgsm }
  exact ⟨e, hf, hg⟩

end DifferentialGeometry.Topology.Manifold
