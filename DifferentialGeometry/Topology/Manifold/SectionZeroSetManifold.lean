import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionSurjectivity
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionZeroEquivalence
import DifferentialGeometry.Topology.Manifold.LocalZeroSetManifold
import DifferentialGeometry.Topology.Maps.RelativeZeroSet
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional


set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Manifold
namespace DifferentialGeometry.Topology.Manifold
universe u v

theorem exists_section_zero_set_manifold_of_open_cover
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {ι : Type v}
    (k : ℕ) (U : ι → Set H) (hU : ∀ i, IsOpen (U i))
    (L : ι → Submodule ℝ H) (hL : ∀ i, Module.finrank ℝ (L i) = k)
    (o : ι → H) (η : H → H) (Q : H → Submodule ℝ H)
    (hη : ContDiffOn ℝ ∞ η (⋃ i, U i))
    (hmem : ∀ i, ∀ z ∈ U i, η z ∈ Q z)
    (hgap : ∀ i, ∀ z ∈ U i, ‖(Q z).starProjection - (L i)ᗮ.starProjection‖ < 1)
    (herror : ∀ i, ∀ z ∈ U i,
      ‖fderiv ℝ (fun y => η y - (L i)ᗮ.starProjection (y - o i)) z‖ < 1) :
    let Ω : Set H := ⋃ i, U i
    let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
    IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : Ω)) ∧
      ∃ cs : ChartedSpace (Fin k → ℝ) Z,
        let _ := cs
        IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
          (Subtype.val : Z → H) := by
  classical
  let Ω : Set H := ⋃ i, U i
  let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
  refine ⟨DifferentialGeometry.Topology.isProperMap_relativeZeroSetInclusion
    Ω η hη.continuousOn, ?_⟩
  have hcover (x : Z) : ∃ i, (x : H) ∈ U i := mem_iUnion.mp x.property.1
  choose i hi using hcover
  let F : Z → Type u := fun x => (L (i x))ᗮ
  let V : Z → Set H := fun x => U (i x)
  let f : ∀ x : Z, H → F x := fun x y => (L (i x))ᗮ.orthogonalProjectionOnto (η y)
  let n : ℕ := Module.finrank ℝ H - k
  have hsum (x : Z) : k + Module.finrank ℝ (F x) = Module.finrank ℝ H := by
    have hh := (L (i x)).finrank_add_finrank_orthogonal
    rwa [hL (i x)] at hh
  have hF (x : Z) : Module.finrank ℝ (F x) = n := by
    have hh := hsum x
    dsimp [n]
    omega
  have hdim (x : Z) : Module.finrank ℝ H = n + k := by
    have hh := hsum x
    rw [hF x] at hh
    omega
  have hVΩ (x : Z) : V x ⊆ Ω := fun _ hy => mem_iUnion.mpr ⟨i x, hy⟩
  have hηlocal (x : Z) : ContDiffOn ℝ ∞ η (V x) := hη.mono (hVΩ x)
  have hf (x : Z) : ContDiffOn ℝ ∞ (f x) (V x) :=
    (L (i x))ᗮ.orthogonalProjectionOnto.contDiff.comp_contDiffOn (hηlocal x)
  have hsurj (x : Z) : Function.Surjective (fderiv ℝ (f x) (x : H)) := by
    exact Submodule.surjective_fderiv_orthogonalProjectionOnto_of_error
      (L (i x))ᗮ η (o (i x)) x
      (((hηlocal x).contDiffAt ((hU (i x)).mem_nhds (hi x))).differentiableAt
        (by simp)) (herror (i x) x (hi x))
  have hzero (x : Z) (y : H) (hy : y ∈ V x) : y ∈ Z ↔ f x y = 0 := by
    have heq := Submodule.orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
      (L (i x))ᗮ (Q y) (hgap (i x) y hy) (hmem (i x) y hy)
    change (y ∈ Ω ∧ η y = 0) ↔ f x y = 0
    simpa only [hVΩ x hy, true_and] using heq.symm
  exact exists_local_zero_set_manifold Z n k hdim F hF V
    (fun x => hU (i x)) hi f hf hsurj hzero

end DifferentialGeometry.Topology.Manifold
