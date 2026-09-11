import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Sets.Opens

noncomputable section
open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_oriented_product_chart
    {E F H G N M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace N] [ChartedSpace H N]
    [TopologicalSpace M] [ChartedSpace G M]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮I.prod 𝓘(ℝ), J⟯ V) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ U : TopologicalSpace.Opens (N × ℝ),
      ∃ hU : ∀ x : N × ℝ, x ∈ U ↔ (x.1, σ * x.2) ∈ O,
      ∃ Ψ : U ≃ₘ⟮I.prod 𝓘(ℝ), J⟯ V,
        (∀ x : U, Ψ x = Φ ⟨((x : N × ℝ).1, σ * (x : N × ℝ).2), (hU x).mp x.property⟩) ∧
        ∀ y : V, (Ψ.symm y : N × ℝ) =
          (((Φ.symm y : O) : N × ℝ).1, σ * ((Φ.symm y : O) : N × ℝ).2) := by
  let flip : N × ℝ → N × ℝ := fun x ↦ (x.1, σ * x.2)
  have hsquare : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hflip (x : N × ℝ) : flip (flip x) = x := by
    change (x.1, σ * (σ * x.2)) = x
    rw [← mul_assoc, hsquare, one_mul]
  have hcont : Continuous flip := continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hsmooth : ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞ flip :=
    contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)
  let U := TopologicalSpace.Opens.comap ⟨flip, hcont⟩ O
  have hU (x : N × ℝ) : x ∈ U ↔ (x.1, σ * x.2) ∈ O := Iff.rfl
  let e : U ≃ O :=
    { toFun := fun x ↦ ⟨flip x, x.property⟩
      invFun := fun y ↦ ⟨flip y, by
        change flip (flip (y : N × ℝ)) ∈ O
        rw [hflip]
        exact y.property⟩
      left_inv := fun x ↦ Subtype.ext (hflip x)
      right_inv := fun y ↦ Subtype.ext (hflip y) }
  let d : U ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ O :=
    { toEquiv := e
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff O e).mp
        change ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
          (flip ∘ (Subtype.val : U → N × ℝ))
        exact hsmooth.comp contMDiff_subtype_val
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff U e.symm).mp
        change ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
          (flip ∘ (Subtype.val : O → N × ℝ))
        exact hsmooth.comp contMDiff_subtype_val }
  exact ⟨U, hU, d.trans Φ, fun _ ↦ rfl, fun _ ↦ rfl⟩

end DifferentialGeometry.Topology.Manifold
