/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndexReduction
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_of_heightIndex_zero_case (I : SchoenfliesInput)
    (hzero : ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      Finite K.faces → IsPLSphere 2 K.space →
      ∀ ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, ℓ ≠ 0 → InjOn ℓ K.vertices →
        heightIndex K.space ℓ = 0 → IsSimplyEmbedded K.space)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S) : IsSimplyEmbedded S := by
  classical
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hrec : ∀ n : ℕ, ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      Finite K.faces → IsPLSphere 2 K.space →
      ∀ ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ, ℓ ≠ 0 → InjOn ℓ K.vertices →
        heightIndex K.space ℓ = n → IsSimplyEmbedded K.space := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hKfin hK ℓ hℓ hinj hindex
      let _ : Finite K.faces := hKfin
      by_cases hz : heightIndex K.space ℓ = 0
      · exact hzero K hKfin hK ℓ hℓ hinj hz
      have hpos : 0 < heightIndex K.space ℓ := lt_of_le_of_ne zero_le (Ne.symm hz)
      refine ⟨hK, ?_⟩
      intro W hWconv hW hKW
      obtain ⟨R₁, R₂, H, f₁, f₂, D, u, r, hR₁fin, hR₂fin, hR₁, hR₂, hf₁ne, hf₂ne,
        hf₁inj, hf₂inj, hlt₁, hlt₂, hH, hfixW, hHKW, hu, hDlevel, hinter, hrecover⟩ :=
        exists_cap_pair_heightIndex_lt_of_pos K hK hdim ℓ hℓ hinj hpos hW hWconv hKW
      let _ : Finite R₁.faces := hR₁fin.to_subtype
      let _ : Finite R₂.faces := hR₂fin.to_subtype
      have hf₁linear : f₁.toLinearMap ≠ 0 := by
        intro h
        apply hf₁ne
        ext x
        exact congrArg (fun a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => a x) h
      have hf₂linear : f₂.toLinearMap ≠ 0 := by
        intro h
        apply hf₂ne
        ext x
        exact congrArg (fun a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => a x) h
      have hcast₁ : ((heightIndex R₁.space f₁).toNat : ℕ∞) = heightIndex R₁.space f₁ :=
        natCast_toNat_heightIndex R₁ hR₁.isCombinatorialManifold hdim
        f₁.toLinearMap hf₁linear hf₁inj
      have hcast₂ : ((heightIndex R₂.space f₂).toNat : ℕ∞) = heightIndex R₂.space f₂ :=
        natCast_toNat_heightIndex R₂ hR₂.isCombinatorialManifold hdim
        f₂.toLinearMap hf₂linear hf₂inj
      have hnat₁ : (heightIndex R₁.space f₁).toNat < n := by
        rw [← ENat.natCast_lt_natCast, hcast₁, ← hindex]
        exact hlt₁
      have hnat₂ : (heightIndex R₂.space f₂).toNat < n := by
        rw [← ENat.natCast_lt_natCast, hcast₂, ← hindex]
        exact hlt₂
      have hsimple₁ := ih _ hnat₁ R₁ inferInstance hR₁ f₁ hf₁ne hf₁inj hcast₁.symm
      have hsimple₂ := ih _ hnat₂ R₂ inferInstance hR₂ f₂ hf₂ne hf₂inj hcast₂.symm
      have hlinear : ℓ.toLinearMap ≠ 0 := by
        intro h
        apply hℓ
        ext x
        exact congrArg (fun a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => a x) h
      have hsimple := I.isSimplyEmbedded_union_sdiff_diskInterior R₁.space R₂.space D u
        ℓ.toLinearMap r hsimple₁ hsimple₂ hu hlinear hDlevel hinter
      rw [hrecover] at hsimple
      obtain ⟨T, G, hT, hcard, hG, hGS, hGfix⟩ := hsimple.2 W hWconv hW hHKW
      refine ⟨T, H.trans G, hT, hcard, hH.trans hG, ?_, ?_⟩
      · change (G ∘ H) '' K.space = _
        rwa [image_comp]
      · intro x hx
        change G (H x) = x
        rw [hfixW hx]
        exact hGfix hx
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLSphere 2 K.space := hKS.symm ▸ hS
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hKfin
  obtain ⟨ℓ, -, hℓ, hinj⟩ := exists_continuousLinearMap_ne_zero_injOn hvertices 0
    (show (0 : ℝ) < 1 by norm_num)
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => a x) h
  have hcast := natCast_toNat_heightIndex K hK.isCombinatorialManifold hdim
    ℓ.toLinearMap hlinear hinj
  rw [← hKS]
  exact hrec _ K inferInstance hK ℓ hℓ hinj hcast.symm

end DifferentialGeometry.Topology.PiecewiseLinear
