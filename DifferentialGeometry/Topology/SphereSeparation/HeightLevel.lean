import DifferentialGeometry.Topology.SphereSeparation.HeightTangent
import DifferentialGeometry.Topology.Manifold.RegularLevel.Tangent
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.CircleComponents

open Set Manifold
open scoped ContDiff
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_height_level_manifold {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (a : ℝ)
    (hr : ∀ x, e x 2 = a →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ C : ChartedSpace (MorseModel 1) {x : SphereTwo // e x 2 = a},
      let _ := C
      ∃ S : IsManifold 𝓘(ℝ, MorseModel 1) ∞ {x : SphereTwo // e x 2 = a},
        let _ := S
        IsSmoothEmbedding 𝓘(ℝ, MorseModel 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
          (Subtype.val : {x : SphereTwo // e x 2 = a} → SphereTwo) ∧
        ∃ W : (x : {y : SphereTwo // e y 2 = a}) → TangentSpace 𝓘(ℝ, MorseModel 1) x,
          ContMDiff 𝓘(ℝ, MorseModel 1) (𝓘(ℝ, MorseModel 1)).tangent ∞
            (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, MorseModel 1)
              {y : SphereTwo // e y 2 = a})) ∧
          ∀ x, W x ≠ 0 := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
  let J := I.transContinuousLinearEquiv (EuclideanSpace.equiv (Fin 2) ℝ)
  let f : SphereTwo → ℝ := fun y => e y 2
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hf' : ContMDiff J 𝓘(ℝ, ℝ) ∞ f := by simpa [J] using hf
  let D : SphereTwo ≃ₘ⟮I, J⟯ SphereTwo :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv I SphereTwo (EuclideanSpace.equiv (Fin 2) ℝ)
  have hdf (x : SphereTwo) : mfderiv I 𝓘(ℝ, ℝ) f x =
      (mfderiv J 𝓘(ℝ, ℝ) f x).comp (mfderiv I J D x) :=
    mfderiv_comp x (hf'.mdifferentiableAt (by simp)) (D.contMDiff.mdifferentiableAt (by simp))
  have hr' (x : SphereTwo) (hx : f x = a) : mfderiv J 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro hz
    apply hr x hx
    change mfderiv I 𝓘(ℝ, ℝ) f x = 0
    rw [hdf, hz]
    rfl
  obtain ⟨V, hV, _, hker, hne⟩ := exists_contMDiff_embeddedSphere_height_tangent_field he
  let V' : (x : SphereTwo) → TangentSpace J x := fun x => mfderiv I J D x (V x)
  have hV' : ContMDiff J J.tangent ∞ (fun x => (⟨x, V' x⟩ : TangentBundle J SphereTwo)) :=
    ((D.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hV).comp D.symm.contMDiff
  have hker' (x : SphereTwo) : mfderiv J 𝓘(ℝ, ℝ) f x (V' x) = 0 := by
    change (mfderiv J 𝓘(ℝ, ℝ) f x).comp (mfderiv I J D x) (V x) = 0
    rw [← hdf]
    exact hker x
  have hne' (x : SphereTwo) (hx : f x = a) : V' x ≠ 0 := by
    let A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] MorseModel 2 :=
      (D.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)
    intro hz
    apply hne x (hr x hx)
    exact A.injective (hz.trans (map_zero A).symm)
  let C := DifferentialGeometry.Manifold.RegularLevel.levelChartedSpace J hf' hr'
  let _ := C
  let S := DifferentialGeometry.Manifold.RegularLevel.levelIsManifold J hf' hr'
  let _ := S
  have hinc :=
    DifferentialGeometry.Manifold.RegularLevel.isSmoothEmbedding_level_inclusion J hf' hr'
  have hD :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D.symm.isLocalDiffeomorph D.symm.injective
  have hinc' : IsSmoothEmbedding 𝓘(ℝ, MorseModel 1) I ∞
      (Subtype.val : {x : SphereTwo // f x = a} → SphereTwo) :=
    hD.comp hinc (by simp)
  obtain ⟨W, hW, hpush⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_contMDiff_tangent_field J hf' hr' V' hV'
      (fun x _ => hker' x)
  refine ⟨C, S, hinc', W, hW, ?_⟩
  intro x hz
  apply hne' x.val x.property
  rw [← hpush, hz, map_zero]

theorem exists_source_height_level_circles {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (a : ℝ)
    (hr : ∀ x, e x 2 = a →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    Finite (ConnectedComponents {x : SphereTwo // e x 2 = a}) ∧
      ∃ γ : ConnectedComponents {x : SphereTwo // e x 2 = a} → AddCircle (1 : ℝ) → SphereTwo,
        (∀ C, IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ (γ C)) ∧
        Pairwise (fun C D => Disjoint (range (γ C)) (range (γ D))) ∧
        (⋃ C, range (γ C)) = {x | e x 2 = a} := by
  obtain ⟨C, S, hinc, V, hV, hne⟩ := exists_height_level_manifold he a hr
  let _ := C
  let _ := S
  let L := {x : SphereTwo // e x 2 = a}
  have hf : Continuous (fun x : SphereTwo => e x 2) :=
    (EuclideanSpace.proj 2).continuous.comp he.contMDiff.continuous
  let : CompactSpace L := isCompact_iff_compactSpace.mp (isClosed_eq hf continuous_const).isCompact
  obtain ⟨hfinite, γ, hγ, hrange⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_circle_embeddings_components
      (I := 𝓘(ℝ, MorseModel 1)) (by simp [MorseModel]) V hV hne
  let j : L → SphereTwo := Subtype.val
  have hj : IsSmoothEmbedding 𝓘(ℝ, MorseModel 1) (𝓡 2) ∞ j := hinc
  refine ⟨hfinite, fun k => j ∘ γ k, fun k => hj.comp (hγ k) (by simp), ?_, ?_⟩
  · intro k l hkl
    rw [disjoint_left]
    rintro z ⟨u, hu⟩ ⟨v, hv⟩
    have heq : γ k u = γ l v := hj.isEmbedding.injective (hu.trans hv.symm)
    have hk : ConnectedComponents.mk (γ k u) = k := by
      have h := (hrange k).subset (mem_range_self u)
      exact h
    have hl : ConnectedComponents.mk (γ l v) = l := by
      have h := (hrange l).subset (mem_range_self v)
      exact h
    exact hkl (hk.symm.trans ((congrArg ConnectedComponents.mk heq).trans hl))
  · ext z
    constructor
    · intro hz
      obtain ⟨k, u, rfl⟩ := mem_iUnion.mp hz
      exact (γ k u).property
    · intro hx
      let y : L := ⟨z, hx⟩
      have hy : y ∈ range (γ (ConnectedComponents.mk y)) :=
        (hrange _).symm.subset rfl
      obtain ⟨t, ht⟩ := hy
      apply mem_iUnion.mpr
      exact ⟨ConnectedComponents.mk y, t, congrArg j ht⟩

theorem exists_height_level_circles {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    (a : ℝ)
    (hr : ∀ x, e x 2 = a →
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    Finite (ConnectedComponents {x : SphereTwo // e x 2 = a}) ∧
      ∃ γ : ConnectedComponents {x : SphereTwo // e x 2 = a} → AddCircle (1 : ℝ) → EuclideanThree,
        (∀ C, IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanThree) ∞ (γ C)) ∧
        Pairwise (fun C D => Disjoint (range (γ C)) (range (γ D))) ∧
        (⋃ C, range (γ C)) = range e ∩ {z | z 2 = a} := by
  obtain ⟨hfinite, η, hη, hdisj, hcover⟩ := exists_source_height_level_circles he a hr
  refine ⟨hfinite, fun C => e ∘ η C, fun C => he.comp (hη C) (by simp), ?_, ?_⟩
  · intro C D hCD
    simpa only [range_comp] using (hdisj hCD).image he.isEmbedding.injective.injOn
      (subset_univ _) (subset_univ _)
  · simp only [range_comp]
    rw [← image_iUnion]
    change e '' (⋃ C, range (η C)) = _
    rw [hcover]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_range_self x, hx⟩
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, hx, rfl⟩

end DifferentialGeometry.Topology.SphereSeparation
