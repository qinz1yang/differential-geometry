import DifferentialGeometry.Topology.PiecewiseLinear.FiniteGraphCircles

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem tsum_lt_tsum_enat_of_embedding
    {α β : Type*} [Finite α] [Finite β] (f : α → ℕ∞) (g : β → ℕ∞)
    (e : α ↪ β) (hf : ∀ a, f a ≠ ⊤) (hg : ∀ b, g b ≠ ⊤)
    (hle : ∀ a, f a ≤ g (e a))
    (hstrict : (∃ a, f a < g (e a)) ∨ ∃ b, b ∉ Set.range e ∧ 0 < g b) :
    ∑' a, f a < ∑' b, g b := by
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  let F : α → ℕ := fun a => (f a).toNat
  let G : β → ℕ := fun b => (g b).toNat
  have hleNat : ∀ a, F a ≤ G (e a) := by
    intro a
    exact ENat.toNat_le_toNat (hle a) (hg (e a))
  have hsumImage : ∑ b ∈ Finset.univ.image e, G b = ∑ a, G (e a) := by
    exact Finset.sum_image e.injective.injOn
  have hNat : ∑ a, F a < ∑ b, G b := by
    rcases hstrict with ⟨a, ha⟩ | ⟨b, hb, hbpos⟩
    · have haNat : F a < G (e a) := by
        rw [← ENat.natCast_lt_natCast]
        rwa [ENat.natCast_toNat (hf a), ENat.natCast_toNat (hg (e a))]
      have hlt : ∑ a, F a < ∑ a, G (e a) :=
        Finset.sum_lt_sum (fun a _ => hleNat a)
          ⟨a, Finset.mem_univ a, haNat⟩
      apply hlt.trans_le
      rw [← hsumImage]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    · have hbnot : b ∉ Finset.univ.image e := by
        intro hmem
        obtain ⟨a, -, hab⟩ := Finset.mem_image.mp hmem
        exact hb ⟨a, hab⟩
      have hbposNat : 0 < G b := by
        apply ENat.natCast_lt_natCast.mp
        rw [Nat.cast_zero, ENat.natCast_toNat (hg b)]
        exact hbpos
      have hleSum : ∑ a, F a ≤ ∑ a, G (e a) :=
        Finset.sum_le_sum fun a _ => hleNat a
      apply hleSum.trans_lt
      rw [← hsumImage]
      exact Finset.sum_lt_sum_of_subset (Finset.subset_univ _)
        (Finset.mem_univ b) hbnot hbposNat (fun _ _ _ => Nat.zero_le _)
  have hsumf : ∑' a, f a = (↑(∑ a, F a) : ℕ∞) := by
    rw [tsum_fintype, Nat.cast_sum]
    exact Finset.sum_congr rfl fun a _ => (ENat.natCast_toNat (hf a)).symm
  have hsumg : ∑' b, g b = (↑(∑ b, G b) : ℕ∞) := by
    rw [tsum_fintype, Nat.cast_sum]
    exact Finset.sum_congr rfl fun b _ => (ENat.natCast_toNat (hg b)).symm
  rw [hsumf, hsumg, ENat.natCast_lt_natCast]
  exact hNat

theorem heightIndex_lt_of_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsPLSphere 2 K.space) (hR : IsPLSphere 2 R.space)
    (hdimE : Module.finrank ℝ E = 3)
    (ℓ f : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hf : f ≠ 0)
    (hinj : InjOn ℓ K.vertices) (hfinj : InjOn f R.vertices)
    (e : heightSingularPoints R.space f ↪ heightSingularPoints K.space ℓ)
    (hle : ∀ q : heightSingularPoints R.space f,
      (levelPolygons R.space f (f q)).encard - 1 ≤
        (levelPolygons K.space ℓ (ℓ (e q))).encard - 1)
    (hstrict :
      (∃ q : heightSingularPoints R.space f,
        (levelPolygons R.space f (f q)).encard - 1 <
        (levelPolygons K.space ℓ (ℓ (e q))).encard - 1) ∨
      ∃ q : heightSingularPoints K.space ℓ, q ∉ Set.range e ∧
        0 < (levelPolygons K.space ℓ (ℓ q)).encard - 1) :
    heightIndex R.space f < heightIndex K.space ℓ := by
  have hℓlin : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hflin : f.toLinearMap ≠ 0 := by
    intro hz
    apply hf
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  let _ : Finite (heightSingularPoints R.space f) :=
    (finite_heightSingularPoints R
      hR.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE f.toLinearMap hflin hfinj).to_subtype
  let _ : Finite (heightSingularPoints K.space ℓ) :=
    (finite_heightSingularPoints K
      hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE ℓ.toLinearMap hℓlin hinj).to_subtype
  apply tsum_lt_tsum_enat_of_embedding
    (fun q : heightSingularPoints R.space f =>
      (levelPolygons R.space f (f q)).encard - 1)
    (fun q : heightSingularPoints K.space ℓ =>
      (levelPolygons K.space ℓ (ℓ q)).encard - 1) e
  · intro q
    exact (lt_of_le_of_lt tsub_le_self
      (finite_levelPolygons R
        (fun s hs => hR.isCombinatorialManifold.card_le R hs)
        hdimE f.toLinearMap hflin hfinj (f q)).encard_lt_top).ne
  · intro q
    exact (lt_of_le_of_lt tsub_le_self
      (finite_levelPolygons K
        (fun s hs => hK.isCombinatorialManifold.card_le K hs)
        hdimE ℓ.toLinearMap hℓlin hinj (ℓ q)).encard_lt_top).ne
  · exact hle
  · exact hstrict

end DifferentialGeometry.Topology.PiecewiseLinear
