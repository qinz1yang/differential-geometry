import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary

/-!
Compact cut pieces with actual spherical and toroidal signed seams and retained boundary collars.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

structure MixedCutSystem (W : CompactCarrier.{u}) (k : CarrierModel) where
  count : ℕ
  count_pos : 0 < count
  Piece : Fin count → Type u
  [topology : ∀ i, TopologicalSpace (Piece i)]
  [charts : ∀ i, ChartedSpace k.Space (Piece i)]
  [smooth : ∀ i, IsManifold k.model ∞ (Piece i)]
  [compact : ∀ i, CompactSpace (Piece i)]
  [hausdorff : ∀ i, T2Space (Piece i)]
  [secondCountable : ∀ i, SecondCountableTopology (Piece i)]
  [connected : ∀ i, ConnectedSpace (Piece i)]
  map : ∀ i, Piece i → W.Carrier
  map_smooth : ∀ i, ContMDiff k.model W.model ∞ (map i)
  map_mfderiv_bijective : ∀ i x, Bijective (mfderiv k.model W.model (map i) x)
  covers : ⋃ i, range (map i) = univ
  torusCount : Fin count → ℕ
  sphereCount : Fin count → ℕ
  torusCollar : ∀ i, Fin (torusCount i) → PartialDiffeomorph halfCollarModel k.model
    (Torus × EuclideanHalfSpace 1) (Piece i) ∞
  sphereCollar : ∀ i, Fin (sphereCount i) → PartialDiffeomorph sphereHalfCollarModel k.model
    (ClosureSphere.{u} × EuclideanHalfSpace 1) (Piece i) ∞
  torus_source : ∀ i a, (torusCollar i a).source = halfCollarSource
  sphere_source : ∀ i a, (sphereCollar i a).source = sphereHalfCollarSource
  torus_disjoint : ∀ i, Pairwise fun a b =>
    Disjoint (torusCollar i a).target (torusCollar i b).target
  sphere_disjoint : ∀ i, Pairwise fun a b =>
    Disjoint (sphereCollar i a).target (sphereCollar i b).target
  cross_disjoint : ∀ i a b, Disjoint (torusCollar i a).target (sphereCollar i b).target
  piece_boundary : ∀ i, k.model.boundary (Piece i) =
    (⋃ a, range fun t => torusCollar i a (t, halfZero)) ∪
      ⋃ a, range fun z => sphereCollar i a (z, halfZero)
  torusSeamCount : ℕ
  sphereSeamCount : ℕ
  torusSide : Fin torusSeamCount → Bool → Σ i, Fin (torusCount i)
  sphereSide : Fin sphereSeamCount → Bool → Σ i, Fin (sphereCount i)
  external : MixedBoundaryCertificate W
  torusExternalSide : Fin external.torusCount → Σ i, Fin (torusCount i)
  sphereExternalSide : Fin external.sphereCount → Σ i, Fin (sphereCount i)
  torus_sides_bijective : Bijective (Sum.elim (Function.uncurry torusSide) torusExternalSide)
  sphere_sides_bijective : Bijective (Sum.elim (Function.uncurry sphereSide) sphereExternalSide)
  torusMatching : Fin torusSeamCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  sphereMatching : Fin sphereSeamCount → (ClosureSphere.{u} ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u})
  torusSeam : Fin torusSeamCount → PartialDiffeomorph signedCollarModel W.model
    (Torus × ℝ) W.Carrier ∞
  sphereSeam : Fin sphereSeamCount → PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞
  torus_seam_source : ∀ a, (torusSeam a).source = signedCollarSource
  sphere_seam_source : ∀ a, (sphereSeam a).source = sphereSignedCollarSource
  torus_neg : ∀ a t s (hs : s ≤ 0), -1 < s → torusSeam a (t, s) =
    map (torusSide a true).1
      (torusCollar _ (torusSide a true).2 (t, halfPoint (-s) (neg_nonneg.2 hs)))
  torus_pos : ∀ a t s (hs : 0 ≤ s), s < 1 → torusSeam a (t, s) =
    map (torusSide a false).1
      (torusCollar _ (torusSide a false).2 (torusMatching a t, halfPoint s hs))
  sphere_neg : ∀ a z s (hs : s ≤ 0), -1 < s → sphereSeam a (z, s) =
    map (sphereSide a true).1
      (sphereCollar _ (sphereSide a true).2 (z, halfPoint (-s) (neg_nonneg.2 hs)))
  sphere_pos : ∀ a z s (hs : 0 ≤ s), s < 1 → sphereSeam a (z, s) =
    map (sphereSide a false).1
      (sphereCollar _ (sphereSide a false).2 (sphereMatching a z, halfPoint s hs))
  torus_seam_interior : ∀ a, (torusSeam a).target ⊆ W.interior
  sphere_seam_interior : ∀ a, (sphereSeam a).target ⊆ W.interior
  torus_seam_disjoint : Pairwise fun a b => Disjoint (torusSeam a).target (torusSeam b).target
  sphere_seam_disjoint : Pairwise fun a b => Disjoint (sphereSeam a).target (sphereSeam b).target
  seam_cross_disjoint : ∀ a b, Disjoint (torusSeam a).target (sphereSeam b).target
  torus_external : ∀ a p, p ∈ halfCollarSource →
    map (torusExternalSide a).1 (torusCollar _ (torusExternalSide a).2 p) =
      external.tori.collar a p
  sphere_external : ∀ a p, p ∈ sphereHalfCollarSource →
    map (sphereExternalSide a).1 (sphereCollar _ (sphereExternalSide a).2 p) =
      external.sphere a p
  overlap : ∀ i j x y, map i x = map j y →
    (⟨i, x⟩ : Σ i, Piece i) = ⟨j, y⟩ ∨
      (∃ a t, map i x = torusSeam a (t, 0)) ∨ ∃ a z, map i x = sphereSeam a (z, 0)

attribute [instance] MixedCutSystem.topology MixedCutSystem.charts MixedCutSystem.smooth
  MixedCutSystem.compact MixedCutSystem.hausdorff MixedCutSystem.secondCountable
  MixedCutSystem.connected

namespace MixedCutSystem

variable {W : CompactCarrier.{u}} {k : CarrierModel} (S : MixedCutSystem W k)

abbrev Cut : Type u := Σ i, S.Piece i

def fold (x : S.Cut) : W.Carrier := S.map x.1 x.2

theorem fold_surjective : Surjective S.fold := by
  intro y
  have hy : y ∈ ⋃ i, range (S.map i) := S.covers ▸ mem_univ y
  obtain ⟨i, x, hx⟩ := mem_iUnion.mp hy
  exact ⟨⟨i, x⟩, hx⟩

theorem fold_smooth : ContMDiff k.model W.model ∞ S.fold :=
  contMDiff_sigma S.map_smooth

theorem fold_mfderiv_bijective (x : S.Cut) :
    Bijective (mfderiv k.model W.model S.fold x) := by
  obtain ⟨i, x⟩ := x
  exact mfderiv_sigma_bijective (S.fold_smooth.mdifferentiableAt (by simp))
    (S.map_mfderiv_bijective i x)

def cutOrientation : ManifoldOrientation k.model S.Cut 3 :=
  Manifold.manifoldOrientationPullback k.model W.model finrank_euclideanSpace_fin S.fold
    S.fold_smooth S.fold_mfderiv_bijective W.orientation

end MixedCutSystem

end GC.GraphManifold
