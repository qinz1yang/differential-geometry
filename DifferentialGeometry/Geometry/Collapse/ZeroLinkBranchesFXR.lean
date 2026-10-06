import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainZeroExit74
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ZeroDomainsOfExits74Consumer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# D78-5, five-branch zero-link check on NON-CLOSED actual selected cores

Lane S-FIX-REG (suffix `_FXR`), G1. `ClosedChainEZRowsSource_RGC.zsp02SmoothExit74` assembles the
zero table from selected cores whichever of the five LFR54 branches they are of
(`SelectedSmoothCore74`: `ball`, `solidTorus`, `twistedIBundle`, `puncturedRP3`, `closed`), through
`zeroDomainsOfExits74` and `zeroLink_of_exits74`. The tree held ONE non-closed inhabitant of
`SelectedSmoothCore74` (the S³ outer ball, `sphereOuterCore74`). This file adds, on actual
three-manifolds:

* `zeroLink_oneCore_FXR`: the one-piece kernel (a selected core of `A`, a regular defining function
  `F` with `{F ≤ 0} = A`, `{F = 0} = frontier A`, a carrier identification `e` of a closed carrier)
  yields the zero table `ZeroDomains` with its `ZeroLink_LND74` (ranges, boundaries, interior
  pieces, global ratio `F ∘ e⁻¹`) and the model of the branch of the core;
* the BALL branch: the S³ outer ball (`sphereOuterCore74`, F = `3/5 − q₀`);
* the SOLID TORUS branch: the Heegaard solid torus `{cliffordHeight ≤ 0} ⊂ S³`
  (`solidTorusCore74_FXR`, F = `cliffordHeight`);
* the TWISTED I-BUNDLE branch: the Möbius bundle `{Q ≤ 0} ⊂ mobiusLens` (`mobiusCore74_FXR`,
  F = `mobiusBundleFunction`).

Each instance has model `.inl (<branch> e)` (non-closed). The branch `puncturedRP3` has NO
inhabitant in the tree (it needs a compact `ℝP³ ∖ open ball` with a smooth boundary atlas and an
`OrientedBallChart` of `ℝP³`); the closed branch is inhabited on the dihedral source
(`dihedralTiny_selectedCore74_CHI`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

attribute [local instance] secondCountableTopology_sphereCarrier

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold (𝓡 3) ∞ X] [T2Space X]
  {W : CompactCarrier.{0}} {A : Set X}

/-- **The one-piece zero table** of a selected core `Q` of `A`, a regular smooth defining function
`F` of `A` and an identification `e` with a closed carrier (`zeroDomainsOfExits74` on a one-element
family, `Ψ = id`, buffer `univ`). -/
def oneCoreZero_FXR (Q : SelectedSmoothCore74.{0, 0} A) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) (F : X → ℝ) (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (hFr : ∀ x, F x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F x ≠ 0) (hle : {x | F x ≤ 0} = A)
    (hfr : {x | F x = 0} = frontier A) : ZeroDomains W :=
  zeroDomainsOfExits74 (ι := Unit) (A := fun _ => A) e hW (fun _ => Q)
    (fun _ => Diffeomorph.refl (𝓡 3) X ∞) (fun _ => A) (fun _ => univ) (fun _ => F)
    (fun _ => Set.image_id _) (fun _ _ h => absurd (Subsingleton.elim _ _) h)
    (fun _ => isOpen_univ) (fun _ => hFs) (fun _ => hFr) (fun _ => hle) (fun _ => hfr)
    (fun _ _ _ => trivial)

/-- The one-piece table has ONE piece. -/
theorem oneCoreZero_count_FXR (Q : SelectedSmoothCore74.{0, 0} A)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅) (F : X → ℝ)
    (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F) (hFr : ∀ x, F x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F x ≠ 0)
    (hle : {x | F x ≤ 0} = A) (hfr : {x | F x = 0} = frontier A) :
    (oneCoreZero_FXR Q e hW F hFs hFr hle hfr).count = 1 :=
  rfl

/-- Its model is the branch of the selected core (`Q.model` along `Ψ = id`). -/
theorem oneCoreZero_model_FXR (Q : SelectedSmoothCore74.{0, 0} A)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅) (F : X → ℝ)
    (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F) (hFr : ∀ x, F x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F x ≠ 0)
    (hle : {x | F x ≤ 0} = A) (hfr : {x | F x = 0} = frontier A)
    (j : Fin (oneCoreZero_FXR Q e hW F hFs hFr hle hfr).count) :
    (oneCoreZero_FXR Q e hW F hFs hFr hle hfr).model j =
      Q.model (Diffeomorph.refl (𝓡 3) X ∞) e :=
  rfl

/-- **The one-piece zero link** (kernel): the table of `oneCoreZero_FXR` satisfies
`ZeroLink_LND74` (interior pieces `interior A`, outer `A`, ratio `F ∘ e⁻¹`). -/
theorem zeroLink_oneCore_FXR (Q : SelectedSmoothCore74.{0, 0} A)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅) (F : X → ℝ)
    (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F) (hFr : ∀ x, F x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) F x ≠ 0)
    (hle : {x | F x ≤ 0} = A) (hfr : {x | F x = 0} = frontier A) :
    ZeroLink_LND74 e.toEquiv (oneCoreZero_FXR Q e hW F hFs hFr hle hfr) (fun _ : Unit => A)
      (fun _ => interior A) (fun _ => A) (fun _ => F) := by
  refine zeroLink_of_exits74 e.toEquiv (oneCoreZero_FXR Q e hW F hFs hFr hle hfr)
    (fun _ : Unit => A) (fun _ => interior A) (fun _ => A) (fun _ => F) (idx74 Unit)
    (fun _ => F) (fun _ => univ) ?_ ?_ ?_ ?_ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => isOpen_univ) (fun _ => subset_univ _) (fun _ _ _ => rfl)
  · exact fun i => zeroDomainsOfExits74_range (ι := Unit) (A := fun _ => A) e hW (fun _ => Q)
      (fun _ => Diffeomorph.refl (𝓡 3) X ∞) (fun _ => A) (fun _ => univ) (fun _ => F)
      (fun _ => Set.image_id _) (fun _ _ h => absurd (Subsingleton.elim _ _) h)
      (fun _ => isOpen_univ) (fun _ => hFs) (fun _ => hFr) (fun _ => hle) (fun _ => hfr)
      (fun _ _ _ => trivial) i
  · intro i
    refine (oneCoreZero_FXR Q e hW F hFs hFr hle hfr).boundary_eq i |>.trans ?_
    exact (preimage_symm_R74 e F {0}).trans (congrArg (fun B => e '' B) hfr)
  · exact fun i => (e.toHomeomorph.image_interior A).subset
  · exact fun i => subset_rfl

end Generic

/-! ## The BALL branch: the S³ outer ball -/

section Ball

/-- **Ball branch**: the zero link of the S³ outer ball (`sphereOuterCore74`, `F = 3/5 − q₀`). -/
theorem sphereOuter_zeroLink_FXR :
    ZeroLink_LND74 sphereId74.toEquiv
      (oneCoreZero_FXR (W := sphereW) sphereOuterCore74 sphereId74
        (closedCarrier_boundary_eq_empty _) (sphereZeroRatio 1) (sphereZeroRatio_smooth 1)
        (fun x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
        (sphereZeroPiece_range 1).symm sphereOuter_frontier74)
      (fun _ : Unit => range (cycleBallPiece true).map)
      (fun _ => interior (range (cycleBallPiece true).map))
      (fun _ => range (cycleBallPiece true).map) (fun _ => sphereZeroRatio 1) :=
  zeroLink_oneCore_FXR (W := sphereW) sphereOuterCore74 sphereId74
    (closedCarrier_boundary_eq_empty _) (sphereZeroRatio 1) (sphereZeroRatio_smooth 1)
    (fun x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
    (sphereZeroPiece_range 1).symm sphereOuter_frontier74

/-- The ball core is not the closed branch, and its model is the ball model. -/
theorem sphereOuter_model_FXR (j : Fin (oneCoreZero_FXR (W := sphereW) sphereOuterCore74 sphereId74
        (closedCarrier_boundary_eq_empty _) (sphereZeroRatio 1) (sphereZeroRatio_smooth 1)
        (fun x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
        (sphereZeroPiece_range 1).symm sphereOuter_frontier74).count) :
    ¬ sphereOuterCore74.IsClosed ∧
      (oneCoreZero_FXR (W := sphereW) sphereOuterCore74 sphereId74
        (closedCarrier_boundary_eq_empty _) (sphereZeroRatio 1) (sphereZeroRatio_smooth 1)
        (fun x hx => sphereZeroRatio_mfderiv 1 x (sphereZeroRatio_zero 1 x hx))
        (sphereZeroPiece_range 1).symm sphereOuter_frontier74).model j =
        .inl sphereOuterModel74 :=
  ⟨fun h => h, rfl⟩

end Ball

/-! ## The SOLID TORUS branch: the Heegaard solid torus in S³ -/

section SolidTorus

/-- The Heegaard solid torus `{cliffordHeight ≤ 0} ⊂ S³` as a solid parametrization. -/
def solidTorusSolid74_FXR : SolidParam74.{0, 0} solidTorusSet.{0} where
  Piece := solidTorusSet.{0}
  param := Subtype.val
  embedding := solidTorusAtlas.isSmoothEmbedding_subtype_val
  range_eq := Subtype.range_coe

/-- **The solid torus branch inhabitant**: the Heegaard solid torus is a selected core. -/
def solidTorusCore74_FXR : SelectedSmoothCore74.{0, 0} solidTorusSet.{0} :=
  .solidTorus solidTorusSolid74_FXR
    (Diffeomorph.refl solidTorusCarrier.{0}.model solidTorusCarrier.{0}.Carrier ∞)

/-- The level `{cliffordHeight = 0}` is the frontier of the solid torus. -/
theorem solidTorus_frontier_FXR :
    {x : SphereCarrier.{0} | cliffordHeight x = 0} = frontier solidTorusSet.{0} := by
  rw [← solidTorusSolid74_FXR.boundary_eq]
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, le_of_eq hx⟩, (solidTorus_isBoundaryPoint_iff _).mpr hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (solidTorus_isBoundaryPoint_iff p).mp hp

/-- **Solid torus branch**: the zero link of the Heegaard solid torus in S³ (`F = cliffordHeight`),
for the identity carrier identification of `S³`. -/
theorem solidTorus_zeroLink_FXR :
    ZeroLink_LND74 sphereId74.toEquiv
      (oneCoreZero_FXR (W := sphereW) solidTorusCore74_FXR sphereId74
        (closedCarrier_boundary_eq_empty _) cliffordHeight contMDiff_cliffordHeight
        cliffordHeight_regular rfl solidTorus_frontier_FXR)
      (fun _ : Unit => solidTorusSet.{0}) (fun _ => interior solidTorusSet.{0})
      (fun _ => solidTorusSet.{0}) (fun _ => cliffordHeight) :=
  zeroLink_oneCore_FXR (W := sphereW) solidTorusCore74_FXR sphereId74
    (closedCarrier_boundary_eq_empty _) cliffordHeight contMDiff_cliffordHeight
    cliffordHeight_regular rfl solidTorus_frontier_FXR

/-- The solid torus core is not the closed branch, and the table's model is the solid torus
model. -/
theorem solidTorus_model_FXR (j : Fin (oneCoreZero_FXR (W := sphereW) solidTorusCore74_FXR
        sphereId74 (closedCarrier_boundary_eq_empty _) cliffordHeight contMDiff_cliffordHeight
        cliffordHeight_regular rfl solidTorus_frontier_FXR).count) :
    ¬ solidTorusCore74_FXR.IsClosed ∧
      (oneCoreZero_FXR (W := sphereW) solidTorusCore74_FXR sphereId74
        (closedCarrier_boundary_eq_empty _) cliffordHeight contMDiff_cliffordHeight
        cliffordHeight_regular rfl solidTorus_frontier_FXR).model j =
        .inl (.solidTorus (Diffeomorph.refl solidTorusCarrier.{0}.model
          solidTorusCarrier.{0}.Carrier ∞)) :=
  ⟨fun h => h, rfl⟩

end SolidTorus

/-! ## The TWISTED I-BUNDLE branch: the Möbius bundle in its lens space -/

section Mobius

open GC.Seifert

private local instance mobiusBundleSet_connected_FXR : ConnectedSpace mobiusBundleSet.{0} :=
  mobiusBundleCarrier_connectedSpace.{0}

private local instance mobiusBundleSet_compact_FXR : CompactSpace mobiusBundleSet.{0} :=
  isCompact_iff_compactSpace.mp
    (isClosed_le contMDiff_mobiusBundleFunction.continuous continuous_const).isCompact

/-- The Möbius bundle `{Q ≤ 0} ⊂ mobiusLens` as a solid parametrization. -/
def mobiusSolid74_FXR : SolidParam74.{0, 0} mobiusBundleSet.{0} where
  Piece := mobiusBundleSet.{0}
  param := Subtype.val
  embedding := mobiusBundleAtlas.isSmoothEmbedding_subtype_val
  range_eq := Subtype.range_coe

/-- **The twisted I-bundle branch inhabitant**: the Möbius bundle is a selected core. -/
def mobiusCore74_FXR : SelectedSmoothCore74.{0, 0} mobiusBundleSet.{0} :=
  .twistedIBundle mobiusSolid74_FXR
    (Diffeomorph.refl mobiusBundleCarrier.{0}.model mobiusBundleCarrier.{0}.Carrier ∞)

/-- The identity carrier identification of the lens space `mobiusLens` (model form `𝓡 3`). -/
def mobiusId74_FXR : mobiusLens.{0}.Carrier ≃ₘ⟮𝓡 3, (NoCuts.carrier mobiusLens.{0}).model⟯
    mobiusLens.{0}.Carrier :=
  Diffeomorph.refl (NoCuts.carrier mobiusLens.{0}).model mobiusLens.{0}.Carrier ∞

/-- The level `{Q = 0}` is the frontier of the Möbius bundle. -/
theorem mobius_frontier_FXR :
    {x : mobiusLens.{0}.Carrier | mobiusBundleFunction x = 0} = frontier mobiusBundleSet.{0} := by
  rw [← mobiusSolid74_FXR.boundary_eq]
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, le_of_eq hx⟩, (mobiusBundleSet_isBoundaryPoint_iff _).mpr hx, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (mobiusBundleSet_isBoundaryPoint_iff p).mp hp

/-- **Twisted I-bundle branch**: the zero link of the Möbius bundle in `mobiusLens`
(`F = mobiusBundleFunction`), for the identity carrier identification. -/
theorem mobius_zeroLink_FXR :
    ZeroLink_LND74 mobiusId74_FXR.toEquiv
      (oneCoreZero_FXR (W := NoCuts.carrier mobiusLens.{0}) mobiusCore74_FXR mobiusId74_FXR
        (closedCarrier_boundary_eq_empty _) mobiusBundleFunction contMDiff_mobiusBundleFunction
        mobiusBundleFunction_regular rfl mobius_frontier_FXR)
      (fun _ : Unit => mobiusBundleSet.{0}) (fun _ => interior mobiusBundleSet.{0})
      (fun _ => mobiusBundleSet.{0}) (fun _ => mobiusBundleFunction) :=
  zeroLink_oneCore_FXR (W := NoCuts.carrier mobiusLens.{0}) mobiusCore74_FXR mobiusId74_FXR
    (closedCarrier_boundary_eq_empty _) mobiusBundleFunction contMDiff_mobiusBundleFunction
    mobiusBundleFunction_regular rfl mobius_frontier_FXR

/-- The Möbius core is not the closed branch, and the table's model is the twisted I-bundle
model. -/
theorem mobius_model_FXR (j : Fin (oneCoreZero_FXR (W := NoCuts.carrier mobiusLens.{0})
        mobiusCore74_FXR mobiusId74_FXR (closedCarrier_boundary_eq_empty _) mobiusBundleFunction
        contMDiff_mobiusBundleFunction mobiusBundleFunction_regular rfl
        mobius_frontier_FXR).count) :
    ¬ mobiusCore74_FXR.IsClosed ∧
      (oneCoreZero_FXR (W := NoCuts.carrier mobiusLens.{0}) mobiusCore74_FXR mobiusId74_FXR
        (closedCarrier_boundary_eq_empty _) mobiusBundleFunction contMDiff_mobiusBundleFunction
        mobiusBundleFunction_regular rfl mobius_frontier_FXR).model j =
        .inl (.twistedIBundle (Diffeomorph.refl mobiusBundleCarrier.{0}.model
          mobiusBundleCarrier.{0}.Carrier ∞)) :=
  ⟨fun h => h, rfl⟩

end Mobius

end DifferentialGeometry.Geometry.Collapse
