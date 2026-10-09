import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksSelected
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksSolid

/-!
# Protected seams and frozen pieces under an actual selected star

The solid arms of an actual selected star cannot be protected: their seam maps factor through
the cyclic fundamental group of the compact solid component. Consequently each protected seam
has a retained index with the exact original signed collar and matching. A star whose center
is not frozen contains no frozen vertex, since a frozen hyperbolic vertex has a noncyclic group
at every point while an actual solid arm has a cyclic group.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {d : SeifertData}

theorem selectedStar_pairing_pos (G : SelectedStarGroup σ.toTorus d) :
    0 < σ.toTorus.pairing.count := by
  let s := G.product.port ⟨0, d.one_le_k⟩
  rcases s.val with j | j | j
  · exact Fin.pos j
  · exact Fin.pos j
  · exact (Fin.cast σ.toTorus.externalCount_eq_zero j).elim0

def selectedStarContraction (G : SelectedStarGroup σ.toTorus d) :
    TorusPresentation (NoCuts.carrier Q) :=
  G.relativeSelectedContraction (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos (σ.selectedStar_pairing_pos G))

variable
  (hInc : ∀ k : σ.ProtSeam, ∀ t₀,
    Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t₀))

include hInc

theorem selectedStar_not_protected (G : SelectedStarGroup σ.toTorus d)
    (j : Fin σ.toTorus.pairing.count) (hj : j ∈ G.selected) : j ∉ σ.prot := by
  obtain ⟨l, rfl⟩ := G.internal hj
  intro hp
  exact solid_incident_seam_not_injective (G.solid l) (Or.inl rfl) (hInc ⟨G.arm l, hp⟩)

def selectedStarProtectedIndex (G : SelectedStarGroup σ.toTorus d) :
    σ.ProtSeam ↪ Fin (σ.selectedStarContraction G).pairing.count where
  toFun j := G.relativeSelectedSeamEquiv
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos (σ.selectedStar_pairing_pos G))
    ⟨j.val, fun hj => σ.selectedStar_not_protected hInc G j.val hj j.property⟩
  inj' j k he := by
    have h := (G.relativeSelectedSeamEquiv
      (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos (σ.selectedStar_pairing_pos G))).injective he
    have hv : j.val = k.val :=
      congrArg (fun a : σ.toTorus.AlongUnpairedSeam G.selected => a.val) h
    exact Subtype.ext hv

theorem selectedStarProtectedIndex_seam (G : SelectedStarGroup σ.toTorus d)
    (j : σ.ProtSeam) :
    (σ.selectedStarContraction G).seam (σ.selectedStarProtectedIndex hInc G j) =
      σ.toTorus.seam j.val :=
  G.relativeSelected_seam (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos (σ.selectedStar_pairing_pos G)) _

theorem selectedStarProtectedIndex_matching (G : SelectedStarGroup σ.toTorus d)
    (j : σ.ProtSeam) :
    (σ.selectedStarContraction G).pairing.matching (σ.selectedStarProtectedIndex hInc G j) =
      σ.toTorus.pairing.matching j.val :=
  G.relativeSelected_matching (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos (σ.selectedStar_pairing_pos G)) _

theorem selectedStarProtectedIndex_injective (G : SelectedStarGroup σ.toTorus d)
    (j : σ.ProtSeam) (t : Torus) :
    Function.Injective (FundamentalGroup.map
      ((σ.selectedStarContraction G).seamTorus (σ.selectedStarProtectedIndex hInc G j)) t) := by
  have he : (σ.selectedStarContraction G).seamTorus
      (σ.selectedStarProtectedIndex hInc G j) = σ.toTorus.seamTorus j.val := by
    ext z
    exact congrArg (fun c => c (z, 0)) (σ.selectedStarProtectedIndex_seam hInc G j)
  rw [he]
  exact hInc j t

theorem selectedStar_set_not_frozen (G : SelectedStarGroup σ.toTorus d)
    (hc : G.center ∉ σ.frozen) (i : Fin σ.toTorus.components.count) (hi : i ∈ G.set) :
    i ∉ σ.frozen := by
  rcases G.mem_set hi with rfl | ⟨l, rfl⟩
  · exact hc
  · intro hf
    let := σ.toTorus.components.connected (σ.toTorus.leftPiece (G.arm l))
    obtain ⟨x⟩ := (inferInstance : Nonempty
      (σ.toTorus.components.piece (σ.toTorus.leftPiece (G.arm l))))
    exact (σ.frozen_indecomposableNoncyclic hInc (Fin.pos (G.arm l)) _ hf x).2
      ((G.solid l).isCyclic_fundamentalGroup x)

end GC.Seifert.RelativeNormalization.MixedStage
