import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStage
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams

/-!
# Linear seams of a mixed stage

Lane MS, tier MS1 (design `handoffs/20261004-design-ms-mixed-split.md` §1.2). A seam of a mixed
stage is linear (`IsLinearSeam`) when its matching is the linear diffeomorphism of its own unit,
the text of `ElementaryPresentation.IsLinearSeam`. `linearize` applies Lane LS's
`linearPresentation` to the torus presentation and `linearPiece` to every product fibred piece;
the cut carrier, its pieces, the gluing and the reconstruction are unchanged, so the protected
seams, the frozen pieces with their hyperbolic geometries, the kinds and the cut map are carried
over literally. Every seam becomes linear (`isLinearSeam_linearize`), the move predicates are
unchanged (`isSplitSeam_linearize`, `isMergeSeam_linearize`, `isAbsorbSeam_linearize`), and the
new seam charts agree with the old ones below height `1/4` (`seam_linearize_of_le`), which is the
only fact the protected collar ledgers of a split need.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

def IsLinearSeam (j : Fin σ.toTorus.pairing.count) : Prop :=
  σ.toTorus.pairing.matching j = linearTorusDiffeomorph (torusUnit (σ.toTorus.pairing.matching j))

variable (hL : TorusMappingClassLinear)

def linearize : MixedStage Q where
  toTorus := linearPresentation hL σ.toTorus
  prot := σ.prot
  frozen := σ.frozen
  hyperbolic := σ.hyperbolic
  kind := σ.kind
  kind_mem := σ.kind_mem
  piece i hi := linearPiece hL (σ.piece i hi)
  left_prot := σ.left_prot
  right_prot := σ.right_prot

theorem linearize_toTorus : (σ.linearize hL).toTorus = linearPresentation hL σ.toTorus := rfl

theorem linearize_prot : (σ.linearize hL).prot = σ.prot := rfl

theorem linearize_frozen : (σ.linearize hL).frozen = σ.frozen := rfl

theorem linearize_kind : (σ.linearize hL).kind = σ.kind := rfl

theorem linearize_cutMap : (σ.linearize hL).toTorus.cutMap = σ.toTorus.cutMap := rfl

theorem innerCount_linearize : (σ.linearize hL).innerCount = σ.innerCount := rfl

theorem linearize_matching (j : Fin σ.toTorus.pairing.count) :
    (σ.linearize hL).toTorus.pairing.matching j =
      linearTorusDiffeomorph (torusUnit (σ.toTorus.pairing.matching j)) := rfl

theorem torusUnit_linearize_matching (j : Fin σ.toTorus.pairing.count) :
    torusUnit ((σ.linearize hL).toTorus.pairing.matching j) =
      torusUnit (σ.toTorus.pairing.matching j) :=
  (torusUnit_eq_of_isotopic (hL _)).symm

theorem isLinearSeam_linearize (j : Fin σ.toTorus.pairing.count) :
    (σ.linearize hL).IsLinearSeam j :=
  congrArg linearTorusDiffeomorph (σ.torusUnit_linearize_matching hL j).symm

theorem seamPiece_linearize (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.linearize hL).seamPiece j b = σ.seamPiece j b := by
  cases b <;> rfl

theorem hostPiece_linearize (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.linearize hL).hostPiece j b = σ.hostPiece j b := by
  cases b <;> rfl

theorem fillingDistance_linearize (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.linearize hL).fillingDistance j b = σ.fillingDistance j b := by
  cases b <;> simp only [fillingDistance, torusUnit_linearize_matching]

theorem isSplitSeam_linearize (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.linearize hL).IsSplitSeam j b ↔ σ.IsSplitSeam j b := by
  unfold IsSplitSeam
  rw [fillingDistance_linearize]
  rfl

theorem isMergeSeam_linearize (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.linearize hL).IsMergeSeam j b ↔ σ.IsMergeSeam j b := by
  unfold IsMergeSeam
  rw [fillingDistance_linearize]
  rfl

theorem isAbsorbSeam_linearize (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    (σ.linearize hL).IsAbsorbSeam j b ↔ σ.IsAbsorbSeam j b := Iff.rfl

theorem seam_linearize (k : Fin σ.toTorus.pairing.count) (p : Torus × ℝ) :
    (σ.linearize hL).toTorus.seam k p =
      σ.toTorus.seam k (seamTwist hL (σ.toTorus.pairing.matching k) p.2 p.1, p.2) := rfl

theorem seam_linearize_of_le (k : Fin σ.toTorus.pairing.count) (t : Torus) {s : ℝ}
    (hs : s ≤ 1 / 4) : (σ.linearize hL).toTorus.seam k (t, s) = σ.toTorus.seam k (t, s) := by
  rw [seam_linearize, seamTwist_of_le hL _ hs]

theorem seamTorus_linearize (k : Fin σ.toTorus.pairing.count) :
    (σ.linearize hL).toTorus.seamTorus k = σ.toTorus.seamTorus k := by
  ext t
  change (σ.linearize hL).toTorus.seam k (t, 0) = σ.toTorus.seam k (t, 0)
  exact σ.seam_linearize_of_le hL k t (by norm_num)

end GC.Seifert.RelativeNormalization.MixedStage
