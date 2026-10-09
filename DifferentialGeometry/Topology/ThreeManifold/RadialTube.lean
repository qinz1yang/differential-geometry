import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section

open Set Manifold Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Interval" => Icc (-2 : ℝ) 2
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local notation "PI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
private local instance tubeBounds : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
private local instance sphereDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private def tubeProjection : ℝ → Interval := projIcc (-2) 2 (by norm_num)

private theorem tubeProjection_val_eventually {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    (Subtype.val : Interval → ℝ) ∘ tubeProjection =ᶠ[𝓝 t] id := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  change (projIcc (-2 : ℝ) 2 (by norm_num) s).val = s
  rw [projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩]

private theorem tubeProjection_contMDiffAt {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ tubeProjection t := by
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2) (n := ∞)).isImmersion.isImmersionAt
      (tubeProjection t))).mpr
  exact ⟨continuous_projIcc.continuousAt,
    (tubeProjection_val_eventually ht).contMDiffAt_iff.mpr contMDiffAt_id⟩

private theorem tubeProjection_injective_mfderiv {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) tubeProjection t) := by
  have hchain := mfderiv_comp t
    ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2) (n := ∞)).mdifferentiableAt (by simp))
    ((tubeProjection_contMDiffAt ht).mdifferentiableAt (by simp))
  rw [(tubeProjection_val_eventually ht).mfderiv_eq, mfderiv_id] at hchain
  replace hchain : ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t) =
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Interval → ℝ) (tubeProjection t)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) tubeProjection t) :=
    (ContinuousLinearMap.ext fun _ => rfl).trans hchain
  have hinj : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id t) := by
    rw [mfderiv_id]
    exact injective_id
  rw [mfderiv_id, hchain] at hinj
  change Injective ((mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Interval → ℝ) (tubeProjection t)) ∘
    mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) tubeProjection t) at hinj
  exact hinj.of_comp

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

private def clampedTube (a : T.Index) (p : Sphere × ℝ) : M.Carrier :=
  T.tube a (p.1, tubeProjection p.2)

private theorem clampedTube_contMDiffAt (a : T.Index) {p : Sphere × ℝ}
    (hp : p.2 ∈ Ioo (-2 : ℝ) 2) :
    ContMDiffAt PI (𝓡 3) ∞ (T.clampedTube a) p :=
  (T.smooth a).contMDiff.contMDiffAt.comp p
    (contMDiffAt_id.prodMap (tubeProjection_contMDiffAt hp))

private theorem clampedTube_injective_mfderiv (a : T.Index) {p : Sphere × ℝ}
    (hp : p.2 ∈ Ioo (-2 : ℝ) 2) :
    Injective (mfderiv PI (𝓡 3) (T.clampedTube a) p) := by
  have hj : ContMDiffAt PI CI ∞ (Prod.map (id : Sphere → Sphere) tubeProjection) p :=
    contMDiffAt_id.prodMap (tubeProjection_contMDiffAt hp)
  change Injective (mfderiv PI (𝓡 3) ((T.tube a) ∘ Prod.map id tubeProjection) p)
  rw [mfderiv_comp p ((T.smooth a).contMDiff.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp)),
    mfderiv_prodMap mdifferentiableAt_id ((tubeProjection_contMDiffAt hp).mdifferentiableAt (by simp)),
    mfderiv_id]
  exact ((T.smooth a).isImmersion.isImmersionAt _ |>.mfderiv_injective (by simp)).comp
    (injective_id.prodMap (tubeProjection_injective_mfderiv hp))

private theorem isLocalDiffeomorphAt_clampedTube (a : T.Index) {p : Sphere × ℝ}
    (hp : p.2 ∈ Ioo (-2 : ℝ) 2) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞ (T.clampedTube a) p := by
  let U : Set (Sphere × ℝ) := {q | q.2 ∈ Ioo (-2 : ℝ) 2}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_snd
  have hs : ContMDiffOn PI (𝓡 3) ∞ (T.clampedTube a) U :=
    fun q hq => (clampedTube_contMDiffAt T a hq).contMDiffWithinAt
  let D : (E2 × ℝ) →L[ℝ] E3 := mfderiv PI (𝓡 3) (T.clampedTube a) p
  have hD : Injective D := clampedTube_injective_mfderiv T a hp
  let A : (E2 × ℝ) ≃L[ℝ] E3 :=
    (D.toLinearMap.linearEquivOfInjective hD (by simp)).toContinuousLinearEquiv
  exact Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (T.clampedTube a) hs hU p hp A
    ((clampedTube_contMDiffAt T a hp).mdifferentiableAt (by simp)).hasMFDerivAt

private def axialSign (side : Bool) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := if side then t else -t
  invFun t := if side then t else -t
  left_inv t := by cases side <;> simp
  right_inv t := by cases side <;> simp
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => if side then t else -t)
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact contMDiff_id.neg
    · exact contMDiff_id
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => if side then t else -t)
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact contMDiff_id.neg
    · exact contMDiff_id

def radialTube (a : T.Index) (A : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere)
    (side : Bool) (v : Sphere) (x : E3) : M.Carrier :=
  T.tube a (A (Manifold.sphereDirection v x),
    projIcc (-2) 2 (by norm_num) (if side then ‖x‖ else -‖x‖))

theorem radialTube_apply (a : T.Index) (A : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere)
    (side : Bool) (v : Sphere) {x : E3} (hx : ‖x‖ < 2) :
    T.radialTube a A side v x = T.tube a
      (A (Manifold.sphereDirection v x),
        ⟨if side then ‖x‖ else -‖x‖, by
          cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
            constructor <;> linarith [norm_nonneg x]⟩) := by
  unfold radialTube
  rw [projIcc_of_mem]

theorem isLocalDiffeomorphAt_radialTube (a : T.Index)
    (A : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere) (side : Bool) (v : Sphere)
    {x : E3} (hx0 : 0 < ‖x‖) (hx2 : ‖x‖ < 2) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (T.radialTube a A side v) x := by
  let P := Manifold.spherePolarChart (n := 2) v
  let R : Diffeomorph PI PI (Sphere × ℝ) (Sphere × ℝ) ∞ := A.prodCongr (axialSign side)
  have hP : IsLocalDiffeomorphAt (𝓡 3) PI ∞ P.symm x :=
    P.symm.isLocalDiffeomorphAt _ _ ∞ (norm_pos_iff.mp hx0)
  have hrange : (R (P.symm x)).2 ∈ Ioo (-2 : ℝ) 2 := by
    change (if side then ‖x‖ else -‖x‖) ∈ Ioo (-2 : ℝ) 2
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true, mem_Ioo] <;>
      constructor <;> linarith
  have hR := hP.comp PI (Sphere × ℝ) (R.isLocalDiffeomorph (P.symm x))
  exact hR.comp (𝓡 3) M.Carrier (isLocalDiffeomorphAt_clampedTube T a hrange)

end DifferentialGeometry.Topology.SphericalTubeSystem
