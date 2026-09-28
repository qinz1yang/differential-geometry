import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.Manifold.Interval.TangentLift
import DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Bundle.Orientation.FrameTransport

set_option autoImplicit false

noncomputable section

open Set Manifold Module Bundle Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u

local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Interval" => Icc (-2 : ℝ) 2
local notation "Tube" => S2 × Interval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def intervalBasis (t : Interval) : Basis (Fin 1) ℝ (TangentSpace (𝓡∂ 1) t) :=
  (Basis.singleton (Fin 1) ℝ).map
    (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm.toLinearEquiv

def normalFirstModelBasis (z : S2) (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z))
    (t : Interval) : Basis (Fin 3) ℝ (TangentSpace CI (z, t)) :=
  (((intervalBasis t).prod b).reindex finSumFinEquiv).map
    (LinearEquiv.prodComm ℝ (TangentSpace (𝓡∂ 1) t) (TangentSpace (𝓡 2) z))

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def tubeDifferential (a : T.Index) (q : Tube) :
    TangentSpace CI q ≃ₗ[ℝ] TangentSpace (𝓡 3) (T.tube a q) :=
  LinearEquiv.ofBijective (mfderiv CI (𝓡 3) (T.tube a) q).toLinearMap
    (DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      CI (𝓡 3) (T.tube a) q ((T.smooth a).isImmersion.isImmersionAt q)
      (by change Module.finrank ℝ (E2 × E1) = Module.finrank ℝ E3; simp))

def tubeFrame (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) :
    Basis (Fin 3) ℝ (TangentSpace (𝓡 3) (T.tube a (z, t))) :=
  (normalFirstModelBasis z b t).map (tubeDifferential T a (z, t))

theorem tubeFrame_apply (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) (i : Fin 3) :
    tubeFrame T a z b t i =
      mfderiv CI (𝓡 3) (T.tube a) (z, t) (normalFirstModelBasis z b t i) := rfl

end DifferentialGeometry.Topology.SphericalTubeSystem

namespace DifferentialGeometry.Topology.SphericalTubeSystem
universe u
local notation "Interval" => Set.Icc (-2 : ℝ) 2
local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem continuous_intervalVector (r : ℝ) :
    Continuous (fun t : Interval =>
      (⟨t, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r⟩ :
        TangentBundle (𝓡∂ 1) Interval)) := by
  exact (DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc_symm.continuous.comp
    (continuous_id.prodMk continuous_const))

end DifferentialGeometry.Topology.SphericalTubeSystem


namespace DifferentialGeometry.Topology.SphericalTubeSystem
universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Interval" => Set.Icc (-2 : ℝ) 2
local notation "Tube" => S2 × Interval
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem continuous_productVector (z : S2) (v : TangentSpace (𝓡 2) z) (r : ℝ) :
    Continuous (fun t : Interval =>
      (⟨(z, t), (v, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r)⟩ :
        TangentBundle CI Tube)) := by
  let hpair : Continuous (fun t : Interval =>
      ((⟨z, v⟩ : TangentBundle (𝓡 2) S2),
        (⟨t, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm r⟩ :
          TangentBundle (𝓡∂ 1) Interval))) :=
    continuous_const.prodMk (continuous_intervalVector r)
  have he := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓡 2) (I' := 𝓡∂ 1) (M := S2) (M' := Interval) (n := (0 : WithTop ℕ∞))).continuous
  have hc := he.comp hpair
  exact hc.congr (fun t => rfl)

private theorem normalFirstModelBasis_zero (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) :
    normalFirstModelBasis z b t 0 =
      (0, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm 1) := by
  erw [normalFirstModelBasis, Basis.map_apply, Basis.reindex_apply]
  change LinearEquiv.prodComm ℝ (TangentSpace (𝓡∂ 1) t) (TangentSpace (𝓡 2) z)
    (((intervalBasis t).prod b) (Sum.inl 0)) = _
  simp [Basis.prod_apply, intervalBasis]
  rfl

private theorem normalFirstModelBasis_succ (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t : Interval) (i : Fin 2) :
    normalFirstModelBasis z b t i.succ = (b i, 0) := by
  erw [normalFirstModelBasis, Basis.map_apply, Basis.reindex_apply]
  have hidx : (finSumFinEquiv (m := 1) (n := 2)).symm i.succ = Sum.inr i := by
    fin_cases i <;> rfl
  rw [hidx]
  simp [Basis.prod_apply]
  rfl

private theorem continuous_normalFirstModelBasis (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (i : Fin 3) :
    Continuous (fun t : Interval =>
      (⟨(z, t), normalFirstModelBasis z b t i⟩ : TangentBundle CI Tube)) := by
  cases i using Fin.cases with
  | zero =>
    apply (continuous_productVector z 0 1).congr
    intro t
    exact congrArg (fun v : TangentSpace CI (z, t) =>
      (⟨(z, t), v⟩ : TangentBundle CI Tube)) (normalFirstModelBasis_zero z b t).symm
  | succ i =>
    apply (continuous_productVector z (b i) 0).congr
    intro t
    apply congrArg (fun v : TangentSpace CI (z, t) =>
      (⟨(z, t), v⟩ : TangentBundle CI Tube))
    change (b i, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc t).symm 0) = _
    rw [map_zero]
    exact (normalFirstModelBasis_succ z b t i).symm

theorem continuous_tubeFrame (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (i : Fin 3) :
    Continuous (fun t : Interval =>
      (⟨T.tube a (z, t), T.tubeFrame a z b t i⟩ : TangentBundle (𝓡 3) M.Carrier)) := by
  have h := ((T.smooth a).contMDiff.continuous_tangentMap (by simp)).comp
    (continuous_normalFirstModelBasis z b i)
  exact h.congr (fun _ => rfl)


theorem tubeFrame_orientation_eq_iff (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (t t' : Interval) :
    (T.tubeFrame a z b t).orientation = M.orientation.orientation (T.tube a (z, t)) ↔
      (T.tubeFrame a z b t').orientation = M.orientation.orientation (T.tube a (z, t')) := by
  let : PreconnectedSpace Interval := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact DifferentialGeometry.VectorBundle.frame_orientation_eq_iff
    (tangentBundleCore (𝓡 3) M.Carrier) (by simp)
    (fun t : Interval => T.tube a (z, t))
    ((T.tube a).continuous.comp (continuous_const.prodMk continuous_id))
    M.orientation.orientation
    (DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_manifoldOrientation M.orientation)
    (T.tubeFrame a z b) (T.continuous_tubeFrame a z b) t t'


def boundaryFrame (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) :
    Basis (Fin 3) ℝ (TangentSpace (𝓡 3) (T.boundarySphere (a, side) z)) :=
  if side then
    (T.tubeFrame a z b (boundaryLevel side)).unitsSMul (Function.update 1 (0 : Fin 3) (-1))
  else T.tubeFrame a z b (boundaryLevel side)

theorem boundaryFrame_normal (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) :
    T.boundaryFrame a z b side 0 =
      mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel side)
        (0, (if side then -1 else 1 : ℝ) •
          (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel side)).symm 1) := by
  cases side with
  | false =>
    change mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel false)
      (normalFirstModelBasis z b (boundaryLevel false) 0) = _
    rw [normalFirstModelBasis_zero]
    simp only [Bool.false_eq_true, ite_false, one_smul]
    rfl
  | true =>
    erw [boundaryFrame, ite_eq_left rfl, Basis.unitsSMul_apply, Function.update_self, Units.neg_smul,
      one_smul, tubeFrame_apply, normalFirstModelBasis_zero]
    simp only [ite_true, neg_smul, one_smul]
    change -(mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel true)
      (0, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel true)).symm 1)) = _
    erw [show ((0 : TangentSpace (𝓡 2) z),
        -(DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel true)).symm 1) =
      -((0 : TangentSpace (𝓡 2) z),
        (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel true)).symm 1) from by simp]
    exact (map_neg (mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel true))
      (0, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (boundaryLevel true)).symm 1)).symm

theorem boundaryFrame_orientation_opposite (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) :
    (T.boundaryFrame a z b false).orientation = M.orientation.orientation (T.boundarySphere (a, false) z) ↔
      (T.boundaryFrame a z b true).orientation ≠ M.orientation.orientation (T.boundarySphere (a, true) z) := by
  have htransport := T.tubeFrame_orientation_eq_iff a z b (boundaryLevel false) (boundaryLevel true)
  have hneg : (T.boundaryFrame a z b true).orientation =
      -(T.tubeFrame a z b (boundaryLevel true)).orientation :=
    Basis.orientation_neg_single _ 0
  change (T.tubeFrame a z b (boundaryLevel false)).orientation =
    M.orientation.orientation (T.tube a (z, boundaryLevel false)) ↔ _
  rw [hneg]
  constructor
  · intro hfalse htrue
    have h := htransport.mp hfalse
    have htrue' : -(T.tubeFrame a z b (boundaryLevel true)).orientation =
        M.orientation.orientation (T.tube a (z, boundaryLevel true)) := htrue
    have hbad : -(M.orientation.orientation (T.tube a (z, boundaryLevel true))) =
        M.orientation.orientation (T.tube a (z, boundaryLevel true)) :=
      (congrArg Neg.neg h).symm.trans htrue'
    exact Module.Ray.ne_neg_self _ hbad.symm
  · intro htrue
    apply htransport.mpr
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (T.tube a (z, boundaryLevel true))) :=
      inferInstanceAs (FiniteDimensional ℝ E3)
    rcases Orientation.eq_or_eq_neg
      (T.tubeFrame a z b (boundaryLevel true)).orientation
      (M.orientation.orientation (T.tube a (z, boundaryLevel true)))
      (by change Fintype.card (Fin 3) = Module.finrank ℝ E3; simp) with h | h
    · exact h
    · apply False.elim
      apply htrue
      change -(T.tubeFrame a z b (boundaryLevel true)).orientation =
        M.orientation.orientation (T.tube a (z, boundaryLevel true))
      rw [h, neg_neg]



theorem boundaryFrame_zero (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) :
    T.boundaryFrame a z b side 0 = T.outwardVector (a, side) z := by
  rw [T.boundaryFrame_normal]
  have ht : (boundaryLevel side).val < 2 := by cases side <;> norm_num [boundaryLevel]
  rw [DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply_of_lt _ ht]
  cases side <;> simp only [outwardVector, Bool.false_eq_true, ite_false, ite_true, one_smul, neg_smul]
  · exact congrArg (mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel false))
      (Prod.ext rfl (one_smul ℝ (EuclideanSpace.single 0 (1 : ℝ))))
  · exact congrArg (mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel true))
      (Prod.ext rfl (neg_one_smul ℝ (EuclideanSpace.single 0 (1 : ℝ))))


theorem boundaryFrame_succ (a : T.Index) (z : S2)
    (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) (side : Bool) (i : Fin 2) :
    T.boundaryFrame a z b side i.succ =
      mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) z (b i) := by
  have hchain : mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) z (b i) =
      mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel side) (b i, 0) := by
    change mfderiv (𝓡 2) (𝓡 3)
      ((T.tube a) ∘ fun y : S2 => (y, boundaryLevel side)) z (b i) = _
    erw [mfderiv_comp_apply z ((T.smooth a).contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_id.prodMk contMDiff_const :
        ContMDiff (𝓡 2) CI ∞ (fun y : S2 => (y, boundaryLevel side))).mdifferentiableAt (by simp)),
      mfderiv_prod_left]
    rfl
  rw [hchain]
  cases side with
  | false =>
    change mfderiv CI (𝓡 3) (T.tube a) (z, boundaryLevel false)
      (normalFirstModelBasis z b (boundaryLevel false) i.succ) = _
    rw [normalFirstModelBasis_succ]
    rfl
  | true =>
    erw [boundaryFrame, ite_eq_left rfl, Basis.unitsSMul_apply,
      Function.update_of_ne (Fin.succ_ne_zero i), Pi.one_apply, one_smul,
      tubeFrame_apply, normalFirstModelBasis_succ]
    rfl

end DifferentialGeometry.Topology.SphericalTubeSystem
