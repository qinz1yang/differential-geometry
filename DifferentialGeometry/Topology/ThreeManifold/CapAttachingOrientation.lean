import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.ThreeManifold.TubeFrameSign
import DifferentialGeometry.Topology.Manifold.SphereOrientation

noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem boundaryFrame_attaching_orientation_iff (a : T.Index)
    (side : Bool) (z : S2) (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) :
    (T.boundaryFrame a (C.attaching (a, side) z)
      (b.map ((C.attaching (a, side)).mfderivToContinuousLinearEquiv
        (by simp) z).toLinearEquiv) side).orientation =
      M.orientation.orientation (T.boundarySphere (a, side) (C.attaching (a, side) z)) ↔
    if side then b.orientation ≠ (sphereOrientation 2 (by decide)).orientation z
    else b.orientation = (sphereOrientation 2 (by decide)).orientation z := by
  let R := C.attaching (a, side)
  let dR := (R.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
  let B := T.boundaryFrame a (R z) (b.map dR) side
  let f : S2 → M.Carrier := T.boundarySphere (a, side) ∘ R
  let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
    inferInstanceAs (FiniteDimensional ℝ E3)
  let o := M.orientation.orientation (f z)
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace (𝓡 3) (f z)) := by
    change Fintype.card (Fin 3) = Module.finrank ℝ E3
    simp
  have hchain (v : TangentSpace (𝓡 2) z) :
      mfderiv (𝓡 2) (𝓡 3) f z v =
        mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) (R z) (dR v) := by
    exact mfderiv_comp_apply z
      (((T.smooth a).contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt
        (by simp)) (R.contMDiff.mdifferentiableAt (by simp)) v
  have hframe : Fin.cons (T.outwardVector (a, side) (R z))
      (Fin.cons (mfderiv (𝓡 2) (𝓡 3) f z (b 0))
        (Fin.cons (mfderiv (𝓡 2) (𝓡 3) f z (b 1)) ![])) = ⇑B := by
    funext i
    fin_cases i
    · exact (T.boundaryFrame_zero a (R z) (b.map dR) side).symm
    · change mfderiv (𝓡 2) (𝓡 3) f z (b 0) = B 1
      erw [show B 1 = mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) (R z)
        ((b.map dR) 0) from T.boundaryFrame_succ a (R z) (b.map dR) side 0]
      exact hchain (b 0)
    · change mfderiv (𝓡 2) (𝓡 3) f z (b 1) = B 2
      erw [show B 2 = mfderiv (𝓡 2) (𝓡 3) (T.boundarySphere (a, side)) (R z)
        ((b.map dR) 1) from T.boundaryFrame_succ a (R z) (b.map dR) side 1]
      exact hchain (b 1)
  have hsphere : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
      (Fin.cons z.val
        (Fin.cons (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) z (b 0))
          (Fin.cons (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) z (b 1)) ![]))) =
      sphereOutwardDeterminant 2 z b := by
    apply congrArg (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
    funext i
    fin_cases i <;> rfl
  have h := C.boundary_orientation_reversing (a, side) z (b 0) (b 1)
  change (0 < (o.someBasis hcard).det
    (Fin.cons (T.outwardVector (a, side) (R z))
      (Fin.cons (mfderiv (𝓡 2) (𝓡 3) f z (b 0))
        (Fin.cons (mfderiv (𝓡 2) (𝓡 3) f z (b 1)) ![])))) ↔ _ at h
  rw [hframe, hsphere] at h
  have hpos : B.orientation = o ↔ 0 < (o.someBasis hcard).det B := by
    rw [← Basis.orientation_eq_iff_det_pos, Orientation.someBasis_orientation, eq_comm]
  change B.orientation = o ↔ _
  rw [hpos, h]
  cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul, neg_neg_iff_pos]
  · exact (sphereOrientation_characterization 2 (by decide) z b).symm
  · change sphereOutwardDeterminant 2 z b < 0 ↔
      ¬ b.orientation = (sphereOrientation 2 (by decide)).orientation z
    rw [sphereOrientation_characterization]
    exact ⟨fun hneg hpos => (not_lt_of_ge hpos.le) hneg,
      fun hpos => lt_of_le_of_ne (le_of_not_gt hpos) (sphereOutwardDeterminant_ne_zero 2 z b)⟩

private theorem boundaryFrame_attaching_symm_orientation_iff (a : T.Index)
    (side : Bool) (z : S2) (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) z)) :
    (T.boundaryFrame a z b side).orientation =
      M.orientation.orientation (T.boundarySphere (a, side) z) ↔
    if side then
      (b.map ((C.attaching (a, side)).symm.mfderivToContinuousLinearEquiv
        (by simp) z).toLinearEquiv).orientation ≠
          (sphereOrientation 2 (by decide)).orientation ((C.attaching (a, side)).symm z)
    else
      (b.map ((C.attaching (a, side)).symm.mfderivToContinuousLinearEquiv
        (by simp) z).toLinearEquiv).orientation =
          (sphereOrientation 2 (by decide)).orientation ((C.attaching (a, side)).symm z) := by
  let R := C.attaching (a, side)
  let dR := (R.mfderivToContinuousLinearEquiv (by simp) (R.symm z)).toLinearEquiv
  let diR := (R.symm.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
  have hmap : (b.map diR).map dR = b := by
    ext i
    change mfderiv (𝓡 2) (𝓡 2) R (R.symm z)
      (mfderiv (𝓡 2) (𝓡 2) R.symm z (b i)) = b i
    have h := mfderiv_comp_apply z (R.mdifferentiable (by simp) (R.symm z))
      (R.symm.mdifferentiable (by simp) z) (b i)
    have heq : (R : S2 → S2) ∘ R.symm = id := funext R.apply_symm_apply
    rw [heq, mfderiv_id] at h
    exact h.symm
  have h := C.boundaryFrame_attaching_orientation_iff a side (R.symm z) (b.map diR)
  change (T.boundaryFrame a (R (R.symm z)) ((b.map diR).map dR) side).orientation = _ ↔ _ at h
  rw [hmap] at h
  change (T.boundaryFrame a (R (R.symm z)) b side).orientation =
      M.orientation.orientation (T.boundarySphere (a, side) (R (R.symm z))) ↔
    if side then (b.map diR).orientation ≠ (sphereOrientation 2 (by decide)).orientation (R.symm z)
    else (b.map diR).orientation = (sphereOrientation 2 (by decide)).orientation (R.symm z) at h
  rw [R.apply_symm_apply] at h
  exact h

theorem attaching_trans_symm_preservesOrientation (a : T.Index) :
    ((C.attaching (a, false)).trans (C.attaching (a, true)).symm).preservesOrientation
      (sphereOrientation 2 (by decide)) (sphereOrientation 2 (by decide)) := by
  intro z
  let R₀ := C.attaching (a, false)
  let R₁ := C.attaching (a, true)
  let R := R₀.trans R₁.symm
  let o := sphereOrientation 2 (by decide)
  let _ : FiniteDimensional ℝ (TangentSpace (𝓡 2) z) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 2)))
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (TangentSpace (𝓡 2) z) := by
    change Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
    simp
  let b := (o.orientation z).someBasis hcard
  have hb : b.orientation = o.orientation z := Orientation.someBasis_orientation _ _
  let d₀ := (R₀.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
  let d₁ := (R₁.symm.mfderivToContinuousLinearEquiv (by simp) (R₀ z)).toLinearEquiv
  let q := R₀ z
  let bq := b.map d₀
  have hfalse : (T.boundaryFrame a q bq false).orientation =
      M.orientation.orientation (T.boundarySphere (a, false) q) :=
    (C.boundaryFrame_attaching_orientation_iff a false z b).mpr hb
  have htrue : (T.boundaryFrame a q bq true).orientation ≠
      M.orientation.orientation (T.boundarySphere (a, true) q) :=
    (T.boundaryFrame_orientation_opposite a q bq).mp hfalse
  have hc : (bq.map d₁).orientation = o.orientation (R₁.symm q) := by
    by_contra hne
    exact htrue ((C.boundaryFrame_attaching_symm_orientation_iff a true q bq).mpr hne)
  have hcomp : b.map (R.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv =
      bq.map d₁ := by
    ext i
    change mfderiv (𝓡 2) (𝓡 2) (R₁.symm ∘ R₀) z (b i) =
      mfderiv (𝓡 2) (𝓡 2) R₁.symm (R₀ z)
        (mfderiv (𝓡 2) (𝓡 2) R₀ z (b i))
    exact mfderiv_comp_apply z (R₁.symm.mdifferentiable (by simp) (R₀ z))
      (R₀.mdifferentiable (by simp) z) (b i)
  change Orientation.map (Fin 2) (R.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv
    (o.orientation z) = o.orientation (R z)
  rw [← hb, ← Basis.orientation_map, hcomp]
  exact hc

end DifferentialGeometry.Topology.SphericalCapping
