import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Faithfulness
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace DifferentialGeometry.Hyperboloid

private theorem inner_upperSheet_coordinates {n : ℕ}
    (x y : DifferentialGeometry.Hyperbolic.LorVec n) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin n => x (Sum.inl i)))
      (WithLp.toLp 2 (fun i : Fin n => y (Sum.inl i))) = DifferentialGeometry.Hyperbolic.sdot x y := by
  simp [PiLp.inner_apply, DifferentialGeometry.Hyperbolic.sdot, mul_comm]

private def ofUpperSheet {n : ℕ} (x : DifferentialGeometry.Hyperbolic.HUpper n) :
    Hyperboloid (EuclideanSpace ℝ (Fin n)) where
  time := x.val (Sum.inr 0)
  space := WithLp.toLp 2 (fun i => x.val (Sum.inl i))
  time_pos := x.future
  time_sq_sub_inner_self := by
    rw [inner_upperSheet_coordinates]
    have hx := x.is_unit
    change DifferentialGeometry.Hyperbolic.sdot x.val x.val -
      x.val (Sum.inr 0) * x.val (Sum.inr 0) = -1 at hx
    nlinarith only [hx]

private def toUpperSheet {n : ℕ} (x : Hyperboloid (EuclideanSpace ℝ (Fin n))) :
    DifferentialGeometry.Hyperbolic.HUpper n where
  val := Sum.elim (fun i => x.space i) (fun _ => x.time)
  is_unit := by
    have hx := x.time_sq_sub_inner_self
    simp only [PiLp.inner_apply, Real.inner_apply] at hx
    change (∑ i : Fin n, x.space i * x.space i) - x.time * x.time = -1
    nlinarith only [hx]
  future := x.time_pos

private theorem toUpperSheet_ofUpperSheet {n : ℕ} (x : DifferentialGeometry.Hyperbolic.HUpper n) :
    toUpperSheet (ofUpperSheet x) = x := by
  apply DifferentialGeometry.Hyperbolic.HUpper.ext
  funext i
  rcases i with i | i
  · rfl
  · have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rfl

private theorem ofUpperSheet_toUpperSheet {n : ℕ}
    (x : Hyperboloid (EuclideanSpace ℝ (Fin n))) : ofUpperSheet (toUpperSheet x) = x := by
  apply Hyperboloid.ext
  apply PiLp.ext
  intro i
  rfl

private theorem dist_ofUpperSheet {n : ℕ} (x y : DifferentialGeometry.Hyperbolic.HUpper n) :
    dist (ofUpperSheet x) (ofUpperSheet y) = dist x y := by
  rw [dist_eq_arcosh]
  change Real.arcosh (x.val (Sum.inr 0) * y.val (Sum.inr 0) -
    inner ℝ (WithLp.toLp 2 (fun i : Fin n => x.val (Sum.inl i)))
      (WithLp.toLp 2 (fun i : Fin n => y.val (Sum.inl i)))) =
    Real.arcosh (-DifferentialGeometry.Hyperbolic.lorB x.val y.val)
  rw [inner_upperSheet_coordinates]
  unfold DifferentialGeometry.Hyperbolic.lorB DifferentialGeometry.Hyperbolic.tc
  congr 1
  ring

def hUpperIsometryEquiv (n : ℕ) : DifferentialGeometry.Hyperbolic.HUpper n ≃ᵢ
    Hyperboloid (EuclideanSpace ℝ (Fin n)) where
  toEquiv :=
    { toFun := ofUpperSheet
      invFun := toUpperSheet
      left_inv := toUpperSheet_ofUpperSheet
      right_inv := ofUpperSheet_toUpperSheet }
  isometry_toFun := Isometry.of_dist_eq dist_ofUpperSheet

@[simp] theorem hUpperIsometryEquiv_time (n : ℕ) (x : DifferentialGeometry.Hyperbolic.HUpper n) :
    (hUpperIsometryEquiv n x).time = x.val (Sum.inr 0) := rfl

@[simp] theorem hUpperIsometryEquiv_space_apply (n : ℕ) (x : DifferentialGeometry.Hyperbolic.HUpper n)
    (i : Fin n) : (hUpperIsometryEquiv n x).space i = x.val (Sum.inl i) := rfl

@[simp] theorem hUpperIsometryEquiv_symm_inl (n : ℕ)
    (x : Hyperboloid (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    ((hUpperIsometryEquiv n).symm x).val (Sum.inl i) = x.space i := rfl

@[simp] theorem hUpperIsometryEquiv_symm_inr (n : ℕ)
    (x : Hyperboloid (EuclideanSpace ℝ (Fin n))) (i : Fin 1) :
    ((hUpperIsometryEquiv n).symm x).val (Sum.inr i) = x.time := rfl

@[simp] theorem hUpperIsometryEquiv_basepointH (n : ℕ) :
    hUpperIsometryEquiv n DifferentialGeometry.HyperbolicFaithful.basepointH = origin := by
  apply Hyperboloid.ext
  apply PiLp.ext
  intro i
  change DifferentialGeometry.HyperbolicFaithful.eTime (Sum.inl i) = 0
  exact DifferentialGeometry.HyperbolicFaithful.eTime_apply_inl i

end DifferentialGeometry.Hyperboloid
