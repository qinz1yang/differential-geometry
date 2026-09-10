import DifferentialGeometry.Topology.Manifold.Orientation.SurfaceFrame
import DifferentialGeometry.Topology.ProjectiveSpace.SphereHalfTurnFrame

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set Module
open scoped Manifold ContDiff Topology

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance antipodalOrientationDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem orientation_ne_of_one_basis_vector_neg
    (b₀ b₁ : Basis (Fin 2) ℝ E)
    (hfirst : b₁ 0 = b₀ 0) (hsecond : b₁ 1 = -(b₀ 1)) :
    b₀.orientation ≠ b₁.orientation := by
  intro horientation
  have hdet : b₀.det b₁ = -1 := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp [Basis.toMatrix_apply, hfirst, hsecond]
  have hpos := (b₀.orientation_eq_iff_det_pos b₁).mp horientation
  rw [hdet] at hpos
  norm_num at hpos

theorem SurfaceOrientation.not_antipodal_localDiffeomorph
    (o : SurfaceOrientation I M) (q : S → M)
    (hq : IsLocalDiffeomorph (𝓡 2) I ∞ q)
    (hantipodal : ∀ x : S, q (-x) = q x) : False := by
  let γ := q ∘ sphereEquator
  let B : (t : ℝ) → Basis (Fin 2) ℝ (TangentSpace I (γ t)) := fun t =>
    (sphereHalfTurnBasis t).map
      (hq.mfderivToContinuousLinearEquiv (by simp) (sphereEquator t)).toLinearEquiv
  have hB (t : ℝ) (i : Fin 2) : B t i =
      mfderiv (𝓡 2) I q (sphereEquator t) (sphereHalfTurnBasis t i) := rfl
  have hγ : Continuous γ := hq.contMDiff.continuous.comp sphereEquator_smooth.continuous
  have hcontinuous : ∀ i : Fin 2, Continuous (fun t =>
      TotalSpace.mk' E (E := TangentSpace I) (γ t) (B t i)) := by
    intro i
    exact (hq.contMDiff.continuous_tangentMap (by simp)).comp (sphereHalfTurnBasis_continuous i)
  have hloop : γ 0 = γ Real.pi := by
    change q (sphereEquator 0) = q (sphereEquator Real.pi)
    rw [sphereEquator_pi, hantipodal]
  have horientation : (B 0).orientation = (B Real.pi).orientation :=
    o.frame_orientation_eq_of_loop γ hγ B hcontinuous 0 Real.pi hloop
  have hcomp : q ∘ sphereAntipodalDiffeomorph = q := by
    funext x
    exact hantipodal x
  have hd (x : S) (v : TangentSpace (𝓡 2) x) :
      mfderiv (𝓡 2) I q (-x)
        (mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph x v) =
          mfderiv (𝓡 2) I q x v := by
    have hc := mfderiv_comp_apply (x := x)
      (hq.mdifferentiable (by simp) (sphereAntipodalDiffeomorph x))
      (sphereAntipodalDiffeomorph.contMDiff.mdifferentiableAt (by simp)) v
    rw [hcomp] at hc
    exact hc.symm
  have hfirst : B Real.pi 0 = B 0 0 := by
    rw [hB, sphereHalfTurnBasis_pi_first, sphereEquator_pi, hd, hB]
  have hsecond : B Real.pi 1 = -(B 0 1) := by
    rw [hB, sphereHalfTurnBasis_pi_second, sphereEquator_pi]
    let v : TangentSpace (𝓡 2) (-sphereEquator 0) :=
      mfderiv (𝓡 2) (𝓡 2) sphereAntipodalDiffeomorph (sphereEquator 0) (sphereHalfTurnBasis 0 1)
    change mfderiv (𝓡 2) I q (-sphereEquator 0) (-v) = -(B 0 1)
    rw [map_neg]
    apply congrArg (fun z : E => -z)
    exact (hd (sphereEquator 0) (sphereHalfTurnBasis 0 1)).trans (hB 0 1).symm
  exact orientation_ne_of_one_basis_vector_neg (E := E) (B 0) (B Real.pi)
    hfirst hsecond horientation

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
