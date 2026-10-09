import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Interpolation
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryClassification
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isometryEquiv_interpolate {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : Hyperboloid E ≃ᵢ Hyperboloid F) (t : unitInterval) (x y : Hyperboloid E) :
    e (interpolate t x y) = interpolate t (e x) (e y) := by
  let A := lorentzExtension e
  let z : ℝ × E := (1 - (t : ℝ)) • (x.time, x.space) + (t : ℝ) • (y.time, y.space)
  have hz : A z = (1 - (t : ℝ)) • ((e x).time, (e x).space) +
      (t : ℝ) • ((e y).time, (e y).space) := by
    simp only [A, z, map_add, map_smul, lorentzExtension_apply]
  have hc : ((e (interpolate t x y)).time, (e (interpolate t x y)).space) =
      ((interpolate t (e x) (e y)).time, (interpolate t (e x) (e y)).space) := by
    rw [← lorentzExtension_apply e (interpolate t x y), interpolate_coordinates, map_smul,
      interpolate_coordinates]
    change (Real.sqrt (-(lorentzForm E z z)))⁻¹ • A z = _
    simp only [← hz, A.map_app]
  exact ext (congrArg Prod.snd hc)

variable {X : Type*} [TopologicalSpace X]

def interpolationHomotopy (f g : C(X, Hyperboloid E)) : ContinuousMap.Homotopy f g where
  toFun p := interpolate p.1 (f p.2) (g p.2)
  continuous_toFun := continuous_interpolate.comp
    (continuous_fst.prodMk ((f.continuous.comp continuous_snd).prodMk
      (g.continuous.comp continuous_snd)))
  map_zero_left x := interpolate_zero (f x) (g x)
  map_one_left x := interpolate_one (f x) (g x)

@[simp] theorem interpolationHomotopy_apply (f g : C(X, Hyperboloid E))
    (t : unitInterval) (x : X) :
    interpolationHomotopy f g (t, x) = interpolate t (f x) (g x) := rfl

theorem interpolationHomotopy_equivariant {G K : Type*} [SMul G X] [Group K]
    [MulAction K (Hyperboloid E)] [IsIsometricSMul K (Hyperboloid E)]
    (f g : C(X, Hyperboloid E)) (φ : G → K)
    (hf : ∀ γ x, f (γ • x) = φ γ • f x)
    (hg : ∀ γ x, g (γ • x) = φ γ • g x)
    (t : unitInterval) (γ : G) (x : X) :
    interpolationHomotopy f g (t, γ • x) = φ γ • interpolationHomotopy f g (t, x) := by
  simp only [interpolationHomotopy_apply, hf, hg]
  exact (isometryEquiv_interpolate (IsometryEquiv.constSMul (φ γ)) t (f x) (g x)).symm

end DifferentialGeometry.Hyperboloid
