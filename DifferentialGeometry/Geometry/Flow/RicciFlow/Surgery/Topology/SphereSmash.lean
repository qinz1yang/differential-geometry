import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FreeLoopClass
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation

noncomputable section
open Set
open scoped Topology unitInterval Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private def smashSphereNorth : Sphere 2 :=
  ⟨EuclideanSpace.single 2 1, by
    simp [Sphere, PiLp.norm_single]⟩


def sphereCircleWedge : Set (Sphere 2 × Circle) :=
  {p | p.1 = smashSphereNorth ∨ p.2 = 0}

def sphereCircleSmashSetoid : Setoid (Sphere 2 × Circle) where
  r a b := a = b ∨ (a ∈ sphereCircleWedge ∧ b ∈ sphereCircleWedge)
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr ⟨hab.1, hbc.2⟩


abbrev SphereCircleSmash := Quotient sphereCircleSmashSetoid

def sphereCircleSmashQuotient : C(Sphere 2 × Circle, SphereCircleSmash) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

def sphereCircleSmashBase : SphereCircleSmash :=
  sphereCircleSmashQuotient (smashSphereNorth, 0)


def cubeSphereCircleParameter : C(I^(Fin 3), Sphere 2 × Circle) where
  toFun z := (sphereCubeParameter ![z 0, z 1], ((z 2 : ℝ) : Circle))
  continuous_toFun := by
    apply Continuous.prodMk
    · exact sphereCubeParameter.continuous.comp (by fun_prop)
    · fun_prop

def smashCubeParameter : C(I^(Fin 3), SphereCircleSmash) :=
  sphereCircleSmashQuotient.comp cubeSphereCircleParameter

private def openCubeCoordinate (t : ℝ) : ℝ := (2 * t - 1) / (t * (1 - t))


def orientedSphereTwoInterior (x : EuclideanSpace ℝ (Fin 2)) : ThreeSpace :=
  let u := openCubeCoordinate (x 0)
  let v := openCubeCoordinate (x 1)
  WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
    (u^2+v^2-1) / (1+u^2+v^2)]

def orientedSphereThreeInterior (x : ThreeSpace) : EuclideanSpace ℝ (Fin 4) :=
  let u := openCubeCoordinate (x 0)
  let v := openCubeCoordinate (x 1)
  let w := openCubeCoordinate (x 2)
  WithLp.toLp 2 ![2*u / (1+u^2+v^2+w^2), 2*v / (1+u^2+v^2+w^2),
    2*w / (1+u^2+v^2+w^2), (u^2+v^2+w^2-1) / (1+u^2+v^2+w^2)]

def sphereThreeCubeVector (z : I^(Fin 3)) : EuclideanSpace ℝ (Fin 4) := by
  classical
  exact if z ∈ Cube.boundary (Fin 3) then EuclideanSpace.single 3 1 else
    orientedSphereThreeInterior (WithLp.toLp 2 (fun i => (z i : ℝ)))

theorem sphereThreeCubeVector_norm (z : I^(Fin 3)) : ‖sphereThreeCubeVector z‖ = 1 := by
  sorry

theorem sphereThreeCubeVector_continuous : Continuous sphereThreeCubeVector := by
  sorry

def sphereThreeCubeParameter : C(I^(Fin 3), Sphere 3) :=
  ⟨fun z => ⟨sphereThreeCubeVector z, by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereThreeCubeVector_norm z⟩,
    sphereThreeCubeVector_continuous.subtype_mk (fun z => by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using
        sphereThreeCubeVector_norm z)⟩

theorem exists_unique_standardSmashHomeomorph :
    ∃! e : SphereCircleSmash ≃ₜ Sphere 3,
      (⟨e, e.continuous⟩ : C(SphereCircleSmash, Sphere 3)).comp smashCubeParameter =
        sphereThreeCubeParameter := by
  sorry

def standardSmashHomeomorph : SphereCircleSmash ≃ₜ Sphere 3 :=
  Classical.choose exists_unique_standardSmashHomeomorph

theorem standardSmashHomeomorph_cube :
    (⟨standardSmashHomeomorph, standardSmashHomeomorph.continuous⟩ :
      C(SphereCircleSmash, Sphere 3)).comp smashCubeParameter = sphereThreeCubeParameter :=
  (Classical.choose_spec exists_unique_standardSmashHomeomorph).1


theorem sphereCubeParameter_interior (z : I^(Fin 2)) (hz : z ∉ Cube.boundary (Fin 2)) :
    (sphereCubeParameter z : ThreeSpace) =
      orientedSphereTwoInterior (WithLp.toLp 2 (fun i => (z i : ℝ))) := by
  classical
  simp [sphereCubeParameter, sphereCubeVector, hz, orientedSphereTwoInterior,
    openCubeCoordinate]


theorem sphereTwo_parameter_positive (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i : Fin 2, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereTwoInterior x ∧
      (0 : ℝ) < Matrix.det (fun i j : Fin 3 =>
        Fin.cases (orientedSphereTwoInterior x i)
          (fun k => (fderiv ℝ orientedSphereTwoInterior x
            (EuclideanSpace.single k 1)) i) j) := by
  sorry

theorem standardSmash_parameter_positive (x : ThreeSpace)
    (hx : ∀ i : Fin 3, x i ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ orientedSphereThreeInterior x ∧
      (0 : ℝ) < Matrix.det (fun i j : Fin 4 =>
        Fin.cases (orientedSphereThreeInterior x i)
          (fun k => (fderiv ℝ orientedSphereThreeInterior x
            (EuclideanSpace.single k 1)) i) j) := by
  sorry


theorem standardSmashHomeomorph_interior (z : I^(Fin 3))
    (hz : z ∉ Cube.boundary (Fin 3)) :
    (standardSmashHomeomorph (smashCubeParameter z) : EuclideanSpace ℝ (Fin 4)) =
      orientedSphereThreeInterior (WithLp.toLp 2 (fun i => (z i : ℝ))) := by
  have h := congrArg (fun f : C(I^(Fin 3), Sphere 3) => (f z : EuclideanSpace ℝ (Fin 4)))
    standardSmashHomeomorph_cube
  dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, sphereThreeCubeParameter] at h
  simpa [sphereThreeCubeVector, hz] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
