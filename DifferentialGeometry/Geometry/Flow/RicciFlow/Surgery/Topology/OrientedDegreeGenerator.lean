import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology

noncomputable section

open Bundle Manifold CategoryTheory AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

def orientedDegreeWith (zM : IntegralHomology M 3) (zN : IntegralHomology N 3)
    (hgenN : Function.Bijective (fun k : ℤ => k • zN)) (f : C(M, N)) : ℤ :=
  Classical.choose (hgenN.surjective (integralHomologyMap 3 f zM))

theorem orientedDegreeWith_spec (zM : IntegralHomology M 3) (zN : IntegralHomology N 3)
    (hgenN : Function.Bijective (fun k : ℤ => k • zN)) (f : C(M, N)) :
    integralHomologyMap 3 f zM = orientedDegreeWith zM zN hgenN f • zN :=
  (Classical.choose_spec (hgenN.surjective (integralHomologyMap 3 f zM))).symm

theorem orientedDegreeWith_eq_iff (zM : IntegralHomology M 3) (zN : IntegralHomology N 3)
    (hgenN : Function.Bijective (fun k : ℤ => k • zN)) (f : C(M, N)) (d : ℤ) :
    orientedDegreeWith zM zN hgenN f = d ↔
      integralHomologyMap 3 f zM = d • zN := by
  rw [orientedDegreeWith_spec]
  exact hgenN.injective.eq_iff.symm

section Charted

variable [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel ∞ N]

def IsFundamentalClass (o : TangentOrientationSection M) (z : IntegralHomology M 3) : Prop :=
  ∀ x : M, absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem orientedDegreeWith_eq_iff_forall_localOrientationClass
    (zM : IntegralHomology M 3) (zN : IntegralHomology N 3)
    (hgenN : Function.Bijective (fun k : ℤ => k • zN)) (f : C(M, N)) (d : ℤ)
    (oN : TangentOrientationSection N) (hzN : IsFundamentalClass oN zN) (y : N)
    (hinj : Function.Injective (absoluteToRelative N ({y}ᶜ) 3)) :
    orientedDegreeWith zM zN hgenN f = d ↔
      ∀ q : N, absoluteToRelative N ({q}ᶜ) 3 (integralHomologyMap 3 f zM) =
        d • localOrientationClass oN q := by
  rw [orientedDegreeWith_eq_iff]
  constructor
  · intro h q
    rw [h, map_zsmul, hzN q]
  · intro h
    apply hinj
    rw [map_zsmul, hzN y, h y]

def OrientedDegreeRelation (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (d : ℤ) : Prop :=
  ∃ zM : IntegralHomology M 3, ∃ zN : IntegralHomology N 3,
    IsFundamentalClass oM zM ∧ IsFundamentalClass oN zN ∧
      Function.Bijective (fun k : ℤ => k • zN) ∧
        integralHomologyMap 3 f zM = d • zN

theorem exists_orientedDegreeWith_eq_iff_orientedDegreeRelation
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N)
    (f : C(M, N)) (d : ℤ) :
    (∃ (zM : IntegralHomology M 3) (zN : IntegralHomology N 3)
      (hgenN : Function.Bijective (fun k : ℤ => k • zN)),
        IsFundamentalClass oM zM ∧ IsFundamentalClass oN zN ∧
          orientedDegreeWith zM zN hgenN f = d) ↔
      OrientedDegreeRelation oM oN f d := by
  constructor
  · rintro ⟨zM, zN, hgenN, hzM, hzN, h⟩
    exact ⟨zM, zN, hzM, hzN, hgenN, (orientedDegreeWith_eq_iff zM zN hgenN f d).mp h⟩
  · rintro ⟨zM', zN', hzM', hzN', hgenN', h⟩
    exact ⟨zM', zN', hgenN', hzM', hzN', (orientedDegreeWith_eq_iff zM' zN' hgenN' f d).mpr h⟩

end Charted

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
