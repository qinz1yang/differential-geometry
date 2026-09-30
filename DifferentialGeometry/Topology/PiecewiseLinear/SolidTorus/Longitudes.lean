import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingLongitudes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingInTubeModel
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy

open Set DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem CarriesFundamentalGroupOnto.not_nullhomotopic_inclusion_in_solid_torus
    {X : Type*} [TopologicalSpace X] {J S : Set X}
    (hcarry : CarriesFundamentalGroupOnto J S) (hJ : J.Nonempty)
    (hS : IsTopologicalSolidTorus S) (hJS : J ⊆ S) :
    ¬ (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic := by
  intro hn
  obtain ⟨x, hx⟩ := hJ
  let i : C(J, S) := ⟨inclusion hJS, continuous_inclusion hJS⟩
  let e := hS.fundamentalGroupEquivInt (i ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := hcarry.2 hJS ⟨x, hx⟩ (e.symm (Multiplicative.ofAdd (1 : ℤ)))
  have hone := fundamentalGroup_map_eq_one_of_nullhomotopic i hn ⟨x, hx⟩ a
  have hbad := congrArg (fun z => (e z).toAdd) (ha.symm.trans hone)
  rw [MulEquiv.apply_symm_apply, e.map_one] at hbad
  exact (one_ne_zero : (1 : ℤ) ≠ 0) hbad

theorem IsPLHomeomorphInto.not_nullhomotopic_model_longitude_of_carrying_image
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C J : Set (EuclideanSpace ℝ (Fin 3))} {S : Set M}
    {u : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P) (hJ : J.Nonempty) (hJC : J ⊆ C)
    (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    (hcarry : CarriesFundamentalGroupOnto (u '' J) S) :
    ¬ (⟨inclusion hJC, continuous_inclusion hJC⟩ : C(J, C)).Nullhomotopic := by
  have huC := (hu.isPLOn.mono_of_isPolyhedron hC.isPolyhedron hCP).isPLHomeomorphInto_model
    hC.isPolyhedron.isCompact (hu.injOn.mono hCP)
  have himage : IsTopologicalSolidTorus (u '' C) :=
    hC.1.image_of_continuousOn_injOn huC.continuousOn huC.injOn
  have hcarry' := hcarry.of_intermediate_solid_torus himage hS (image_mono hJC) hCS
  have hmodel := huC.carriesFundamentalGroupOnto_of_image_of_subset hC.isPolyhedron.isCompact hJC hcarry'
  exact hmodel.not_nullhomotopic_inclusion_in_solid_torus hJ hC.1 hJC

end DifferentialGeometry.Topology.PiecewiseLinear
