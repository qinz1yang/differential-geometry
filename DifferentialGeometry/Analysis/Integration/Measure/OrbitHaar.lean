import DifferentialGeometry.Topology.GroupAction.OrbitSection
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Tactic.Group

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal

namespace MulAction

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

private def stabilizerCocycle (o : X) (s : X → G) (hs : ∀ x, s x • o = x)
    (a : G) (x : X) : stabilizer G o :=
  ⟨(s (a • x))⁻¹ * a * s x, by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, hs]
    calc
      (s (a • x))⁻¹ • (a • x) = (s (a • x))⁻¹ • (s (a • x) • o) :=
        congrArg (fun y => (s (a • x))⁻¹ • y) (hs (a • x)).symm
      _ = o := inv_smul_smul _ _⟩

private theorem continuous_stabilizerCocycle (o : X) (s : X → G)
    (hs : ∀ x, s x • o = x) (hc : Continuous s) (a : G) :
    Continuous (stabilizerCocycle o s hs a) :=
  (((hc.comp (continuous_const.smul continuous_id)).inv.mul continuous_const).mul hc).subtype_mk _

private theorem orbitSectionHomeomorph_cocycle (o : X) (s : X → G)
    (hs : ∀ x, s x • o = x) (hc : Continuous s)
    (a : G) (x : X) (k : stabilizer G o) :
    orbitSectionHomeomorph o s hs hc (a • x, stabilizerCocycle o s hs a x * k) =
      a * orbitSectionHomeomorph o s hs hc (x, k) := by
  change s (a • x) * (((s (a • x))⁻¹ * a * s x) * (k : G)) = a * (s x * (k : G))
  group

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology G] [SecondCountableTopology X]

omit [SecondCountableTopology G] in
theorem isMulLeftInvariant_map_orbitSectionHomeomorph (o : X) (s : X → G)
    (hs : ∀ x, s x • o = x) (hc : Continuous s)
    (μ : Measure X) (ν : Measure (stabilizer G o))
    [SFinite μ] [SFinite ν] [SMulInvariantMeasure G X μ] [IsMulLeftInvariant ν] :
    IsMulLeftInvariant ((μ.prod ν).map (orbitSectionHomeomorph o s hs hc)) where
  map_mul_left_eq_self a := by
    let T := orbitSectionHomeomorph o s hs hc
    let R : X × stabilizer G o → X × stabilizer G o :=
      fun z => (a • z.1, stabilizerCocycle o s hs a z.1 * z.2)
    have hR : MeasurePreserving R (μ.prod ν) (μ.prod ν) :=
      (measurePreserving_smul a μ).skew_product
        (((continuous_stabilizerCocycle o s hs hc a).comp continuous_fst).mul
          continuous_snd).measurable
        (Filter.Eventually.of_forall fun x =>
          (measurePreserving_mul_left ν (stabilizerCocycle o s hs a x)).map_eq)
    have heq : (fun g : G => a * g) ∘ T = T ∘ R := by
      funext z
      exact (orbitSectionHomeomorph_cocycle o s hs hc a z.1 z.2).symm
    change Measure.map (fun g : G => a * g) ((μ.prod ν).map T) = (μ.prod ν).map T
    rw [Measure.map_map (measurable_const_mul a) T.continuous.measurable, heq,
      ← Measure.map_map T.continuous.measurable hR.measurable, hR.map_eq]

omit [SecondCountableTopology G] in
theorem map_orbit_map_orbitSectionHomeomorph (o : X) (s : X → G)
    (hs : ∀ x, s x • o = x) (hc : Continuous s)
    (μ : Measure X) (ν : Measure (stabilizer G o)) [SFinite ν] :
    Measure.map (fun g : G => g • o)
      ((μ.prod ν).map (orbitSectionHomeomorph o s hs hc)) = (ν Set.univ) • μ := by
  let T := orbitSectionHomeomorph o s hs hc
  have heq : (fun g : G => g • o) ∘ T = Prod.fst := by
    funext z
    change (s z.1 * (z.2 : G)) • o = z.1
    rw [mul_smul, show (z.2 : G) • o = o from z.2.property, hs]
  change Measure.map (fun g : G => g • o) ((μ.prod ν).map T) = _
  have hmeas : Measurable (fun g : G => g • o) :=
    (continuous_id.smul continuous_const).measurable
  rw [Measure.map_map hmeas T.continuous.measurable, heq, Measure.map_fst_prod]

theorem exists_pos_map_haar_orbit_eq_smul [LocallyCompactSpace G]
    (o : X) [CompactSpace (stabilizer G o)] (s : X → G)
    (hs : ∀ x, s x • o = x) (hc : Continuous s)
    (μG : Measure G) [IsHaarMeasure μG]
    (μ : Measure X) [SFinite μ] [SMulInvariantMeasure G X μ]
    [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ] :
    ∃ c : ℝ≥0, 0 < c ∧ Measure.map (fun g : G => g • o) μG = c • μ := by
  let K := stabilizer G o
  let K₀ : TopologicalSpace.PositiveCompacts K := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν : Measure K := Measure.haarMeasure K₀
  let : IsHaarMeasure ν := inferInstance
  let : IsProbabilityMeasure ν := ⟨by exact Measure.haarMeasure_self (K₀ := K₀)⟩
  let T := orbitSectionHomeomorph o s hs hc
  let η : Measure G := (μ.prod ν).map T
  let : IsMulLeftInvariant η := isMulLeftInvariant_map_orbitSectionHomeomorph o s hs hc μ ν
  let : IsFiniteMeasureOnCompacts η := IsFiniteMeasureOnCompacts.map (μ.prod ν) T
  let : IsOpenPosMeasure η := T.continuous.isOpenPosMeasure_map T.surjective
  let : IsHaarMeasure η :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  let c : ℝ≥0 := Measure.haarScalarFactor μG η
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hhaar : μG = c • η :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have horbit : Measure.map (fun g : G => g • o) η = μ := by
    have h := map_orbit_map_orbitSectionHomeomorph o s hs hc μ ν
    simpa only [measure_univ, one_smul] using h
  refine ⟨c, hcpos, ?_⟩
  have hmeas : Measurable (fun g : G => g • o) :=
    (continuous_id.smul continuous_const).measurable
  rw [hhaar, Measure.map_smul _ hmeas.aemeasurable, horbit]

end MulAction
