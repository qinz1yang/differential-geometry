/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.EuclideanCharts
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.HorosphericalGenerators
import Mathlib.Topology.Separation.CompletelyRegular

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryMeasure

open HyperbolicBoundary BoundaryTopology MobiusBoundary Horospherical
open EuclideanBoundary GeodesicFlow LorentzGenerators

variable {n m : ℕ}

instance : MeasurableSpace (BoundaryH n) := borel _
instance : BorelSpace (BoundaryH n) := ⟨rfl⟩

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

theorem measurableEmbedding_embed :
    MeasurableEmbedding (embed : Horizontal m → BoundaryH (m + 1)) :=
  continuous_embed.measurableEmbedding embed_injective

def boundaryMeasure (m : ℕ) : Measure (BoundaryH (m + 1)) :=
  (volume : Measure (Horizontal m)).map embed

instance : SFinite (boundaryMeasure m) := by
  unfold boundaryMeasure
  infer_instance

theorem boundaryMeasure_apply {U : Set (BoundaryH (m + 1))} (hU : MeasurableSet U) :
    boundaryMeasure m U = volume (embed ⁻¹' U) :=
  Measure.map_apply measurableEmbedding_embed.measurable hU

theorem boundaryMeasure_infty : boundaryMeasure m {ptInfty} = 0 := by
  rw [boundaryMeasure_apply (measurableSet_singleton _)]
  have he : (embed : Horizontal m → BoundaryH (m + 1)) ⁻¹' {ptInfty} = ∅ := by
    ext x
    simp [embed_ne_infty]
  rw [he, measure_empty]

theorem translation_embed (x y : Horizontal m) :
    translation (fun i => x i) • embed y = embed (y + x) :=
  translation_horo _ _

theorem continuous_horizontal_translation :
    Continuous (fun x : Horizontal m => (translation (fun i => x i) : IsometryGroup m)) :=
  continuous_translation.comp (EuclideanSpace.equiv (Fin m) ℝ).continuous

theorem orbit_away_infty_ne_zero (ξ : BoundaryH (m + 1)) :
    volume {g : IsometryGroup m | g • ξ ≠ ptInfty} ≠ 0 := by
  apply IsOpen.measure_ne_zero
  · exact isClosed_singleton.isOpen_compl.preimage
      (continuous_id.smul continuous_const)
  · obtain ⟨a, ha⟩ := CuspCharts.exists_normalizing_element ξ
    refine ⟨inversion * a, ?_⟩
    change (inversion * a) • ξ ≠ ptInfty
    change a • ξ = ptInfty at ha
    rw [mul_smul, ha, inversion_infty]
    exact horo_ne_ptInfty _

theorem haar_orbit_embed_null_iff (ξ : BoundaryH (m + 1))
    {S : Set (Horizontal m)} (hS : MeasurableSet S) :
    volume {g : IsometryGroup m | g • ξ ∈ embed '' S} = 0 ↔ volume S = 0 := by
  classical
  let U := embed '' S
  have hU : MeasurableSet U := measurableEmbedding_embed.measurableSet_image.mpr hS
  have hm : MeasurableSet {p : Horizontal m × IsometryGroup m |
      (translation (fun i => p.1 i) * p.2) • ξ ∈ U} :=
    ((continuous_horizontal_translation.comp continuous_fst).mul continuous_snd
      |>.smul continuous_const).measurable hU
  have hleft (x : Horizontal m) :
      volume {g : IsometryGroup m | (translation (fun i => x i) * g) • ξ ∈ U} =
        volume {g : IsometryGroup m | g • ξ ∈ U} :=
    measure_preimage_mul (volume : Measure (IsometryGroup m))
      (translation (fun i => x i)) {g : IsometryGroup m | g • ξ ∈ U}
  have hright (g : IsometryGroup m) :
      volume {x : Horizontal m | (translation (fun i => x i) * g) • ξ ∈ U} =
        if g • ξ = ptInfty then 0 else volume S := by
    by_cases hg : g • ξ = ptInfty
    · rw [ite_eq_left hg]
      have he : {x : Horizontal m | (translation (fun i => x i) * g) • ξ ∈ U} = ∅ := by
        ext x
        simp [mul_smul, hg, translation_infty, U, embed_ne_infty]
      rw [he, measure_empty]
    · rw [ite_eq_right hg]
      have he : {x : Horizontal m | (translation (fun i => x i) * g) • ξ ∈ U} =
          (fun x : Horizontal m => coords (g • ξ) + x) ⁻¹' S := by
        ext x
        change (translation (fun i => x i) * g) • ξ ∈ embed '' S ↔
          coords (g • ξ) + x ∈ S
        rw [mul_smul]
        conv_lhs => rw [← embed_coords hg, translation_embed]
        exact embed_injective.mem_set_image
      rw [he, measure_preimage_add]
  constructor
  · intro h
    have hprod : (volume : Measure (Horizontal m)).prod volume
        {p : Horizontal m × IsometryGroup m |
          (translation (fun i => p.1 i) * p.2) • ξ ∈ U} = 0 := by
      apply measure_prod_null_of_ae_null hm
      exact Eventually.of_forall (fun x => (hleft x).trans h)
    have hswap : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
        volume {x : Horizontal m | (translation (fun i => x i) * g) • ξ ∈ U} = 0 :=
      measure_ae_null_of_prod_null ((Measure.measurePreserving_swap).measure_preimage
        hm.nullMeasurableSet |>.trans hprod)
    by_contra hSzero
    have hbad : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)), g • ξ = ptInfty := by
      filter_upwards [hswap] with g hg
      rw [hright] at hg
      by_contra hne
      rw [ite_eq_right hne] at hg
      exact hSzero hg
    exact orbit_away_infty_ne_zero ξ hbad
  · intro h
    have hr : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
        ∀ᵐ x ∂(volume : Measure (Horizontal m)),
          (translation (fun i => x i) * g) • ξ ∉ U := by
      apply Eventually.of_forall
      intro g
      apply measure_eq_zero_iff_ae_notMem.mp
      change volume {x : Horizontal m | (translation (fun i => x i) * g) • ξ ∈ U} = 0
      rw [hright, h]
      simp
    have hl := (ae_ae_comm hm.compl).mpr hr
    obtain ⟨x, hx⟩ := hl.exists
    exact (hleft x).symm.trans (measure_eq_zero_iff_ae_notMem.mpr hx)

variable [Nonempty (Fin m)]

instance : NullSingletonClass (boundaryMeasure m) where
  measure_singleton v := by
    rw [boundaryMeasure_apply (measurableSet_singleton _)]
    exact (subsingleton_singleton.preimage embed_injective).measure_zero volume

instance : NeZero (boundaryMeasure m) :=
  ⟨(Measure.map_ne_zero_iff measurableEmbedding_embed.measurable.aemeasurable).mpr
    (NeZero.ne (volume : Measure (Horizontal m)))⟩

theorem haar_orbit_infty_null (ξ : BoundaryH (m + 1)) :
    volume {g : IsometryGroup m | g • ξ = ptInfty} = 0 := by
  have hz : volume {g : IsometryGroup m | g • ξ = embed (0 : Horizontal m)} = 0 := by
    simpa only [image_singleton, mem_singleton_iff] using
      (haar_orbit_embed_null_iff ξ (measurableSet_singleton (0 : Horizontal m))).mpr
        (measure_singleton _)
  have he : {g : IsometryGroup m | g • ξ = ptInfty} =
      (fun g : IsometryGroup m => inversion * g) ⁻¹'
        {g : IsometryGroup m | g • ξ = embed (0 : Horizontal m)} := by
    ext g
    change g • ξ = ptInfty ↔ (inversion * g) • ξ = embed (0 : Horizontal m)
    rw [mul_smul, show embed (0 : Horizontal m) = inversion • ptInfty from inversion_infty.symm]
    exact (MulAction.injective (inversion : IsometryGroup m)).eq_iff.symm
  rw [he, measure_preimage_mul, hz]

theorem haar_orbit_null_iff (ξ : BoundaryH (m + 1))
    {U : Set (BoundaryH (m + 1))} (hU : MeasurableSet U) :
    volume {g : IsometryGroup m | g • ξ ∈ U} = 0 ↔ boundaryMeasure m U = 0 := by
  rw [boundaryMeasure_apply hU]
  have hc := haar_orbit_embed_null_iff ξ (measurableEmbedding_embed.measurable hU)
  constructor
  · intro h
    apply hc.mp
    apply measure_mono_null _ h
    intro g hg
    obtain ⟨x, hx, he⟩ := hg
    change g • ξ ∈ U
    exact he ▸ hx
  · intro h
    apply measure_mono_null _ (measure_union_null (hc.mpr h) (haar_orbit_infty_null ξ))
    intro g hg
    change g • ξ ∈ U at hg
    by_cases hξ : g • ξ = ptInfty
    · exact Or.inr hξ
    · exact Or.inl ⟨coords (g • ξ), by simpa only [mem_preimage, embed_coords hξ] using hg,
        embed_coords hξ⟩

theorem haar_orbit_ae_iff (ξ : BoundaryH (m + 1)) {P : BoundaryH (m + 1) → Prop}
    (hP : MeasurableSet {v | P v}) :
    (∀ᵐ g ∂(volume : Measure (IsometryGroup m)), P (g • ξ)) ↔
      ∀ᵐ v ∂boundaryMeasure m, P v :=
  haar_orbit_null_iff ξ hP.compl

theorem quasiMeasurePreserving_orbit (ξ : BoundaryH (m + 1)) :
    QuasiMeasurePreserving (fun g : IsometryGroup m => g • ξ) volume (boundaryMeasure m) := by
  have hm : Measurable (fun g : IsometryGroup m => g • ξ) :=
    (continuous_id.smul continuous_const).measurable
  refine ⟨hm, AbsolutelyContinuous.mk fun U hU hzero => ?_⟩
  rw [Measure.map_apply hm hU]
  exact (haar_orbit_null_iff ξ hU).mpr hzero

theorem boundaryMeasure_smul_null_iff (g : IsometryGroup m)
    {U : Set (BoundaryH (m + 1))} (hU : MeasurableSet U) :
    boundaryMeasure m ((fun v : BoundaryH (m + 1) => g • v) ⁻¹' U) = 0 ↔
      boundaryMeasure m U = 0 := by
  rw [← haar_orbit_null_iff ptInfty ((continuous_const_smul g).measurable hU),
    ← haar_orbit_null_iff ptInfty hU]
  have he := measure_preimage_mul (volume : Measure (IsometryGroup m)) g
    {h : IsometryGroup m | h • (ptInfty : BoundaryH (m + 1)) ∈ U}
  have he' : volume {h : IsometryGroup m | g • h • (ptInfty : BoundaryH (m + 1)) ∈ U} =
      volume {h : IsometryGroup m | h • ptInfty ∈ U} := by
    simpa only [preimage, mem_ofPred_eq, mul_smul] using he
  change volume {h : IsometryGroup m | g • h • (ptInfty : BoundaryH (m + 1)) ∈ U} = 0 ↔ _
  rw [he']

theorem quasiMeasurePreserving_smul (g : IsometryGroup m) :
    QuasiMeasurePreserving (fun v : BoundaryH (m + 1) => g • v)
      (boundaryMeasure m) (boundaryMeasure m) := by
  refine ⟨(continuous_const_smul g).measurable, AbsolutelyContinuous.mk fun U hU hzero => ?_⟩
  rw [Measure.map_apply (continuous_const_smul g).measurable hU]
  exact (boundaryMeasure_smul_null_iff g hU).mpr hzero

theorem chart_smul_null_iff (g : IsometryGroup m)
    {U : Set (BoundaryH (m + 1))} (hU : MeasurableSet U) :
    volume {x : Horizontal m | g • embed x ∈ U} = 0 ↔ boundaryMeasure m U = 0 := by
  change volume (embed ⁻¹' ((fun v : BoundaryH (m + 1) => g • v) ⁻¹' U)) = 0 ↔ _
  rw [← boundaryMeasure_apply ((continuous_const_smul g).measurable hU)]
  exact boundaryMeasure_smul_null_iff g hU

def endpointPair (g : IsometryGroup m) : BoundaryH (m + 1) × BoundaryH (m + 1) :=
  (g • ptInfty, g • embed (0 : Horizontal m))

omit [Nonempty (Fin m)] in
theorem continuous_endpointPair : Continuous (endpointPair (m := m)) :=
  (continuous_id.smul continuous_const).prodMk (continuous_id.smul continuous_const)

omit [Nonempty (Fin m)] in
theorem endpointPair_ne (g : IsometryGroup m) : (endpointPair g).1 ≠ (endpointPair g).2 :=
  fun h => embed_ne_infty (0 : Horizontal m) ((MulAction.injective g h).symm)

theorem boundaryPair_diagonal_null :
    ((boundaryMeasure m).prod (boundaryMeasure m))
      {p : BoundaryH (m + 1) × BoundaryH (m + 1) | p.1 = p.2} = 0 := by
  apply measure_prod_null_of_ae_null (measurableSet_eq_fun measurable_fst measurable_snd)
  apply Eventually.of_forall
  intro v
  change boundaryMeasure m {w | v = w} = 0
  rw [show {w | v = w} = {v} from by ext w; exact eq_comm]
  exact measure_singleton v

variable [IsMulRightInvariant (volume : Measure (IsometryGroup m))]

theorem haar_endpointPair_null_iff {U : Set (BoundaryH (m + 1) × BoundaryH (m + 1))}
    (hU : MeasurableSet U) :
    volume (endpointPair ⁻¹' U) = 0 ↔
      ((boundaryMeasure m).prod (boundaryMeasure m)) U = 0 := by
  have hm : MeasurableSet {p : Horizontal m × IsometryGroup m |
      (p.2 • (ptInfty : BoundaryH (m + 1)), p.2 • embed p.1) ∈ U} :=
    ((continuous_snd.smul continuous_const).prodMk
      (continuous_snd.smul (continuous_embed.comp continuous_fst))).measurable hU
  have hleft (x : Horizontal m) :
      volume {g : IsometryGroup m | (g • ptInfty, g • embed x) ∈ U} =
        volume (endpointPair ⁻¹' U) := by
    have he : {g : IsometryGroup m | (g • ptInfty, g • embed x) ∈ U} =
        (fun g : IsometryGroup m => g * translation (fun i => x i)) ⁻¹'
          (endpointPair ⁻¹' U) := by
      ext g
      simp only [mem_preimage, mem_ofPred_eq, endpointPair, mul_smul, translation_infty,
        translation_embed, zero_add]
    rw [he, measure_preimage_mul_right]
  have hsection (v : BoundaryH (m + 1)) : MeasurableSet {w | (v, w) ∈ U} :=
    (measurable_const.prodMk measurable_id) hU
  have hright (g : IsometryGroup m) :
      volume {x : Horizontal m | (g • ptInfty, g • embed x) ∈ U} = 0 ↔
        boundaryMeasure m {w | (g • ptInfty, w) ∈ U} = 0 :=
    chart_smul_null_iff g (hsection _)
  have hequiv : volume (endpointPair ⁻¹' U) = 0 ↔
      ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
        boundaryMeasure m {w | (g • ptInfty, w) ∈ U} = 0 := by
    constructor
    · intro h
      have hl : ∀ᵐ x ∂(volume : Measure (Horizontal m)),
          ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
            (g • ptInfty, g • embed x) ∉ U :=
        Eventually.of_forall fun x => measure_eq_zero_iff_ae_notMem.mp ((hleft x).trans h)
      exact ((ae_ae_comm hm.compl).mp hl).mono fun g hg =>
        (hright g).mp (measure_eq_zero_iff_ae_notMem.mpr hg)
    · intro h
      have hr : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
          ∀ᵐ x ∂(volume : Measure (Horizontal m)),
            (g • ptInfty, g • embed x) ∉ U :=
        h.mono fun g hg => measure_eq_zero_iff_ae_notMem.mp ((hright g).mpr hg)
      obtain ⟨x, hx⟩ := ((ae_ae_comm hm.compl).mpr hr).exists
      exact (hleft x).symm.trans (measure_eq_zero_iff_ae_notMem.mpr hx)
  exact hequiv.trans ((haar_orbit_ae_iff ptInfty
    (measurableSet_eq_fun (measurable_measure_prodMk_left (ν := boundaryMeasure m) hU)
      (measurable_const (a := (0 : ENNReal))))).trans (measure_prod_null hU).symm)

end DifferentialGeometry.BoundaryMeasure
