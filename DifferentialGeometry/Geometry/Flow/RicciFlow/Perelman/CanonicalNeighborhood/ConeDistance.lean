import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs
import DifferentialGeometry.Topology.Compactness.MapLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Homeomorph.Lemmas

section

noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {Y : Type*} [MetricSpace Y]

theorem openConeDistance_sq {z w : ℝ × Y} (hz : 0 ≤ z.1) (hw : 0 ≤ w.1) :
    openConeDistance z w ^ 2 =
      z.1 ^ 2 + w.1 ^ 2 - 2 * z.1 * w.1 * Real.cos (min Real.pi (dist z.2 w.2)) := by
  apply Real.sq_sqrt
  have hcos := Real.cos_le_one (min Real.pi (dist z.2 w.2))
  have hmul := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * z.1 * w.1 by positivity)
  nlinarith [sq_nonneg (z.1 - w.1)]

theorem radial_sq_eq_of_openConeDistance {z : ℝ × Y} {a b : ℝ}
    (hz : 0 ≤ z.1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) (q : Y) :
    z.1 ^ 2 =
      (b * openConeDistance z (a, q) ^ 2 - a * openConeDistance z (b, q) ^ 2) / (b - a) + a * b := by
  rw [openConeDistance_sq hz ha, openConeDistance_sq hz hb]
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [hne]
  ring

theorem sub_radial_le_openConeDistance {z w : ℝ × Y}
    (hz : 0 ≤ z.1) (hw : 0 ≤ w.1) :
    w.1 - z.1 ≤ openConeDistance z w := by
  have hs := openConeDistance_sq hz hw
  have hd : 0 ≤ openConeDistance z w := Real.sqrt_nonneg _
  have hcos := Real.cos_le_one (min Real.pi (dist z.2 w.2))
  have hmul := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * z.1 * w.1 by positivity)
  nlinarith [sq_nonneg (openConeDistance z w - (w.1 - z.1))]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {Y : Type*} [MetricSpace Y]

theorem continuous_openConeDistance :
    Continuous (fun p : (ℝ × Y) × (ℝ × Y) => openConeDistance p.1 p.2) := by
  unfold openConeDistance
  fun_prop


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {Y : Type*} [MetricSpace Y]

theorem openConeDistance_eq_zero_iff {z w : ℝ × Y} (hz : 0 < z.1) (hw : 0 < w.1) :
    openConeDistance z w = 0 ↔ z = w := by
  constructor
  · intro h
    have hs := openConeDistance_sq hz.le hw.le
    rw [h, zero_pow (by decide)] at hs
    have hc := Real.cos_le_one (min Real.pi (dist z.2 w.2))
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * z.1 * w.1 by positivity)
    have hr : z.1 = w.1 := by nlinarith [sq_nonneg (z.1 - w.1)]
    have hfactor : 2 * z.1 * w.1 ≠ 0 := ne_of_gt (by positivity)
    have hcos : Real.cos (min Real.pi (dist z.2 w.2)) = 1 := by
      have hmul : (2 * z.1 * w.1) * (1 - Real.cos (min Real.pi (dist z.2 w.2))) = 0 := by
        nlinarith [hs]
      have := (mul_eq_zero.mp hmul).resolve_left hfactor
      linarith
    have hangle : min Real.pi (dist z.2 w.2) = 0 := by
      apply (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp hcos
      · exact lt_of_lt_of_le (by linarith [Real.pi_pos])
          (le_min Real.pi_pos.le dist_nonneg)
      · exact (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
    have hang : z.2 = w.2 := by
      by_contra hne
      have hh := lt_min Real.pi_pos (dist_pos.mpr hne)
      rw [hangle] at hh
      exact lt_irrefl 0 hh
    exact Prod.ext hr hang
  · rintro rfl
    unfold openConeDistance
    simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
    rw [show z.1 ^ 2 + z.1 ^ 2 - 2 * z.1 * z.1 = 0 by ring, Real.sqrt_zero]


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]
  {T : Type*} [MetricSpace T] {a b lambda : ℝ}

theorem isEmbedding_of_scaled_cone_distance
    (ha : 0 < a) (hlambda : 0 < lambda) (D : Set (ℝ × Y))
    (hD : ∀ x ∈ D, x.1 ∈ Icc a b)
    (F : D → T)
    (hmetric : ∀ x y : D, dist (F x) (F y) =
      lambda * openConeDistance (x : ℝ × Y) (y : ℝ × Y)) :
    Topology.IsEmbedding F := by
  have hself (x : D) : openConeDistance (x : ℝ × Y) (x : ℝ × Y) = 0 :=
    (openConeDistance_eq_zero_iff (ha.trans_le (hD x x.property).1)
      (ha.trans_le (hD x x.property).1)).mpr rfl
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hc : Continuous (fun y : D => lambda * openConeDistance (y : ℝ × Y) (x : ℝ × Y)) :=
      continuous_const.mul (continuous_openConeDistance.comp
        (continuous_subtype_val.prodMk continuous_const))
    simpa only [hmetric, hself, mul_zero] using hc.tendsto x
  have hinj : Function.Injective F := by
    intro x y hxy
    have h := hmetric x y
    rw [hxy, dist_self] at h
    have hz : openConeDistance (x : ℝ × Y) (y : ℝ × Y) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left hlambda.ne'
    exact Subtype.ext ((openConeDistance_eq_zero_iff (ha.trans_le (hD x x.property).1)
      (ha.trans_le (hD y y.property).1)).mp hz)
  let e : D ≃ range F := Equiv.ofInjective F hinj
  let B := Icc a b × Y
  let P : B → ℝ × Y := fun z => (z.1.1, z.2)
  let inv : range F → B := fun z => (⟨((e.symm z : D) : ℝ × Y).1,
    hD (e.symm z) (e.symm z).property⟩, ((e.symm z : D) : ℝ × Y).2)
  have hP : Continuous P := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hback (z : range F) : F (e.symm z) = (z : T) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hinv : Continuous inv := by
    apply Topology.continuous_of_compact_separating_kernel
      (fun z : B × B => lambda * openConeDistance (P z.1) (P z.2))
      (continuous_const.mul (continuous_openConeDistance.comp
        ((hP.comp continuous_fst).prodMk (hP.comp continuous_snd))))
      ?_ inv ?_
    · intro x y h
      have hz := (mul_eq_zero.mp h).resolve_left hlambda.ne'
      have heq := (openConeDistance_eq_zero_iff (ha.trans_le x.1.2.1)
        (ha.trans_le y.1.2.1)).mp hz
      change ((x.1.1, x.2) : ℝ × Y) = (y.1.1, y.2) at heq
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
        (congrArg (fun z : ℝ × Y => z.2) heq)
    · intro x y
      change lambda * openConeDistance ((e.symm x : D) : ℝ × Y)
        ((e.symm y : D) : ℝ × Y) = dist (x : T) (y : T)
      rw [← hmetric, hback, hback]
  have hinve : Continuous (e.symm : range F → D) := by
    apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
    exact hP.comp hinv
  let he : D ≃ₜ range F := { e with
    continuous_toFun := hcont.subtype_mk (fun x => mem_range_self x)
    continuous_invFun := hinve }
  exact Topology.IsEmbedding.subtypeVal.comp he.isEmbedding

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]
  {T : Type*} [MetricSpace T] [CompactSpace T] {a b lambda : ℝ}

theorem exists_marked_cone_embedding_of_compact_pair_limits
    (ha : 0 < a) (hlambda : 0 < lambda) (D : Set (ℝ × Y))
    (hD : ∀ x ∈ D, x.1 ∈ Icc a b)
    (u : ℕ → D → T)
    (hpair : ∀ x y : D, Tendsto (fun i => dist (u i x) (u i y)) atTop
      (𝓝 (lambda * openConeDistance (x : ℝ × Y) (y : ℝ × Y))))
    (o : D) (q : T) (hbase : Tendsto (fun i => dist (u i o) q) atTop (𝓝 0)) :
    ∃ F : D → T, MapClusterPt F atTop u ∧ Topology.IsEmbedding F ∧ F o = q ∧
      ∀ x y : D, dist (F x) (F y) =
        lambda * openConeDistance (x : ℝ × Y) (y : ℝ × Y) := by
  obtain ⟨F, hF, hmetric⟩ := Topology.exists_mapClusterPt_of_continuous_pairwise_limits u
    (fun p : T × T => dist p.1 p.2) (continuous_fst.dist continuous_snd)
    (fun x y : D => lambda * openConeDistance (x : ℝ × Y) (y : ℝ × Y)) hpair
  refine ⟨F, hF, isEmbedding_of_scaled_cone_distance ha hlambda D hD F hmetric, ?_, hmetric⟩
  have hobs : Continuous (fun G : D → T => dist (G o) q) :=
    (continuous_apply o).dist continuous_const
  have hc := hF.continuousAt_comp hobs.continuousAt
  apply dist_eq_zero.mp
  exact eq_of_nhds_neBot (hc.clusterPt.mono hbase)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
