import DifferentialGeometry.Topology.MetricSpace.FiniteFamilyIsometry
import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {L δ : ℕ → ι → ℝ} {R ε : ℕ → ℝ}

theorem exists_isometric_lines_of_signed_prefixes
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hLpos : ∀ i j, 0 ≤ L i j) (hL : ∀ j, Tendsto (fun i => L i j) atTop atTop)
    (hδ : ∀ j, Tendsto (fun i => δ i j) atTop (𝓝 0))
    (σ : ∀ i j, Icc (-(L i j)) (L i j) → A i)
    (hLip : ∀ i j, LipschitzWith 1 (σ i j))
    (hbase : ∀ i j, σ i j ⟨0, ⟨by linarith [hLpos i j], hLpos i j⟩⟩ = o i)
    (hlower : ∀ i j s t, |s.val - t.val| - δ i j ≤ dist (σ i j s) (σ i j t)) :
    ∃ (γ : ι → ℝ → Y) (φ : ℕ → ℕ),
      (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧ StrictMono φ ∧
      ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
        S ≤ R (φ i) ∧ ∀ j, S ≤ L (φ i) j ∧
        ∀ t : Icc (-(L (φ i) j)) (L (φ i) j), |t.val| ≤ S →
          ∀ ht : dist (σ (φ i) j t) (o (φ i)) ≤ R (φ i),
            dist ((f (φ i)).toFun ⟨σ (φ i) j t, ht⟩) (γ j t.val) < η := by
  classical
  let := Fintype.ofFinite ι
  let Δ : ℕ → ℝ := fun i => ‖δ i‖
  have hΔzero : Tendsto Δ atTop (𝓝 0) := by
    have hh : Tendsto δ atTop (𝓝 (0 : ι → ℝ)) := tendsto_pi_nhds.mpr hδ
    simpa only [norm_zero] using hh.norm
  have hδbound (i : ℕ) (j : ι) : δ i j ≤ Δ i := by
    exact (le_abs_self _).trans (norm_le_pi_norm (δ i) j)
  have hrad (i : ℕ) (j : ι) (t : Icc (-(L i j)) (L i j)) : dist (σ i j t) (o i) ≤ |t.val| := by
    have hh := (hLip i j).dist_le_mul t ⟨0, ⟨by linarith [hLpos i j], hLpos i j⟩⟩
    rw [hbase] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, sub_zero] using hh
  let g (i : ℕ) (j : ι) (t : ℝ) : Y :=
    if ht : |t| ≤ min (L i j) (R i) then
      (f i).toFun ⟨σ i j ⟨t, (abs_le.mp (ht.trans (min_le_left _ _)))⟩,
        (hrad i j _).trans (ht.trans (min_le_right _ _))⟩ else p
  have hg (i : ℕ) (j : ι) (t : Icc (-(L i j)) (L i j)) (ht : |t.val| ≤ R i) :
      g i j t.val = (f i).toFun ⟨σ i j t, (hrad i j t).trans ht⟩ := by
    have hh : |t.val| ≤ min (L i j) (R i) := le_min (abs_le.mpr t.property) ht
    simp only [g, dite_eq_left hh]
  have hgbase (i : ℕ) (j : ι) : g i j 0 = p := by
    have hRi : 0 ≤ R i := (f i).error_pos.le.trans (f i).error_lt_radius.le
    have hh := hg i j ⟨0, ⟨by linarith [hLpos i j], hLpos i j⟩⟩ (by simpa only [abs_zero] using hRi)
    rw [hh]
    have heq : (⟨σ i j ⟨0, ⟨by linarith [hLpos i j], hLpos i j⟩⟩, (hrad i j _).trans
        (by simpa only [abs_zero] using hRi)⟩ : BallCarrier (o i) (R i)) =
        ⟨o i, by simpa only [dist_self] using hRi⟩ := Subtype.ext (hbase i j)
    rw [heq]
    exact (f i).basepoint
  have hd : ∀ S : ℝ, ∀ᶠ i in atTop, ∀ j, ∀ s t : ℝ,
      dist s 0 ≤ S → dist t 0 ≤ S → |dist (g i j s) (g i j t) - dist s t| ≤ Δ i + ε i := by
    intro S
    filter_upwards [Filter.eventually_all.mpr (fun j => (hL j).eventually (eventually_ge_atTop S)),
      hR.eventually (eventually_ge_atTop S)]
      with i hiL hiR
    intro j s t hs ht
    rw [Real.dist_eq, sub_zero] at hs ht
    let ss : Icc (-(L i j)) (L i j) := ⟨s, abs_le.mp (hs.trans (hiL j))⟩
    let tt : Icc (-(L i j)) (L i j) := ⟨t, abs_le.mp (ht.trans (hiL j))⟩
    have hsR : |ss.val| ≤ R i := hs.trans hiR
    have htR : |tt.val| ≤ R i := ht.trans hiR
    have hgs := hg i j ss hsR
    have hgt := hg i j tt htR
    change g i j s = _ at hgs
    change g i j t = _ at hgt
    rw [hgs, hgt, Real.dist_eq]
    have hdist := (f i).distortion ⟨σ i j ss, (hrad i j ss).trans hsR⟩
      ⟨σ i j tt, (hrad i j tt).trans htR⟩
    have hlo := hlower i j ss tt
    have hhi := (hLip i j).dist_le_mul ss tt
    change dist (σ i j ss) (σ i j tt) ≤ 1 * |s-t| at hhi
    have hΔnonneg : 0 ≤ Δ i := norm_nonneg _
    have hδle := hδbound i j
    apply abs_le.mpr
    constructor <;> linarith [(abs_lt.mp hdist).1, (abs_lt.mp hdist).2]
  have hδε : Tendsto (fun i => Δ i + ε i) atTop (𝓝 0) := by
    simpa only [zero_add] using hΔzero.add hε
  obtain ⟨γ, φ, hγ, hγ0, hφ, huniform⟩ :=
    exists_isometry_family_subsequence_of_local_distortion g hgbase hδε hd
  refine ⟨γ, φ, hγ, hγ0, hφ, ?_⟩
  intro S η hη
  filter_upwards [Filter.eventually_all.mpr (fun j =>
    ((hL j).comp hφ.tendsto_atTop).eventually (eventually_ge_atTop S)),
    (hR.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop S), huniform S η hη]
    with i hiL hiR hi
  refine ⟨hiR, fun j => ⟨hiL j, ?_⟩⟩
  intro t ht htR
  have hh := hi j t.val (by simpa only [Real.dist_eq, sub_zero] using ht)
  rw [hg (φ i) j t (ht.trans hiR)] at hh
  exact hh

end GC.MetricGeometry
