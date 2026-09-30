import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCoverVolume
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem spatialRound_volume_lower_div_fundamental_degree
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M} {U : Set M}
    (D : SpatialRoundComponent g eps x U) (y₀ : U) :
    Finite (FundamentalGroup U y₀) ∧ 0 < Nat.card (FundamentalGroup U y₀) ∧
    ENNReal.ofReal ((4 * Real.sqrt 3 * Real.pi / (Nat.card (FundamentalGroup U y₀) : ℝ)) /
        (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 M g U := by
  let _ := D.topology
  let _ := D.charted
  let _ := D.smooth
  let _ := D.t2
  let _ := D.compact
  let _ := D.connected
  set Q := metricScalarAt g x
  have hQ : 0 < Q := D.Q_pos
  let e : D.Z ≃ₜ U :=
    ((Homeomorph.Set.univ D.Z).symm.trans (Homeomorph.setCongr D.source_eq.symm)).trans
      (D.map.toOpenPartialHomeomorph.toHomeomorphSourceTarget.trans
        (Homeomorph.setCongr D.target_eq))
  let eπ := DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv
    (e.symm y₀) y₀ (e.apply_symm_apply y₀)
  have hcard := Nat.card_congr eπ.toEquiv
  obtain ⟨hfin,hpos,hvolZ⟩ :=
    round_volume_lower_div_fundamental_degree D.metric (e.symm y₀) D.constant_curvature
  let _ := hfin
  have hfU : Finite (FundamentalGroup U y₀) := Finite.of_equiv _ eπ.toEquiv
  rw [hcard] at hpos hvolZ
  refine ⟨hfU,hpos,?_⟩
  have hsand := riemannianVolumeMeasure_image_sandwich D.metric g D.map isOpen_univ
    (by rw [D.source_eq]) isCompact_univ (subset_univ _)
    (by positivity : (0 : ℝ) < 2 * Q) (by positivity : (0 : ℝ) < 2 / Q)
    (fun y _ v => by
      have hb := (D.metric_bounds y v).1
      nlinarith)
    (fun y _ v => by
      have hb := (D.metric_bounds y v).2
      rw [div_mul_eq_mul_div, le_div_iff₀ hQ]
      nlinarith)
  have himage : (D.map : D.Z → M) '' univ = U := by
    have h1 : (D.map : D.Z → M) '' univ = (D.map : D.Z → M) '' D.map.source := by
      rw [D.source_eq]
    exact h1.trans (D.map.toPartialEquiv.image_source_eq_target.trans D.target_eq)
  have hlower := hsand.1
  rw [himage] at hlower
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hlower
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsQ : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hsqrt : Real.sqrt ((2 * Q) ^ 3) = 2 * Real.sqrt 2 * (Q * Real.sqrt Q) := by
    have hnn : 0 ≤ 2 * Real.sqrt 2 * (Q * Real.sqrt Q) := by positivity
    rw [show (2 * Q) ^ 3 = (2 * Real.sqrt 2 * (Q * Real.sqrt Q)) ^ 2 by
      have hexp : (2 * Real.sqrt 2 * (Q * Real.sqrt Q)) ^ 2 =
          4 * Real.sqrt 2 ^ 2 * Q ^ 2 * Real.sqrt Q ^ 2 := by ring
      rw [hexp, hs2, hsQ]
      ring]
    exact Real.sqrt_sq hnn
  have hsix : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have hQs : 0 < Q * Real.sqrt Q := mul_pos hQ (Real.sqrt_pos.mpr hQ)
  have hprod : ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) *
      ENNReal.ofReal ((4 * Real.sqrt 3 * Real.pi / (Nat.card (FundamentalGroup U y₀) : ℝ)) / (Q * Real.sqrt Q)) =
      ENNReal.ofReal ((8 * Real.sqrt 6 * Real.pi) / (Nat.card (FundamentalGroup U y₀) : ℝ)) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsqrt, hsix]
    congr 1
    field_simp
    ring
  have hB0 : ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) ≠ 0 := by
    rw [hsqrt]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hchain : ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) *
      ENNReal.ofReal ((4 * Real.sqrt 3 * Real.pi / (Nat.card (FundamentalGroup U y₀) : ℝ)) / (Q * Real.sqrt Q)) ≤
      ENNReal.ofReal (Real.sqrt ((2 * Q) ^ 3)) * riemannianVolumeMeasure I3 M g U := by
    rw [hprod]
    exact hvolZ.trans hlower
  exact (ENNReal.mul_le_mul_iff_right hB0 ENNReal.ofReal_ne_top).mp hchain

end GC.GeneralFlow
