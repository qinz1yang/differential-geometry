import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBalls
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTorusDiameter
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarLocalization

/-!
# Small balls of a nearly cuspidal collar have volume `≤ 1000 δ² r` (BSA01 (ii), (vi) — kernels)

Blueprint 207B, BSA01 (`B:7606–7611`) and BCP01's proof (`B:8159–8162`). Write
`μ_H = (vol_{g_T} ⊗ Leb).withDensity e^{-z}` on `T² × ℝ` (torus factor on `borel Torus`; the
frozen form of statement V.1). For a cusp embedding with `δ ≤ 1/100`, a centre of height `≤ 96` and
`r ≤ 1`:

* `cusp_measure_le_torusArea_mul`: a set of nonnegative heights inside `(a, b)` has
  `μ_H`-measure at most `Area(T², g_T) · (b - a)` (`e^{-z} ≤ 1`; no measurability needed);
* kernel `CuspEmbedding.ballVolume_le_of_volume_transfer`: if `Area(T², g_T) ≤ 4πδ²` and the UPPER
  half of V.1 holds for this collar, `vol B(e p, r) ≤ 1000 δ² r` (the ball lies in a height band of
  length `2.02 r` below `98` by G-ball; `(1 + δ)^{3/2} · 4πδ² · 2.02 r ≤ 1000 δ² r`);
* `NearlyCuspidalBoundary.ballVolume_le_of_volume_transfer`: the same with the area bound from G-diam;
* `NearlyCuspidalBoundary.ballVolume_le_of_distanceToBoundary_le_ten`: the volume part of the first
  clause of `G_consumer_clauses` (`d(p, ∂W) ≤ 10`, `0 < a ≤ 1`), via BSA01 (iii).

The input `hV` is the second conjunct of `CuspEmbedding.volume_transfer` (lane BDY-V, V.1),
verbatim; once V.1 lands, the binding drops it.
-/

set_option autoImplicit false

noncomputable section

open Set Function MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open GC.Endpoint DifferentialGeometry.Topology.Manifold DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- A set of nonnegative heights in `(a, b)` has `μ_H`-measure at most `Area(T², g_T) · (b - a)`. -/
theorem cusp_measure_le_torusArea_mul (Hc : HyperbolicCusp) {S : Set (Torus × ℝ)} {a b : ℝ}
    (hS : ∀ q ∈ S, 0 ≤ q.2 ∧ a < q.2 ∧ q.2 < b) :
    (@Measure.prod Torus ℝ (borel Torus) _
        (riemannianVolumeMeasure torusModel Torus Hc.torusMetric) volume).withDensity
          (fun q => ENNReal.ofReal (Real.exp (-q.2))) S ≤
      riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ * ENNReal.ofReal (b - a) := by
  let : MeasurableSpace Torus := borel Torus
  set μ₀ := (riemannianVolumeMeasure torusModel Torus Hc.torusMetric).prod
    (volume : Measure ℝ) with hμ₀
  set T : Set (Torus × ℝ) := univ ×ˢ (Ioo a b ∩ Ici 0) with hT
  have hTm : MeasurableSet T := MeasurableSet.univ.prod (measurableSet_Ioo.inter measurableSet_Ici)
  have hST : S ⊆ T := fun q hq => ⟨mem_univ _, ⟨(hS q hq).2.1, (hS q hq).2.2⟩, (hS q hq).1⟩
  calc μ₀.withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) S
      ≤ μ₀.withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) T := measure_mono hST
    _ = ∫⁻ q in T, ENNReal.ofReal (Real.exp (-q.2)) ∂μ₀ := withDensity_apply _ hTm
    _ ≤ ∫⁻ _ in T, (1 : ℝ≥0∞) ∂μ₀ := by
        refine setLIntegral_mono' hTm fun q hq => ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by linarith [hq.2.2.out]))
    _ = μ₀ T := by rw [setLIntegral_const, one_mul]
    _ ≤ riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ *
          volume (Ioo a b ∩ Ici 0) := Measure.prod_prod_le _ _
    _ ≤ riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ * ENNReal.ofReal (b - a) := by
        gcongr
        exact (measure_mono inter_subset_left).trans (Real.volume_Ioo).le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **BSA01 (ii)/(vi), volume (kernel).** For `δ ≤ 1/100`, a reference torus of area `≤ 4πδ²` and
the upper half of the volume transfer V.1 for this collar, every ball `B(e p, r)` with
`z(p) ≤ 96` and `r ≤ 1` has volume at most `1000 δ² r`. -/
theorem CuspEmbedding.ballVolume_le_of_volume_transfer {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ ≤ 1 / 100)
    (hA : (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric univ).toReal ≤
      4 * Real.pi * δ ^ 2)
    (hV : ∀ S : Set (Torus × ℝ), MeasurableSet[borel (Torus × ℝ)] S →
      (∀ q ∈ S, 0 ≤ q.2 ∧ q.2 < cuspDepth) →
      riemannianVolumeMeasure W.model W.Carrier g
          (e.toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S)) ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
          (@Measure.prod Torus ℝ (borel Torus) _
            (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric) volume).withDensity
              (fun q => ENNReal.ofReal (Real.exp (-q.2))) S)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) {r : ℝ} (hr : r ≤ 1) :
    ballVolume g (e.toFun p) r ≤ ENNReal.ofReal (1000 * δ ^ 2 * r) := by
  have hδ0 : 0 ≤ δ := e.delta_nonneg
  rcases le_or_gt r 0 with hr0 | hr0
  · have hempty : riemannianBallOf g (e.toFun p) r = ∅ := by
      ext y
      simp only [riemannianBallOf, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt,
        ENNReal.ofReal_of_nonpos hr0, zero_le]
    rw [ballVolume, hempty, measure_empty]
    exact zero_le
  set z : ℝ := p.2.val 0 with hz
  set c : ℝ := 101 / 100 * r with hc
  set S : Set (Torus × ℝ) := Prod.snd ⁻¹' {s : ℝ | 0 ≤ s ∧ |s - z| < c ∧ s < 98} with hS
  -- the ball lies in the image of `S`
  have hball : riemannianBallOf g (e.toFun p) r ⊆
      e.toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S) := by
    refine (e.riemannianBallOf_subset_image_window_of_le_hundredth hδ hp hr).trans ?_
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    refine ⟨q, ⟨(q.1, q.2.val 0), ⟨q.2.2, hq1, hq2⟩, ?_⟩, rfl⟩
    exact Prod.ext rfl (halfSpaceOneLift_val_zero_self q.2)
  -- measurability of `S` for the Borel σ-algebra of the product
  have hSm : MeasurableSet[borel (Torus × ℝ)] S := by
    have hA' : MeasurableSet {s : ℝ | 0 ≤ s ∧ |s - z| < c ∧ s < 98} :=
      measurableSet_Ici.inter ((measurableSet_lt
        (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
        measurable_const).inter measurableSet_Iio)
    have hA'' : MeasurableSet[borel ℝ] {s : ℝ | 0 ≤ s ∧ |s - z| < c ∧ s < 98} := by
      rw [← BorelSpace.measurable_eq]
      exact hA'
    exact continuous_snd.borel_measurable hA''
  have hSd : ∀ q ∈ S, 0 ≤ q.2 ∧ q.2 < cuspDepth := fun q hq =>
    ⟨hq.1, lt_trans hq.2.2 (by norm_num [cuspDepth])⟩
  have hμ := cusp_measure_le_torusArea_mul e.cusp (S := S) (a := z - c) (b := z + c)
    fun q hq => ⟨hq.1, by linarith [(abs_lt.mp hq.2.1).1], by linarith [(abs_lt.mp hq.2.1).2]⟩
  -- the torus area as an extended real
  have hfin : riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric univ ≠ ⊤ := by
    let : MeasurableSpace Torus := borel Torus
    have : IsFiniteMeasure (riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := torusModel) (M := Torus)
        e.cusp.torusMetric
    exact measure_ne_top _ _
  have hAe : riemannianVolumeMeasure torusModel Torus e.cusp.torusMetric univ ≤
      ENNReal.ofReal (4 * Real.pi * δ ^ 2) := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hA
  -- the numerical constant
  have hpow : (1 + δ) ^ ((3 : ℝ) / 2) ≤ 2 := by
    have h1 : (1 + δ) ^ ((3 : ℝ) / 2) ≤ (1 + δ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_two] at h1
    nlinarith
  have hpos : 0 ≤ (1 + δ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hnum : (1 + δ) ^ ((3 : ℝ) / 2) * (4 * Real.pi * δ ^ 2 * (z + c - (z - c))) ≤
      1000 * δ ^ 2 * r := by
    have hπ := Real.pi_le_four
    have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    have hX : 0 ≤ 4 * Real.pi * δ ^ 2 * (z + c - (z - c)) := by
      have := Real.pi_pos
      rw [show z + c - (z - c) = 2 * c by ring, hc]
      positivity
    calc (1 + δ) ^ ((3 : ℝ) / 2) * (4 * Real.pi * δ ^ 2 * (z + c - (z - c)))
        ≤ 2 * (4 * Real.pi * δ ^ 2 * (z + c - (z - c))) := mul_le_mul_of_nonneg_right hpow hX
      _ = 404 / 25 * Real.pi * δ ^ 2 * r := by rw [hc]; ring
      _ ≤ 1000 * δ ^ 2 * r := by
          have : 0 ≤ δ ^ 2 * r := mul_nonneg hδ2 hr0.le
          nlinarith
  calc ballVolume g (e.toFun p) r
      ≤ riemannianVolumeMeasure W.model W.Carrier g
          (e.toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S)) :=
        measure_mono hball
    _ ≤ _ := hV S hSm hSd
    _ ≤ ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
          (ENNReal.ofReal (4 * Real.pi * δ ^ 2) * ENNReal.ofReal (z + c - (z - c))) := by
        gcongr
        exact hμ.trans (by gcongr)
    _ = ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2) *
          (4 * Real.pi * δ ^ 2 * (z + c - (z - c)))) := by
        rw [ENNReal.ofReal_mul hpos, ENNReal.ofReal_mul (p := 4 * Real.pi * δ ^ 2) (by positivity)]
    _ ≤ ENNReal.ofReal (1000 * δ ^ 2 * r) := ENNReal.ofReal_le_ofReal hnum

/-- **BSA01 (ii)/(vi), volume, for a nearly cuspidal boundary.** For `δ ≤ 1/100` and the upper half
of V.1 on the collar `i`, every ball `B(e_i p, r)` with `z(p) ≤ 96`, `r ≤ 1` has volume
`≤ 1000 δ² r` (the area bound `4πδ²` is G-diam). -/
theorem NearlyCuspidalBoundary.ballVolume_le_of_volume_transfer {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 100) (i : Fin B.count)
    (hV : ∀ S : Set (Torus × ℝ), MeasurableSet[borel (Torus × ℝ)] S →
      (∀ q ∈ S, 0 ≤ q.2 ∧ q.2 < cuspDepth) →
      riemannianVolumeMeasure W.model W.Carrier g
          ((B.collar i).toFun '' ((fun q : Torus × ℝ => (q.1, halfSpaceOneLift q.2)) '' S)) ≤
        ENNReal.ofReal ((1 + δ) ^ ((3 : ℝ) / 2)) *
          (@Measure.prod Torus ℝ (borel Torus) _
            (riemannianVolumeMeasure torusModel Torus (B.collar i).cusp.torusMetric)
              volume).withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) S)
    {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) {r : ℝ} (hr : r ≤ 1) :
    ballVolume g ((B.collar i).toFun p) r ≤ ENNReal.ofReal (1000 * δ ^ 2 * r) :=
  (B.collar i).ballVolume_le_of_volume_transfer hδ (B.torus_area_le_four_pi_mul_sq hδ i) hV hp hr

end DifferentialGeometry.Geometry.Collapse
