import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.Smooth

/-!
# Chart-bilinear identity for non-smooth elements of `H1Compl g`

This module packages the chart-pulled variational identity for a possibly
non-smooth element of `H1Compl g`. The data structure
`ChartBilinearH1ComplData` records:

* a chart-pulled scalar `u_chart : EuclN → ℝ`,
* explicit weak partial derivatives `weak_partial i` of `u_chart` (in the
  DeGiorgi sense, against plain Lebesgue volume on
  `chartTargetEuclid α`),
* a chart-pulled right-hand side `f_chart : EuclN → ℝ`,
* membership of `u_chart`, `weak_partial i`, and `f_chart` in `L²` of the
  chart-pulled measure `volume.withDensity (densityOnEuclid g α)`,
* and the natural density-weighted variational identity

```
∫_{chartTarget} ∑_{i, j} weightedInvGramOnEuclid · (weak_partial i) · ∂_j ψ
  + ∫_{chartTarget} densityOnEuclid · u_chart · ψ
  = ∫_{chartTarget} densityOnEuclid · f_chart · ψ
```
for every smooth test function `ψ` with `tsupport ψ ⊆ chartTargetEuclid α`.

The data structure is **non-vacuous** for non-smooth `u_chart`: the principal
integrand uses the explicit weak partial derivative, not the classical Fréchet
derivative (which would vanish a.e. for non-smooth `u_chart`).

The natural reference measure is `volume.withDensity densityOnEuclid g α`
(restricted to `chartTargetEuclid α`). This is the chart-pull of the
Riemannian volume measure `μ_g` to Euclidean coordinates, and is finite
when restricted to the chart source. This formulation is robust to
non-precompact charts (e.g., stereographic projection).

## Main definitions

* `ChartBilinearH1ComplData`: packaged data for a non-smooth chart-bilinear
  identity on a closed Riemannian manifold.
* `chartPulledWeightedMeasure g α`: the chart-pulled volume measure on
  `EuclideanSpace ℝ (Fin n)`.

## Main results

* `chart_bilinear_identity_h1Compl`: hypothesis-bearing form of the
  non-smooth chart-bilinear identity, expressed via the data structure.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The chart-pulled weighted measure on `EuclideanSpace ℝ (Fin n)`:
`volume` weighted by `densityOnEuclid g α`. This is the natural Euclidean
counterpart of the Riemannian volume measure `μ_g` on the chart source,
restricted to the chart-target image `chartTargetEuclid α`.

Because `densityOnEuclid g α` is positive on `chartTargetEuclid α`, this
measure is mutually absolutely continuous with `volume.restrict
(chartTargetEuclid α)` on the chart-target image. Outside `chartTargetEuclid α`
the density vanishes (junk values), so the measure has effective support
inside `chartTargetEuclid α`. -/
def chartPulledWeightedMeasure (g : SmoothRiemannianMetric I M) (α : M) :
    Measure EuclN :=
  (volume : Measure EuclN).withDensity
    (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))

/-- Data describing a non-smooth chart-bilinear identity on
`chartTargetEuclid α`. The hypotheses encode:

(1) a chart-pulled scalar `u_chart : EuclN → ℝ` together with explicit weak
partial derivatives `weak_partial i : EuclN → ℝ`, all in `L²` of the
chart-pulled weighted measure restricted to `chartTargetEuclid α`;

(2) a chart-pulled `L²` right-hand side `f_chart : EuclN → ℝ`;

(3) the density-weighted variational identity
```
∫ ∑_{i,j} (√det g · g^{ij}) · (weak_partial i) · ∂_j ψ
  + ∫ √det g · u_chart · ψ = ∫ √det g · f_chart · ψ
```
on `chartTargetEuclid α`, for every smooth test ψ with
`tsupport ψ ⊆ chartTargetEuclid α`.

The principal integrand uses the EXPLICIT weak partial `weak_partial i`,
not the classical Fréchet derivative `fderiv ℝ u_chart`. This is essential
for the identity to be non-vacuous when `u_chart` is non-smooth (in which
case `fderiv ℝ u_chart` vanishes a.e.). -/
structure ChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where
  /-- The chart-pulled `H¹` function. -/
  u_chart : EuclN → ℝ
  /-- The chart-pulled `L²` right-hand-side data. -/
  f_chart : EuclN → ℝ
  /-- Explicit weak partial derivatives of `u_chart`. -/
  weak_partial : Fin (Module.finrank ℝ E) → EuclN → ℝ
  /-- `u_chart` is `MemLp 2` w.r.t. the chart-pulled weighted measure
  restricted to `chartTargetEuclid α`. -/
  u_chart_memLp_weighted :
    MemLp u_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  /-- `f_chart` is `MemLp 2` w.r.t. the chart-pulled weighted measure
  restricted to `chartTargetEuclid α`. -/
  f_chart_memLp_weighted :
    MemLp f_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  /-- Each weak partial derivative is locally `MemLp 2` (with respect to
  plain Lebesgue volume) on every compact subset of `chartTargetEuclid α`.

  Local L² is the natural integrability for chart-pulled gradients. The
  principal integrand of the variational identity is integrated against
  test functions of compact support, so only local L² is needed for the
  variational identity to make sense.

  In the constructor `chartBilinearH1ComplData_of_laplacianDomain`, the
  partials in fact satisfy the stronger bound `MemLp 2` w.r.t. the
  chart-pulled weighted measure restricted to `chartTargetEuclid α`
  (since the chart-pulled Gram matrix has uniformly bounded eigenvalues
  on a closed manifold). The local statement here is the minimum
  needed for the variational identity to make sense and for the consumer
  `h2_chart_loc_of_uniform_bound` to extract `H²` regularity. -/
  weak_partial_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K → K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial i) 2 ((volume : Measure EuclN).restrict K)
  /-- Each weak partial derivative is in fact a weak partial of `u_chart`
  on `chartTargetEuclid α` (DeGiorgi sense, against plain volume). -/
  weak_partial_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (weak_partial i) u_chart
      (chartTargetEuclid (I := I) (M := M) α)
  /-- The variational identity in density-weighted form. -/
  variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * u_chart y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f_chart y * ψ y
        ∂(volume : Measure EuclN)

/-- Headline form of the chart-bilinear identity for a non-smooth element of
`H1Compl g`: given the data `D`, the variational identity
```
∫ ∑_{i,j} (√det g · g^{ij}) · (weak_partial i) · ∂_j ψ
  + ∫ √det g · u_chart · ψ = ∫ √det g · f_chart · ψ
```
on `chartTargetEuclid α` holds for every smooth test function `ψ` with
`tsupport ψ ⊆ chartTargetEuclid α`. This is a re-export of
`D.variational_identity` for ergonomics. -/
theorem chart_bilinear_identity_h1Compl
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.variational_identity ψ hψ hψ_cs hψ_supp

/-- The density `densityOnEuclid g α` is bounded above and below by positive
constants on any compact subset of `chartTargetEuclid α`. -/
lemma densityOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c_min c_max : ℝ, 0 < c_min ∧ c_min ≤ c_max ∧
      ∀ y ∈ K, c_min ≤ densityOnEuclid (I := I) g α y ∧
        densityOnEuclid (I := I) g α y ≤ c_max := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨1, 1, by norm_num, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_dens_contOn_K : ContinuousOn (densityOnEuclid (I := I) g α) K :=
    h_dens_contOn.mono hK_in
  have h_dens_pos : ∀ y ∈ K, 0 < densityOnEuclid (I := I) g α y :=
    fun y hy => densityOnEuclid_pos (I := I) g α (hK_in hy)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_min, hy_min, h_min_eq⟩ := hK.exists_isMinOn h_K_ne h_dens_contOn_K
  obtain ⟨y_max, hy_max, h_max_eq⟩ := hK.exists_isMaxOn h_K_ne h_dens_contOn_K
  set c_min : ℝ := densityOnEuclid (I := I) g α y_min with hcmin_def
  set c_max : ℝ := densityOnEuclid (I := I) g α y_max with hcmax_def
  have hc_min_pos : 0 < c_min := h_dens_pos y_min hy_min
  have hc_min_le_max : c_min ≤ c_max := by
    have h := h_min_eq hy_max
    exact h
  refine ⟨c_min, c_max, hc_min_pos, hc_min_le_max, ?_⟩
  intro y hy
  refine ⟨h_min_eq hy, h_max_eq hy⟩

/-- The continuity of `densityOnEuclid g α` on the open chart-target image. -/
lemma densityOnEuclid_continuousOn (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).continuousOn

/-- For a measurable subset `K ⊆ chartTargetEuclid α` (in particular any
compact subset), the plain volume `volume.restrict K` is dominated by a
positive scalar multiple of the chart-pulled weighted measure restricted to
`chartTargetEuclid α`:

```
volume.restrict K ≤ ENNReal.ofReal (1 / c_min) •
  (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)
```

where `c_min > 0` is the lower bound for `densityOnEuclid g α` on `K`. -/
lemma volume_restrict_compact_le_chartPulledWeightedMeasure
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (volume : Measure EuclN).restrict K ≤
        ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨c_min, _c_max, hc_min_pos, _hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨1 / c_min, by positivity, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA]
  rw [Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter (chartTargetEuclid_isOpen
    (I := I) (M := M) α).measurableSet)]
  have h_subset : A ∩ K ⊆ A ∩ chartTargetEuclid (I := I) (M := M) α :=
    Set.inter_subset_inter_right A hK_in
  have h_setmono :
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN) ≤
      ∫⁻ y in A ∩ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN) := by
    apply MeasureTheory.lintegral_mono_set h_subset
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K, ENNReal.ofReal c_min ∂(volume : Measure EuclN) ≤
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).1
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_min ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_min * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  have h_step1 : (volume : Measure EuclN) (A ∩ K) =
      ENNReal.ofReal (1 / c_min) *
        (ENNReal.ofReal c_min * (volume : Measure EuclN) (A ∩ K)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / c_min) * c_min = 1 from by field_simp]
    rw [ENNReal.ofReal_one, one_mul]
  rw [h_step1]
  rw [smul_eq_mul]
  gcongr
  exact le_trans (le_of_eq h_const_eval.symm) (h_pointwise_bd.trans h_setmono)

/-- Conversion: weighted `MemLp 2` on `chartTargetEuclid α` implies plain
`MemLp 2` on any compact subset `K ⊆ chartTargetEuclid α`. -/
lemma memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {α : M} {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      α hK_compact hK_meas hK_in
  exact hw.of_measure_le_smul (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top h_le

end ChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry
