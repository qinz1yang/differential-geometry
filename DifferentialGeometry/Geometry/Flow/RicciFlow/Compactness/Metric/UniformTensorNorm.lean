import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormChartConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTimeJetConvergence


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem sampled_mapCInf_zero_of_uniform_jets
    {U : Set E} (hU : IsOpen U) {J : Set ℝ}
    (f : ℕ → ℝ → E → F) (hf : ∀ n t, t ∈ J → ContDiffOn ℝ ∞ (f n t) U)
    (hunif : ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K, ‖iteratedFDeriv ℝ r (f n t) y‖ ≤ ε)
    (θ : ℕ → ℕ) (hθ : Tendsto θ atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J) :
    MapCInfConvergenceOnCompacts U (fun n => f (θ n) (τ n)) (fun _ => 0) := by
  intro K hK hKU m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hU hKU
    (fun n => (hf (θ n) (τ n) (hτ n)).of_le (by exact_mod_cast le_top)) contDiffOn_const
  intro r _hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hunif K hK hKU r (ε / 2) (by positivity)
  filter_upwards [hθ.eventually_ge_atTop N] with n hn
  intro y hy
  have hh := hN (θ n) hn (τ n) (hτ n) y hy
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, dist_eq_norm, zero_sub, norm_neg]
    using hh.trans_lt (by linarith : ε / 2 < ε)

end Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformCovTensorC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem uniform_tensor02_covariant_norm_of_time_convergence
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : IsCompact J)
    (hcontinuity : ∀ p : M, ∀ τ : ℕ → ℝ, (∀ n, τ n ∈ J) →
      ∀ t ∈ J, Tendsto τ atTop (𝓝 t) → ∀ i j : CoordinateIdx (𝕜 := ℝ) E,
      MapCInfConvergenceOnCompacts (extChartAt I p).target
        (fun n => chartGramOnE (I := I) (g (τ n)) p i j)
        (chartGramOnE (I := I) (g t) p i j))
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hcoord : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E,
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (fun z => A n t ((extChartAt I p).symm z)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (a : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      tensor02CovDerivNormWith (I := I) a (A n t) (g t) (g t)
        ((extChartAt I p).symm y) ≤ ε := by
  classical
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk τ hτ y hy hbad using hbad
  have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨w, hw, σ, hσ, hlim⟩ := (hJ.prod hK).tendsto_subseq
    (x := fun n => (τ n, y n)) (fun n => ⟨hτ n, hy n⟩)
  have htime : Tendsto (fun n => τ (σ n)) atTop (𝓝 w.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto w).comp hlim
  have hspace : Tendsto (fun n => y (σ n)) atTop (𝓝 w.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto w).comp hlim
  have hindex : Tendsto (fun n => k (σ n)) atTop atTop := hkTop.comp hσ.tendsto_atTop
  have hgram (i j : CoordinateIdx (𝕜 := ℝ) E) : MapCInfConvergenceOnCompacts U
      (fun n => chartGramOnE (I := I) (g (τ (σ n))) p i j)
      (chartGramOnE (I := I) (g w.1) p i j) := by
    intro Q hQ hQU m
    exact hcontinuity p (fun n => τ (σ n)) (fun n => hτ (σ n))
      w.1 hw.1 htime i j Q hQ (hQU.trans hUt) m
  have hA (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) : MapCInfConvergenceOnCompacts U
      (fun n z => A (k (σ n)) (τ (σ n)) ((extChartAt I p).symm z)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z)))
      (fun _ => 0) :=
    sampled_mapCInf_zero_of_uniform_jets hU
      (fun n t z => A n t ((extChartAt I p).symm z)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z)))
      (fun n t _ => tensor_field_chart_components_contDiffOn (A n t) p hUt slots)
      (hcoord slots) (fun n => k (σ n)) hindex (fun n => τ (σ n)) (fun n => hτ (σ n))
  have hn := tensor02_covariant_norm_tendsto_zero_of_smooth_chart_convergence
    (fun n => g (τ (σ n))) (g w.1)
    (fun n => A (k (σ n)) (τ (σ n))) p hU hUt hgram hA hK hKU
    (fun n => y (σ n)) (fun n => hy (σ n)) hw.2 hspace a
  obtain ⟨n, hsmall⟩ := (hn.eventually (Iio_mem_nhds hε)).exists
  exact (not_lt_of_ge hsmall.le) (hbad (σ n))

theorem uniform_tensor02_covariant_norm_on_compact_time {D : RealTimeInterval}
    (L : SolutionOn (I := I) (M := M) D) (hL : IsSolutionOn L)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ Iic b)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hcoord : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E,
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (fun z => A n t ((extChartAt I p).symm z)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (a : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      tensor02CovDerivNormWith (I := I) a (A n t) (L.base.metric t) (L.base.metric t)
        ((extChartAt I p).symm y) ≤ ε := by
  apply uniform_tensor02_covariant_norm_of_time_convergence L.base.metric hJ _
    A p hU hUt hcoord hK hKU a
  intro z τ hτ t ht hτt i j Q hQ hQt m
  exact solution_chartGram_mapCInf_of_carrier_time_sequence L hL hcarrier hregular
    (hJb ht) z τ (fun n => hJb (hτ n)) hτt i j Q hQ hQt m

theorem uniform_tensor02_covariant_norm_on_compact_time_of_closed_interval {D : RealTimeInterval}
    (L : SolutionOn (I := I) (M := M) D) (hL : IsSolutionOn L)
    {d c b : ℝ} (hdc : d < c) (hcb : c < b)
    (hslab : Icc d b ⊆ D.carrier) (hregular : Ioo d b ⊆ D.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ Icc c b)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hcoord : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E,
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (fun z => A n t ((extChartAt I p).symm z)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (a : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      tensor02CovDerivNormWith (I := I) a (A n t) (L.base.metric t) (L.base.metric t)
        ((extChartAt I p).symm y) ≤ ε := by
  apply uniform_tensor02_covariant_norm_of_time_convergence L.base.metric hJ _
    A p hU hUt hcoord hK hKU a
  intro z τ hτ t ht hτt i j
  exact solution_chartGram_mapCInf_of_closed_time_sequence L hL hdc hcb hslab hregular
    (hJb ht) z τ (fun n => hJb (hτ n)) hτt i j

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
