import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Filter Set
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tendsto_fderiv_of_joint_limit
    {A B J : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {l : Filter J} [NeBot l] {U : Set A}
    (f : J → A → B) (f₀ : A → B) (D : A → A →L[ℝ] B) (hU : IsOpen U)
    (hf : ∀ n x, x ∈ U → DifferentiableAt ℝ (f n) x)
    (hval : ∀ x ∈ U, Tendsto (fun n => f n x) l (𝓝 (f₀ x)))
    (hderiv : ∀ x ∈ U, Tendsto (fun nx : J × A => fderiv ℝ (f nx.1) nx.2)
      (l ×ˢ 𝓝 x) (𝓝 (D x))) :
    ∀ x ∈ U, Tendsto (fun n => fderiv ℝ (f n) x) l (𝓝 (fderiv ℝ f₀ x)) := by
  intro x hx
  have hactual : HasFDerivAt f₀ (D x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := f)
      (tendsto_prod_filter_iff (F := fun n y => fderiv ℝ (f n) y) |>.mp (hderiv x hx))
    · filter_upwards [tendsto_snd.eventually (hU.mem_nhds hx)] with nx hnx
      exact (hf nx.1 nx.2 hnx).hasFDerivAt
    · exact eventually_of_mem (hU.mem_nhds hx) fun y hy => hval y hy
  rw [hactual.fderiv]
  have hconst : Tendsto (fun n : J => (n, x)) l (l ×ˢ 𝓝 x) :=
    tendsto_id.prodMk tendsto_const_nhds
  exact (hderiv x hx).comp hconst

private theorem linearMap_eq_sum_basis (L : E →L[ℝ] ℝ) :
    L = ∑ k : Fin (Module.finrank ℝ E),
      L (chartModelBasis E k) • ((chartModelBasis E).coord k).toContinuousLinearMap := by
  ext v
  calc
    L v = L (∑ k, (chartModelBasis E).repr v k • chartModelBasis E k) := by
      rw [(chartModelBasis E).sum_repr v]
    _ = ∑ k, (chartModelBasis E).repr v k * L (chartModelBasis E k) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      simp [Module.Basis.coord_apply, mul_comm]

private theorem tendsto_on_product_nhds
    {ι X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {l : Filter ι} {U : Set X} {F : ι → X → Y} {f : X → Y}
    (hf : TendstoLocallyUniformlyOn F f l U) (hc : ContinuousOn f U)
    {x : X} (hx : x ∈ U) :
    Tendsto (fun tx : ι × X => F tx.1 tx.2) (l ×ˢ 𝓝[U] x) (𝓝 (f x)) := by
  have hbase : Tendsto (fun tx : ι × X => f tx.2) (l ×ˢ 𝓝[U] x) (𝓝 (f x)) :=
    (hc x hx).tendsto.comp tendsto_snd
  exact hbase.congr_uniformity (tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hf x hx)

private theorem tendsto_fderiv_chartGram_joint
    {ι : Type*} {l : Filter ι} [NeBot l]
    (g : ι → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ interior (extChartAt I α).target)
    (Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → E → ℝ)
    (hgram : ∀ i j, TendstoLocallyUniformlyOn
      (fun n => chartGramOnE (I := I) (g n) α i j)
      (chartGramOnE (I := I) g₀ α i j) l U)
    (hconn : ∀ i j k, TendstoLocallyUniformlyOn
      (fun n => chartChristoffel (I := I) (g n) α i j k) (Γ i j k) l U) :
    ∀ x ∈ U, ∀ i j,
      Tendsto (fun nx : ι × E => fderiv ℝ (chartGramOnE (I := I) (g nx.1) α i j) nx.2)
        (l ×ˢ 𝓝 x) (𝓝 (∑ k : Fin (Module.finrank ℝ E),
          ((∑ r, Γ k i r x * chartGramOnE (I := I) g₀ α r j x) +
           (∑ r, Γ k j r x * chartGramOnE (I := I) g₀ α r i x)) •
            ((chartModelBasis E).coord k).toContinuousLinearMap)) := by
  classical
  let B := chartModelBasis E
  let G₀ := fun i j => chartGramOnE (I := I) g₀ α i j
  let D := fun i j x => ∑ k : Fin (Module.finrank ℝ E),
    ((∑ r, Γ k i r x * G₀ r j x) + (∑ r, Γ k j r x * G₀ r i x)) •
      (B.coord k).toContinuousLinearMap
  have hΓcont : ∀ i j k, ContinuousOn (Γ i j k) U := by
    intro i j k
    apply (hconn i j k).continuousOn
    apply Eventually.frequently
    exact Eventually.of_forall fun n =>
      ((chartChristoffel_contDiffOn_interior (I := I) (g n) α i j k).continuousOn).mono hchart
  have hGcont : ∀ i j, ContinuousOn (G₀ i j) U := by
    intro i j
    exact ((chartGramOnE_contDiffOn (I := I) g₀ α i j).continuousOn).mono
      (hchart.trans interior_subset)
  have hFD : ∀ n x, x ∈ U → ∀ i j,
      fderiv ℝ (chartGramOnE (I := I) (g n) α i j) x =
        ∑ k : Fin (Module.finrank ℝ E),
          ((∑ r, chartChristoffel (I := I) (g n) α k i r x *
            chartGramOnE (I := I) (g n) α r j x) +
           (∑ r, chartChristoffel (I := I) (g n) α k j r x *
            chartGramOnE (I := I) (g n) α r i x)) •
            (B.coord k).toContinuousLinearMap := by
    intro n x hx i j
    rw [linearMap_eq_sum_basis (fderiv ℝ (chartGramOnE (I := I) (g n) α i j) x)]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    exact partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) (g n) α i j k (hchart hx)
  have hDprod : ∀ x ∈ U, ∀ i j,
      Tendsto (fun nx : ι × E => fderiv ℝ (chartGramOnE (I := I) (g nx.1) α i j) nx.2)
        (l ×ˢ 𝓝 x) (𝓝 (D i j x)) := by
    intro x hx i j
    have hΓ : ∀ p q r, Tendsto (fun nx : ι × E =>
        chartChristoffel (I := I) (g nx.1) α p q r nx.2)
        (l ×ˢ 𝓝 x) (𝓝 (Γ p q r x)) := by
      intro p q r
      simpa only [hU.nhdsWithin_eq hx] using
        tendsto_on_product_nhds (hconn p q r) (hΓcont p q r) hx
    have hG : ∀ p q, Tendsto (fun nx : ι × E =>
        chartGramOnE (I := I) (g nx.1) α p q nx.2)
        (l ×ˢ 𝓝 x) (𝓝 (G₀ p q x)) := by
      intro p q
      simpa only [hU.nhdsWithin_eq hx] using
        tendsto_on_product_nhds (hgram p q) (hGcont p q) hx
    have hsum := tendsto_finsetSum Finset.univ (fun k _ =>
      ((tendsto_finsetSum Finset.univ (fun r _ => (hΓ k i r).mul (hG r j))).add
        (tendsto_finsetSum Finset.univ (fun r _ => (hΓ k j r).mul (hG r i)))).smul
          (tendsto_const_nhds (x := (B.coord k).toContinuousLinearMap)))
    apply hsum.congr'
    filter_upwards [tendsto_snd.eventually (hU.mem_nhds hx)] with nx hnx
    exact (hFD nx.1 nx.2 hnx i j).symm
  exact hDprod

private theorem tendsto_fderiv_chartGram
    {ι : Type*} {l : Filter ι} [NeBot l]
    (g : ι → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ interior (extChartAt I α).target)
    (Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → E → ℝ)
    (hgram : ∀ i j, TendstoLocallyUniformlyOn
      (fun n => chartGramOnE (I := I) (g n) α i j)
      (chartGramOnE (I := I) g₀ α i j) l U)
    (hconn : ∀ i j k, TendstoLocallyUniformlyOn
      (fun n => chartChristoffel (I := I) (g n) α i j k) (Γ i j k) l U) :
    ∀ x ∈ U, ∀ i j,
      Tendsto (fun n => fderiv ℝ (chartGramOnE (I := I) (g n) α i j) x)
        l (𝓝 (fderiv ℝ (chartGramOnE (I := I) g₀ α i j) x)) := by
  classical
  let B := chartModelBasis E
  let G₀ := fun i j => chartGramOnE (I := I) g₀ α i j
  let D := fun i j x => ∑ k : Fin (Module.finrank ℝ E),
    ((∑ r, Γ k i r x * G₀ r j x) + (∑ r, Γ k j r x * G₀ r i x)) •
      (B.coord k).toContinuousLinearMap
  have hDprod : ∀ x ∈ U, ∀ i j,
      Tendsto (fun nx : ι × E => fderiv ℝ (chartGramOnE (I := I) (g nx.1) α i j) nx.2)
        (l ×ˢ 𝓝 x) (𝓝 (D i j x)) :=
    tendsto_fderiv_chartGram_joint g g₀ α hU hchart Γ hgram hconn
  intro x hx i j
  exact tendsto_fderiv_of_joint_limit
    (fun n => chartGramOnE (I := I) (g n) α i j)
    (chartGramOnE (I := I) g₀ α i j) (D i j) hU
    (fun n y hy => chartGramOnE_differentiableAt_interior (I := I) (g n) α i j (hchart hy))
    (fun y hy => (hgram i j).tendsto_at hy)
    (fun y hy => hDprod y hy i j) x hx

theorem chartChristoffel_limit_eq
    {ι : Type*} {l : Filter ι} [NeBot l]
    (g : ι → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (α : M) {U : Set E} (hU : IsOpen U)
    (hchart : U ⊆ interior (extChartAt I α).target)
    (Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → E → ℝ)
    (hgram : ∀ i j, TendstoLocallyUniformlyOn
      (fun n => chartGramOnE (I := I) (g n) α i j)
      (chartGramOnE (I := I) g₀ α i j) l U)
    (hconn : ∀ i j k, TendstoLocallyUniformlyOn
      (fun n => chartChristoffel (I := I) (g n) α i j k) (Γ i j k) l U) :
    ∀ x ∈ U, ∀ i j k,
      Γ i j k x = chartChristoffel (I := I) g₀ α i j k x := by
  classical
  have hDpoint := tendsto_fderiv_chartGram g g₀ α hU hchart Γ hgram hconn
  intro x hx i j k
  have hGM : Tendsto (fun n => chartGramMatrix (I := I) (g n) α ((extChartAt I α).symm x))
      l (𝓝 (chartGramMatrix (I := I) g₀ α ((extChartAt I α).symm x))) :=
    tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => (hgram p q).tendsto_at hx
  have hdet : (chartGramMatrix (I := I) g₀ α ((extChartAt I α).symm x)).det ≠ 0 :=
    (chartGramMatrix_det_pos (I := I) g₀ α
      (extChartAt_symm_mem_trivializationAt_baseSet α (interior_subset (hchart hx)))).ne'
  have hInv : Tendsto (fun n => chartInvGramMatrix (I := I) (g n) α ((extChartAt I α).symm x))
      l (𝓝 (chartInvGramMatrix (I := I) g₀ α ((extChartAt I α).symm x))) := by
    apply (continuousAt_matrix_inv _ ?_).tendsto.comp hGM
    rw [Ring.inverse_eq_inv']
    exact continuousAt_id.inv₀ hdet
  have hPart : ∀ p q r, Tendsto (fun n => partialDeriv p
      (chartGramOnE (I := I) (g n) α q r) x) l
      (𝓝 (partialDeriv p (chartGramOnE (I := I) g₀ α q r) x)) := by
    intro p q r
    exact ((continuous_id.clm_apply continuous_const).tendsto _).comp (hDpoint x hx q r)
  have hActual : Tendsto (fun n => chartChristoffel (I := I) (g n) α i j k x)
      l (𝓝 (chartChristoffel (I := I) g₀ α i j k x)) := by
    simp only [chartChristoffel_def]
    exact tendsto_const_nhds.mul (tendsto_finsetSum Finset.univ (fun r _ =>
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hInv k) r).mul
        (((hPart i r j).add (hPart j r i)).sub (hPart r i j))))
  exact tendsto_nhds_unique ((hconn i j k).tendsto_at hx) hActual

end DifferentialGeometry.Geometry.Connection
