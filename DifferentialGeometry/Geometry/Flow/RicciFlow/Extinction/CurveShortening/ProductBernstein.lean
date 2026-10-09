import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Bernstein

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem exists_uniform_curvatureDerivative_bound_of_curvatureSq_le_div
    (B : RicciBackground (I := I) (M := M) D a b) :
    ∃ C : ℝ, B.C ≤ C ∧ ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      ∀ s u K : ℝ, s < u → Icc s u ⊆ Icc a b → Icc s u ⊆ J → 1 ≤ K → u - s ≤ 1 →
      (∀ x t, t ∈ Ioc s u → c.curvatureSq B.family.metric lambda x t ≤ K / (t - s)) →
      ∀ x, c.normSq B.family.metric lambda
        (c.iteratedDs B.family.metric lambda 1 (c.curvatureVector B.family.metric lambda)) x u ≤
        16 * (1 + 64 * (1 + C)) ^ 2 * (K / (u - s)) ^ 2 := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  obtain ⟨C, hC, _, _, hprod⟩ := B.exists_uniform_product_curvature_derivative_bounds A
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda c J hJ hc s u K hsu hwindow hinterval hK hlen hk
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hBG⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hfamily, _, _, _, hBC⟩ := hBG lambda hlambda
  have hm : Bhat.family.metric = fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun G => G.metric) hfamily
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map A B.family.metric lambda hlambda hJ hc).mono hinterval
      (fun t ht => (uniqueDiffOn_Icc hsu t ht).uniqueMDiffWithinAt)
  have hsq (x t : ℝ) (ht : t ∈ Icc s u) :
      c.map.curvatureSq Bhat.family.metric x t = c.curvatureSq B.family.metric lambda x t := by
    rw [hm]
    exact c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x t (hinterval ht)
  have hC' : Bhat.C ≤ C := hBC.trans_le hC
  have hDR (x t : ℝ) (ht : t ∈ Icc s u) :
      DifferentialGeometry.Tensor0SBundle.normSq0S (Bhat.family.metric t) (c.map.lift x t) 5
        (DifferentialGeometry.Tensor0SBundle.totalNabla0SFun 4 (Bhat.family.connection t) (Bhat.family.rm04 t) (c.map.lift x t)) ≤ C ^ 2 := by
    rw [hfamily]
    exact (hprod lambda hlambda t (hwindow ht) (c.map.lift x t)).1
  have hDDRic (x t : ℝ) (ht : t ∈ Icc s u) :
      DifferentialGeometry.Tensor0SBundle.normSq0S (Bhat.family.metric t) (c.map.lift x t) 4
        (DifferentialGeometry.Tensor0SBundle.totalNabla0SFun 3 (Bhat.family.connection t)
          (DifferentialGeometry.CheegerGromovCompactness.covStep (Bhat.family.metric t) 2 (Bhat.family.ricci t)) (c.map.lift x t)) ≤ C ^ 2 := by
    rw [hfamily]
    exact (hprod lambda hlambda t (hwindow ht) (c.map.lift x t)).2
  have hh := c.map.curvatureDerivative_bernstein_bound_of_curvatureSq_le_div Bhat hsu hwindow
    hsol C K hC' hK hlen (fun x t ht => by rw [hsq x t ⟨ht.1.le, ht.2⟩]; exact hk x t ht)
    hDR hDDRic
  intro x
  have htransport := c.map_iteratedDs_curvature_normSq A B.family.metric lambda hlambda
    hc.smooth hc.immersed x u (hinterval ⟨hsu.le, le_rfl⟩) 1
  have hresult := hh x
  rw [hm] at hresult
  change c.map.normSq _ (c.map.iteratedDs _ 1 (c.map.curvatureVector _)) x u ≤ _ at hresult
  rwa [htransport] at hresult

theorem exists_uniform_curvature_and_derivative_bounds
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ A₁ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < A₁ ∧
      ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M, ∀ J : Set ℝ,
      UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s u r : ℝ, a ≤ s → s < u → u ≤ b → Icc a u ⊆ J →
      0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s → u ≤ s + δ * r ^ 2 →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      ∀ x : ℝ, c.curvatureSq B.family.metric lambda x u ≤ 4 / (u - s) ∧
        c.normSq B.family.metric lambda
          (c.iteratedDs B.family.metric lambda 1 (c.curvatureVector B.family.metric lambda)) x u ≤
          A₁ / (u - s) ^ 2 := by
  obtain ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, hzero⟩ :=
    exists_uniform_curvatureSq_bound_of_small_arcTotalCurvature B L₀ Θ₀ hL₀ hΘ₀
  obtain ⟨C, hC, hderiv⟩ := exists_uniform_curvatureDerivative_bound_of_curvatureSq_le_div B
  have hC0 : 0 ≤ C := by
    have h0 := B.B₀_nonneg
    have h1 := B.B₁_nonneg
    have h2 := B.B₂_nonneg
    dsimp only [RicciBackground.C] at hC
    linarith only [hC, h0, h1, h2]
  refine ⟨δ, r₀, 256 * (1 + 64 * (1 + C)) ^ 2, hδ, hδ1, hr₀, hr₀1, by positivity, ?_⟩
  intro lambda hlambda c J hJ hc hlen₀ htotal₀ s u r has hsu hub hinterval hr hrr₀ hlen htime hsmall x
  have hk : ∀ y t, t ∈ Ioc s u → c.curvatureSq B.family.metric lambda y t ≤ 4 / (t - s) := by
    intro y t ht
    exact hzero lambda hlambda c J hJ hc hlen₀ htotal₀ s t r has ht.1 (ht.2.trans hub)
      ((Icc_subset_Icc le_rfl ht.2).trans hinterval) hr hrr₀ hlen (ht.2.trans htime) hsmall y
  have hsub : Icc s u ⊆ J := (Icc_subset_Icc has le_rfl).trans hinterval
  have htime1 : u - s ≤ 1 := by
    have hr1 := hrr₀.trans hr₀1
    have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
    have hh := (mul_le_mul_of_nonneg_left hr2 hδ.le).trans (by simpa only [mul_one] using hδ1.le)
    linarith only [htime, hh]
  refine ⟨hk x u ⟨hsu, le_rfl⟩, ?_⟩
  have hh := hderiv lambda hlambda c J hJ hc s u 4 hsu (Icc_subset_Icc has hub) hsub
    (by norm_num) htime1 hk x
  exact hh.trans_eq (by rw [div_pow]; ring)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
