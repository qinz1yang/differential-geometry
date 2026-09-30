import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapComparisonTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]

theorem CanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {alpha eps C a b t rho R margin : ℝ} {x : P} {W : Set P}
    (A : CanonicalAlternative S eps C x t W)
    (hshape : (∃ Ln, A = .neck Ln) ∨ ∃ Lc deep, A = .cap Lc deep)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (heps : eps ≤ neckModelTolerance alpha)
    (hQ : 0 < S.scalar t x) (hab : a < b) (hwindow : b ≤ t - 2 * (S.scalar t x)⁻¹)
    (hslab : Icc a t ⊆ D.carrier) (hreg : Ioo a t ⊆ D.regular)
    (V : TopologicalSpace.Opens P) (hVcompact : IsCompact (closure (V : Set P)))
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) (hWK : W ⊆ K)
    (hneck : ∀ Ln, A = .neck Ln →
      ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, Ln.strong.map y ∈ K)
    (hcap : ∀ Lc deep, A = .cap Lc deep →
      (∀ i, b ≤ t - 2 * (S.scalar t (Lc.chain.centers i))⁻¹) ∧
      (∀ i, ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, (Lc.chain.necks i).map y ∈ K) ∧
      0 < margin ∧ 0 ≤ rho ∧ 3 * rho < R ∧
      riemannianClosedBallOf (I := I3) (S.base.metric t) x R ⊆ K ∧
      Lc.tube ⊆ riemannianClosedBallOf (I := I3) (S.base.metric t) x rho ∧
      ∀ y ∈ Lc.tube,
        10000 / Real.sqrt (S.scalar t x) + margin ≤ metricDistance (S.base.metric t) x y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N],
      ∀ {D' : RealTimeInterval} (S' : SolutionOn (I := I3) (M := N) D'), IsSolutionOn S' →
      Icc a t ⊆ D'.carrier → Ioo a t ⊆ D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P N ∞, (V : Set P) ⊆ F.source →
      MetricComparisonOn S.base.metric S'.base.metric F V (Icc b t) ⌈(2 * alpha)⁻¹⌉₊ delta →
      Nonempty (CanonicalAlternative S' (2 * alpha) C (F x) t (F '' W)) := by
  rcases hshape with ⟨Ln, rfl⟩ | ⟨Lc, deep, rfl⟩
  · have hmodel : neckModelTolerance alpha < 1 / 11 :=
      (neckModelTolerance_le alpha).trans_lt (by linarith)
    let L₁ := Ln.monoEps heps hmodel
    obtain ⟨delta, hdelta, htr⟩ := L₁.exists_transport_tolerance_of_metricComparisonOn hS ha
      hsmall (hab.trans_le hwindow) hslab hreg V hVcompact hK hKV (hneck Ln rfl)
    refine ⟨delta, hdelta, ?_⟩
    intro N _ _ _ _ _ D' S' hS' hslab' hreg' F hF Cmp
    have hlt : t - 2 * (S.scalar t x)⁻¹ < t := by
      have := inv_pos.mpr hQ
      linarith
    have hbt : b < t := hwindow.trans_lt hlt
    have hsub : Icc (t - 2 * (S.scalar t x)⁻¹) t ⊆ Icc b t := Icc_subset_Icc_left hwindow
    obtain ⟨L', _⟩ := htr N S' hS' hslab' hreg' F hF
      (Cmp.restrictTimes hsub (uniqueDiffOn_Icc hlt) fun q s hs y hy v =>
        (Cmp.jet_contDiffOn_of_solutions S hS S' hS' hab hab hbt hslab hreg hslab' hreg' q y
          hy v).differentiableOn (by simp) s (hsub hs))
    exact ⟨.neck L'⟩
  · obtain ⟨hwin, houter, hmargin, hrho, hroom, hball, htube, hdeep⟩ := hcap Lc deep rfl
    obtain ⟨delta, hdelta, htr⟩ := Lc.exists_deep_transport_tolerance_of_metricComparisonOn hS
      ha hsmall heps hab hwin hslab hreg V hVcompact hK hKV hWK houter hQ hmargin hrho hroom
      hball htube hdeep
    refine ⟨delta, hdelta, ?_⟩
    intro N _ _ _ _ _ D' S' hS' hslab' hreg' F hF Cmp
    obtain ⟨L', _, _, _, hdeep'⟩ := htr N S' hS' hslab' hreg' F hF Cmp
    exact ⟨.cap L' hdeep'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
