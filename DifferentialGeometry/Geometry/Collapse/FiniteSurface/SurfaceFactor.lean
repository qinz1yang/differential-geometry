import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingRow

/-!
# LFR16: the surface clause of the compact factor

Chapter 13, row LFR16 (`lem:collapse-finite-compact-factor`), the clause that depends on LFR11.
Let `N` be a complete connected Riemannian 3-manifold with a `C^{r+1}` metric `G` (`r ≥ 2`) of
nonnegative sectional curvature and let `e : N ≃ᵢ ℓ²(ℝ × W)` be an exact line splitting whose
residual factor `W` is compact with diameter at most `D`. Then the SAME factor
`Z = {x | (e x).fst = 0}` of LFR11 (X96's regular-zero atlas, induced metric `h`) is a compact
connected boundaryless surface of class `C^{r+2}` with diameter at most `D`, `h` is a
nonnegatively curved `C^{r+1}` metric whose distance is the subtype distance, and the actual
product map `ℝ × Z → N` is a `C^{r+2}` diffeomorphism with `Ψ^* G = dt² + h`
(`surfaceFactor_of_exactSplitting`).

`surfaceFactor_of_finite_limit` is the same clause in the shape of the finite Cheeger–Gromov
limits of L-CONS (`exists_finite_cheeger_gromov_limit_with_coordinate_pullback`): metric of order
`K - 1` (`K ≥ 4`) carried by the bundle `⟨G.toRiemannianMetric⟩`.

NOT included (recorded in build-logs/resume/sheet-F7-LFR11b.md): the word "orientable" (finite-order
orientation, U4), and the merge of L-CONS (a), (b), (c) onto one subsequence.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_F7LFR11b :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

theorem finrank_euclidean_three_sub_one :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ = 2 := by
  rw [finrank_euclideanSpace_fin, Module.finrank_self]

section Kernel

variable {N W : Type*} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) N]
  [CompleteSpace N] [MetricSpace W] {r : ℕ∞}

/-- **LFR16, surface clause (kernel on the limit data).** -/
theorem surfaceFactor_of_exactSplitting [ConnectedSpace N] [CompactSpace W]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hr hnorm e
    letI := splittingFactor_isManifold_one G hr hnorm e
    Module.finrank ℝ E3 - Module.finrank ℝ ℝ = 2 ∧
    CompactSpace {x : N // (e x).fst = 0} ∧ ConnectedSpace {x : N // (e x).fst = 0} ∧
    (∀ z z' : {x : N // (e x).fst = 0}, dist z z' ≤ D) ∧
    (𝓘(ℝ, P)).Boundaryless ∧
    IsManifold 𝓘(ℝ, P) ((r : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
    (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, P) : {x : N // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric G hr hnorm e).toRiemannianMetric⟩
     IsRiemannianManifold 𝓘(ℝ, P) {x : N // (e x).fst = 0}) ∧
    (∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace 𝓘(ℝ, P) z),
      0 ≤ (inducedMetric G hr hnorm e).sectionalCurvature z v w) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) ((r : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G hr hnorm e) ∧
    ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) ((r : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G hr hnorm e).symm ∧
    (∀ (p : ℝ × {x : N // (e x).fst = 0})
      (v w : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) p),
      G.inner (splittingProductDiffeomorph G hr hnorm e p)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) (splittingProductDiffeomorph G hr hnorm e) p v)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) (splittingProductDiffeomorph G hr hnorm e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric G hr hnorm e).inner p.2 v.2 w.2) := by
  let _ := splittingFactorChartedSpace G hr hnorm e
  let _ := splittingFactor_isManifold_one G hr hnorm e
  obtain ⟨-, hZm, -, -, -, -, hRiem, -, hconn, -, hΨ, hΨs, -, hmet, -, hnn⟩ :=
    exactSplitting_regularity G hr hnorm e
  let φ := splittingFactorEquiv e
  refine ⟨finrank_euclidean_three_sub_one, φ.toHomeomorph.compactSpace, hconn inferInstance,
    fun z z' => ?_, inferInstance, hZm, hRiem, hnn hsec, hΨ, hΨs, hmet⟩
  rw [← φ.apply_symm_apply z, ← φ.apply_symm_apply z', φ.dist_eq]
  exact hD _ _

end Kernel

section FiniteLimit

variable {N W : Type*} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
  [MetricSpace W]

/-- A finite metric of natural order `K - 1` (`K ≥ 4`), re-indexed as `((K - 2 : ℕ) : ℕ∞) + 1`,
the order convention of LFR11. The inner product is unchanged. -/
def finiteMetricReindex (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) :
    ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _) :=
  { G with
    contMDiff := by
      have h : ((K - 1 : ℕ) : ℕ∞ω) = (((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 1 := by
        have hk : K - 1 = (K - 2) + 1 := by omega
        rw [hk]
        push_cast
        rfl
      exact h ▸ G.contMDiff }

theorem finiteMetricReindex_inner (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (x : N) :
    (finiteMetricReindex K hK G).inner x = G.inner x := rfl

theorem two_le_reindex (K : ℕ) (hK : 4 ≤ K) : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
  exact_mod_cast (show 2 ≤ K - 2 by omega)

theorem finiteMetricReindex_enorm (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) :
    letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
    ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((finiteMetricReindex K hK G).inner x v v)) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  intro x v
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

/-- **LFR16, surface clause, in the shape of the L-CONS limits.** A finite Cheeger–Gromov limit
`N` (order `K - 1`, `K ≥ 4`, carried by `⟨G.toRiemannianMetric⟩`, proper and connected) with
nonnegative curvature and an exact line splitting with compact residual factor of diameter
`≤ D` has a compact connected boundaryless `C^{K}` surface factor of diameter `≤ D`, a
nonnegatively curved `C^{K-1}` induced metric, and a `C^K` product diffeomorphism. -/
theorem surfaceFactor_of_finite_limit [ProperSpace N] [ConnectedSpace N] [CompactSpace W]
    (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
    letI := splittingFactorChartedSpace (finiteMetricReindex K hK G) (two_le_reindex K hK)
      (finiteMetricReindex_enorm K hK G) e
    letI := splittingFactor_isManifold_one (finiteMetricReindex K hK G) (two_le_reindex K hK)
      (finiteMetricReindex_enorm K hK G) e
    CompactSpace {x : N // (e x).fst = 0} ∧ ConnectedSpace {x : N // (e x).fst = 0} ∧
    (∀ z z' : {x : N // (e x).fst = 0}, dist z z' ≤ D) ∧
    IsManifold 𝓘(ℝ, P) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
    (∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace 𝓘(ℝ, P) z),
      0 ≤ (inducedMetric (finiteMetricReindex K hK G) (two_le_reindex K hK)
        (finiteMetricReindex_enorm K hK G) e).sectionalCurvature z v w) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
      (splittingProductDiffeomorph (finiteMetricReindex K hK G) (two_le_reindex K hK)
        (finiteMetricReindex_enorm K hK G) e) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  let _ := splittingFactorChartedSpace (finiteMetricReindex K hK G) (two_le_reindex K hK)
    (finiteMetricReindex_enorm K hK G) e
  let _ := splittingFactor_isManifold_one (finiteMetricReindex K hK G) (two_le_reindex K hK)
    (finiteMetricReindex_enorm K hK G) e
  have hsec' : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x),
      0 ≤ (finiteMetricReindex K hK G).sectionalCurvature x v w := fun x v w => hsec x v w
  obtain ⟨-, hc, hconn, hdiam, -, hZm, -, hnn, hΨ, -, -⟩ :=
    surfaceFactor_of_exactSplitting (finiteMetricReindex K hK G) (two_le_reindex K hK)
      (finiteMetricReindex_enorm K hK G) hsec' hD e
  exact ⟨hc, hconn, hdiam, hZm, hnn, hΨ⟩

end FiniteLimit

end DifferentialGeometry.Geometry.Collapse
