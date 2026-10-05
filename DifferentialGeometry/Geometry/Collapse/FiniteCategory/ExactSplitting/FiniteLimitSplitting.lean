import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingRow

/-!
# LFR11 at metric order `K - 1` on a finite Cheeger–Gromov limit (LFR15, product clause)

The limits of L-CONS carry a metric `G` of natural order `K - 1` and the Riemannian structure
`⟨G.toRiemannianMetric⟩`. `finiteOrderMetricReindex` re-indexes `G` (`K ≥ 4`) to LFR11's order
convention `((K - 2 : ℕ) : ℕ∞) + 1`, and `exactSplitting_of_finite_limit` applies LFR11
(`exactSplitting_regularity`) to the ACTUAL metric isometry `e : N ≃ᵢ ℓ²(F × W)`: the exact
coordinate `t` is `C^K`, the zero factor `Z` is a `C^K` manifold with complete induced
`C^{K-1}` metric, nonnegatively curved when `G` is, and the actual product map is a `C^K`
diffeomorphism with `Ψ^* G = du² + h`. Any model space, any rank of `F`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Reindex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

/-- A finite metric of natural order `K - 1` (`K ≥ 4`), re-indexed as `((K - 2 : ℕ) : ℕ∞) + 1`
(LFR11's convention); the inner product is unchanged. -/
def finiteOrderMetricReindex (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _)) :
    ContMDiffRiemannianMetric 𝓘(ℝ, E) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 1) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _) :=
  { G with
    contMDiff := by
      have h : ((K - 1 : ℕ) : ℕ∞ω) = (((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 1 := by
        have hk : K - 1 = (K - 2) + 1 := by omega
        rw [hk]
        push_cast
        rfl
      exact h ▸ G.contMDiff }

omit [FiniteDimensional ℝ E] in
theorem finiteOrderMetricReindex_inner (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _)) (x : N) :
    (finiteOrderMetricReindex K hK G).inner x = G.inner x := rfl

theorem two_le_finiteOrderReindex (K : ℕ) (hK : 4 ≤ K) : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
  exact_mod_cast (show 2 ≤ K - 2 by omega)

omit [FiniteDimensional ℝ E] in
theorem finiteOrderMetricReindex_enorm (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _)) :
    letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
    ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((finiteOrderMetricReindex K hK G).inner x v v)) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  intro x v
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

end Reindex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {N W : Type*} [MetricSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [CompleteSpace N]
  [MetricSpace W]

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

/-- **LFR11 at metric order `K - 1` on a finite limit (LFR15's product clause).** For a complete
manifold `N` carrying a metric `G` of natural order `K - 1` (`K ≥ 4`) as its Riemannian structure
and an exact splitting `e : N ≃ᵢ ℓ²(F × W)`: `t = (e ·).fst` is `C^K`; `Z = t⁻¹(0)` is a `C^K`
manifold, complete, with the induced `C^{K-1}` metric `h` (Riemannian distance = subtype
distance), `sec_h ≥ 0` if `sec_G ≥ 0`; the actual product map `Ψ (u, z) = e⁻¹ (u, π_W e z)` is a
`C^K` diffeomorphism `F × Z → N` with `Ψ^* G = du² + h`. -/
theorem exactSplitting_of_finite_limit (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E) N)
    (e : N ≃ᵢ WithLp 2 (F × W)) :
    letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
    letI := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
      (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
    letI := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
      (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) (fun x => (e x).fst) ∧
    IsManifold IZ ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
    (letI : RiemannianBundle (TangentSpace IZ : {x : N // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
        (finiteOrderMetricReindex_enorm K hK G) e).toRiemannianMetric⟩
     IsRiemannianManifold IZ {x : N // (e x).fst = 0}) ∧
    CompleteSpace {x : N // (e x).fst = 0} ∧
    ((∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E) x), 0 ≤ G.sectionalCurvature x v w) →
      ∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace IZ z),
        0 ≤ (inducedMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
          (finiteOrderMetricReindex_enorm K hK G) e).sectionalCurvature z v w) ∧
    ContMDiff IP 𝓘(ℝ, E) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
      (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
        (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) ∧
    ContMDiff 𝓘(ℝ, E) IP ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
      (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
        (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).symm ∧
    (∀ p : F × {x : N // (e x).fst = 0},
      splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
        (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p =
        e.symm (toLp 2 (p.1, (e p.2.val).snd))) ∧
    (∀ (p : F × {x : N // (e x).fst = 0}) (v w : TangentSpace IP p),
      G.inner (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
        (mfderiv IP 𝓘(ℝ, E) (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) p v)
        (mfderiv IP 𝓘(ℝ, E) (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
          (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric (finiteOrderMetricReindex K hK G)
        (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).inner
          p.2 v.2 w.2) := by
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E) N := hRiem
  let _ := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  let _ := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  obtain ⟨hT, hZ, -, -, -, -, hRZ, hcZ, -, -, hΨ, hΨs, hΨe, hΨm, -, hsec⟩ :=
    exactSplitting_regularity (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
      (finiteOrderMetricReindex_enorm K hK G) e
  exact ⟨hT, hZ, hRZ, hcZ, fun h => hsec h, hΨ, hΨs, hΨe, hΨm⟩

end DifferentialGeometry.Geometry.ExactSplitting
