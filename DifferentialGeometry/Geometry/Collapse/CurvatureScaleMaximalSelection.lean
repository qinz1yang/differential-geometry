import DifferentialGeometry.Geometry.Collapse.CurvatureScaleCoverApplications
import DifferentialGeometry.Geometry.Comparison.Volume.RicciScaleMultiplicityFamily

/-!
# LC86 for maximal families at the curvature scale (consumer)

The whole-row form of LC86 (`maximal_scale_selection_of_ricci_bound`,
`Geometry/Comparison/Volume/RicciScaleMultiplicityFamily.lean`) is bound to the actual curvature
scale `ρ p = c R_p` of a smooth metric `g` on a compact connected manifold, with the distance
induced by `g`; every ball in the statements is a `g`-ball.  Nothing about the selection is
assumed: maximal families exist, and EVERY maximal disjoint family of `a ρ`-balls with centres in a
stratum `S` is finite, its `4 a ρ`-balls cover `S`, and its `C ρ`-balls have multiplicity at most
`V_{-q²}(3C + 2a) / V_{-q²}(a)`, `q = (3C + 2a)⁻¹`.

* `maximal_curvatureScale_selection_riemannianBallOf`: general `c, a, C` with `c a ≤ 1/100`,
  `c C ≤ 1/4`.
* `closedThreeManifold_maximal_curvatureScale_selection`: on an actual connected closed oriented
  3-manifold with somewhere negative sectional curvature, `ρ = R / 100`, `a = 1/3`, `C = 1`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Topology
open Bundle Set
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]
  [T3Space M] [ConnectedSpace M] [CompactSpace M]

/-- LC86 for maximal families at the curvature scale `ρ p = c R_p`, every ball a `g`-ball. -/
theorem maximal_curvatureScale_selection_riemannianBallOf
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤) (S : Set M)
    {c a C : ℝ} (hc : 0 < c) (ha : 0 < a) (hC : 0 ≤ C)
    (hsel : c * a ≤ 1 / 100) (hover : c * C ≤ 1 / 4) :
    let ρ : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    let q : ℝ := (3 * C + 2 * a)⁻¹
    (∃ J : Set M, Maximal (fun K : Set M => K ⊆ S ∧
      K.PairwiseDisjoint (fun i => riemannianBallOf g i (a * ρ i))) J) ∧
    ∀ J : Set M, Maximal (fun K : Set M => K ⊆ S ∧
      K.PairwiseDisjoint (fun i => riemannianBallOf g i (a * ρ i))) J →
      J.Finite ∧ S ⊆ ⋃ i ∈ J, riemannianBallOf g i (4 * a * ρ i) ∧
      ∀ x : M, ((J ∩ {i | x ∈ riemannianBallOf g i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * a) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  intro ρ q
  let := inducedMetricSpace g
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian g
  have := hRM
  have := hcont
  have hLip : LipschitzWith ⟨c, hc.le⟩ ρ :=
    inducedMetricSpace_lipschitzWith_iff.2 (abs_curvatureScale_sub_le g hfin hc.le)
  have hD : 0 < 3 * C + 2 * a := by positivity
  have hDc : (3 * C + 2 * a) * c < 1 := by nlinarith
  have h := maximal_scale_selection_of_ricci_bound g hEnorm S hLip
    (fun p => mul_pos hc (toReal_curvatureRadius_pos g (hfin p))) ha hC (inv_nonneg.mpr hD.le)
    (show c * a ≤ 1 / 2 by linarith) hover (fun p _ => by
      rw [inducedMetricSpace_ball g]
      exact ricciBoundedBelowOn_curvatureScale g (hfin p) hc hD hDc)
  simp only [inducedMetricSpace_ball g] at h
  exact h

end Inner

/-- LC86 for maximal families on an actual connected closed oriented 3-manifold with somewhere
negative sectional curvature, at `ρ = R / 100` with `a = 1/3`, `C = 1`: every maximal disjoint
family of `R/300`-balls with centres in `S` is finite, its `R/75`-balls cover `S`, and every point
lies in at most `V_{-q²}(11/3) / V_{-q²}(1/3)` of its `R/100`-balls (`q = 3/11`). -/
theorem closedThreeManifold_maximal_curvatureScale_selection
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) (S : Set M.Carrier) :
    (∃ J : Set M.Carrier, Maximal (fun K : Set M.Carrier => K ⊆ S ∧
      K.PairwiseDisjoint (fun i => riemannianBallOf g i ((curvatureRadius g i).toReal / 300))) J) ∧
    ∀ J : Set M.Carrier, Maximal (fun K : Set M.Carrier => K ⊆ S ∧
      K.PairwiseDisjoint (fun i => riemannianBallOf g i ((curvatureRadius g i).toReal / 300))) J →
      J.Finite ∧ S ⊆ ⋃ i ∈ J, riemannianBallOf g i ((curvatureRadius g i).toReal / 75) ∧
      ∀ x : M.Carrier,
        ((J ∩ {i | x ∈ riemannianBallOf g i ((curvatureRadius g i).toReal / 100)}).ncard : ℝ) ≤
          modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (11 / 3) /
            modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (1 / 3) := by
  have := closedOrientedManifold_t2Space_tangentBundle M.toClosedOrientedManifold
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
  have hfin := curvatureRadius_ne_top_of_not_sectionalBoundedBelow hneg
  have h := maximal_curvatureScale_selection_riemannianBallOf g hfin S
    (c := 1 / 100) (a := 1 / 3) (C := 1) (by norm_num) (by norm_num) zero_le_one
    (by norm_num) (by norm_num)
  have h1 (p : M.Carrier) : 1 / 3 * (1 / 100 * (curvatureRadius g p).toReal) =
      (curvatureRadius g p).toReal / 300 := by ring
  have h2 (p : M.Carrier) : 4 * (1 / 3) * (1 / 100 * (curvatureRadius g p).toReal) =
      (curvatureRadius g p).toReal / 75 := by ring
  have h3 (p : M.Carrier) : 1 * (1 / 100 * (curvatureRadius g p).toReal) =
      (curvatureRadius g p).toReal / 100 := by ring
  have hD : (3 : ℝ) * 1 + 2 * (1 / 3) = 11 / 3 := by norm_num
  have hq : ((11 : ℝ) / 3)⁻¹ = 3 / 11 := by norm_num
  simp only [h1, h2, h3, hD, hq, finrank_euclideanSpace, Fintype.card_fin] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
