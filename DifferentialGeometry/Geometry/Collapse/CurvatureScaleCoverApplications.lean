import DifferentialGeometry.Geometry.Collapse.CurvatureScaleCover
import DifferentialGeometry.Topology.Manifold.ClosedOriented

/-!
# Consumers of the curvature-scale cover on closed 3-manifolds

The selection and the LC86 cover of `CurvatureScaleCover.lean` are applied to an arbitrary smooth
metric `g` on an actual connected closed oriented 3-manifold
(`DifferentialGeometry.Topology.ConnectedClosedOrientedManifold 3`) whose sectional curvature is
somewhere negative. The instance block of the cover (boundaryless model, `T3Space`, the tangent
bundle's `T2Space`, `NeZero` of the dimension) is discharged here from the manifold structure; no
hypothesis about the cover is made.

* `closedThreeManifold_curvatureScale_selection`: LC63 for the radii `R_p / 100` from any set of
  centres, with `g`-balls and the distance of `g`.
* `closedThreeManifold_curvatureScale_cover`: LC86 at the scale `ρ = R / 100` with `Δ = C = 1`:
  disjoint `ρ/3`-balls, `2ρ`-balls covering every `ρ`-ball, and multiplicity of the `ρ`-balls at
  most `V_{-q²}(11/3) / V_{-q²}(1/3)` in dimension 3, `q = 3/11`.
* `exists_nat_curvatureScale_cover_multiplicity`: one natural number `N` bounds that multiplicity
  for every such metric on every connected closed oriented 3-manifold.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Topology
open Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Collapse
universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The tangent bundle of a closed oriented manifold is Hausdorff. -/
theorem closedOrientedManifold_t2Space_tangentBundle {n : ℕ}
    (M : ClosedOrientedManifold.{u} n) :
    T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M.Carrier) := by
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 M.Carrier :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  infer_instance

/-- LC63 at the curvature scale on a connected closed oriented 3-manifold: radii `R_p / 100`,
centres in an arbitrary set `P`. -/
theorem closedThreeManifold_curvatureScale_selection (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) (P : Set M.Carrier) :
    ∃ J : Set M.Carrier, J ⊆ P ∧ J.Finite ∧
      J.PairwiseDisjoint (fun p => riemannianBallOf g p ((curvatureRadius g p).toReal / 100)) ∧
      ∀ p ∈ P, ∃ i ∈ J,
        (riemannianBallOf g p ((curvatureRadius g p).toReal / 100) ∩
          riemannianBallOf g i ((curvatureRadius g i).toReal / 100)).Nonempty ∧
        (curvatureRadius g p).toReal ≤ 2 * (curvatureRadius g i).toReal ∧
        (riemannianEDistOf g p i).toReal < 3 * ((curvatureRadius g i).toReal / 100) ∧
        riemannianBallOf g p ((curvatureRadius g p).toReal / 100) ⊆
          riemannianBallOf g i (5 * ((curvatureRadius g i).toReal / 100)) := by
  have hfin := curvatureRadius_ne_top_of_not_sectionalBoundedBelow hneg
  obtain ⟨J, hJP, hJ, hdisj, hsel⟩ :=
    exists_finite_disjoint_curvatureScale_selection_riemannianBallOf g hfin P
      (by norm_num : (0 : ℝ) < 1 / 100)
  have hr (p : M.Carrier) : 1 / 100 * (curvatureRadius g p).toReal =
      (curvatureRadius g p).toReal / 100 := by ring
  simp only [hr] at hdisj hsel
  refine ⟨J, hJP, hJ, hdisj, fun p hp => ?_⟩
  obtain ⟨i, hi, hmeet, hscale, hdist, hball⟩ := hsel p hp
  exact ⟨i, hi, hmeet, by linarith, hdist, hball⟩

/-- LC86 at the curvature scale on a connected closed oriented 3-manifold, at `ρ = R / 100` with
`Δ = C = 1`; the multiplicity bound is the 3-dimensional model-volume ratio for `q = 3/11`. -/
theorem closedThreeManifold_curvatureScale_cover (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M.Carrier)
    (hneg : ¬ SectionalBoundedBelow g 0) :
    ∃ J : Set M.Carrier, J.Finite ∧
      J.PairwiseDisjoint
        (fun p => riemannianBallOf g p ((curvatureRadius g p).toReal / 100 / 3)) ∧
      (∀ p : M.Carrier, ∃ i ∈ J,
        riemannianBallOf g p ((curvatureRadius g p).toReal / 100) ⊆
          riemannianBallOf g i (2 * ((curvatureRadius g i).toReal / 100))) ∧
      ∀ x : M.Carrier,
        ((J ∩ {i | x ∈ riemannianBallOf g i ((curvatureRadius g i).toReal / 100)}).ncard : ℝ) ≤
          modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (11 / 3) /
            modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (1 / 3) := by
  have := closedOrientedManifold_t2Space_tangentBundle M.toClosedOrientedManifold
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩
  have hfin := curvatureRadius_ne_top_of_not_sectionalBoundedBelow hneg
  obtain ⟨J, -, hJ, hdisj, hcover, hmult⟩ :=
    exists_finite_curvatureScale_cover_riemannianBallOf g hfin univ
      (by norm_num : (0 : ℝ) < 1 / 100) one_pos zero_le_one (by norm_num) (by norm_num)
  have hr (p : M.Carrier) : 1 / 100 * (curvatureRadius g p).toReal =
      (curvatureRadius g p).toReal / 100 := by ring
  have hD : (3 : ℝ) + 2 * (1 / 3) = 11 / 3 := by norm_num
  have hq : ((11 : ℝ) / 3)⁻¹ = 3 / 11 := by norm_num
  simp only [hr, one_mul, mul_one, finrank_euclideanSpace, Fintype.card_fin, hD, hq]
    at hdisj hcover hmult
  exact ⟨J, hJ, hdisj, fun p => hcover p (mem_univ p), hmult⟩

/-- The multiplicity of the curvature-scale cover is bounded by one natural number, uniformly over
all connected closed oriented 3-manifolds and all metrics with somewhere negative sectional
curvature. -/
theorem exists_nat_curvatureScale_cover_multiplicity :
    ∃ N : ℕ, ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
      (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M.Carrier),
      ¬ SectionalBoundedBelow g 0 →
      ∃ J : Set M.Carrier, J.Finite ∧
        J.PairwiseDisjoint
          (fun p => riemannianBallOf g p ((curvatureRadius g p).toReal / 100 / 3)) ∧
        (∀ p : M.Carrier, ∃ i ∈ J,
          riemannianBallOf g p ((curvatureRadius g p).toReal / 100) ⊆
            riemannianBallOf g i (2 * ((curvatureRadius g i).toReal / 100))) ∧
        ∀ x : M.Carrier,
          (J ∩ {i | x ∈ riemannianBallOf g i ((curvatureRadius g i).toReal / 100)}).ncard ≤ N := by
  refine ⟨⌈modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (11 / 3) /
      modelVolume (-((3 / 11 : ℝ) ^ 2)) 3 (1 / 3)⌉₊, fun M g hneg => ?_⟩
  obtain ⟨J, hJ, hdisj, hcover, hmult⟩ := closedThreeManifold_curvatureScale_cover M g hneg
  exact ⟨J, hJ, hdisj, hcover, fun x => Nat.cast_le.mp ((hmult x).trans (Nat.le_ceil _))⟩

end DifferentialGeometry.Geometry.Collapse
