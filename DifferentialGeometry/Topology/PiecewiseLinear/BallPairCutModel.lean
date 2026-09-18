import DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairTwoSimplices
import DifferentialGeometry.Topology.PiecewiseLinear.SegmentSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem vertex_mem_simplexBoundary_space {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {v : E} (hv : v ∈ T) (hcard : 2 ≤ T.card) :
    v ∈ (simplexBoundary T hT).space := by
  refine (simplexBoundary T hT).convexHull_subset_space
    (mem_simplexBoundary_faces_iff.mpr ⟨Finset.singleton_subset_iff.mpr hv,
      Finset.singleton_nonempty v, fun h => ?_⟩) ?_
  · rw [← h, Finset.card_singleton] at hcard
    omega
  · rw [Finset.coe_singleton, convexHull_singleton]
    rfl

section CutModel

variable [DecidableEq E] {F : Finset E} {c d m p z : E} {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ}
  (hFcard : F.card = 2) (hcdF : c ∉ insert d F) (hdF : d ∉ F) (hcmF : c ∉ insert m F)
  (hmF : m ∉ F)
  (hT : AffineIndependent ℝ ((↑) : (insert c (insert d F) : Finset E) → E))
  (hT₁ : AffineIndependent ℝ ((↑) : (insert c (insert m F) : Finset E) → E))
  (hℓ : ∀ v ∈ (insert m F : Finset E), ℓ v = r) (hℓc : ℓ c < r) (hℓd : r < ℓ d)
  (hz : z ∈ openSimplex (insert m F : Finset E)) (hzs : z ∈ segment ℝ p d)

include hFcard hcdF hdF hT in
theorem isPLBallPair_cut_union (hp : p ∈ openSimplex (insert c (insert d F) : Finset E))
    (hcd : c ≠ d) (hpc : p ≠ c) (hpd : p ≠ d)
    (hrad : IsRadiallyInjective p ({c, d} : Set E)) :
    IsPLBallPair 2 1 (convexHull ℝ ((insert c (insert d F) : Finset E) : Set E))
      (segment ℝ p c ∪ segment ℝ p d) := by
  have hcard : (insert c (insert d F) : Finset E).card = 2 + 2 := by
    rw [Finset.card_insert_of_notMem hcdF, Finset.card_insert_of_notMem hdF, hFcard]
  have h2 : 2 ≤ (insert c (insert d F) : Finset E).card := by omega
  refine isPLBallPair_convexHull_arc_of_radial hT hcard hp ?_ hcd hpc hpd hrad
  rintro x (rfl | hx)
  · exact vertex_mem_simplexBoundary_space hT (Finset.mem_insert_self _ _) h2
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact vertex_mem_simplexBoundary_space hT
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h2

include hFcard hcmF hmF hT₁ hℓ hℓc hℓd hz hzs in
theorem isPLBallPair_cut_left (hp₁ : p ∈ openSimplex (insert c (insert m F) : Finset E))
    (hcz : c ≠ z) (hpc : p ≠ c) (hpz : p ≠ z)
    (hrad₁ : IsRadiallyInjective p ({c, z} : Set E)) :
    IsPLBallPair 2 1 (convexHull ℝ ((insert c (insert m F) : Finset E) : Set E))
        (segment ℝ p c ∪ segment ℝ p z) ∧
      convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) ∩
        (segment ℝ p c ∪ segment ℝ p d) = segment ℝ p c ∪ segment ℝ p z := by
  have hcard : (insert c (insert m F) : Finset E).card = 2 + 2 := by
    rw [Finset.card_insert_of_notMem hcmF, Finset.card_insert_of_notMem hmF, hFcard]
  have h2 : 2 ≤ (insert c (insert m F) : Finset E).card := by omega
  have hFmsub : (convexHull ℝ ((insert m F : Finset E) : Set E)) ⊆
      convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert c _))
  have hzFm : z ∈ convexHull ℝ ((insert m F : Finset E) : Set E) :=
    openSimplex_subset_convexHull _ hz
  have hFmplane : convexHull ℝ ((insert m F : Finset E) : Set E) ⊆ {x : E | ℓ x = r} :=
    convexHull_min (fun v hv => hℓ v (Finset.mem_coe.mp hv)) (convex_hyperplane ℓ.isLinear r)
  have hzr : ℓ z = r := hFmplane hzFm
  have hle : convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) ⊆ {x : E | ℓ x ≤ r} :=
    convexHull_insert_subset_halfSpace_le ℓ hℓ hℓc.le
  have hpT₁ : p ∈ convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) :=
    openSimplex_subset_convexHull _ hp₁
  have hcT₁ : c ∈ convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) :=
    subset_convexHull ℝ _ (by simp)
  have hpr : ℓ p ≤ r := hle hpT₁
  have hpcsub : segment ℝ p c ⊆ convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) :=
    (convex_convexHull ℝ _).segment_subset hpT₁ hcT₁
  have hpzsub : segment ℝ p z ⊆ convexHull ℝ ((insert c (insert m F) : Finset E) : Set E) :=
    (convex_convexHull ℝ _).segment_subset hpT₁ (hFmsub hzFm)
  refine ⟨isPLBallPair_convexHull_arc_of_radial hT₁ hcard hp₁ ?_ hcz hpc hpz hrad₁,
    inter_arc_of_subset_halfSpace_le hle hpcsub hpzsub hzs hzr hpr hℓd⟩
  rintro x (rfl | hx)
  · exact vertex_mem_simplexBoundary_space hT₁ (Finset.mem_insert_self _ _) h2
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine (simplexBoundary _ hT₁).convexHull_subset_space
      (mem_simplexBoundary_faces_iff.mpr ⟨Finset.subset_insert c _,
        ⟨m, Finset.mem_insert_self m F⟩, fun h => hcmF (h ▸ Finset.mem_insert_self c _)⟩) hzFm

end CutModel

end DifferentialGeometry.Topology.PiecewiseLinear
