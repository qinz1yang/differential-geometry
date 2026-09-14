import DifferentialGeometry.Topology.Homology.HurewiczSphereGenerationCriterion

noncomputable section

open ContinuousMap Metric Set

universe u

namespace DifferentialGeometry.Topology

private def hemisphereLastCoordinate (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : ℝ :=
  p.1 (Fin.last n)

private def hemisphereBallProjection (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => p.1 (Fin.castSucc i)

private theorem hemisphereLastCoordinate_continuous (n : ℕ) :
    Continuous (hemisphereLastCoordinate n) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).continuous).comp continuous_subtype_val

private theorem hemisphereBallProjection_continuous (n : ℕ) :
    Continuous (hemisphereBallProjection n) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    (continuous_pi fun i => ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).continuous).comp
      continuous_subtype_val)

private theorem norm_eq_one_of_mem_unit_sphere (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : ‖p.1‖ = 1 := by
  have h := Metric.mem_sphere.mp p.2
  rwa [dist_eq_norm, sub_zero] at h

private theorem hemisphereBallProjection_norm_sq (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ‖hemisphereBallProjection n p‖ ^ 2 = ∑ i : Fin n, (p.1 (Fin.castSucc i)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [hemisphereBallProjection]

private theorem hemisphereBallProjection_norm_le (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ‖hemisphereBallProjection n p‖ ≤ 1 := by
  have hsplit : ‖p.1‖ ^ 2 =
      ∑ i : Fin n, (p.1 (Fin.castSucc i)) ^ 2 + (p.1 (Fin.last n)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Fin.sum_univ_castSucc (fun i => (p.1.ofLp i) ^ 2)
  have hsq : ‖hemisphereBallProjection n p‖ ^ 2 ≤ 1 := by
    rw [hemisphereBallProjection_norm_sq]
    nlinarith [hsplit, norm_eq_one_of_mem_unit_sphere n p, sq_nonneg (p.1 (Fin.last n))]
  nlinarith [hsq, norm_nonneg (hemisphereBallProjection n p)]

private theorem hemisphereBallProjection_mem_unit_sphere_of_lastCoordinate_eq_zero (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (h : hemisphereLastCoordinate n p = 0) :
    hemisphereBallProjection n p ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have hsplit : ‖p.1‖ ^ 2 =
      ∑ i : Fin n, (p.1 (Fin.castSucc i)) ^ 2 + (p.1 (Fin.last n)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Fin.sum_univ_castSucc (fun i => (p.1.ofLp i) ^ 2)
  have hlast : p.1 (Fin.last n) = 0 := h
  have hsq : ‖hemisphereBallProjection n p‖ ^ 2 = 1 := by
    rw [hemisphereBallProjection_norm_sq]
    nlinarith [hsplit, norm_eq_one_of_mem_unit_sphere n p, hlast]
  nlinarith [hsq, norm_nonneg (hemisphereBallProjection n p)]

private def hemisphereBall (n : ℕ) (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨hemisphereBallProjection n p, by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hemisphereBallProjection_norm_le n p⟩

private theorem hemisphereBall_continuous (n : ℕ) : Continuous (hemisphereBall n) :=
  (hemisphereBallProjection_continuous n).subtype_mk _

def sphereBallBoundaryInclusion (n : ℕ) :
    C(sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ⟨fun q => ⟨q.1, sphere_subset_closedBall q.2⟩, continuous_subtype_val.subtype_mk _⟩

private theorem hemisphereBall_eq_boundaryInclusion_of_lastCoordinate_eq_zero (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (h : hemisphereLastCoordinate n p = 0) :
    hemisphereBall n p = sphereBallBoundaryInclusion n
      ⟨hemisphereBallProjection n p,
        hemisphereBallProjection_mem_unit_sphere_of_lastCoordinate_eq_zero n p h⟩ :=
  Subtype.ext rfl

private theorem hemisphereLastCoordinate_eq_zero_of_mem_frontier (n : ℕ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hp : p ∈ frontier {x | 0 ≤ hemisphereLastCoordinate n x}) :
    hemisphereLastCoordinate n p = 0 := by
  simp only [frontier, Set.mem_sdiff] at hp
  have hc := hemisphereLastCoordinate_continuous n
  have hge : 0 ≤ hemisphereLastCoordinate n p :=
    closure_minimal (fun x hx => hx) (isClosed_Ici.preimage hc) hp.1
  have hle : hemisphereLastCoordinate n p ≤ 0 := by
    by_contra h
    have hlt : 0 < hemisphereLastCoordinate n p := not_le.mp h
    have hopen : IsOpen {x | 0 < hemisphereLastCoordinate n x} := isOpen_Ioi.preimage hc
    have hsub : {x | 0 < hemisphereLastCoordinate n x} ⊆
        {x | 0 ≤ hemisphereLastCoordinate n x} := fun x hx => le_of_lt (by simpa using hx)
    exact hp.2 (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds hlt) hsub))
  exact le_antisymm hle hge

variable {X : Type u} [TopologicalSpace X]

def gluedSphereMap (n : ℕ) (u v : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X))
    (h : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      u (sphereBallBoundaryInclusion (n + 1) q) = v (sphereBallBoundaryInclusion (n + 1) q)) :
    C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  ⟨fun p => if 0 ≤ hemisphereLastCoordinate (n + 1) p then u (hemisphereBall (n + 1) p)
    else v (hemisphereBall (n + 1) p), by
      refine continuous_if (fun p hp => ?_)
        (u.continuous.comp (hemisphereBall_continuous (n + 1))).continuousOn
        (v.continuous.comp (hemisphereBall_continuous (n + 1))).continuousOn
      rw [hemisphereBall_eq_boundaryInclusion_of_lastCoordinate_eq_zero (n + 1) p
        (hemisphereLastCoordinate_eq_zero_of_mem_frontier (n + 1) p hp)]
      exact h _⟩

theorem gluedSphereMap_apply_of_nonneg (n : ℕ)
    (u v : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X))
    (h : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      u (sphereBallBoundaryInclusion (n + 1) q) = v (sphereBallBoundaryInclusion (n + 1) q))
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (hp : 0 ≤ hemisphereLastCoordinate (n + 1) p) :
    gluedSphereMap n u v h p = u (hemisphereBall (n + 1) p) := by
  simp only [gluedSphereMap, ContinuousMap.coe_mk, if_pos hp]

theorem gluedSphereMap_apply_of_neg (n : ℕ)
    (u v : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, X))
    (h : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      u (sphereBallBoundaryInclusion (n + 1) q) = v (sphereBallBoundaryInclusion (n + 1) q))
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (hp : hemisphereLastCoordinate (n + 1) p < 0) :
    gluedSphereMap n u v h p = v (hemisphereBall (n + 1) p) := by
  simp only [gluedSphereMap, ContinuousMap.coe_mk, if_neg (not_le.mpr hp)]

def OpenCoverLinkingRealization (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) : Prop :=
  ∀ y : integralSingularHomology (n + 1) X,
    ∃ f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      integralOpenCoverLinkingMap n A B hA hB hcover
          (freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk f)) =
        integralOpenCoverLinkingMap n A B hA hB hcover y

def OpenCoverSphereGluingRealization (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) : Prop :=
  ∀ y : integralSingularHomology (n + 1) X,
    ∃ (u : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ↥A))
      (v : C(closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ↥B))
      (h : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        (u (sphereBallBoundaryInclusion (n + 1) q) : X) =
          (v (sphereBallBoundaryInclusion (n + 1) q) : X)),
      integralOpenCoverLinkingMap n A B hA hB hcover
          (freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk (gluedSphereMap n ((singularSubspaceInclusion A).comp u)
              ((singularSubspaceInclusion B).comp v) h))) =
        integralOpenCoverLinkingMap n A B hA hB hcover y

theorem openCoverLinkingRealization_of_sphereGluingRealization (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (h : OpenCoverSphereGluingRealization n A B hA hB hcover) :
    OpenCoverLinkingRealization n A B hA hB hcover := by
  intro y
  obtain ⟨u, v, hu, hf⟩ := h y
  exact ⟨gluedSphereMap n ((singularSubspaceInclusion A).comp u)
    ((singularSubspaceInclusion B).comp v) hu, hf⟩

theorem openCoverSphereGluingRealization_of_subsingleton_linking (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (z : ↥(subspaceIntersection A B))
    (hI : Subsingleton (integralSingularHomology n ↥(subspaceIntersection A B))) :
    OpenCoverSphereGluingRealization n A B hA hB hcover := by
  intro y
  refine ⟨ContinuousMap.const _ ⟨z.1.1, z.2⟩, ContinuousMap.const _ z.1, ?_,
    Subsingleton.elim _ _⟩
  intro q
  rfl

theorem hurewiczThreeSphereGeneration_of_openCoverLinkingRealization [PathConnectedSpace X]
    (x₀ : X) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology 3 ↥A))
    (hgen : HurewiczThreeSphereGeneration ↥B)
    (hmul : ∀ a b : HomotopyGroup (Fin 3) X x₀,
      sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2) b)
    (hlink : OpenCoverLinkingRealization 2 A B hA hB hcover) :
    HurewiczThreeSphereGeneration X :=
  hurewiczThreeSphereGeneration_of_open_cover_of_linkingRealization x₀ A B hA hB hcover
    hA' hgen hmul hlink

theorem openCoverLinkingRealization_of_hurewiczThreeSphereGeneration (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hgen : HurewiczThreeSphereGeneration X) :
    OpenCoverLinkingRealization 2 A B hA hB hcover := by
  intro y
  obtain ⟨f, hf⟩ := hgen y
  exact ⟨f, by rw [hf]⟩

theorem openCoverLinkingRealization_of_subsingleton_linking [Nonempty X] (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hI : Subsingleton (integralSingularHomology n ↥(subspaceIntersection A B))) :
    OpenCoverLinkingRealization n A B hA hB hcover := by
  intro y
  exact ⟨ContinuousMap.const _ (Classical.arbitrary X), Subsingleton.elim _ _⟩

theorem openCoverLinkingRealization_and_not_hurewiczThreeSphereGeneration
    [PathConnectedSpace X] (x : X) (hpi : Subsingleton (HomotopyGroup (Fin 3) X x))
    (hnh : ¬ Subsingleton (integralSingularHomology 3 X)) (A B : Set X) (hA : IsOpen A)
    (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hI : Subsingleton (integralSingularHomology 2 ↥(subspaceIntersection A B))) :
    OpenCoverLinkingRealization 2 A B hA hB hcover ∧ ¬ HurewiczThreeSphereGeneration X :=
  ⟨openCoverLinkingRealization_of_subsingleton_linking 2 A B hA hB hcover hI,
    not_hurewiczThreeSphereGeneration_of_subsingleton_homotopyGroup_of_not_subsingleton_homology
      x hpi hnh⟩

end DifferentialGeometry.Topology
