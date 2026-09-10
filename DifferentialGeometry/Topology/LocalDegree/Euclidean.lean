import DifferentialGeometry.Topology.LocalDegree.IsolatedZero
import DifferentialGeometry.Topology.LocalDegree.SphereDegree

set_option autoImplicit false
open Filter Metric Set
open scoped Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {d : ℕ}


theorem euclideanSphereDegree_sphereMap_eq
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanSpace ℝ (Fin (d + 1))) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hz : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0) (r₀ r₁ : Ioc (0 : ℝ) R) :
    euclideanSphereDegree (sphereMap f x R hf hz r₀) =
      euclideanSphereDegree (sphereMap f x R hf hz r₁) :=
  euclideanSphereDegree_eq_of_homotopy (sphereMapHomotopy f x R hf hz r₀ r₁)

private def radiusSphereMap
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (h : IsolatingRadius f x R) :
    C(EuclideanSphere d, EuclideanSphere d) :=
  sphereMap f x R h.continuousOn h.nonzero ⟨R, h.pos, le_rfl⟩

private theorem radius_degree_eq
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R S : ℝ}
    (hR : IsolatingRadius f x R) (hS : IsolatingRadius f x S) :
    euclideanSphereDegree (radiusSphereMap hR) = euclideanSphereDegree (radiusSphereMap hS) := by
  let r : ℝ := min R S
  have hr : 0 < r := lt_min hR.pos hS.pos
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r ≤ S := min_le_right _ _
  calc
    euclideanSphereDegree (radiusSphereMap hR) =
        euclideanSphereDegree (sphereMap f x R hR.continuousOn hR.nonzero ⟨r, hr, hrR⟩) :=
      euclideanSphereDegree_sphereMap_eq _ _ _ _ _ _ _
    _ = euclideanSphereDegree (sphereMap f x S hS.continuousOn hS.nonzero ⟨r, hr, hrS⟩) := by
      congr 1
    _ = euclideanSphereDegree (radiusSphereMap hS) :=
      euclideanSphereDegree_sphereMap_eq _ _ _ _ _ _ _

def euclideanLocalDegree
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (x : EuclideanSpace ℝ (Fin (d + 1))) (h : isolatedZero f x) : ℤ :=
  euclideanSphereDegree (radiusSphereMap h.choose_spec)


theorem euclideanLocalDegree_eq_sphereDegree
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero f x)
    {R : ℝ} (hR : IsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    euclideanLocalDegree f x h =
      euclideanSphereDegree (sphereMap f x R hR.continuousOn hR.nonzero r) :=
  (radius_degree_eq h.choose_spec hR).trans
    (euclideanSphereDegree_sphereMap_eq _ _ _ _ _ _ _)


theorem euclideanLocalDegree_generator
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero f x)
    {R : ℝ} (hR : IsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    DifferentialGeometry.Homology.reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom (sphereMap f x R hR.continuousOn hR.nonzero r)) d
          (euclideanSphereTopGenerator d) =
      euclideanLocalDegree f x h • euclideanSphereTopGenerator d := by
  rw [euclideanLocalDegree_eq_sphereDegree h hR r]
  exact euclideanSphereDegree_generator _


theorem euclideanLocalDegree_congr
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hf : isolatedZero f x) (hg : isolatedZero g x) (hfg : f =ᶠ[𝓝 x] g) :
    euclideanLocalDegree f x hf = euclideanLocalDegree g x hg := by
  let R := hf.choose
  have hR : IsolatingRadius f x R := hf.choose_spec
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfg
  let r := min R (ε / 2)
  have hr : 0 < r := lt_min hR.pos (by positivity)
  have hrr : r ≤ R := min_le_left _ _
  have heq : EqOn f g (closedBall x r) := fun y hy ↦
    hball (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hy)
  have hfr := hR.mono hr hrr
  have hgr := hfr.congr heq
  rw [euclideanLocalDegree_eq_sphereDegree hf hfr ⟨r, hr, le_rfl⟩,
    euclideanLocalDegree_eq_sphereDegree hg hgr ⟨r, hr, le_rfl⟩]
  congr 1
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply]
  rw [heq (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere v, mul_one])]


theorem isolatedZero_euclidean_id :
    isolatedZero (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y) 0 :=
  ⟨1, ⟨by norm_num, continuousOn_id, fun _ _ => Iff.rfl⟩⟩


@[simp]
theorem euclideanLocalDegree_id :
    euclideanLocalDegree (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y) 0
      isolatedZero_euclidean_id = 1 := by
  have hR : IsolatingRadius (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y) 0 1 :=
    ⟨by norm_num, continuousOn_id, fun _ _ => Iff.rfl⟩
  rw [euclideanLocalDegree_eq_sphereDegree isolatedZero_euclidean_id hR ⟨1, by norm_num, le_rfl⟩]
  change euclideanSphereDegree (sphereMap (fun y : EuclideanSpace ℝ (Fin (d + 1)) => y)
    0 1 continuousOn_id (fun _ _ h => h) ⟨1, by norm_num, le_rfl⟩) = 1
  rw [sphereMap_id, euclideanSphereDegree_id]

end DifferentialGeometry.LocalDegree
