import DifferentialGeometry.Geometry.Metric.L2Product

set_option autoImplicit false

open Set Metric

namespace IsometryEquiv

variable {E Y Z : Type*} [MetricSpace E] [MetricSpace Y] [MetricSpace Z]
variable {q : Y} {z : Z} {R : ℝ}

noncomputable def l2ProductBall (hR : 0 < R) (e : ball q R ≃ᵢ ball z R)
    (he : (e ⟨q, mem_ball_self hR⟩).val = z) (u : E) :
    ball (WithLp.toLp 2 (u, q)) R ≃ᵢ ball (WithLp.toLp 2 (u, z)) R := by
  have hfactor (x : ball (WithLp.toLp 2 (u, q)) R) : x.val.snd ∈ ball q R :=
    (WithLp.dist_snd_le x.val (WithLp.toLp 2 (u, q))).trans_lt x.property
  have hrad (a : ball q R) : dist (e a).val z = dist a.val q := by
    have h := e.dist_eq a ⟨q, mem_ball_self hR⟩
    change dist (e a).val (e ⟨q, mem_ball_self hR⟩).val = dist a.val q at h
    simpa only [he] using h
  let F : ball (WithLp.toLp 2 (u, q)) R → ball (WithLp.toLp 2 (u, z)) R := fun x =>
    ⟨WithLp.toLp 2 (x.val.fst, (e ⟨x.val.snd, hfactor x⟩).val), by
      have hd : dist (WithLp.toLp 2 (x.val.fst, (e ⟨x.val.snd, hfactor x⟩).val))
          (WithLp.toLp 2 (u, z)) = dist x.val (WithLp.toLp 2 (u, q)) := by
        apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
        rw [WithLp.prod_dist_sq_eq_add_sq, WithLp.prod_dist_sq_eq_add_sq]
        simp only [WithLp.toLp_fst, WithLp.toLp_snd, hrad]
      exact hd.trans_lt x.property⟩
  have hisom : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    have hd := e.dist_eq ⟨x.val.snd, hfactor x⟩ ⟨y.val.snd, hfactor y⟩
    change dist (e ⟨x.val.snd, hfactor x⟩).val (e ⟨y.val.snd, hfactor y⟩).val =
      dist x.val.snd y.val.snd at hd
    change dist (F x).val (F y).val = dist x.val y.val
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [WithLp.prod_dist_sq_eq_add_sq, WithLp.prod_dist_sq_eq_add_sq]
    change dist x.val.fst y.val.fst ^ 2 +
      dist (e ⟨x.val.snd, hfactor x⟩).val (e ⟨y.val.snd, hfactor y⟩).val ^ 2 = _
    rw [hd]
  have hsurj : Function.Surjective F := by
    intro y
    have hyf : y.val.snd ∈ ball z R :=
      (WithLp.dist_snd_le y.val (WithLp.toLp 2 (u, z))).trans_lt y.property
    let a := e.symm ⟨y.val.snd, hyf⟩
    have hea : (e a).val = y.val.snd := by simp only [a, e.apply_symm_apply]
    have ha : dist a.val q = dist y.val.snd z := by rw [← hrad, hea]
    let x : ball (WithLp.toLp 2 (u, q)) R := ⟨WithLp.toLp 2 (y.val.fst, a.val), by
      have hd : dist (WithLp.toLp 2 (y.val.fst, a.val)) (WithLp.toLp 2 (u, q)) =
          dist y.val (WithLp.toLp 2 (u, z)) := by
        apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
        rw [WithLp.prod_dist_sq_eq_add_sq, WithLp.prod_dist_sq_eq_add_sq]
        simp only [WithLp.toLp_fst, WithLp.toLp_snd, ha]
      exact hd.trans_lt y.property⟩
    refine ⟨x, Subtype.ext ?_⟩
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · rfl
    · exact hea
  exact ⟨Equiv.ofBijective F ⟨hisom.injective, hsurj⟩, hisom⟩

@[simp] theorem l2ProductBall_fst (hR : 0 < R) (e : ball q R ≃ᵢ ball z R)
    (he : (e ⟨q, mem_ball_self hR⟩).val = z) (u : E)
    (x : ball (WithLp.toLp 2 (u, q)) R) :
    ((e.l2ProductBall hR he u) x).val.fst = x.val.fst := rfl

theorem l2ProductBall_snd (hR : 0 < R) (e : ball q R ≃ᵢ ball z R)
    (he : (e ⟨q, mem_ball_self hR⟩).val = z) (u : E)
    (x : ball (WithLp.toLp 2 (u, q)) R) :
    ((e.l2ProductBall hR he u) x).val.snd =
      (e ⟨x.val.snd, (WithLp.dist_snd_le x.val (WithLp.toLp 2 (u, q))).trans_lt x.property⟩).val := rfl


theorem l2ProductBall_basepoint (hR : 0 < R) (e : ball q R ≃ᵢ ball z R)
    (he : (e ⟨q, mem_ball_self hR⟩).val = z) (u : E) :
    ((e.l2ProductBall hR he u) ⟨WithLp.toLp 2 (u, q), mem_ball_self hR⟩).val =
      WithLp.toLp 2 (u, z) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · exact he

end IsometryEquiv
