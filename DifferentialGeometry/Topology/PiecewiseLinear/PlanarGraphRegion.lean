import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PolytopeSection
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def planePoint (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x, y]

theorem planePoint_apply_zero (x y : ℝ) : planePoint x y 0 = x := rfl

theorem planePoint_apply_one (x y : ℝ) : planePoint x y 1 = y := rfl

def graphRegion (a : ℝ → ℝ) (s t : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {w | w 1 ∈ Icc s t ∧ 0 ≤ w 0 ∧ w 0 ≤ a (w 1)}

theorem coordPair_apply (w : EuclideanSpace ℝ (Fin 2)) :
    (((EuclideanSpace.projₗ (0 : Fin 2)).prod
      (EuclideanSpace.projₗ (1 : Fin 2))).toAffineMap) w = (w 0, w 1) := rfl

theorem isHPolytope_coordBox (b c s t : ℝ) :
    IsHPolytope {w : EuclideanSpace ℝ (Fin 2) | w 0 ∈ Icc b c ∧ w 1 ∈ Icc s t} := by
  have hP : IsHPolytope
      ((((EuclideanSpace.projₗ (0 : Fin 2)).prod
        (EuclideanSpace.projₗ (1 : Fin 2))).toAffineMap) ⁻¹' (Icc b c ×ˢ Icc s t)) := by
    refine ((isHPolytope_Icc (a := b) (b := c)).prod
      (isHPolytope_Icc (a := s) (b := t))).preimage_affineMap_of_injective _ ?_
    intro w v h
    rw [coordPair_apply, coordPair_apply, Prod.mk.injEq] at h
    refine PiLp.ext ?_
    rw [Fin.forall_fin_two]
    exact ⟨h.1, h.2⟩
  convert hP using 1
  ext w
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem isHPolytope_graphRegion_of_affineOn {a : ℝ → ℝ} {s t p q : ℝ}
    (haff : ∀ v ∈ Icc s t, a v = p * v + q) : IsHPolytope (graphRegion a s t) := by
  have hcut := (isHPolytope_coordBox 0 (max (p * s + q) (p * t + q)) s t).inter_affine_le
    (LinearMap.toAffineMap (EuclideanSpace.projₗ (0 : Fin 2) -
      p • EuclideanSpace.projₗ (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ)) q
  convert hcut using 1
  ext w
  constructor
  · rintro ⟨⟨hs, ht⟩, h0, h1⟩
    rw [haff (w 1) ⟨hs, ht⟩] at h1
    refine ⟨⟨⟨h0, ?_⟩, hs, ht⟩, ?_⟩
    · rcases le_or_gt 0 p with hp | hp
      · have hmul : 0 ≤ p * (t - w 1) := mul_nonneg hp (by linarith)
        exact le_trans (by linarith) (le_max_right _ _)
      · have hmul : 0 ≤ (-p) * (w 1 - s) := mul_nonneg (by linarith) (by linarith)
        exact le_trans (by linarith) (le_max_left _ _)
    · change w 0 - p * w 1 ≤ q
      linarith
  · rintro ⟨⟨⟨h0, -⟩, hs, ht⟩, hc⟩
    have hc' : w 0 - p * w 1 ≤ q := hc
    refine ⟨⟨hs, ht⟩, h0, ?_⟩
    rw [haff (w 1) ⟨hs, ht⟩]
    linarith

theorem isOpen_openGraphRegion (s t p q : ℝ) :
    IsOpen {w : EuclideanSpace ℝ (Fin 2) | s < w 1 ∧ w 1 < t ∧ 0 < w 0 ∧ w 0 < p * w 1 + q} := by
  have hc0 : Continuous fun w : EuclideanSpace ℝ (Fin 2) => w 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous
  have hc1 : Continuous fun w : EuclideanSpace ℝ (Fin 2) => w 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous
  exact (isOpen_lt continuous_const hc1).inter ((isOpen_lt hc1 continuous_const).inter
    ((isOpen_lt continuous_const hc0).inter
      (isOpen_lt hc0 ((continuous_const.mul hc1).add continuous_const))))

theorem interior_graphRegion_nonempty {a : ℝ → ℝ} {s t p q u : ℝ}
    (haff : ∀ v ∈ Icc s t, a v = p * v + q) (hu : u ∈ Ioo s t) (hau : 0 < a u) :
    (interior (graphRegion a s t)).Nonempty := by
  have hau' : a u = p * u + q := haff u ⟨hu.1.le, hu.2.le⟩
  refine ⟨planePoint (a u / 2) u, interior_maximal ?_ (isOpen_openGraphRegion s t p q) ?_⟩
  · rintro w ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1.le, h2.le⟩, h3.le, ?_⟩
    rw [haff (w 1) ⟨h1.le, h2.le⟩]
    exact h4.le
  · refine ⟨hu.1, hu.2, ?_, ?_⟩
    · change (0 : ℝ) < a u / 2
      linarith
    · change a u / 2 < p * u + q
      linarith

theorem isPLBall_two_graphRegion_of_affineOn {a : ℝ → ℝ} {s t p q u : ℝ}
    (haff : ∀ v ∈ Icc s t, a v = p * v + q) (hu : u ∈ Ioo s t) (hau : 0 < a u) :
    IsPLBall 2 (graphRegion a s t) := by
  have h := (isHPolytope_graphRegion_of_affineOn haff).isPLBall
    (interior_graphRegion_nonempty haff hu hau)
  rwa [finrank_euclideanSpace_fin] at h

theorem forall_add_single_mem_of_mem_interior {C : Set (EuclideanSpace ℝ (Fin 2))}
    {w : EuclideanSpace ℝ (Fin 2)} (hw : w ∈ interior C) (i : Fin 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε → w + PiLp.single 2 i δ ∈ C := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  refine ⟨ε, hε, fun δ hδ => interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, PiLp.norm_single]
  simpa using hδ

theorem notMem_interior_of_forall_le {C : Set (EuclideanSpace ℝ (Fin 2))} {i : Fin 2} {r : ℝ}
    (hC : ∀ x ∈ C, x i ≤ r) {w : EuclideanSpace ℝ (Fin 2)} (hw : r ≤ w i) : w ∉ interior C := by
  intro hmem
  obtain ⟨ε, hε, hall⟩ := forall_add_single_mem_of_mem_interior hmem i
  have h := hC _ (hall (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))
  rw [PiLp.add_apply, PiLp.single_eq_same] at h
  linarith

theorem notMem_interior_of_forall_ge {C : Set (EuclideanSpace ℝ (Fin 2))} {i : Fin 2} {r : ℝ}
    (hC : ∀ x ∈ C, r ≤ x i) {w : EuclideanSpace ℝ (Fin 2)} (hw : w i ≤ r) : w ∉ interior C := by
  intro hmem
  obtain ⟨ε, hε, hall⟩ := forall_add_single_mem_of_mem_interior hmem i
  have h := hC _ (hall (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))
  rw [PiLp.add_apply, PiLp.single_eq_same] at h
  linarith

theorem union_graphRegion {a : ℝ → ℝ} {s t v : ℝ} (hst : s ≤ t) (htv : t ≤ v) :
    graphRegion a s t ∪ graphRegion a t v = graphRegion a s v := by
  ext w
  constructor
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
    · exact ⟨⟨h1, h2.trans htv⟩, h3, h4⟩
    · exact ⟨⟨hst.trans h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rcases le_or_gt (w 1) t with h | h
    · exact Or.inl ⟨⟨h1, h⟩, h3, h4⟩
    · exact Or.inr ⟨⟨h.le, h2⟩, h3, h4⟩

theorem inter_graphRegion {a : ℝ → ℝ} {s t v : ℝ} (hst : s ≤ t) (htv : t ≤ v) (hat : 0 < a t) :
    graphRegion a s t ∩ graphRegion a t v =
      segment ℝ (planePoint 0 t) (planePoint (a t) t) := by
  ext w
  constructor
  · rintro ⟨⟨⟨-, ht1⟩, h0, h1⟩, ⟨⟨ht2, -⟩, -, -⟩⟩
    have hw1 : w 1 = t := le_antisymm ht1 ht2
    rw [hw1] at h1
    refine ⟨1 - w 0 / a t, w 0 / a t, ?_, ?_, by ring, ?_⟩
    · have : w 0 / a t ≤ 1 := (div_le_one hat).mpr h1
      linarith
    · exact div_nonneg h0 hat.le
    · refine PiLp.ext ?_
      rw [Fin.forall_fin_two]
      constructor
      · change (1 - w 0 / a t) * (0 : ℝ) + w 0 / a t * a t = w 0
        field_simp
        ring
      · change (1 - w 0 / a t) * t + w 0 / a t * t = w 1
        rw [hw1]
        ring
  · rintro ⟨α, β, hα, hβ, hαβ, heq⟩
    have h0 : w 0 = β * a t := by
      rw [← heq]
      change α * (0 : ℝ) + β * a t = β * a t
      ring
    have h1 : w 1 = t := by
      rw [← heq]
      change α * t + β * t = t
      rw [← add_mul, hαβ, one_mul]
    have hβ1 : β ≤ 1 := by linarith
    have hle : w 0 ≤ a t := by
      rw [h0]
      nlinarith
    exact ⟨⟨⟨h1 ▸ hst, h1.le⟩, h0 ▸ mul_nonneg hβ hat.le, by rw [h1]; exact hle⟩,
      ⟨⟨h1.ge, h1 ▸ htv⟩, h0 ▸ mul_nonneg hβ hat.le, by rw [h1]; exact hle⟩⟩

theorem isPLBall_two_graphRegion_union {a : ℝ → ℝ} {s t v : ℝ} (hst : s ≤ t) (htv : t ≤ v)
    (hat : 0 < a t) (hC : IsPLBall 2 (graphRegion a s t))
    (hD : IsPLBall 2 (graphRegion a t v)) : IsPLBall 2 (graphRegion a s v) := by
  have hne : planePoint 0 t ≠ planePoint (a t) t := by
    intro h
    have h' := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
    rw [planePoint_apply_zero, planePoint_apply_zero] at h'
    exact absurd h'.symm (ne_of_gt hat)
  have hI : IsPLBall 1 (graphRegion a s t ∩ graphRegion a t v) := by
    rw [inter_graphRegion hst htv hat]
    exact isPLBall_segment hne
  have hIC : graphRegion a s t ∩ graphRegion a t v ⊆ frontier (graphRegion a s t) := by
    rintro w ⟨hw1, hw2⟩
    exact (mem_frontier_iff_notMem_interior hw1).mpr
      (notMem_interior_of_forall_le (fun x hx => hx.1.2) hw2.1.1)
  have hID : graphRegion a s t ∩ graphRegion a t v ⊆ frontier (graphRegion a t v) := by
    rintro w ⟨hw1, hw2⟩
    exact (mem_frontier_iff_notMem_interior hw2).mpr
      (notMem_interior_of_forall_ge (fun x hx => hx.1.1) hw1.1.2)
  rw [← union_graphRegion hst htv]
  exact (isPLBall_union_and_finite_frontier_inter hC hD hI hIC hID).1

theorem lt_of_subdivision {N : ℕ} {σ : ℕ → ℝ} (hσ : ∀ k ≤ N, σ k < σ (k + 1)) :
    σ 0 < σ (N + 1) := by
  induction N with
  | zero => exact hσ 0 le_rfl
  | succ n ih => exact lt_trans (ih fun k hk => hσ k (by omega)) (hσ (n + 1) le_rfl)

theorem isPLBall_two_graphRegion_of_subdivision {N : ℕ} {σ : ℕ → ℝ} {a : ℝ → ℝ}
    (hσ : ∀ k ≤ N, σ k < σ (k + 1))
    (haff : ∀ k ≤ N, ∃ p q : ℝ, ∀ u ∈ Icc (σ k) (σ (k + 1)), a u = p * u + q)
    (hpos : ∀ u ∈ Ioo (σ 0) (σ (N + 1)), 0 < a u) :
    IsPLBall 2 (graphRegion a (σ 0) (σ (N + 1))) := by
  induction N with
  | zero =>
    obtain ⟨p, q, hpq⟩ := haff 0 le_rfl
    have hlt : σ 0 < σ (0 + 1) := hσ 0 le_rfl
    exact isPLBall_two_graphRegion_of_affineOn (u := (σ 0 + σ (0 + 1)) / 2) hpq
      ⟨by linarith, by linarith⟩ (hpos _ ⟨by linarith, by linarith⟩)
  | succ n ih =>
    have hmid : σ 0 < σ (n + 1) := lt_of_subdivision fun k hk => hσ k (by omega)
    have hlast : σ (n + 1) < σ (n + 1 + 1) := hσ (n + 1) le_rfl
    have hIH : IsPLBall 2 (graphRegion a (σ 0) (σ (n + 1))) :=
      ih (fun k hk => hσ k (by omega)) (fun k hk => haff k (by omega))
        fun u hu => hpos u ⟨hu.1, by linarith [hu.2]⟩
    obtain ⟨p, q, hpq⟩ := haff (n + 1) le_rfl
    have hD : IsPLBall 2 (graphRegion a (σ (n + 1)) (σ (n + 1 + 1))) :=
      isPLBall_two_graphRegion_of_affineOn (u := (σ (n + 1) + σ (n + 1 + 1)) / 2) hpq
        ⟨by linarith, by linarith⟩ (hpos _ ⟨by linarith, by linarith⟩)
    exact isPLBall_two_graphRegion_union hmid.le hlast.le (hpos _ ⟨hmid, hlast⟩) hIH hD

theorem IsPLBall.closure_inside_frontier {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) : closure (Schoenflies.inside (frontier C)) = C :=
  PlanarJordan.closure_inside_frontier_eq_of_isCompact hC.isPolyhedron.isCompact
    (isJordanCurve_of_isPLSphere_one hC.isPLSphere_frontier) hC.interior_nonempty

theorem isPLBall_two_and_closure_inside_frontier_graphRegion {N : ℕ} {σ : ℕ → ℝ} {a : ℝ → ℝ}
    (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1) (hσ : ∀ k ≤ N, σ k < σ (k + 1))
    (haff : ∀ k ≤ N, ∃ p q : ℝ, ∀ u ∈ Icc (σ k) (σ (k + 1)), a u = p * u + q)
    (hpos : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < a u) :
    IsPLBall 2 (graphRegion a 0 1) ∧
      closure (Schoenflies.inside (frontier (graphRegion a 0 1))) = graphRegion a 0 1 := by
  have hball : IsPLBall 2 (graphRegion a 0 1) := by
    have h := isPLBall_two_graphRegion_of_subdivision hσ haff (by rw [hσ0, hσN]; exact hpos)
    rwa [hσ0, hσN] at h
  exact ⟨hball, hball.closure_inside_frontier⟩

end DifferentialGeometry.Topology.PiecewiseLinear
