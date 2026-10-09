import DifferentialGeometry.Geometry.Comparison.ProductLineCoordinates
import DifferentialGeometry.Analysis.InnerProductSpace.OrthonormalProductCoordinates
import DifferentialGeometry.Geometry.Metric.SharedCoordinateCancellation
import DifferentialGeometry.Geometry.Comparison.FactorGeometry
import DifferentialGeometry.Geometry.Comparison.LineSplitting
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanProduct

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]

private theorem lineCoordinate_eq_inner_of_aligned_unit_isometry {k : ℕ}
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    {γ : ℝ → X} {ξ : EuclideanSpace ℝ (Fin k)} {b₀ : B}
    (hξ : ‖ξ‖ = 1) (halign : ∀ t, e (γ t) = WithLp.toLp 2 (t • ξ, b₀)) (x : X) :
    lineCoordinate γ x = inner ℝ (e x).fst ξ := by
  have hzero := WithLp.prod_dist_sq_eq_add_sq (e x) (e (γ 0))
  have hone := WithLp.prod_dist_sq_eq_add_sq (e x) (e (γ 1))
  rw [e.dist_eq, halign, zero_smul] at hzero
  rw [e.dist_eq, halign, one_smul] at hone
  change dist x (γ 0) ^ 2 = dist (e x).fst 0 ^ 2 + dist (e x).snd b₀ ^ 2 at hzero
  change dist x (γ 1) ^ 2 = dist (e x).fst ξ ^ 2 + dist (e x).snd b₀ ^ 2 at hone
  rw [dist_zero_right] at hzero
  rw [dist_eq_norm, norm_sub_sq_real, hξ, one_pow] at hone
  unfold lineCoordinate
  linarith

theorem exists_exact_compatibility_of_no_factor_line {j k : ℕ}
    (hs : fourPointComparison 0 (Set.univ : Set X)) (hjk : j ≤ k)
    (a : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
    (b : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    (hnoline : ¬ ∃ η : ℝ → B, Isometry η)
    {p : X} {a₀ : A} {b₀ : B}
    (ha : a p = WithLp.toLp 2 (0, a₀)) (hb : b p = WithLp.toLp 2 (0, b₀)) :
    ∃ (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
      (H : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ A),
      H (WithLp.toLp 2 (0, b₀)) = a₀ ∧
        ∀ x, a x = WithLp.toLp 2 ((Q (b x).fst).fst,
          H (WithLp.toLp 2 ((Q (b x).fst).snd, (b x).snd))) := by
  let γ : Fin j → ℝ → X := fun l t => a.symm (WithLp.toLp 2 (PiLp.single 2 l t, a₀))
  have hγ (l : Fin j) : Isometry (γ l) := a.symm.isometry.comp
    ((WithLp.isometry_prodMk_right a₀).comp (Isometry.of_dist_eq
      (fun s t => PiLp.dist_single_same 2 (fun _ : Fin j => ℝ) l s t)))
  have hγa (l : Fin j) (t : ℝ) : a (γ l t) = WithLp.toLp 2 (PiLp.single 2 l t, a₀) :=
    a.apply_symm_apply _
  have hγzero (l : Fin j) : γ l 0 = p := by
    apply a.injective
    rw [hγa, ha, (PiLp.single_eq_zero_iff 2 l).mpr rfl]
  let ξ : Fin j → EuclideanSpace ℝ (Fin k) := fun l => (b (γ l 1)).fst
  have hξ (l : Fin j) : ‖ξ l‖ = 1 ∧
      ∀ t : ℝ, b (γ l t) = WithLp.toLp 2 (t • ξ l, b₀) :=
    isometry_line_eq_euclidean_smul_of_no_factor_line hs b hnoline (hγ l)
      (by rw [hγzero, hb])
  have hcoord (x : X) (l : Fin j) : (a x).fst l = inner ℝ (b x).fst (ξ l) := by
    rw [← lineCoordinate_eq_euclidean_coordinate_of_aligned_isometry a (hγa l)]
    exact lineCoordinate_eq_inner_of_aligned_unit_isometry b (hξ l).1 (hξ l).2 x
  have horth : Orthonormal ℝ ξ := by
    refine ⟨fun l => (hξ l).1, ?_⟩
    intro l m hlm
    have hh := hcoord (γ l 1) m
    rw [hγa] at hh
    change (PiLp.single 2 l (1 : ℝ) : EuclideanSpace ℝ (Fin j)) m = inner ℝ (ξ l) (ξ m) at hh
    simpa only [PiLp.single_eq_of_ne _ (Ne.symm hlm)] using hh.symm
  obtain ⟨Q, hQ⟩ := horth.exists_euclidean_product_coordinates hjk
  let c : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin j) ×
      WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B)) :=
    (b.trans (IsometryEquiv.withLpProdCongr 2 Q.toIsometryEquiv (IsometryEquiv.refl B))).trans
      (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin j))
        (EuclideanSpace ℝ (Fin (k - j))) B)
  have hc (x : X) : c x = WithLp.toLp 2 ((Q (b x).fst).fst,
      WithLp.toLp 2 ((Q (b x).fst).snd, (b x).snd)) := rfl
  have hfst (x : X) : (a x).fst = (c x).fst := by
    ext l
    exact (hcoord x l).trans (hQ (b x).fst l).symm
  have hcbase : c p = WithLp.toLp 2 (0, WithLp.toLp 2 (0, b₀)) := by
    rw [hc, hb]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, map_zero]
    rfl
  obtain ⟨H, hH, _⟩ := a.exists_unique_l2ProductFactor_of_fst_eq c hfst ha hcbase
  refine ⟨Q, H, hH.1, ?_⟩
  intro x
  exact hH.2 x

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

private theorem no_factor_line_of_no_successor_splitting
    {X B : Type u} [MetricSpace X] [ProperSpace X] [MetricSpace B] {k : ℕ}
    (hs : fourPointComparison 0 (Set.univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Set.Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (b : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B)) (p : X)
    (hmax : ¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
      ∃ (w : W) (F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × W)),
        F p = WithLp.toLp 2 (0, w)) :
    ¬ ∃ η : ℝ → B, Isometry η := by
  rintro ⟨η, hη⟩
  let := b.properSpace_l2_product_factor (0 : EuclideanSpace ℝ (Fin k))
  have hB := fourPointComparison_l2_product_factor hs b (0 : EuclideanSpace ℝ (Fin k))
  have hsegB := b.exists_segment_l2_product_factor (0 : EuclideanSpace ℝ (Fin k)) hsegments
  let D := {y : B // lineCoordinate η y = 0}
  let eB : B ≃ᵢ WithLp 2 (ℝ × D) := lineSplitting hB hη hsegB
  let d : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × D) :=
    ((b.trans (IsometryEquiv.withLpProdCongr 2
      (IsometryEquiv.refl (EuclideanSpace ℝ (Fin k))) eB)).trans
      (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin k)) ℝ D).symm).trans
      (IsometryEquiv.withLpProdCongr 2
        (EuclideanSpace.finSuccProdIsometry k).symm.toIsometryEquiv (IsometryEquiv.refl D))
  let F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × D) :=
    d.trans (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.subRight (d p).fst)
      (IsometryEquiv.refl D))
  apply hmax
  refine ⟨D, inferInstance, (d p).snd, F, ?_⟩
  change WithLp.toLp 2 ((d p).fst - (d p).fst, (d p).snd) = _
  rw [sub_self]

theorem exists_exact_compatibility_of_maximal_splitting
    {X A B : Type u} [MetricSpace X] [ProperSpace X] [MetricSpace A] [MetricSpace B]
    {j k : ℕ} (hs : fourPointComparison 0 (Set.univ : Set X)) (hjk : j ≤ k)
    (hsegments : ∀ x y : X, ∃ f : Set.Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (a : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
    (b : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    {p : X} {a₀ : A} {b₀ : B}
    (ha : a p = WithLp.toLp 2 (0, a₀)) (hb : b p = WithLp.toLp 2 (0, b₀))
    (hmax : ¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
      ∃ (w : W) (F : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin (k + 1)) × W)),
        F p = WithLp.toLp 2 (0, w)) :
    ∃ (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
      (H : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ A),
      H (WithLp.toLp 2 (0, b₀)) = a₀ ∧
        ∀ x, a x = WithLp.toLp 2 ((Q (b x).fst).fst,
          H (WithLp.toLp 2 ((Q (b x).fst).snd, (b x).snd))) :=
  exists_exact_compatibility_of_no_factor_line hs hjk a b
    (no_factor_line_of_no_successor_splitting hs hsegments b p hmax) ha hb

end DifferentialGeometry.Geometry.Comparison.Toponogov
