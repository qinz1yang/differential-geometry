import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallRoof
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallFrontiers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingMarkerRoutes
import DifferentialGeometry.Topology.PiecewiseLinear.SignedHeightCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_crossing_pierced_square_ball_pair {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKP : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ (A B : Set ((ℝ × ℝ) × ℝ)) (f₀ f₁ : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) × ℝ),
      IsPLBall 3 A ∧ IsPLBall 3 B ∧
      IsPLHomeomorphOn f₀ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) A ∧
      IsPLHomeomorphOn f₁ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (0 : ℝ) 1) B ∧
      IsPLHomeomorphOn f₀ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
      IsPLHomeomorphOn f₁ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
      EqOn f₀ id (univ ×ˢ Ioo (-a) a)ᶜ ∧ EqOn f₁ id (univ ×ˢ Ioo (-a) a)ᶜ ∧
      (interior A ∩ interior B).Nonempty ∧ IsPLSphere 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ {(0 : ℝ)} ∧
      A ∩ B ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1) ×ˢ Icc (-a / 2) (a / 2) ∧
      A ∪ B ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ∧
      K ×ˢ Ioo (-1 : ℝ) 1 ⊆ interior A ∪ interior B ∧
      A \ (univ ×ˢ Ioo (-a) a) =
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) \ (univ ×ˢ Ioo (-a) a) ∧
      B \ (univ ×ˢ Ioo (-a) a) =
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (univ ×ˢ Ioo (-a) a) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A \ B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B ∩ interior A)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B \ A)) ∧
      ∀ p₀ ∈ K ×ˢ {(0 : ℝ)}, ∀ p₁ ∈ K ×ˢ {(0 : ℝ)}, p₀ ≠ p₁ →
        ∃ (L₀ L₁ : Set ((ℝ × ℝ) × ℝ)) (q₀ q₁ : (ℝ × ℝ) × ℝ),
          IsCompact L₀ ∧ IsCompact L₁ ∧ IsConnected L₀ ∧ IsConnected L₁ ∧
          Disjoint L₀ L₁ ∧ p₀ ∈ L₀ ∧ q₀ ∈ L₀ ∧ p₁ ∈ L₁ ∧ q₁ ∈ L₁ ∧
          L₀ ⊆ interior A ∩ (univ ×ˢ Ioo (-a) a) ∧
          L₁ ⊆ interior B ∩ (univ ×ˢ Ioo (-a) a) ∧ q₀ ∉ B ∧ q₁ ∉ A := by
  have h0 : (0 : ℝ × ℝ) ∈ interior (Metric.closedBall (0 : ℝ × ℝ) 1) := by
    rw [interior_closedBall _ one_ne_zero]
    exact Metric.mem_ball_self zero_lt_one
  obtain ⟨g, hg, hga, hgfront, hgK', hzero, hpos, hnegzero⟩ :=
    exists_piercing_square_roof_with_sign_closures
    (hK.union isCompact_singleton) (union_subset hKP (singleton_subset_iff.mpr h0)) ha
  have hgK (x) (hx : x ∈ K) : 0 < g x := hgK' x (Or.inl hx)
  have hg0 : 0 < g 0 := hgK' 0 (Or.inr rfl)
  have hP : IsPLBall 2 (Metric.closedBall (0 : ℝ × ℝ) 1) :=
    isPLBall_square_closedBall zero_lt_one
  obtain ⟨A, B, hA, hB, hAe, hBe, hAB, hcover⟩ :=
    exists_pierced_prism_ball_pair hg ha ha1 hP hga
  have hbound (x) (hx : x ∈ Metric.closedBall (0 : ℝ × ℝ) 1) : |g x| < 1 := by
    exact (hga x hx).trans_lt (by linarith)
  have hfront : frontier A ∩ frontier B =
      {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} ×ˢ {(0 : ℝ)} := by
    rw [hAe, hBe]
    exact frontier_inter_signed_height_balls Metric.isClosed_closedBall
      (continuousOn_univ.mp hg.continuousOn) hbound hgfront
  have hcross : (frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier A \ B)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B ∩ interior A)) ∧
      (frontier A ∩ frontier B ⊆ closure (frontier B \ A)) := by
    rw [hfront, hAe, hBe]
    exact signed_height_regions_cross_along_zero_set
      (continuousOn_univ.mp hg.continuousOn) hbound hpos hnegzero
  have hneg : IsPiecewiseAffineOn (fun x => -g x) univ := by
    have hn : IsPiecewiseAffineOn (fun t : ℝ => -t) univ :=
      isPiecewiseAffineOn_of_affine (-(AffineMap.id ℝ ℝ)) isOpen_univ
    simpa only [preimage_univ, inter_univ, Function.comp_def] using hn.comp hg
  have hnga : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1, |(-g x)| ≤ a / 2 := by
    simpa only [abs_neg] using hga
  have hfix (f : (ℝ × ℝ) → ℝ) : EqOn (piercingHeightMove f a) id
      (univ ×ˢ Ioo (-a) a)ᶜ := by
    intro x hx
    apply piercingHeightMove_eq_self
    by_cases hxl : x.2 ≤ -a
    · exact Or.inl hxl
    · exact Or.inr (le_of_not_gt fun hxu => hx ⟨mem_univ _, lt_of_not_ge hxl, hxu⟩)
  refine ⟨A, B, piercingHeightMove g a, piercingHeightMove (fun x => -g x) a,
    hA, hB, ?_, ?_, isPLHomeomorphOn_piercingHeightMove_self hg ha1 hP.isPolyhedron,
    isPLHomeomorphOn_piercingHeightMove_self hneg ha1 hP.isPolyhedron,
    hfix _, hfix _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hcross.1, hcross.2.1, hcross.2.2.1, hcross.2.2.2, ?_⟩
  · have hp := isPLHomeomorphOn_piercingHeightMove hg a hP.isPolyhedron (-1) 0
    rwa [piercingHeightMove_image_lower ha ha1 hga, ← hAe] at hp
  · have hp := isPLHomeomorphOn_piercingHeightMove hneg a hP.isPolyhedron 0 1
    rwa [piercingHeightMove_image_upper ha ha1 hnga, ← hBe] at hp
  · have hO : IsOpen {y : (ℝ × ℝ) × ℝ |
        y.1 ∈ interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∧ |y.2| < g y.1} :=
      (isOpen_interior.preimage continuous_fst).inter
        (isOpen_lt continuous_snd.abs
          ((continuousOn_univ.mp hg.continuousOn).comp continuous_fst))
    have hsub : {y : (ℝ × ℝ) × ℝ |
        y.1 ∈ interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∧ |y.2| < g y.1} ⊆ A ∩ B := by
      rw [hAB]
      exact fun _ hy => ⟨interior_subset hy.1, hy.2.le⟩
    have hi := interior_maximal hsub hO
    rw [interior_inter] at hi
    exact ⟨(0, 0), hi ⟨h0, by simpa only [abs_zero] using hg0⟩⟩
  · rw [hfront]
    exact hzero.of_isPLHomeomorphOn (hzero.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  · rw [hfront]
    exact prod_mono (fun _ hx => hx.1) Subset.rfl
  · rw [hAB]
    intro y hy
    have hypos : 0 ≤ g y.1 := (abs_nonneg y.2).trans hy.2
    have hyint : y.1 ∈ interior (Metric.closedBall (0 : ℝ × ℝ) 1) := by
      by_contra hn
      exact (not_lt_of_ge hypos) (hgfront y.1 ⟨subset_closure hy.1, hn⟩)
    have hz : |y.2| ≤ a / 2 :=
      hy.2.trans ((le_abs_self (g y.1)).trans (hga y.1 hy.1))
    exact ⟨hyint, by simpa only [mem_Icc, neg_div] using abs_le.mp hz⟩
  · rw [hAe, hBe]
    rintro y (hy | hy)
    · have hb := (abs_lt.mp (hbound y.1 hy.1)).2
      exact ⟨hy.1, hy.2.1, hy.2.2.trans hb.le⟩
    · have hb := (abs_lt.mp (hbound y.1 hy.1)).2
      exact ⟨hy.1, (by linarith : (-1 : ℝ) ≤ -g y.1).trans hy.2.1, hy.2.2⟩
  · have hbase : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∩ {x | 0 < g x} :=
      fun x hx => ⟨hKP hx, hgK x hx⟩
    exact (prod_mono hbase Subset.rfl).trans hcover
  · rw [hAe, ← piercingHeightMove_image_lower ha ha1 hga]
    exact piercingHeightMove_image_diff_slab g a _
  · rw [hBe, ← piercingHeightMove_image_upper ha ha1
      hnga]
    exact piercingHeightMove_image_diff_slab (fun x => -g x) a _
  · intro p₀ hp₀ p₁ hp₁ hne
    have ht₀ : p₀.2 = 0 := hp₀.2
    have ht₁ : p₁.2 = 0 := hp₁.2
    have hg₀ := (le_abs_self (g p₀.1)).trans (hga p₀.1 (interior_subset (hKP hp₀.1)))
    have hg₁ := (le_abs_self (g p₁.1)).trans (hga p₁.1 (interior_subset (hKP hp₁.1)))
    rw [hAe, hBe]
    exact exists_disjoint_piercing_marker_routes (continuousOn_univ.mp hg.continuousOn) ha1
      (hKP hp₀.1) (hKP hp₁.1) (by rw [ht₀]; constructor <;> linarith)
      (by rw [ht₁]; constructor <;> linarith) ⟨hgK _ hp₀.1, hg₀⟩ ⟨hgK _ hp₁.1, hg₁⟩ hne

theorem exists_pierced_square_ball_pair {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKP : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ (A B : Set ((ℝ × ℝ) × ℝ)) (f₀ f₁ : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) × ℝ),
      IsPLBall 3 A ∧ IsPLBall 3 B ∧
      IsPLHomeomorphOn f₀ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) A ∧
      IsPLHomeomorphOn f₁ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (0 : ℝ) 1) B ∧
      IsPLHomeomorphOn f₀ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
      IsPLHomeomorphOn f₁ (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
      EqOn f₀ id (univ ×ˢ Ioo (-a) a)ᶜ ∧ EqOn f₁ id (univ ×ˢ Ioo (-a) a)ᶜ ∧
      (interior A ∩ interior B).Nonempty ∧ IsPLSphere 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ {(0 : ℝ)} ∧
      A ∩ B ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1) ×ˢ Icc (-a / 2) (a / 2) ∧
      A ∪ B ⊆ Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ∧
      K ×ˢ Ioo (-1 : ℝ) 1 ⊆ interior A ∪ interior B ∧
      A \ (univ ×ˢ Ioo (-a) a) =
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) \ (univ ×ˢ Ioo (-a) a) ∧
      B \ (univ ×ˢ Ioo (-a) a) =
        (Metric.closedBall (0 : ℝ × ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (univ ×ˢ Ioo (-a) a) ∧
      ∀ p₀ ∈ K ×ˢ {(0 : ℝ)}, ∀ p₁ ∈ K ×ˢ {(0 : ℝ)}, p₀ ≠ p₁ →
        ∃ (L₀ L₁ : Set ((ℝ × ℝ) × ℝ)) (q₀ q₁ : (ℝ × ℝ) × ℝ),
          IsCompact L₀ ∧ IsCompact L₁ ∧ IsConnected L₀ ∧ IsConnected L₁ ∧
          Disjoint L₀ L₁ ∧ p₀ ∈ L₀ ∧ q₀ ∈ L₀ ∧ p₁ ∈ L₁ ∧ q₁ ∈ L₁ ∧
          L₀ ⊆ interior A ∩ (univ ×ˢ Ioo (-a) a) ∧
          L₁ ⊆ interior B ∩ (univ ×ˢ Ioo (-a) a) ∧ q₀ ∉ B ∧ q₁ ∉ A := by
  obtain ⟨A, B, f₀, f₁, hA, hB, hf₀, hf₁, hs₀, hs₁, hfix₀, hfix₁, hint,
    hcircle, hsub, hlens, hU, hcover, hAdiff, hBdiff, -, -, -, -, hroutes⟩ :=
    exists_crossing_pierced_square_ball_pair hK hKP ha ha1
  exact ⟨A, B, f₀, f₁, hA, hB, hf₀, hf₁, hs₀, hs₁, hfix₀, hfix₁, hint,
    hcircle, hsub, hlens, hU, hcover, hAdiff, hBdiff, hroutes⟩

end DifferentialGeometry.Topology.PiecewiseLinear
