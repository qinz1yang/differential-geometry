import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSliceSpatialCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMargins

open private distance_lower_of_radial distance_upper_of_radial radial_neck_image_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSliceSpatialCanonical

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_uniform_spatialNeck_canonicalWitness_with_margins (B K G : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}, SpatialNeck g eps x →
        (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
        (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
        (∀ v : TangentSpace I3 x,
          |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
            G * Real.sqrt (g.inner x v v)) →
        ∃ W : SpatialCanonicalWitness g eps 9 C x,
          W.capTubeHasNeckChart eps ∧ W.HasMargins (1 / 20) := by
  obtain ⟨κ, hκ, hvol⟩ := exists_pos_le_spatialNeck_unit_slab_volume.{u}
  set V := κ * (2 * (K + B + 1))⁻¹ ^ 3 with hVdef
  refine ⟨max 1 (max B (max K (max G V⁻¹))), le_max_left _ _, ?_⟩
  intro M _ _ _ _ _ g eps x nk hR hRm hG
  set C := max 1 (max B (max K (max G V⁻¹))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCB : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : K ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCG : G ≤ C := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hCV : V⁻¹ ≤ C := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hRm x)
  have hB1 : 1 ≤ B := (hR x).1.trans (hR x).2
  have hV : 0 < V := by positivity
  have hCp : 0 < C := zero_lt_one.trans_le hC1
  set Q := metricScalarAt g x with hQdef
  have hQ1 : 1 ≤ Q := (hR x).1
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hroot1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr hQ1
  have hQQ : 1 ≤ Q * Real.sqrt Q := one_le_mul_of_one_le_of_one_le hQ1 hroot1
  have hsmall : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  obtain ⟨dom, hdom, hxdom, hfront⟩ := nk.exists_compactDomain_region
  have hinner' : riemannianBallOf g x ((1 + 1 / 20) * (9 / Real.sqrt Q)) ⊆ dom.carrier := by
    have hbound : (1 + 1 / 20) * 9 ≤ 10 * Real.sqrt (1 - eps) := by
      have h : (189 / 200 : ℝ) ≤ Real.sqrt (1 - eps) := by
        apply Real.le_sqrt_of_sq_le
        linarith [nk.eps_small]
      linarith
    have hball := nk.ball_subset_image_slab (r := 10) (by norm_num) hsmall
    rw [← hQdef] at hball
    rw [hdom, ← mul_div_assoc]
    exact (riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hbound hroot.le)).trans hball
  have hinner : riemannianBallOf g x (9 / Real.sqrt Q) ⊆ dom.carrier :=
    (riemannianBallOf_mono _ _ (le_mul_of_one_le_left (by positivity) (by norm_num))).trans
      hinner'
  have houter' : dom.carrier ⊆ riemannianBallOf g x ((2 - 1 / 20) * (9 / Real.sqrt Q)) := by
    have hnum : (10 + 6) * Real.sqrt (1 + eps) < (2 - 1 / 20) * 9 := by
      have hs := Real.sq_sqrt (by linarith [nk.eps_pos] : 0 ≤ 1 + eps)
      nlinarith [nk.eps_small, Real.sqrt_nonneg (1 + eps)]
    rw [hdom]
    intro y hy
    have hcb := nk.image_slab_subset_closedBall (r := 10) (by norm_num) hsmall
    rw [← hQdef] at hcb
    have hc := hcb hy
    change riemannianEDistOf g x y ≤ _ at hc
    change riemannianEDistOf g x y < _
    apply hc.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [← mul_div_assoc]
    exact div_lt_div_of_pos_right hnum hroot
  have houter : dom.carrier ⊆ riemannianBallOf g x (2 * (9 / Real.sqrt Q)) :=
    houter'.trans (riemannianBallOf_mono _ _
      (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)))
  let data : SpatialLocalNeck g eps x dom.carrier :=
    { neck := nk
      region_eq := hdom
      boundary_eq := hfront }
  have hslab : nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ dom.carrier := by
    rw [hdom]
    exact image_mono (prod_mono subset_rfl (Icc_subset_Icc (by norm_num) (by norm_num)))
  have hvolume := (hvol nk hB1 (hR x).2 (hRm x)).trans (MeasureTheory.measure_mono hslab)
  let W : SpatialCanonicalWitness g eps 9 C x :=
    { Q_pos := hQ
      eps_pos := nk.eps_pos
      eps_lt_one := nk.eps_small.trans (by norm_num)
      domain := dom
      center_inside := hxdom
      radius := 9 / Real.sqrt Q
      radius_lower := by
        rw [← one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hroot.le
      radius_upper := le_rfl
      ball_inside := hinner
      inside_ball := houter
      scalar_bounds := by
        intro y _
        have hQC : C⁻¹ * Q ≤ 1 := by
          rw [← div_eq_inv_mul, div_le_one hCp]
          exact (hR x).2.trans hCB
        exact ⟨hQC.trans (hR y).1, ((hR y).2.trans hCB).trans (le_mul_of_one_le_right hCp.le hQ1)⟩
      rm_bound := fun y _ => ((hRm y).trans hCK).trans (le_mul_of_one_le_right hCp.le hQ1)
      alternative := SpatialCanonicalAlternative.neck data
      volume := by
        intro _
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
        have h1 : C⁻¹ / (Q * Real.sqrt Q) ≤ C⁻¹ :=
          div_le_self (inv_nonneg.mpr hCp.le) hQQ
        have h2 : C⁻¹ ≤ V := by
          rw [inv_le_comm₀ hCp hV]
          exact hCV
        exact h1.trans h2
      gradient := by
        intro v
        apply (hG v).trans
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h := mul_le_mul hCG hQQ zero_le_one hCp.le
        rw [mul_one] at h
        simpa only [mul_assoc] using h }
  refine ⟨W, ?_, ⟨Or.inl ⟨data, rfl⟩, ?_, hinner', houter', ?_⟩⟩
  · intro cap depth heq
    change SpatialCanonicalAlternative.neck data = _ at heq
    cases heq
  · exact div_le_div_of_nonneg_right (by norm_num) hroot.le
  · intro c d heq
    change SpatialCanonicalAlternative.neck data = _ at heq
    cases heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem exists_tip_spatialCanonicalWitness_with_margins
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (B K G Λ D : ℝ) (hΛ : 1 ≤ Λ)
    (hD : 0 < D) :
    ∃ C1 C2 : ℝ, 1 ≤ C2 ∧ ∀ g : SmoothRiemannianMetric I3 ThreeSpace,
      (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
      (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
      (∀ y (v : TangentSpace I3 y),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) y v)| ≤
          G * Real.sqrt (g.inner y v v)) →
      (∀ y v : ThreeSpace, StandardCap.metric.inner y v v ≤ Λ * g.inner y v v) →
      (∀ y v : ThreeSpace, g.inner y v v ≤ Λ * StandardCap.metric.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∀ v : ThreeSpace,
        ⟪y, v⟫_ℝ ^ 2 * (1 - 1 / 100) ≤ ‖y‖ ^ 2 * g.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → g.inner y y y ≤ (1 + 1 / 100) * ‖y‖ ^ 2) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ nk : SpatialNeck g eps y,
        ∀ z : neckBuffer eps,
          nk.map z.val = (‖y‖ + c * z.val.2) • StandardCap.pointedInitialRotation y z.val.1) →
      ∀ x : ThreeSpace, ‖x‖ ≤ D →
        ∃ W : SpatialCanonicalWitness g eps C1 C2 x,
          W.capTubeHasNeckChart eps ∧ W.HasMargins (1 / 20) := by
  obtain ⟨κ, hκ, hvol⟩ := exists_pos_le_spatialNeck_unit_slab_volume.{0}
  set V := κ * (2 * (K + B + 1))⁻¹ ^ 3 with hVdef
  set D₁ := D + 1 + Λ with hD₁
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = StandardCap.transitionEnd + eps⁻¹ + 2 +
      4 * (Real.sqrt Λ * D) + 4 * D₁ + 11200 + D := ⟨_, rfl⟩
  have hT := StandardCap.transitionEnd_pos
  have hi : 0 < eps⁻¹ := inv_pos.mpr heps
  have hi11 : (11 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) heps).mpr (by linarith)
  have hsΛ : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
  have hSD : 0 ≤ Real.sqrt Λ * D := mul_nonneg hsΛ hD.le
  have hD₁pos : D + 2 ≤ D₁ := by linarith
  have hrD : D ≤ r := by linarith
  have hr1 : 1 < r := by linarith
  have hrend : StandardCap.transitionEnd + eps⁻¹ + 1 < r := by linarith
  refine ⟨(r + 1) * Real.sqrt B, max 1 (max B (max K (max G V⁻¹))), le_max_left _ _, ?_⟩
  intro g hR hRm hG hlow hup hfar1 hfar2 hneck x hx
  set C := max 1 (max B (max K (max G V⁻¹))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCB : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : K ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCG : G ≤ C := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hCV : V⁻¹ ≤ C := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hRm x)
  have hB1 : 1 ≤ B := (hR x).1.trans (hR x).2
  have hV : 0 < V := by positivity
  have hCp : 0 < C := zero_lt_one.trans_le hC1
  set Q := metricScalarAt g x with hQdef
  have hQ1 : 1 ≤ Q := (hR x).1
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hroot1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr hQ1
  have hrootB : Real.sqrt Q ≤ Real.sqrt B := Real.sqrt_le_sqrt (hR x).2
  have hQQ : 1 ≤ Q * Real.sqrt Q := one_le_mul_of_one_le_of_one_le hQ1 hroot1
  obtain ⟨p, hpdef⟩ : ∃ p : ThreeSpace,
      p = r • ((Geometry.Neck.spherePoint : Metric.sphere (0 : ThreeSpace) 1) : ThreeSpace) :=
    ⟨_, rfl⟩
  have hp : ‖p‖ = r := by
    rw [hpdef, norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  obtain ⟨c, hc, hc1, nk, hnk⟩ := hneck p (by rw [hp]; exact hrD)
  rw [hp] at hnk
  obtain ⟨_, _, K1, hK1, _⟩ := StandardCap.exists_spatial_neck_closed_ball_frontier heps hsmall
    hrend (s := c) ⟨by linarith, by linarith⟩
  obtain ⟨_, _, K0, hK0, hcore0, _⟩ := StandardCap.exists_spatial_neck_closed_ball_frontier heps
    hsmall hrend (s := 0) ⟨by linarith, by linarith⟩
  rw [add_zero] at hK0
  have himg := fun {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) =>
    radial_neck_image_eq heps hr1 hc hc1 (StandardCap.pointedInitialRotation p) nk.map hnk hS
  have hIcc : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  set T := nk.map '' (univ ×ˢ Icc (0 : ℝ) 1) with hTdef
  have hTmem : ∀ y, y ∈ T ↔ r ≤ ‖y‖ ∧ ‖y‖ ≤ r + c := by
    intro y
    rw [hTdef, himg hIcc]
    change (‖y‖ - r) / c ∈ Icc (0 : ℝ) 1 ↔ _
    rw [mem_Icc, le_div_iff₀ hc, div_le_iff₀ hc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hdomain : univ ×ˢ Icc (0 : ℝ) 1 ⊆ nk.map.source := fun z hz =>
    nk.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hr0 : r ≠ 0 := by linarith
  have hrc0 : r + c ≠ 0 := by linarith
  have hfront0 : frontier K0.carrier = Metric.sphere 0 r := by
    rw [hK0, frontier_closedBall _ hr0]
  have hfront1 : frontier K1.carrier = Metric.sphere 0 (r + c) := by
    rw [hK1, frontier_closedBall _ hrc0]
  have hsph (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
      nk.map '' (univ ×ˢ ({a} : Set ℝ)) = Metric.sphere 0 (r + c * a) := by
    rw [himg (singleton_subset_iff.mpr ha)]
    ext y
    simp only [mem_ofPred_eq, mem_singleton_iff, mem_sphere_zero_iff_norm]
    rw [div_eq_iff hc.ne']
    constructor <;> intro h <;> linarith
  have hsph0 := hsph 0 ⟨by norm_num, by norm_num⟩
  have hsph1 := hsph 1 ⟨by norm_num, le_rfl⟩
  rw [mul_zero, add_zero] at hsph0
  rw [mul_one] at hsph1
  have hclosedTube : IsClosed T := by
    rw [hTdef, himg hIcc]
    exact isClosed_Icc.preimage ((continuous_norm.sub continuous_const).div_const c)
  let chain : SpatialOrderedNeckChain g eps T :=
    { count := 1
      count_pos := one_pos
      centers := fun _ => p
      necks := fun _ => nk
      lo := fun _ => 0
      hi := fun _ => 1
      lo_lt_hi := fun _ => one_pos
      inside := fun _ => hdomain
      swept_eq := (iUnion_const _).symm
      transition_increasing := by
        intro i j hij
        have := i.isLt
        have := j.isLt
        omega }
  have hxr : ‖x‖ < r := by linarith
  let cap : SpatialLocalCap g eps x K1.carrier :=
    { core := K0
      core_inside := by
        rw [hK0, hK1, interior_closedBall _ hrc0]
        exact Metric.closedBall_subset_ball (lt_add_of_pos_right r hc)
      center_inside := by
        rw [hK0, interior_closedBall _ hr0, mem_ball_zero_iff]
        exact hxr
      coreModel := Classical.choice hcore0
      tube := T
      tubeMap := nk.map
      tube_domain := hdomain
      tube_eq := rfl
      union_eq := by
        rw [hK1, hK0]
        ext y
        rw [mem_union, hTmem, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right]
        constructor
        · intro h
          by_cases hy : ‖y‖ ≤ r
          · exact Or.inl hy
          · exact Or.inr ⟨by linarith, h⟩
        · rintro (h | h)
          · linarith
          · exact h.2
      overlap_eq := by
        rw [hfront0, hK0]
        ext y
        rw [mem_inter_iff, hTmem, Metric.mem_closedBall, dist_zero_right,
          mem_sphere_zero_iff_norm]
        constructor
        · rintro ⟨h1, h2, _⟩
          linarith
        · intro h
          exact ⟨h.le, h.ge, by linarith⟩
      inner_boundary := hsph0.trans hfront0.symm
      outer_boundary := hsph1.trans hfront1.symm
      boundary_eq := by
        rw [frontier_image_univ_prod_Icc zero_le_one nk.map hdomain hclosedTube, hfront0,
          hfront1, ← hsph0, ← hsph1, ← image_union, ← prod_union]
        rfl
      boundaries_disjoint := by
        rw [hfront0, hfront1, Set.disjoint_left]
        intro y h1 h2
        rw [mem_sphere_zero_iff_norm] at h1 h2
        linarith
      chain := chain
      coreBoundaryMap := fun z => nk.map (z, 0)
      core_boundary_eq := fun _ => rfl }
  set α := Real.sqrt (1 - 1 / 100) with hαdef
  set β := Real.sqrt (1 + 1 / 100) with hβdef
  have hα9 : 9 / 10 ≤ α := Real.le_sqrt_of_sq_le (by norm_num)
  have hα1 : α ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hβ : β ≤ 11 / 10 := by
    rw [hβdef, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hL : ∀ b, riemannianEDistOf g x b ≠ ⊤ ∧
      α * (‖b‖ - D₁) - 1 ≤ (riemannianEDistOf g x b).toReal := fun b =>
    distance_lower_of_radial g (by norm_num) (by norm_num) hΛ hfar1 hlow hup hx
  have hU : ∀ b, riemannianEDistOf g x b ≤
      ENNReal.ofReal (2 * Real.sqrt Λ * D + β * max 0 (‖b‖ - D)) := fun b =>
    distance_upper_of_radial g hD (by norm_num) hΛ hfar2 hup hx
  have hrD₁ : 11200 ≤ r - D₁ := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = α * (r + c - D₁) - 1 := ⟨_, rfl⟩
  have hρ : 10000 ≤ ρ := by
    have h := mul_le_mul hα9 (show (11200 : ℝ) ≤ r + c - D₁ by linarith) (by norm_num)
      (by linarith)
    linarith
  have hdepth' : ∀ y ∈ cap.tube, (10000 + 1 / 20) / Real.sqrt Q ≤ metricDistance g x y := by
    intro y hy
    have hy' := (hTmem y).mp hy
    have h1 := (hL y).2
    have h3 : (10000 + 1 / 20) / Real.sqrt Q ≤ 10000 + 1 / 20 := div_le_self (by norm_num) hroot1
    change (10000 + 1 / 20) / Real.sqrt Q ≤ (riemannianEDistOf g x y).toReal
    have h4 := mul_le_mul hα9 (show (11200 : ℝ) ≤ ‖y‖ - D₁ by linarith) (by norm_num)
      (by linarith)
    linarith
  have hdepth : ∀ y ∈ cap.tube, 10000 / Real.sqrt Q ≤ metricDistance g x y := fun y hy =>
    (div_le_div_of_nonneg_right (by norm_num) hroot.le).trans (hdepth' y hy)
  have hxin : x ∈ interior K1.carrier := by
    rw [hK1, interior_closedBall _ hrc0, mem_ball_zero_iff]
    linarith
  have hball : riemannianBallOf g x ρ ⊆ K1.carrier := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal ρ at hy
    rw [ENNReal.lt_ofReal_iff_toReal_lt (hL y).1] at hy
    rw [hK1, Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    have h1 := (hL y).2
    have h4 := mul_lt_mul_of_pos_left (show r + c - D₁ < ‖y‖ - D₁ by linarith)
      (show (0 : ℝ) < α by linarith)
    linarith
  have hout' : K1.carrier ⊆ riemannianBallOf g x ((2 - 1 / 20) * (20 / 21 * ρ)) := by
    intro y hy
    rw [hK1, Metric.mem_closedBall, dist_zero_right] at hy
    change riemannianEDistOf g x y < ENNReal.ofReal ((2 - 1 / 20) * (20 / 21 * ρ))
    refine (hU y).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr ?_)
    have hm : max 0 (‖y‖ - D) ≤ r + c := max_le (by linarith) (by linarith)
    have h1 : β * max 0 (‖y‖ - D) ≤ 11 / 10 * (r + c) :=
      (mul_le_mul_of_nonneg_left hm hβ0).trans (mul_le_mul_of_nonneg_right hβ (by linarith))
    have h2 : 9 / 10 * (r + c - D₁) ≤ α * (r + c - D₁) :=
      mul_le_mul_of_nonneg_right hα9 (by linarith)
    linarith
  have hout : K1.carrier ⊆ riemannianBallOf g x (2 * (20 / 21 * ρ)) :=
    hout'.trans (riemannianBallOf_mono _ _
      (mul_le_mul_of_nonneg_right (by norm_num) (by linarith)))
  have hball' : riemannianBallOf g x ((1 + 1 / 20) * (20 / 21 * ρ)) ⊆ K1.carrier := by
    have h : (1 + 1 / 20 : ℝ) * (20 / 21 * ρ) = ρ := by ring
    rw [h]
    exact hball
  have hslab : nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ K1.carrier := by
    rw [himg le_rfl, hK1]
    intro y hy
    change (‖y‖ - r) / c ∈ Icc (-1 : ℝ) 1 at hy
    rw [mem_Icc, div_le_iff₀ hc] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hy.2]
  have hvolume := (hvol nk hB1 (hR p).2 (hRm p)).trans (MeasureTheory.measure_mono hslab)
  have hQinv : (Real.sqrt Q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hroot1
  let W : SpatialCanonicalWitness g eps ((r + 1) * Real.sqrt B) C x :=
    { Q_pos := hQ
      eps_pos := heps
      eps_lt_one := hsmall.trans (by norm_num)
      domain := K1
      center_inside := hxin
      radius := 20 / 21 * ρ
      radius_lower := by linarith
      radius_upper := by
        rw [le_div_iff₀ hroot]
        have hρr : 20 / 21 * ρ ≤ r + 1 := by
          have h := mul_le_mul_of_nonneg_right hα1 (show 0 ≤ r + c - D₁ by linarith)
          linarith
        calc 20 / 21 * ρ * Real.sqrt Q ≤ (r + 1) * Real.sqrt Q :=
              mul_le_mul_of_nonneg_right hρr hroot.le
          _ ≤ (r + 1) * Real.sqrt B := mul_le_mul_of_nonneg_left hrootB (by linarith)
      ball_inside := (riemannianBallOf_mono _ _ (by linarith)).trans hball
      inside_ball := hout
      scalar_bounds := by
        intro y _
        have hQC : C⁻¹ * Q ≤ 1 := by
          rw [← div_eq_inv_mul, div_le_one hCp]
          exact (hR x).2.trans hCB
        exact ⟨hQC.trans (hR y).1, ((hR y).2.trans hCB).trans (le_mul_of_one_le_right hCp.le hQ1)⟩
      rm_bound := fun y _ => ((hRm y).trans hCK).trans (le_mul_of_one_le_right hCp.le hQ1)
      alternative := SpatialCanonicalAlternative.cap cap hdepth
      volume := by
        intro _
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
        have h1 : C⁻¹ / (Q * Real.sqrt Q) ≤ C⁻¹ :=
          div_le_self (inv_nonneg.mpr hCp.le) hQQ
        have h2 : C⁻¹ ≤ V := by
          rw [inv_le_comm₀ hCp hV]
          exact hCV
        exact h1.trans h2
      gradient := by
        intro v
        apply (hG x v).trans
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h := mul_le_mul hCG hQQ zero_le_one hCp.le
        rw [mul_one] at h
        simpa only [mul_assoc] using h }
  refine ⟨W, ?_, ⟨Or.inr ⟨cap, hdepth, rfl⟩, ?_, hball', hout', ?_⟩⟩
  · intro cap2 depth2 heq
    change SpatialCanonicalAlternative.cap cap hdepth = _ at heq
    cases heq
    exact ⟨_, nk, fun _ => rfl⟩
  · change (1 + 1 / 20) / Real.sqrt Q ≤ 20 / 21 * ρ
    have h : (1 + 1 / 20) / Real.sqrt Q ≤ 1 + 1 / 20 := div_le_self (by norm_num) hroot1
    linarith
  · intro c' d' heq
    change SpatialCanonicalAlternative.cap cap hdepth = _ at heq
    cases heq
    exact hdepth'

private theorem exists_uniform_spatialCanonicalWitness_with_margins_of_radial_far_region
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (B K G Λ D : ℝ) (hΛ : 1 ≤ Λ)
    (hD : 0 < D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : SmoothRiemannianMetric I3 ThreeSpace,
      (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
      (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
      (∀ y (v : TangentSpace I3 y),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) y v)| ≤
          G * Real.sqrt (g.inner y v v)) →
      (∀ y v : ThreeSpace, StandardCap.metric.inner y v v ≤ Λ * g.inner y v v) →
      (∀ y v : ThreeSpace, g.inner y v v ≤ Λ * StandardCap.metric.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∀ v : ThreeSpace,
        ⟪y, v⟫_ℝ ^ 2 * (1 - 1 / 100) ≤ ‖y‖ ^ 2 * g.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → g.inner y y y ≤ (1 + 1 / 100) * ‖y‖ ^ 2) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ nk : SpatialNeck g eps y,
        ∀ z : neckBuffer eps,
          nk.map z.val = (‖y‖ + c * z.val.2) • StandardCap.pointedInitialRotation y z.val.1) →
      ∀ x : ThreeSpace, ∃ W : SpatialCanonicalWitness g eps C C x,
        W.capTubeHasNeckChart eps ∧ W.HasMargins (1 / 20) := by
  obtain ⟨C1, C2, hC2, htip⟩ :=
    exists_tip_spatialCanonicalWitness_with_margins heps hsmall B K G Λ D hΛ hD
  obtain ⟨Cn, hCn, hneckW⟩ := exists_uniform_spatialNeck_canonicalWitness_with_margins.{0} B K G
  set C := max 9 (max C1 (max C2 Cn)) with hCdef
  have h9 : (9 : ℝ) ≤ C := le_max_left _ _
  have hC1 : C1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC2' : C2 ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCn' : Cn ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  intro g hR hRm hG hlow hup hfar1 hfar2 hneck x
  rcases le_or_gt D ‖x‖ with hx | hx
  · obtain ⟨_, _, _, nk, _⟩ := hneck x hx
    obtain ⟨W, hW, hM⟩ := hneckW nk hR hRm (hG x)
    exact ⟨W.enlargeConstants h9 hCn', hW.enlarge_constants h9 hCn',
      hM.enlarge_constants h9 hCn'⟩
  · obtain ⟨W, hW, hM⟩ := htip g hR hRm hG hlow hup hfar1 hfar2 hneck x hx.le
    exact ⟨W.enlargeConstants hC1 hC2', hW.enlarge_constants hC1 hC2',
      hM.enlarge_constants hC1 hC2'⟩

theorem StandardSolution.exists_spatialCanonicalWitness_with_margins
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ Icc 0 Θ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x,
          W.capTubeHasNeckChart eps ∧ W.HasMargins (1 / 20) := by
  set Θp := max Θ 0 with hΘp
  have hΘp0 : 0 ≤ Θp := le_max_right _ _
  have hΘp1 : Θp < 1 := max_lt hΘ zero_lt_one
  have hlt : ENNReal.ofReal Θp < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hΘp1
  obtain ⟨hlife, K, hK, hcurv⟩ := uniformStandardLifetime_slab Θp hΘp0 hlt
  obtain ⟨Cd, hCd, hder⟩ := uniformStandardLifetime_curvature_derivative_bounds_closed Θp hΘp0
    hlt 1
  obtain ⟨Λ, hΛ, hcmp⟩ := uniformStandardLifetime_metricComparison Θp hΘp0 hlt
  obtain ⟨D, hD, hfar⟩ := StandardSolution.exists_far_radial_spatialNeck heps hsmall hΘp1
    (show (0 : ℝ) < 1 / 100 by norm_num)
  obtain ⟨C, hC, hstatic⟩ := exists_uniform_spatialCanonicalWitness_with_margins_of_radial_far_region
    heps hsmall (9 * K) K (9 * Cd) Λ D hΛ hD
  refine ⟨C, hC, fun S x t ht => ?_⟩
  have htp : t ∈ Icc 0 Θp := ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  have hdom : t ∈ S.val.domain := S.mem_domain_of_mem_Icc hΘp1 htp
  have hRm : ∀ y, Real.sqrt (normSq0S (S.val.metric t) y 4 (metricRm04 (S.val.metric t) y)) ≤ K :=
    fun y => hcurv S t htp y
  have hR : ∀ y, 1 ≤ metricScalarAt (S.val.metric t) y ∧
      metricScalarAt (S.val.metric t) y ≤ 9 * K := by
    intro y
    refine ⟨S.val.one_le_scalar t hdom y, ?_⟩
    have hrm := hRm y
    rw [metricRm04_apply] at hrm
    have habs := scalar_abs_le_rm (S.val.metric t) y
    have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) y) : ℝ) = 3 := by
      rw [show Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at habs
    have hle : (3 : ℝ) ^ 2 *
        Real.sqrt (normSq0S (S.val.metric t) y 4 (metricRm04At (S.val.metric t) y)) ≤ 9 * K := by
      nlinarith
    exact (le_abs_self _).trans (habs.trans hle)
  have hG : ∀ y (v : TangentSpace I3 y),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.val.metric t)) y v)| ≤
        9 * Cd * Real.sqrt ((S.val.metric t).inner y v v) := by
    intro y v
    have h := Perelman.CanonicalNeighborhood.abs_scalarDifferential_le S.val.toSolutionOn t y v
    have hd := hder S 1 le_rfl t htp y
    have hdim : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by
      rw [show Module.finrank ℝ ThreeSpace = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at h
    refine h.trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)) (by norm_num)
  have hlow : ∀ y v : ThreeSpace,
      StandardCap.metric.inner y v v ≤ Λ * (S.val.metric t).inner y v v := by
    intro y v
    have h := ((hcmp S t htp).2 y v).1
    have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
    rw [inv_mul_le_iff₀ hΛ0] at h
    exact h
  have hup : ∀ y v : ThreeSpace,
      (S.val.metric t).inner y v v ≤ Λ * StandardCap.metric.inner y v v :=
    fun y v => ((hcmp S t htp).2 y v).2
  exact hstatic (S.val.metric t) hR hRm hG hlow hup
    (fun y hy => (hfar S t htp y hy).2.1) (fun y hy => (hfar S t htp y hy).2.2)
    (fun y hy => (hfar S t htp y hy).1) x

end DifferentialGeometry.PDE.RicciFlow
