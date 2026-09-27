import DifferentialGeometry.Geometry.Neck.CapSeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Metric.Distance.Basic

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_tolerance_alternative_eq_neck_of_spatialNeck (C1 C2 : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
      [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M)
      (epsc epsb eps : ℝ) (y : M) (W : SpatialCanonicalWitness g epsc C1 C2 y),
      W.capTubeHasNeckChart epsb → epsb ≤ 1 / 1000 → eps ≤ eta →
      Nonempty (SpatialNeck g eps y) →
      ∃ neck : SpatialLocalNeck g epsc y W.domain.carrier,
        W.alternative = SpatialCanonicalAlternative.neck neck := by
  set C := max C2 1 with hCdef
  set D := 4 * max C1 0 with hDdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨eta₀, heta₀, hsep⟩ := exists_neck_cap_separation_tolerance_of_subset
    (C := C) (D := D) (c := C⁻¹) hC (by positivity) (inv_pos.mpr hC)
  set r := 4 * max C1 1 with hrdef
  have hr : 0 < r := by positivity
  refine ⟨min eta₀ (min (1 / 2) (1 / (r + 2))), by positivity, ?_⟩
  intro M _ _ _ _ _ g epsc epsb eps y W hW hb heps ⟨nk⟩
  have hepspos := nk.eps_pos
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hCeq : C = C2 := max_eq_left hC2
  have hq := W.Q_pos
  set q := metricScalarAt g y with hqdef
  have hsq := Real.sqrt_pos.mpr hq
  have hC1 : 1 ≤ C1 := by
    have h := W.radius_lower.trans W.radius_upper
    rw [inv_eq_one_div, div_le_div_iff_of_pos_right hsq] at h
    exact h
  have hDeq : D = 4 * C1 := by rw [hDdef, max_eq_left (by linarith)]
  have hreq : r = 4 * C1 := by rw [hrdef, max_eq_left hC1]
  have hdom : ∀ a ∈ W.domain.carrier,
      riemannianEDistOf g y a < ENNReal.ofReal (2 * (C1 / Real.sqrt q)) := by
    intro a ha
    have h : riemannianEDistOf g y a < ENNReal.ofReal (2 * W.radius) := W.inside_ball ha
    exact h.trans_le (ENNReal.ofReal_le_ofReal (by linarith [W.radius_upper]))
  have heps2 : eps ≤ 1 / 2 := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsr : eps ≤ 1 / (r + 2) := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlong : r + 1 < eps⁻¹ := by
    have h1 : (1 / (r + 2))⁻¹ ≤ eps⁻¹ := inv_anti₀ hepspos hepsr
    rw [one_div, inv_inv] at h1
    linarith
  have hproper : W.domain.carrier ≠ connectedComponent y := by
    intro hwhole
    let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : ThreeSpace)
        (by norm_num : (0 : ℝ) ≤ 1))
    have hwin : (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ ⊆ nk.map.source := nk.domain
    have hS : IsPreconnected (nk.map '' ((univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹)) :=
      (isPreconnected_univ.prod isPreconnected_Ioo).image _
        (nk.map.contMDiffOn_toFun.continuousOn.mono hwin)
    have hinv := inv_pos.mpr hepspos
    have hzwin : (nk.center, r + 1) ∈ (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
      ⟨mem_univ _, by linarith, hlong⟩
    have hywin : (nk.center, (0 : ℝ)) ∈ (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ :=
      ⟨mem_univ _, by linarith, hinv⟩
    have hycomp : y ∈ nk.map '' ((univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹) :=
      ⟨_, hywin, nk.center_eq⟩
    have hz : nk.map (nk.center, r + 1) ∈ W.domain.carrier := by
      rw [hwhole]
      exact hS.subset_connectedComponent hycomp ⟨_, hzwin, rfl⟩
    have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - eps) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hball : nk.map (nk.center, r + 1) ∈
        riemannianBallOf g y (r * Real.sqrt (1 - eps) / Real.sqrt q) := by
      have h := hdom _ hz
      refine h.trans_le (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_div_assoc', le_div_iff₀ hsq, div_mul_cancel₀ _ hsq.ne']
      rw [hreq]
      nlinarith
    obtain ⟨⟨u, a⟩, ⟨-, ha⟩, heq⟩ :=
      nk.ball_subset_image_slab hr (by linarith) hball
    have hawin : (u, a) ∈ nk.map.source :=
      hwin ⟨mem_univ _, by linarith [ha.1], by linarith [ha.2]⟩
    have he := nk.map.injOn hawin (hwin hzwin) heq
    have ha' : a = r + 1 := congrArg Prod.snd he
    linarith [ha.2]
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | positive whole data sec => exact (hproper whole).elim
  | round whole data => exact (hproper whole).elim
  | cap cap depth =>
    exfalso
    obtain ⟨v, bnk, hbmap⟩ := hW cap depth halt
    have hfront : frontier cap.core.carrier = range (fun z : Sphere 2 => bnk.map (z, 0)) := by
      rw [← cap.inner_boundary]
      ext w
      constructor
      · rintro ⟨⟨z, t⟩, ⟨-, ht⟩, rfl⟩
        have ht' : t = 0 := ht
        subst ht'
        exact ⟨z, (hbmap _).symm⟩
      · rintro ⟨z, rfl⟩
        exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, hbmap _⟩
    have hvtube : v ∈ cap.tube := by
      rw [← cap.tube_eq]
      exact ⟨(bnk.center, 0), ⟨mem_univ _, by norm_num⟩, (hbmap _).trans bnk.center_eq⟩
    have hvdom : v ∈ W.domain.carrier := by
      rw [cap.union_eq]
      exact Or.inr hvtube
    have hscalar : ∀ x ∈ W.domain.carrier, metricScalarAt g x ≤ C * q := fun x hx => by
      rw [hCeq]
      exact (W.scalar_bounds x hx).2
    have hbound : C⁻¹ * q ≤ metricScalarAt g v := by
      rw [hCeq]
      exact (W.scalar_bounds v hvdom).1
    have hdiam : ∀ a ∈ W.domain.carrier, ∀ b ∈ W.domain.carrier,
        riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) a b ≤ ENNReal.ofReal D := by
      intro a ha b hb'
      rw [edistOf_scale]
      have htri : riemannianEDistOf g a b ≤ ENNReal.ofReal (4 * (C1 / Real.sqrt q)) := by
        refine (riemannianEDistOf_triangle g a y b).trans ?_
        rw [riemannianEDistOf_comm g a y]
        refine (add_le_add (hdom a ha).le (hdom b hb').le).trans ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      refine (mul_le_mul_right htri _).trans ?_
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg q), hDeq]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by field_simp))
    have hdisj := hsep M g eps epsb y v (heps.trans (min_le_left _ _)) nk bnk hb 0
      ⟨neg_lt_zero.mpr (inv_pos.mpr bnk.eps_pos), inv_pos.mpr bnk.eps_pos⟩
      cap.core.carrier W.domain.carrier (cap.core_inside.trans interior_subset)
      cap.core.compact ⟨y, cap.center_inside⟩ hfront q hq hscalar hbound hdiam
    exact disjoint_left.mp hdisj (interior_subset W.center_inside)
      ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
