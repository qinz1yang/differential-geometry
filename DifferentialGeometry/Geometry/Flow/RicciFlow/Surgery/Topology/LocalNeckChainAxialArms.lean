import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckChainAxialArms

noncomputable section

open Set
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem mul_metricDistance_ge_of_neckChain {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete g) {eps L : ℝ} (hL : 0 < L) (hLeps : L < eps⁻¹)
    (c : ℕ → M) (nk : ∀ k, SpatialNeck g eps (c k)) {x : M} {i n : ℕ} (hin : i < n)
    (hstep : ∀ k, i ≤ k → k < n → c (k + 1) = (nk k).map ((nk k).center, L))
    (hscalar : ∀ k, i ≤ k → k < n → metricScalarAt g (c k) ≤ 4 * metricScalarAt g x)
    (hsep : ∀ k, i < k → k < n →
      Disjoint ((nk (k + 1)).map '' (univ ×ˢ ({0} : Set ℝ)))
        (connectedComponentIn ((nk k).map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ (c i))) :
    (Real.sqrt (1 - eps) * L - 14) * ((n - i : ℕ) : ℝ) / 2 ≤
      Real.sqrt (metricScalarAt g x) * metricDistance g (c i) (c n) := by
  set A := Real.sqrt (1 - eps) * L - 14 with hA
  set sQ := Real.sqrt (metricScalarAt g x) with hsQdef
  have hsQ0 : 0 ≤ sQ := Real.sqrt_nonneg _
  have hd0 : 0 ≤ metricDistance g (c i) (c n) := ENNReal.toReal_nonneg
  rcases lt_or_ge A 0 with hAneg | hApos
  · have : A * ((n - i : ℕ) : ℝ) / 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hAneg.le (by positivity))
        (by norm_num)
    exact this.trans (mul_nonneg hsQ0 hd0)
  let ell' : ℕ → ℝ := fun k => metricDistance g (c k) (c (k + 1))
  let e : ℕ → ℝ := fun k => 7 / Real.sqrt (metricScalarAt g (c k))
  have he : ∀ k, 0 ≤ e k := fun k => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hstepb : ∀ k, i ≤ k → k < n → riemannianEDistOf g (c k) (c (k + 1)) ≠ ⊤ ∧
      Real.sqrt (1 - eps) * L / Real.sqrt (metricScalarAt g (c k)) ≤ ell' k ∧
      ell' k ≤ Real.sqrt (1 + eps) * L / Real.sqrt (metricScalarAt g (c k)) := by
    intro k hk1 hk2
    simp only [ell']
    rw [hstep k hk1 hk2]
    exact (nk k).metricDistance_center_axial_bounds hL hLeps
  have hslice := metricDistance_ge_of_separating_slices hg c
    (fun k => (nk k).map '' (univ ×ˢ ({0} : Set ℝ))) e (i := i) (m := n) hin he
    (fun k _ _ => ⟨((nk k).center, 0), ⟨mem_univ _, mem_singleton 0⟩, (nk k).center_eq⟩)
    (fun k _ _ y hy => (nk k).central_sphere_subset_closedBall hy)
    (fun k hk1 hk2 => (hstepb k hk1 hk2).1) hsep
  have hsub : ∑ j ∈ Finset.Ico (i + 1) n, e j ≤ ∑ j ∈ Finset.Ico i n, e j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (by omega))
      (fun j _ _ => he j)
  have hterm : ∀ j ∈ Finset.Ico i n, A / 2 ≤ sQ * (ell' j - 2 * e j) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    have hQj : 0 < Real.sqrt (metricScalarAt g (c j)) := Real.sqrt_pos.mpr (nk j).Q_pos
    have hle : Real.sqrt (metricScalarAt g (c j)) ≤ 2 * sQ := by
      have h := Real.sqrt_le_sqrt (hscalar j hj1 hj2)
      rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    set r := sQ / Real.sqrt (metricScalarAt g (c j)) with hr
    have hr2 : 1 / 2 ≤ r := by
      rw [hr, le_div_iff₀ hQj]
      linarith
    have hlo := (hstepb j hj1 hj2).2.1
    have h1 : Real.sqrt (1 - eps) * L * r ≤ sQ * ell' j := by
      have := mul_le_mul_of_nonneg_left hlo hsQ0
      calc Real.sqrt (1 - eps) * L * r
          = sQ * (Real.sqrt (1 - eps) * L / Real.sqrt (metricScalarAt g (c j))) := by
            rw [hr]
            ring
        _ ≤ sQ * ell' j := this
    have h2 : sQ * (2 * e j) = 14 * r := by
      simp only [e, hr]
      ring
    have h3 : A / 2 ≤ A * r := by nlinarith
    have h4 : A * r = Real.sqrt (1 - eps) * L * r - 14 * r := by rw [hA]; ring
    rw [mul_sub, h2]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  have hmono : sQ * (∑ j ∈ Finset.Ico i n, ell' j - 2 * ∑ j ∈ Finset.Ico i n, e j) ≤
      sQ * metricDistance g (c i) (c n) :=
    mul_le_mul_of_nonneg_left (by linarith) hsQ0
  have hcast : ((n - i : ℕ) : ℝ) * (A / 2) = A * ((n - i : ℕ) : ℝ) / 2 := by ring
  linarith

theorem exists_minimizingArms_of_localNeckChain {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete g) {eps L D : ℝ} (hL : 0 < L) (hLeps : L < eps⁻¹)
    (hLD : 3 * L ≤ D) (c : ℕ → M) (nk : ∀ k, SpatialNeck g eps (c k)) {m : ℕ}
    (hstep : ∀ k < 2 * m, c (k + 1) = (nk k).map ((nk k).center, L))
    (hscalar : ∀ k ≤ 2 * m, metricScalarAt g (c m) ≤ 4 * metricScalarAt g (c k) ∧
      metricScalarAt g (c k) ≤ 4 * metricScalarAt g (c m))
    (hsep : ∀ i k, i < k → k < 2 * m →
      Disjoint ((nk (k + 1)).map '' (univ ×ˢ ({0} : Set ℝ)))
        (connectedComponentIn ((nk k).map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ (c i)))
    (hlong : 2 * D ≤ (Real.sqrt (1 - eps) * L - 14) * m) :
    ∃ (arms : Fin 2 → MinimizingArm g (c m)) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (metricScalarAt g (c m)) * ell j ∈ Icc D (2 * D)) ∧
      Real.arccos (9 / 2 * (14 / (Real.sqrt (1 - eps) * L)) - 1) ≤
        comparisonAngle (ell 0) (ell 1)
          (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) := by
  have hD : 0 < D := by linarith
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hlong
      linarith
    · exact h
  have hhigh := mul_metricDistance_ge_of_neckChain hg hL hLeps c nk (x := c m) (i := m)
    (n := 2 * m) (by omega) (fun k _ hk => hstep k hk)
    (fun k _ hk => (hscalar k hk.le).2) (fun k hk1 hk2 => hsep m k hk1 hk2)
  have hlow := mul_metricDistance_ge_of_neckChain hg hL hLeps c nk (x := c m) (i := 0)
    (n := m) hm (fun k _ hk => hstep k (by omega))
    (fun k _ hk => (hscalar k (by omega)).2) (fun k hk1 hk2 => hsep 0 k hk1 (by omega))
  rw [show 2 * m - m = m by omega] at hhigh
  rw [Nat.sub_zero] at hlow
  have hcomm : metricDistance g (c 0) (c m) = metricDistance g (c m) (c 0) := by
    unfold metricDistance
    rw [DifferentialGeometry.riemannianEDistOf_comm]
  rw [hcomm] at hlow
  exact exists_minimizingArms_of_neckNecklace hg hL hLeps hLD c nk (i₀ := m) (m := 2 * m)
    (by omega) hstep (fun k hk => (hscalar k hk).1) hsep (by linarith) (by linarith)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private theorem pi_div_two_le_arccos_of_nonpos {z : ℝ} (hz : z ≤ 0) :
    Real.pi / 2 ≤ Real.arccos z := by
  refine le_of_not_gt fun hlt => ?_
  have hpos := Real.arccos_lt_pi_div_two.mp hlt
  linarith

theorem exists_strongNeck_threshold_of_localNeckChain
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1 / 11)
    {kappa : ℝ} (hkappa : 0 < kappa) {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ D Q₀ theta : ℝ, 0 < D ∧ 0 < Q₀ ∧ 0 < theta ∧
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s) (t : ℝ)
        (c : ℕ → P.Carrier) (nk : ∀ k, SpatialNeck (G.flow.base.metric t) (3000)⁻¹ (c k))
        (m : ℕ), D ≤ 40 * m →
        (∀ k < 2 * m, c (k + 1) = (nk k).map ((nk k).center, 100)) →
        (∀ k ≤ 2 * m, G.flow.scalar t (c m) ≤ 4 * G.flow.scalar t (c k) ∧
          G.flow.scalar t (c k) ≤ 4 * G.flow.scalar t (c m)) →
        (∀ i k, i < k → k < 2 * m →
          Disjoint ((nk (k + 1)).map '' (Set.univ ×ˢ ({0} : Set ℝ)))
            (connectedComponentIn ((nk k).map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ (c i))) →
        t < s → Q₀ ≤ G.flow.scalar t (c m) →
        a ≤ t - theta / G.flow.scalar t (c m) →
        Perelman.PhiAlmostNonnegative G.flow
          (Set.Icc (t - theta / G.flow.scalar t (c m)) t) Phi →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t - theta / G.flow.scalar t (c m) ≤ τ → (τ : ℝ) ≤ t → B.radius ≤ rho →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
        Nonempty (StrongNeck G.flow delta (c m) t) := by
  obtain ⟨D, Q₀, theta, hD, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_minimizing_arms.{u} hdelta hdelta1 Real.pi_div_two_pos
      hkappa hrho hPhi
  refine ⟨D, Q₀, theta, hD, hQ₀, htheta, ?_⟩
  intro P a s G t c nk m hDm hstep hscalar hsep hts hQ hwin hpinch hnc
  have hcomplete := RiemannianMetricComplete.of_compact (G.flow.base.metric t)
  rcases lt_or_ge (9 * D) ((3000 : ℝ)⁻¹)⁻¹ with hsmall | hlarge
  · obtain ⟨arms, ell, hell, hlen, hang⟩ :=
      (nk m).exists_axial_minimizingArms hcomplete hD hsmall
    refine hthr P a s G (c m) t hts hQ hwin hpinch hnc arms ell hell hlen
      ((pi_div_two_le_arccos_of_nonpos ?_).trans hang)
    apply div_nonpos_of_nonpos_of_nonneg <;> norm_num
  · have hLD : 3 * (100 : ℝ) ≤ D := by
      rw [inv_inv] at hlarge
      linarith
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - (3000 : ℝ)⁻¹ by norm_num)
    have hs0 := Real.sqrt_nonneg (1 - (3000 : ℝ)⁻¹)
    have hs : (99 : ℝ) / 100 ≤ Real.sqrt (1 - (3000 : ℝ)⁻¹) := by nlinarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlong : 2 * D ≤ (Real.sqrt (1 - (3000 : ℝ)⁻¹) * 100 - 14) * m := by nlinarith
    obtain ⟨arms, ell, hell, hlen, hang⟩ :=
      exists_minimizingArms_of_localNeckChain hcomplete (by norm_num : (0 : ℝ) < 100)
        (by norm_num : (100 : ℝ) < ((3000 : ℝ)⁻¹)⁻¹) hLD c nk hstep hscalar hsep hlong
    refine hthr P a s G (c m) t hts hQ hwin hpinch hnc arms ell hell hlen
      ((pi_div_two_le_arccos_of_nonpos ?_).trans hang)
    have hpos : 0 < Real.sqrt (1 - (3000 : ℝ)⁻¹) * 100 := by positivity
    have hle : 14 / (Real.sqrt (1 - (3000 : ℝ)⁻¹) * 100) ≤ 2 / 9 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      nlinarith
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
