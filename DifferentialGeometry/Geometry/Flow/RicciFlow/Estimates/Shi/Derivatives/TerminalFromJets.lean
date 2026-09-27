import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompleteGlobal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood.FiniteHorn
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance terminalShiJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalShiJetsC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem shi_local_curvDerivNorm_terminal_of_solution_jets
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : 2 ≤ Module.finrank ℝ E)
    {a b K R : ℝ} (hab : a < b) (hK : 0 < K) (hR : 0 < R)
    (hcarrier : Set.Icc a b ⊆ D.carrier) (hregular : Set.Ico a b ⊆ D.regular)
    (p : M)
    (hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)})
    (hcurv : ∀ t ∈ Set.Icc a b, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 (S.base.metric t) y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc a b, ∀ y : M,
      riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K)) →
          curvDerivNorm (I := I) m (S.base.metric t) y ≤
            shiLocalUniformBound (Module.finrank ℝ E) m (K * (b - a)) R * K /
              Real.sqrt (t - a) ^ m := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have ha : a ∈ D.regular := hregular ⟨le_rfl, hab⟩
  obtain ⟨lo, hi, hlo, hnear⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (D.regular_isOpen.mem_nhds ha)
  obtain ⟨a0, ha0lo, ha0a⟩ := exists_between hlo.1
  have ha0b : a0 < b := ha0a.trans hab
  have hextended : Set.Ico a0 b ⊆ D.regular := by
    intro s hs
    by_cases hsa : s ≤ a
    · exact hnear ⟨ha0lo.trans_le hs.1, hsa.trans_lt hlo.2⟩
    · exact hregular ⟨(lt_of_not_ge hsa).le, hs.2⟩
  let Sr := S.timeRestrict (RealTimeInterval.closedOpen a0 b ha0b)
  have hSr : IsSolutionOn Sr :=
    isSolutionOn_timeRestrict hS (fun s hs => D.regular_subset (hextended hs))
      (fun s hs => hextended ⟨hs.1.le, hs.2⟩)
  let St := timeShiftSolution Sr a
  have hSt : IsSolutionOn St := isSolutionOn_timeShiftSolution hSr a
  have hmetric (s : ℝ) : St.base.metric s = S.base.metric (s + a) := rfl
  have hmetric0 : St.base.metric 0 = S.base.metric a := by rw [hmetric, zero_add]
  have hball' : IsCompact {y : M |
      riemannianEDistOf (I := I) (St.base.metric 0) p y ≤
        ENNReal.ofReal (R / Real.sqrt K)} := by
    rw [hmetric0]
    exact hball
  have hinterior (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo a b) (y : M)
      (hy : riemannianEDistOf (I := I) (S.base.metric a) p y ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K))) :
      curvDerivNorm (I := I) m (S.base.metric t) y ≤
        shiLocalUniformBound (Module.finrank ℝ E) m (K * (b - a)) R * K /
          Real.sqrt (t - a) ^ m := by
    have hcurv' : ∀ s ∈ Set.Icc (0 : ℝ) (t - a), ∀ z : M,
        riemannianEDistOf (I := I) (St.base.metric 0) p z ≤
          ENNReal.ofReal (R / Real.sqrt K) →
            nablaKRm04NormSqIntrinsic (I := I) St 0 s z ≤ K ^ 2 := by
      intro s hs z hz
      rw [hmetric0] at hz
      rw [← curvNormSq_eq St 0 s z, hmetric]
      exact hcurv (s + a) ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩ z hz
    have hpoint : riemannianEDistOf (I := I) (St.base.metric 0) p y ≤
        ENNReal.ofReal (R / (2 * Real.sqrt K)) := by
      rw [hmetric0]
      exact hy
    have h := (shi_local_all_orders_curvature_scale_of_solution_uniform St hSt p
      (sub_neg.mpr ha0a) hK (sub_pos.mpr ht.1) (sub_lt_sub_right ht.2 a) hR
      (by exact ⟨by linarith, by linarith⟩) hball' hcurv'
      m (t - a) ⟨sub_pos.mpr ht.1, le_rfl⟩ y hpoint).2
    rw [← curvNormSq_eq St m (t - a) y] at h
    change curvDerivNorm (I := I) m (St.base.metric (t - a)) y ≤ _ at h
    rw [hmetric, sub_add_cancel] at h
    apply h.trans
    apply div_le_div_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) _)
    apply mul_le_mul_of_nonneg_right _ hK.le
    exact shiLocalUniformBound_mono _ _ hR (mul_nonneg hK.le (sub_pos.mpr ht.1).le)
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) hK.le)
  intro m t ht y hy
  rcases lt_or_eq_of_le ht.2 with htb | htb
  · exact hinterior m t ⟨ht.1, htb⟩ y hy
  · subst t
    have hleft : Tendsto (fun s => curvDerivNorm (I := I) m (S.base.metric s) y)
        (𝓝[<] b) (𝓝 (curvDerivNorm (I := I) m (S.base.metric b) y)) := by
      have hc := solution_nablaKRm04NormSqIntrinsic_continuousWithinAt_terminal
        S hS hab hcarrier (fun s hs => hregular ⟨hs.1.le, hs.2⟩) m y
      simpa only [curvDerivNorm, curvNormSq_eq] using
        (hc.mono Set.Iio_subset_Iic_self).sqrt.tendsto
    have hright : ContinuousAt (fun s : ℝ =>
        shiLocalUniformBound (Module.finrank ℝ E) m (K * (b - a)) R * K /
          Real.sqrt (s - a) ^ m) b :=
      continuousAt_const.div ((continuousAt_id.sub continuousAt_const).sqrt.pow m)
        (pow_ne_zero m (Real.sqrt_pos.mpr (sub_pos.mpr hab)).ne')
    apply le_of_tendsto_of_tendsto hleft (hright.tendsto.mono_left inf_le_left)
    filter_upwards [Ioo_mem_nhdsLT hab] with s hs
    exact hinterior m s hs y hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
