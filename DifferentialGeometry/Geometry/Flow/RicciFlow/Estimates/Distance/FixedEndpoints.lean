import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.EndpointRicci
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Comparison.DistanceFamily

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open scoped ENNReal Manifold ContDiff Topology

open private endpoint_le_of_no_events from
  DifferentialGeometry.Analysis.Calculus.DiniComparison

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] {D : RealTimeInterval}

/-- A backward distance bound from Ricci control on the two endpoint balls.
Finiteness selects the actual common component; the ambient manifold may be
disconnected. The two endpoint times need only belong to the carrier. -/
theorem riemannianEDistOf_le_add_of_endpoint_ricci_on_interval
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b ell : ℝ} (hab : a ≤ b) (hell : 0 < ell)
    (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Icc a b,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (p x : M)
    (hfin : riemannianEDistOf (S.base.metric b) p x ≠ ⊤)
    (hRic : ∀ t ∈ Ioo a b, ∀ z : M, ∀ ξ : TangentSpace I z,
      (riemannianEDistOf (S.base.metric t) p z < ENNReal.ofReal ell ∨
        riemannianEDistOf (S.base.metric t) x z < ENNReal.ofReal ell) →
      ricciTensor (S.base.metric t) z ξ ξ ≤
        (3 / ell ^ 2) * (S.base.metric t).inner z ξ ξ) :
    (∀ t ∈ Icc a b, riemannianEDistOf (S.base.metric t) p x ≠ ⊤) ∧
      riemannianEDistOf (S.base.metric a) p x ≤
        riemannianEDistOf (S.base.metric b) p x +
          ENNReal.ofReal ((8 / ell) * (b - a)) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · constructor
    · intro t ht
      have ht' : t = a := le_antisymm ht.2 ht.1
      subst t
      exact hfin
    · simp only [sub_self, mul_zero, ENNReal.ofReal_zero, add_zero, le_refl]
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let U := connectedComponentOpen (I := I) p
  let _ : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := I) p
  let _ : SigmaCompactSpace U :=
    (isClosed_connectedComponent (x := p)).sigmaCompactSpace
  let _ : IsManifold I ((∞ : WithTop ℕ∞) + 1) U := by
    simpa using (inferInstance : IsManifold I ∞ U)
  have hxU : x ∈ U := by
    apply edistOf_ball_subset_connCompOpen (S.base.metric b) p
      ((riemannianEDistOf (S.base.metric b) p x).toReal + 1)
    calc
      riemannianEDistOf (S.base.metric b) p x =
          ENNReal.ofReal (riemannianEDistOf (S.base.metric b) p x).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
      _ < ENNReal.ofReal ((riemannianEDistOf (S.base.metric b) p x).toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  let pU : U := connectedComponentPoint (I := I) p
  let xU : U := ⟨x, hxU⟩
  have hpU : (pU : M) = p := rfl
  have hxUval : (xU : M) = x := rfl
  let SU := solutionOnRestrictOpen S U
  have hSU : IsSolutionOn SU := isSolutionOn_restrictOpen S hS U
  have hdist (t : ℝ) (y z : U) :
      riemannianEDistOf (SU.base.metric t) y z =
        riemannianEDistOf (S.base.metric t) (y : M) (z : M) :=
    edistOf_restrictOpen_connCompOpen (S.base.metric t) p y z
  have hfinite (t : ℝ) : riemannianEDistOf (S.base.metric t) p x ≠ ⊤ := by
    change riemannianEDistOf (S.base.metric t) (pU : M) (xU : M) ≠ ⊤
    rw [← hdist t pU xU]
    exact riemannianEDistOf_ne_top _ _ _
  refine ⟨fun t _ => hfinite t, ?_⟩
  have hRicU (t : ℝ) (ht : t ∈ Ioo a b) (z : U) (ξ : TangentSpace I z)
      (hz : riemannianEDistOf (SU.base.metric t) pU z < ENNReal.ofReal ell ∨
        riemannianEDistOf (SU.base.metric t) xU z < ENNReal.ofReal ell) :
      ricciTensor (SU.base.metric t) z ξ ξ ≤
        (3 / ell ^ 2) * (SU.base.metric t).inner z ξ ξ := by
    have hz' : riemannianEDistOf (S.base.metric t) p (z : M) <
          ENNReal.ofReal ell ∨
        riemannianEDistOf (S.base.metric t) x (z : M) < ENNReal.ofReal ell := by
      simpa only [hdist, hpU, hxUval] using hz
    have hh := hRic t ht (z : M) (mfderiv I I (Subtype.val : U → M) z ξ) hz'
    change ricciTensor ((S.base.metric t).restrictOpen U) z ξ ξ ≤
      (3 / ell ^ 2) * ((S.base.metric t).restrictOpen U).inner z ξ ξ
    simpa only [DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
      SmoothRiemannianMetric.restrictOpen_inner,
      mfderiv_subtype_val_apply] using hh
  let d : ℝ → ℝ := fun τ =>
    (riemannianEDistOf (S.base.metric (b + 1 - τ)) p x).toReal
  have hDini (τ : ℝ) (hτ : τ ∈ Ioo 1 (b + 1 - a)) :
      UpperRightDiniLE d τ (8 / ell) := by
    have hτpos : 0 < τ := lt_trans zero_lt_one hτ.1
    have ht : b + 1 - τ ∈ Ioo a b := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hroot : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
    have hradius : Real.sqrt τ / (Real.sqrt τ / ell) = ell := by
      field_simp [hroot.ne', hell.ne']
    have hcoef : 3 * (Real.sqrt τ / ell) ^ 2 / τ = 3 / ell ^ 2 := by
      field_simp [hell.ne', hτpos.ne']
      nlinarith only [Real.sq_sqrt hτpos.le]
    have hslope : 8 * (Real.sqrt τ / ell) / Real.sqrt τ = 8 / ell := by
      field_simp [hroot.ne', hell.ne']
    have hh := upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds
      SU hSU hdim (T := b + 1) (t := τ) (B := Real.sqrt τ / ell)
      (vx := 0) (vy := 0) hτpos (div_pos hroot hell) (hregular ht)
      (riemannianMetricComplete_restrictOpen_connCompOpen
        (S.base.metric (b + 1 - τ)) p (hcomplete _ ⟨ht.1.le, ht.2.le⟩))
      (fun _ => pU) (fun _ => xU) contMDiffAt_const contMDiffAt_const
      (by simp) (by simp) (by
        intro z ξ hz
        rw [hradius] at hz
        rw [hcoef]
        exact hRicU _ ht z ξ hz)
    rw [hslope, add_zero, add_zero] at hh
    simpa only [d, hdist, hpU, hxUval] using hh
  have hmetric := metricTensor_cont_restrict_of_metricFamilySmoothOn
    S.base.metric hS.smoothMetric hcarrier
  have hedist := Geometry.Riemannian.continuousOn_riemannianEDistOf
    S.base.metric (J := Icc a b) ordConnected_Icc hmetric hcomplete p
  have hedistTime : ContinuousOn
      (fun t => riemannianEDistOf (S.base.metric t) p x) (Icc a b) := by
    simpa only [Function.comp_def, id_eq] using hedist.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ x⟩)
  have hrealTime : ContinuousOn
      (fun t => (riemannianEDistOf (S.base.metric t) p x).toReal) (Icc a b) :=
    ENNReal.continuousOn_toReal.comp hedistTime (fun t _ => hfinite t)
  have hd : ContinuousOn d (Icc 1 (b + 1 - a)) := by
    apply hrealTime.comp (continuous_const.sub continuous_id).continuousOn
    intro τ hτ
    change a ≤ b + 1 - τ ∧ b + 1 - τ ≤ b
    exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  let f : ℝ → ℝ := fun τ => d τ - (8 / ell) * τ
  have hf : ContinuousOn f (Icc 1 (b + 1 - a)) :=
    hd.sub (continuous_const.mul continuous_id).continuousOn
  have hfDini (τ : ℝ) (hτ : τ ∈ Ioo 1 (b + 1 - a)) :
      UpperRightDiniLE f τ 0 := by
    intro ε hε
    filter_upwards [hDini τ hτ ε hε, self_mem_nhdsWithin] with y hy hyτ
    have hne : y - τ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hyτ)
    rw [slope_def_field] at hy ⊢
    dsimp only [f]
    have hsub : ((d y - (8 / ell) * y) - (d τ - (8 / ell) * τ)) / (y - τ) =
        (d y - d τ) / (y - τ) - 8 / ell := by
      field_simp [hne, hell.ne']
      ring
    rw [hsub]
    linarith
  have hclock : 1 < b + 1 - a := by linarith
  have hfleft : ContinuousWithinAt f (Ici 1) 1 :=
    (continuousWithinAt_Icc_iff_Ici hclock).mp (hf 1 ⟨le_rfl, hclock.le⟩)
  have hfright : Tendsto f (𝓝[<] (b + 1 - a)) (𝓝 (f (b + 1 - a))) :=
    (hf _ ⟨hclock.le, le_rfl⟩).mono_left
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT_of_mem ⟨hclock, le_rfl⟩))
  have hbound : f (b + 1 - a) ≤ f 1 :=
    endpoint_le_of_no_events hclock
      (fun τ hτ => (hf τ ⟨hτ.1.le, hτ.2.le⟩).continuousAt
        (Icc_mem_nhds hτ.1 hτ.2))
      hfDini hfleft (fun r hr => hfright (Ioi_mem_nhds hr))
  have hreal : (riemannianEDistOf (S.base.metric a) p x).toReal ≤
      (riemannianEDistOf (S.base.metric b) p x).toReal + (8 / ell) * (b - a) := by
    dsimp only [f, d] at hbound
    rw [show b + 1 - (b + 1 - a) = a by ring,
      show b + 1 - 1 = b by ring] at hbound
    linarith
  have hinc : 0 ≤ (8 / ell) * (b - a) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hab.le)
  calc
    riemannianEDistOf (S.base.metric a) p x =
        ENNReal.ofReal (riemannianEDistOf (S.base.metric a) p x).toReal :=
      (ENNReal.ofReal_toReal (hfinite a)).symm
    _ ≤ ENNReal.ofReal
        ((riemannianEDistOf (S.base.metric b) p x).toReal + (8 / ell) * (b - a)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = riemannianEDistOf (S.base.metric b) p x +
        ENNReal.ofReal ((8 / ell) * (b - a)) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hinc,
        ENNReal.ofReal_toReal (hfinite b)]

end DifferentialGeometry.PDE.RicciFlow
