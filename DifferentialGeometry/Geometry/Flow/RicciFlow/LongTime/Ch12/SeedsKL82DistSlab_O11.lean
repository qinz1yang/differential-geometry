import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.EndpointRicci

/-!
# CH12-O11, Group G1 (PP-slab): additive distance distortion under a `(t − a)⁻¹` Ricci bound

Local form of Perelman I.8.3(b) / Kleiner–Lott Lemma 27.8 on one smooth Ricci flow, integrated in
time, for the curvature profile of Kleiner–Lott Lemma 82.1 / Perelman I.11.6:
if on the time slab `(v0, v1]` the Ricci curvature is at most `C / (v − a)` on the balls of radius
`√(3 (v − a) / C)` around two fixed points `x, y`, then

  `d_{v0}(x, y) + 16 √(C/3) √(v0 − a) ≤ d_{v1}(x, y) + 16 √(C/3) √(v1 − a)`.

The rate `8 √(C/3) / √(v − a)` is integrable at `v = a`, so `v0 = a` is allowed.  This is the
slab step of Group PP (distance of a trace point to the centre trace), frozen in
`[FROZEN v2] CH12-O11 kl82_1`.  The pointwise input is the tree's
`upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds`; we only shift the time origin
(`upperRightDiniLE_comp_add_O11`) and integrate with `antitoneOn_of_upperRightDiniLE`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open scoped ENNReal Manifold ContDiff Topology

namespace GC.LongTime.Ch12

/-- A derivative gives an upper right Dini bound. -/
theorem upperRightDiniLE_of_hasDerivAt_O11 {f : ℝ → ℝ} {x d : ℝ} (h : HasDerivAt f d x) :
    UpperRightDiniLE f x d := by
  intro ε hε
  have ht : Tendsto (slope f x) (𝓝[≠] x) (𝓝 d) := hasDerivAt_iff_tendsto_slope.mp h
  have ht' : Tendsto (slope f x) (𝓝[>] x) (𝓝 d) :=
    ht.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
  exact ht'.eventually (Iic_mem_nhds (by linarith : d < d + ε))

/-- Upper right Dini bounds are invariant under a shift of the variable. -/
theorem upperRightDiniLE_comp_add_O11 {g : ℝ → ℝ} {x c d : ℝ}
    (h : UpperRightDiniLE g (x + c) d) : UpperRightDiniLE (fun y => g (y + c)) x d := by
  intro ε hε
  have hmap : Tendsto (fun y => y + c) (𝓝[>] x) (𝓝[>] (x + c)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Continuous fun y : ℝ => y + c := continuous_id.add continuous_const
      exact (hcont.tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_Ioi] at hy ⊢
      linarith
  filter_upwards [hmap.eventually (h ε hε)] with y hy
  have hs : slope (fun y => g (y + c)) x y = slope g (x + c) (y + c) := by
    simp only [slope_def_field]
    congr 1
    ring
  rw [hs]
  exact hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  {D : RealTimeInterval}

/-- **G1 (PP-slab).** Additive distance distortion on one smooth slab under the endpoint Ricci
bound `Ric ≤ C/(v − a)` on balls of radius `√(3(v − a)/C)` (KL 27.8 / Perelman I.8.3(b),
integrated against the KL 82.1 curvature profile). -/
theorem dist_le_of_ricci_inv_time_O11 [PreconnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a v0 v1 C : ℝ} (hC : 0 < C) (hav0 : a ≤ v0)
    (hv01 : v0 ≤ v1) (hreg : Ioc v0 v1 ⊆ D.regular)
    (hcomplete : ∀ v ∈ Ioc v0 v1, RiemannianMetricComplete (I := I) (S.base.metric v))
    (x y : M)
    (hcont : ContinuousOn
      (fun v => (riemannianEDistOf (I := I) (S.base.metric v) x y).toReal) (Icc v0 v1))
    (hRic : ∀ v ∈ Ioc v0 v1, ∀ z : M, ∀ w : TangentSpace I z,
      (riemannianEDistOf (I := I) (S.base.metric v) x z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C)) ∨
        riemannianEDistOf (I := I) (S.base.metric v) y z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C))) →
      ricciTensor (S.base.metric v) z w w ≤ C / (v - a) * (S.base.metric v).inner z w w) :
    (riemannianEDistOf (I := I) (S.base.metric v0) x y).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v0 - a) ≤
      (riemannianEDistOf (I := I) (S.base.metric v1) x y).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v1 - a) := by
  set c := Real.sqrt (C / 3) with hcdef
  have hC3 : 0 < C / 3 := by positivity
  have hc : 0 < c := Real.sqrt_pos.2 hC3
  have hcsq : c ^ 2 = C / 3 := Real.sq_sqrt hC3.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = v1 + 1 := ⟨_, rfl⟩
  let d : ℝ → ℝ := fun v => (riemannianEDistOf (I := I) (S.base.metric v) x y).toReal
  let F : ℝ → ℝ := fun s => d (T - s) + 16 * c * Real.sqrt (T - s - a)
  have hFc : ContinuousOn F (Icc 1 (T - v0)) := by
    have h1 : ContinuousOn (fun s : ℝ => d (T - s)) (Icc 1 (T - v0)) := by
      refine hcont.comp (f := fun s : ℝ => T - s) (continuous_const.sub continuous_id).continuousOn
        ?_
      intro s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h2 : Continuous (fun s : ℝ => 16 * c * Real.sqrt (T - s - a)) := by fun_prop
    exact h1.add h2.continuousOn
  have hFd : ∀ s ∈ Ico 1 (T - v0), UpperRightDiniLE F s 0 := by
    intro s hs
    have hv : T - s ∈ Ioc v0 v1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hva : 0 < T - s - a := by linarith [hv.1]
    set t' := T - s - a with ht'
    -- the distance part, via the endpoint Ricci Dini bound with time origin `T' = (T-s) + t'`
    have hTt : (T - s + t') - t' = T - s := by ring
    have hreg' : (T - s + t') - t' ∈ D.regular := by rw [hTt]; exact hreg hv
    have hcomp' : RiemannianMetricComplete (I := I) (S.base.metric ((T - s + t') - t')) := by
      rw [hTt]; exact hcomplete _ hv
    have hrad : Real.sqrt t' / c = Real.sqrt (3 * (T - s - a) / C) := by
      rw [hcdef, ← Real.sqrt_div' _ hC3.le]
      congr 1
      rw [ht']
      field_simp
    have hbd : 3 * c ^ 2 / t' = C / (T - s - a) := by
      rw [hcsq, ht']
      field_simp
    have hRic' : ∀ z : M, ∀ w : TangentSpace I z,
        (riemannianEDistOf (I := I) (S.base.metric ((T - s + t') - t'))
            ((fun _ : ℝ => x) t') z < ENNReal.ofReal (Real.sqrt t' / c) ∨
          riemannianEDistOf (I := I) (S.base.metric ((T - s + t') - t'))
            ((fun _ : ℝ => y) t') z < ENNReal.ofReal (Real.sqrt t' / c)) →
        ricciTensor (S.base.metric ((T - s + t') - t')) z w w ≤
          3 * c ^ 2 / t' * (S.base.metric ((T - s + t') - t')).inner z w w := by
      intro z w hz
      rw [hTt] at hz ⊢
      rw [hrad] at hz
      rw [hbd]
      exact hRic _ hv z w hz
    have hspeed : ∀ p : M, Real.sqrt ((S.base.metric ((T - s + t') - t')).inner
        ((fun _ : ℝ => p) t') (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => p) t' 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => p) t' 1)) ≤ 0 := by
      intro p
      simp [mfderiv_const]
    have hD := upperRightDiniLE_moving_distance_of_endpoint_ricci_bounds S hS hdim hva hc
      hreg' hcomp' (fun _ : ℝ => x) (fun _ : ℝ => y) contMDiffAt_const contMDiffAt_const
      (hspeed x) (hspeed y) hRic'
    have hshift : UpperRightDiniLE (fun s'' => d (T - s'')) s (8 * c / Real.sqrt t' + 0 + 0) := by
      have h := upperRightDiniLE_comp_add_O11 (c := t' - s)
        (g := fun s' => (riemannianEDistOf (I := I) (S.base.metric ((T - s + t') - s'))
          ((fun _ : ℝ => x) s') ((fun _ : ℝ => y) s')).toReal)
        (x := s) (d := 8 * c / Real.sqrt t' + 0 + 0) (by
          rw [show s + (t' - s) = t' by ring]
          exact hD)
      have hfun : (fun s'' => d (T - s'')) = fun y' =>
          (fun s' => (riemannianEDistOf (I := I) (S.base.metric ((T - s + t') - s'))
            ((fun _ : ℝ => x) s') ((fun _ : ℝ => y) s')).toReal) (y' + (t' - s)) := by
        funext y'
        simp only [d]
        rw [show T - s + t' - (y' + (t' - s)) = T - y' by ring]
      rw [hfun]
      exact h
    -- the correction term
    have hin : HasDerivAt (fun s'' : ℝ => T - s'' - a) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub T).sub_const a
    have hsq := (hin.sqrt hva.ne').const_mul (16 * c)
    have hcorr := upperRightDiniLE_of_hasDerivAt_O11 hsq
    have hsum := upperRightDiniLE_add hshift hcorr
    have hzero : 8 * c / Real.sqrt t' + 0 + 0 + 16 * c * (-1 / (2 * Real.sqrt (T - s - a))) = 0 := by
      rw [← ht']
      have hst : 0 < Real.sqrt t' := Real.sqrt_pos.2 hva
      field_simp
      ring
    rw [hzero] at hsum
    exact hsum
  have hanti := antitoneOn_of_upperRightDiniLE hFc hFd
  have hmem1 : (1 : ℝ) ∈ Icc 1 (T - v0) := ⟨le_rfl, by linarith⟩
  have hmem2 : T - v0 ∈ Icc 1 (T - v0) := ⟨by linarith, le_rfl⟩
  have key := hanti hmem1 hmem2 (by linarith)
  simp only [F, d] at key
  rw [show T - (T - v0) = v0 by ring, show T - 1 = v1 by rw [hT]; ring] at key
  exact key

end GC.LongTime.Ch12
