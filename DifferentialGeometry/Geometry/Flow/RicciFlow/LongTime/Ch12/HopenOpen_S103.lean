import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RicciJoint_S103
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakStrong_S85

set_option autoImplicit false

/-!
# CH12-S103 / G2: `hopen` of the first-failure bootstrap (openness of `Weak (η)` from `Strong (η/2)`)

* `uniform_defect_core_S103` : abstract compactness core.  On a compact manifold, with `Q r`, `D r`
  quadratic in the tangent vector and jointly continuous on `[s, s'] × TangentBundle`, if
  `|D s| ≤ (η/2) Q s` on the vectors over `T`, then `|D r| ≤ η Q r` over `T` for `r ∈ [s, s + ε]`
  (unit-sphere bundle of `g_s` over `closure T`, `metricUnitOn_compact`).
* `defect_open_stage_S103` : the same for `D r = 2 r Ric_r(V,V) + g_r(V,V)`, `Q r = g_r(V,V)` of a stage
  (joint continuity = `ricci_jointly_continuous_S103`).
* `hopen_S103` : the `hopen` binder of `weak_bootstrap_S93` (needs `0 < η`; it is false at `η = 0`).
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

/-- Abstract compactness core of `hopen`. -/
theorem uniform_defect_core_S103 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [T2Space M] (gs : SmoothRiemannianMetric I M) (Q D : ℝ → (x : M) → TangentSpace I x → ℝ)
    {s s' : ℝ} (hss' : s < s')
    (hQ : Continuous (fun q : {r : ℝ // r ∈ Icc s s'} × TangentBundle I M =>
      Q q.1.1 q.2.proj q.2.2))
    (hD : Continuous (fun q : {r : ℝ // r ∈ Icc s s'} × TangentBundle I M =>
      D q.1.1 q.2.proj q.2.2))
    (hQ2 : ∀ r x (V : TangentSpace I x) (c : ℝ), Q r x (c • V) = c * c * Q r x V)
    (hD2 : ∀ r x (V : TangentSpace I x) (c : ℝ), D r x (c • V) = c * c * D r x V)
    (hQs : ∀ x (V : TangentSpace I x), Q s x V = gs.inner x V V) {η : ℝ} (hη : 0 < η) (T : Set M)
    (h0 : ∀ z ∈ T, ∀ V : TangentSpace I z, |D s z V| ≤ (η / 2) * Q s z V) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ s' - s ∧
      ∀ r ∈ Icc s (s + ε), ∀ z ∈ T, ∀ V : TangentSpace I z, |D r z V| ≤ η * Q r z V := by
  classical
  let U := MetricUnitTangent (I := I) (M := M) gs
  have : CompactSpace U := ⟨metricUnit_compact (I := I) (M := M) gs⟩
  let Iss := {r : ℝ // r ∈ Icc s s'}
  let ts : Iss := ⟨s, le_rfl, hss'.le⟩
  let f : Iss → U → ℝ := fun r p =>
    |D r.1 p.1.proj p.1.2| - η * Q r.1 p.1.proj p.1.2
  have hpull : Continuous (fun p : Iss × U => ((p.1, p.2.1) : Iss × TangentBundle I M)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hf : Continuous (fun p : Iss × U => f p.1 p.2) :=
    ((hD.comp hpull).abs).sub (continuous_const.mul (hQ.comp hpull))
  let B : Set U := {p | MetricUnitTangent.base (I := I) (M := M) p ∈ T}
  let X : Set U := closure B
  have hX : IsCompact X := isClosed_closure.isCompact
  have hXs : ∀ p ∈ X, f ts p ≤ -(η / 2) := by
    have hcl : IsClosed {p : U | f ts p ≤ -(η / 2)} :=
      isClosed_le (hf.comp (continuous_const.prodMk continuous_id)) continuous_const
    refine closure_minimal (fun p hp => ?_) hcl
    have h1 : |D s p.1.proj p.1.2| ≤ (η / 2) * Q s p.1.proj p.1.2 := h0 _ hp p.1.2
    have hu : Q s p.1.proj p.1.2 = 1 := by
      rw [hQs]
      exact p.2
    change |D s p.1.proj p.1.2| - η * Q s p.1.proj p.1.2 ≤ -(η / 2)
    rw [hu] at h1 ⊢
    linarith
  have hsmall : ∀ᶠ r in 𝓝 ts, ∀ p ∈ X, f r p < 0 := by
    apply hX.eventually_forall_of_forall_eventually
    intro p hp
    exact hf.continuousAt.eventually_lt_const (by linarith [hXs p hp])
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  have hmin : 0 < min (s' - s) ρ := lt_min (sub_pos.mpr hss') hρ
  have hε1 : min (s' - s) ρ / 2 ≤ s' - s := by linarith [min_le_left (s' - s) ρ]
  have hε2 : min (s' - s) ρ / 2 < ρ := by linarith [min_le_right (s' - s) ρ]
  refine ⟨min (s' - s) ρ / 2, by positivity, hε1, ?_⟩
  intro r hr z hz V
  have hrI : r ∈ Icc s s' := ⟨hr.1, by linarith [hr.2]⟩
  have hrs : (⟨r, hrI⟩ : Iss) ∈ Metric.ball ts ρ := by
    rw [Metric.mem_ball]
    change dist r s < ρ
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith [hr.2]
  by_cases hV : V = 0
  · subst hV
    have hD0 : D r z 0 = 0 := by
      have := hD2 r z 0 0
      simpa using this
    have hQ0 : Q r z 0 = 0 := by
      have := hQ2 r z 0 0
      simpa using this
    simp [hD0, hQ0]
  · have hpos : 0 < gs.inner z V V := gs.pos z V hV
    have hsq : 0 < Real.sqrt (gs.inner z V V) := Real.sqrt_pos.mpr hpos
    set c : ℝ := (Real.sqrt (gs.inner z V V))⁻¹ with hc
    have hss : Real.sqrt (gs.inner z V V) * Real.sqrt (gs.inner z V V) = gs.inner z V V := by
      simpa only [sq] using Real.sq_sqrt hpos.le
    have hunit : gs.inner z (c • V) (c • V) = 1 := by
      rw [metric_smul2, hc]
      field_simp [hsq.ne']
      linarith [hss]
    let p : U := ⟨(⟨z, c • V⟩ : TangentBundle I M), hunit⟩
    have hpX : p ∈ X := subset_closure hz
    have h1 : f ⟨r, hrI⟩ p < 0 := hball hrs p hpX
    have hcc : 0 < c * c := by positivity
    change |D r z (c • V)| - η * Q r z (c • V) < 0 at h1
    rw [hD2, hQ2, abs_mul, abs_of_nonneg hcc.le] at h1
    have h3 : |D r z V| - η * Q r z V < 0 := by
      by_contra hh
      have := mul_nonneg hcc.le (not_lt.mp hh)
      nlinarith
    linarith

/-- **G2 stage version**: the defect `|2 r Ric(V,V) + g_r(V,V)| ≤ η g_r(V,V)` persists on `[s, s + ε]`
from `(η/2)` at `s`, uniformly over every `T ⊆ stage j` (all vectors). -/
theorem defect_open_stage_S103 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    {s s' : ℝ} (hss' : s < s') (hdom : Icc s s' ⊆ K.stageDomain j)
    (hlt : ∀ r ∈ Icc s s', r < K.horizon) {η : ℝ} (hη : 0 < η) (T : Set (K.stage j).Carrier)
    (h0 : ∀ z ∈ T, ∀ V : TangentSpace ThreeModel z, DefectAt_S85 K j z V (η / 2) s) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ s' - s ∧
      ∀ r ∈ Icc s (s + ε), ∀ z ∈ T, ∀ V : TangentSpace ThreeModel z, DefectAt_S85 K j z V η r := by
  obtain ⟨hR, hG⟩ := ricci_jointly_continuous_S103 K j hdom hlt
  refine uniform_defect_core_S103 (K.stageMetric j s)
    (fun r x V => (K.stageMetric j r).inner x V V)
    (fun r x V => 2 * r * ricciTensor (K.stageMetric j r) x V V + (K.stageMetric j r).inner x V V)
    hss' hG ?_ (fun r x V c => metric_smul2 _ c V) ?_ (fun x V => rfl) hη T h0
  · exact ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).mul hR).add hG
  · intro r x V c
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

theorem defectAll_of_stage_S103 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η r : ℝ} {j : Fin (K.eventCount + 1)}
    (hact : actS_S70 K r = j)
    (h : ∀ (h : j0 ≤ j), ∀ x ∈ B, ∀ z : (K.stage j).Carrier, TrackedAt_S70 K h J x z →
      ∀ V : TangentSpace ThreeModel z, DefectAt_S85 K j z V η r) :
    DefectAllAt_S85 K j0 J B η r := by
  subst hact
  exact h

/-- **G2** : the `hopen` binder of `weak_bootstrap_S93` (shape verbatim, plus `0 < η` : at `η = 0` it is
false in general). -/
theorem hopen_S103 (K : ObservedHistory.{u}) (j0 : Fin (K.eventCount + 1)) {X : Type v}
    (J : X → (K.stage j0).Carrier) (B : Set X) {η t : ℝ} (hη : 0 < η) (ht0 : 0 < t)
    (h2t : 2 * t ≤ K.horizon) :
    ∀ s ∈ Ico t (2 * t), WeakAt_S85 K j0 J B (η / 2) s →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc s (s + ε), WeakAt_S85 K j0 J B η r := by
  intro s hs hW
  have hs0 : s ∈ Icc (0 : ℝ) K.horizon := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsh : s < K.horizon := by linarith [hs.2]
  obtain ⟨ε₁, hε₁, hεh, hact⟩ := exists_actS_eq_right_S70 K hs0 hsh
  obtain ⟨j, hj⟩ : ∃ j, actS_S70 K s = j := ⟨_, rfl⟩
  obtain ⟨hle, hsurv⟩ := hW.1
  have hle' : j0 ≤ j := hj ▸ hle
  have hrange : ∀ r ∈ Icc s (s + ε₁), r ∈ Icc (0 : ℝ) K.horizon := fun r hr =>
    ⟨hs0.1.trans hr.1, hr.2.trans hεh⟩
  have hdom : Icc s (s + ε₁ / 2) ⊆ K.stageDomain j := by
    intro r hr
    have hr' : r ∈ Icc s (s + ε₁) := ⟨hr.1, by linarith [hr.2]⟩
    have h1 := actS_mem_stageDomain_S85 K (hrange r hr')
    rwa [hact r hr', hj] at h1
  have hlt : ∀ r ∈ Icc s (s + ε₁ / 2), r < K.horizon := fun r hr => by
    linarith [hr.2]
  let T : Set (K.stage j).Carrier := {z | ∃ x ∈ B, TrackedAt_S70 K hle' J x z}
  have hdefs := defectAllAt_transport_S85 K j0 J B hj hW.2
  obtain ⟨ε, hε, hεle, hmain⟩ := defect_open_stage_S103 K j (s := s) (s' := s + ε₁ / 2)
    (by linarith) hdom hlt hη T (fun z ⟨x, hx, hz⟩ V => hdefs hle' x hx z hz V)
  refine ⟨ε, hε, fun r hr => ?_⟩
  have hr' : r ∈ Icc s (s + ε₁) := ⟨hr.1, by linarith [hr.2, hεle]⟩
  have hrj : actS_S70 K r = j := (hact r hr').trans hj
  refine ⟨survAt_of_actS_eq_S85 K j0 J B (hact r hr').symm hW.1, ?_⟩
  exact defectAll_of_stage_S103 K j0 J B hrj fun _ x hx z hz V => hmain r hr z ⟨x, hx, hz⟩ V

end GC.LongTime.Ch12
