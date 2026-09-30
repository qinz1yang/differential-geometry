import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitBoundedCurvature
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMonotone
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticComparison
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessComparisonTransport

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem abs_sub_le_mul_of_abs_deriv_le_of_finite {u : ℝ → ℝ} {L : ℝ} {S : Set ℝ}
    (hS : S.Finite) : ∀ {a b : ℝ}, a ≤ b → (∀ s ∈ Icc a b, DifferentiableAt ℝ u s) →
      (∀ s ∈ Ioo a b, s ∉ S → |deriv u s| ≤ L) → |u b - u a| ≤ L * (b - a) := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro a b hab hdiff hbound
    rcases hab.eq_or_lt with rfl | hlt
    · simp
    obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope u hlt
      (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hdiff s (Ioo_subset_Icc_self hs)).differentiableWithinAt)
    have hb := hbound c hc (by simp)
    rw [hslope, abs_div, abs_of_pos (sub_pos.mpr hlt), div_le_iff₀ (sub_pos.mpr hlt)] at hb
    exact hb
  | @insert p S' hp _ ih =>
    intro a b hab hdiff hbound
    by_cases hpab : p ∈ Ioo a b
    · have h1 := ih hpab.1.le (fun s hs => hdiff s ⟨hs.1, hs.2.trans hpab.2.le⟩)
        (fun s hs hsS => hbound s ⟨hs.1, hs.2.trans hpab.2⟩ (by
          rintro (rfl | h)
          · exact lt_irrefl _ hs.2
          · exact hsS h))
      have h2 := ih hpab.2.le (fun s hs => hdiff s ⟨hpab.1.le.trans hs.1, hs.2⟩)
        (fun s hs hsS => hbound s ⟨hpab.1.trans hs.1, hs.2⟩ (by
          rintro (rfl | h)
          · exact lt_irrefl _ hs.1
          · exact hsS h))
      calc |u b - u a| = |(u b - u p) + (u p - u a)| := by ring_nf
        _ ≤ |u b - u p| + |u p - u a| := abs_add_le _ _
        _ ≤ L * (b - p) + L * (p - a) := add_le_add h2 h1
        _ = L * (b - a) := by ring
    · exact ih hab hdiff (fun s hs hsS => hbound s hs (by
        rintro (rfl | h)
        · exact hpab hs
        · exact hsS h))

theorem le_two_mul_of_abs_deriv_le_mul_sq_of_right_le_of_finite {u : ℝ → ℝ} {B K a b : ℝ}
    {S : Set ℝ} (hS : S.Finite) (hB : 0 < B) (hK : 0 ≤ K)
    (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, s ∉ S → B < u s → |deriv u s| ≤ K * u s ^ 2) (hb : u b ≤ B)
    (hlen : K * (b - a) ≤ 1 / (2 * B)) : ∀ s ∈ Icc a b, u s ≤ 2 * B := by
  intro s₁ hs₁
  by_contra hlt
  push Not at hlt
  have hcont : ContinuousOn u (Icc a b) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  let T := {s ∈ Icc s₁ b | u s ≤ B}
  have hsub : Icc s₁ b ⊆ Icc a b := Icc_subset_Icc_left hs₁.1
  have hTclosed : IsClosed T :=
    (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hTne : T.Nonempty := ⟨b, ⟨hs₁.2, le_rfl⟩, hb⟩
  have hTbdd : BddBelow T := ⟨s₁, fun s hs => hs.1.1⟩
  set c := sInf T with hc
  have hcT : c ∈ T := hTclosed.csInf_mem hTne hTbdd
  have hs₁c : s₁ < c := by
    rcases hcT.1.1.eq_or_lt with h | h
    · rw [← h] at hcT
      linarith [hcT.2]
    · exact h
  have hgt : ∀ s ∈ Ico s₁ c, B < u s := by
    intro s hs
    by_contra hle
    push Not at hle
    exact absurd (csInf_le hTbdd ⟨⟨hs.1, hs.2.le.trans hcT.1.2⟩, hle⟩) (not_le.mpr hs.2)
  have hsc : Icc s₁ c ⊆ Icc a b := fun s hs => hsub ⟨hs.1, hs.2.trans hcT.1.2⟩
  have hge : ∀ s ∈ Icc s₁ c, B ≤ u s := by
    have hclosed : IsClosed {s ∈ Icc s₁ c | B ≤ u s} :=
      (hcont.mono hsc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hIco : Ico s₁ c ⊆ {s ∈ Icc s₁ c | B ≤ u s} :=
      fun s hs => ⟨Ico_subset_Icc_self hs, (hgt s hs).le⟩
    have hcl := hclosed.closure_subset_iff.mpr hIco
    rw [closure_Ico hs₁c.ne] at hcl
    exact fun s hs => (hcl hs).2
  have hpos : ∀ s ∈ Icc s₁ c, 0 < u s := fun s hs => hB.trans_le (hge s hs)
  have hmvt := abs_sub_le_mul_of_abs_deriv_le_of_finite (u := fun s => (u s)⁻¹) (L := K) hS
    hs₁c.le (fun s hs => ((hdiff s (hsc hs)).inv (hpos s hs).ne'))
    (fun s hs hsS => by
      have hs' := Ioo_subset_Icc_self hs
      change |deriv (u⁻¹) s| ≤ K
      rw [((hdiff s (hsc hs')).hasDerivAt.inv (hpos s hs').ne').deriv, abs_div, abs_neg,
        abs_of_pos (pow_pos (hpos s hs') 2), div_le_iff₀ (pow_pos (hpos s hs') 2)]
      exact hder s (hsc hs') hsS (hgt s (Ioo_subset_Ico_self hs)))
  have hcb : c - s₁ ≤ b - a := by linarith [hcT.1.2, hs₁.1]
  have hKlen : K * (c - s₁) ≤ 1 / (2 * B) := (mul_le_mul_of_nonneg_left hcb hK).trans hlen
  have hinvc : 1 / B ≤ (u c)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (hpos c ⟨hs₁c.le, le_rfl⟩) hcT.2
  have hdiffle : (u c)⁻¹ - (u s₁)⁻¹ ≤ K * (c - s₁) := (le_abs_self _).trans hmvt
  have hfinal : 1 / (2 * B) ≤ (u s₁)⁻¹ := by
    have : 1 / B - 1 / (2 * B) = 1 / (2 * B) := by field_simp; ring
    linarith
  have hu1 : 0 < u s₁ := by linarith
  rw [one_div, inv_le_inv₀ (by positivity) hu1] at hfinal
  linarith

theorem half_lt_of_abs_deriv_le_mul_sq_of_le_right_of_finite {u : ℝ → ℝ} {A K a b : ℝ}
    {S : Set ℝ} (hS : S.Finite) (hA : 0 < A) (hK : 0 ≤ K)
    (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, s ∉ S → A / 2 < u s → |deriv u s| ≤ K * u s ^ 2) (hb : A ≤ u b)
    (hlen : K * (b - a) ≤ 1 / (2 * A)) : ∀ s ∈ Icc a b, A / 2 < u s := by
  intro s₁ hs₁
  by_contra hle
  push Not at hle
  have hcont : ContinuousOn u (Icc a b) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  let T := {s ∈ Icc s₁ b | u s ≤ A / 2}
  have hsub : Icc s₁ b ⊆ Icc a b := Icc_subset_Icc_left hs₁.1
  have hTclosed : IsClosed T :=
    (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hTne : T.Nonempty := ⟨s₁, ⟨le_rfl, hs₁.2⟩, hle⟩
  have hTbdd : BddAbove T := ⟨b, fun s hs => hs.1.2⟩
  set c := sSup T with hc
  have hcT : c ∈ T := hTclosed.csSup_mem hTne hTbdd
  have hcb : c < b := by
    rcases hcT.1.2.eq_or_lt with h | h
    · rw [h] at hcT
      linarith [hcT.2]
    · exact h
  have hgt : ∀ s ∈ Ioc c b, A / 2 < u s := by
    intro s hs
    by_contra hle'
    push Not at hle'
    exact absurd (le_csSup hTbdd ⟨⟨hcT.1.1.trans hs.1.le, hs.2⟩, hle'⟩) (not_le.mpr hs.1)
  have hsc : Icc c b ⊆ Icc a b := fun s hs => hsub ⟨hcT.1.1.trans hs.1, hs.2⟩
  have hge : ∀ s ∈ Icc c b, A / 2 ≤ u s := by
    have hclosed : IsClosed {s ∈ Icc c b | A / 2 ≤ u s} :=
      (hcont.mono hsc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hIoc : Ioc c b ⊆ {s ∈ Icc c b | A / 2 ≤ u s} :=
      fun s hs => ⟨Ioc_subset_Icc_self hs, (hgt s hs).le⟩
    have hcl := hclosed.closure_subset_iff.mpr hIoc
    rw [closure_Ioc hcb.ne] at hcl
    exact fun s hs => (hcl hs).2
  have hpos : ∀ s ∈ Icc c b, 0 < u s := fun s hs => (half_pos hA).trans_le (hge s hs)
  have hmvt := abs_sub_le_mul_of_abs_deriv_le_of_finite (u := fun s => (u s)⁻¹) (L := K) hS
    hcb.le (fun s hs => ((hdiff s (hsc hs)).inv (hpos s hs).ne'))
    (fun s hs hsS => by
      have hs' := Ioo_subset_Icc_self hs
      change |deriv (u⁻¹) s| ≤ K
      rw [((hdiff s (hsc hs')).hasDerivAt.inv (hpos s hs').ne').deriv, abs_div, abs_neg,
        abs_of_pos (pow_pos (hpos s hs') 2), div_le_iff₀ (pow_pos (hpos s hs') 2)]
      exact hder s (hsc hs') hsS (hgt s (Ioo_subset_Ioc_self hs)))
  have hlenc : b - c ≤ b - a := by linarith [hcT.1.1, hs₁.1]
  have hKlen : K * (b - c) ≤ 1 / (2 * A) := (mul_le_mul_of_nonneg_left hlenc hK).trans hlen
  have hinvb : (u b)⁻¹ ≤ 1 / A := by
    rw [one_div]
    exact inv_anti₀ hA hb
  have hinvc : 2 / A ≤ (u c)⁻¹ := by
    have hu : 0 < u c := hpos c ⟨le_rfl, hcb.le⟩
    have h1 := inv_anti₀ hu hcT.2
    have h2 : (A / 2)⁻¹ = 2 / A := by field_simp
    linarith
  have hdiffle : (u c)⁻¹ - (u b)⁻¹ ≤ K * (b - c) := by
    rw [abs_sub_comm] at hmvt
    exact (le_abs_self _).trans hmvt
  have : 1 / A + 1 / (2 * A) < 2 / A := by
    have : 1 / A + 1 / (2 * A) = 3 / (2 * A) := by field_simp; ring
    rw [this, div_lt_div_iff₀ (by positivity) hA]
    nlinarith
  linarith

theorem reflect_hypotheses_of_finite {u : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite) {a b : ℝ}
    (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s) :
    (Neg.neg ⁻¹' S).Finite ∧
      ∀ s ∈ Icc (-b) (-a), DifferentiableAt ℝ (fun v => u (-v)) s := by
  refine ⟨hS.preimage (neg_injective.injOn), fun s hs => ?_⟩
  exact (hdiff (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).comp s
    (differentiableAt_neg_iff.mpr differentiableAt_id)

theorem le_two_mul_of_abs_deriv_le_mul_sq_of_left_le_of_finite {u : ℝ → ℝ} {B K a b : ℝ}
    {S : Set ℝ} (hS : S.Finite) (hB : 0 < B) (hK : 0 ≤ K)
    (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, s ∉ S → B < u s → |deriv u s| ≤ K * u s ^ 2) (ha : u a ≤ B)
    (hlen : K * (b - a) ≤ 1 / (2 * B)) : ∀ s ∈ Icc a b, u s ≤ 2 * B := by
  obtain ⟨hS', hdiff'⟩ := reflect_hypotheses_of_finite hS hdiff
  have hmem : ∀ s ∈ Icc (-b) (-a), -s ∈ Icc a b :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hv := le_two_mul_of_abs_deriv_le_mul_sq_of_right_le_of_finite (u := fun s => u (-s))
    (a := -b) (b := -a) hS' hB hK hdiff'
    (fun s hs hsS hlt => by
      rw [deriv_comp_neg, abs_neg]
      exact hder (-s) (hmem s hs) hsS hlt)
    (by simpa only [neg_neg] using ha) (by linarith)
  intro s hs
  simpa only [neg_neg] using hv (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

theorem half_lt_of_abs_deriv_le_mul_sq_of_le_left_of_finite {u : ℝ → ℝ} {A K a b : ℝ}
    {S : Set ℝ} (hS : S.Finite) (hA : 0 < A) (hK : 0 ≤ K)
    (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, s ∉ S → A / 2 < u s → |deriv u s| ≤ K * u s ^ 2) (ha : A ≤ u a)
    (hlen : K * (b - a) ≤ 1 / (2 * A)) : ∀ s ∈ Icc a b, A / 2 < u s := by
  obtain ⟨hS', hdiff'⟩ := reflect_hypotheses_of_finite hS hdiff
  have hmem : ∀ s ∈ Icc (-b) (-a), -s ∈ Icc a b :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hv := half_lt_of_abs_deriv_le_mul_sq_of_le_right_of_finite (u := fun s => u (-s))
    (a := -b) (b := -a) hS' hA hK hdiff'
    (fun s hs hsS hlt => by
      rw [deriv_comp_neg, abs_neg]
      exact hder (-s) (hmem s hs) hsS hlt)
    (by simpa only [neg_neg] using ha) (by linarith)
  intro s hs
  simpa only [neg_neg] using hv (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

theorem abs_sub_le_of_abs_deriv_le_mul_sq_of_finite {u : ℝ → ℝ} {A B K a b t₀ : ℝ}
    {S : Set ℝ} (hS : S.Finite) (hA : 0 < A) (hAB : A ≤ B) (hK : 0 ≤ K)
    (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, s ∉ S → A / 2 < u s → |deriv u s| ≤ K * u s ^ 2)
    (ht₀ : t₀ ∈ Icc a b) (hlow : A ≤ u t₀) (hup : u t₀ ≤ B) (hlen : K * (b - a) ≤ 1 / (2 * B)) :
    ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, |u s - u s'| ≤ K * (2 * B) ^ 2 * |s - s'| := by
  have hB : 0 < B := hA.trans_le hAB
  have hlenA : K * (b - a) ≤ 1 / (2 * A) :=
    hlen.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hsub1 : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hsub2 : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  have hl1 : K * (t₀ - a) ≤ K * (b - a) := mul_le_mul_of_nonneg_left (by linarith [ht₀.2]) hK
  have hl2 : K * (b - t₀) ≤ K * (b - a) := mul_le_mul_of_nonneg_left (by linarith [ht₀.1]) hK
  have hlower : ∀ s ∈ Icc a b, A / 2 < u s := by
    intro s hs
    rcases le_total s t₀ with hst | hst
    · exact half_lt_of_abs_deriv_le_mul_sq_of_le_right_of_finite hS hA hK
        (fun v hv => hdiff v (hsub1 hv)) (fun v hv => hder v (hsub1 hv)) hlow
        (hl1.trans hlenA) s ⟨hs.1, hst⟩
    · exact half_lt_of_abs_deriv_le_mul_sq_of_le_left_of_finite hS hA hK
        (fun v hv => hdiff v (hsub2 hv)) (fun v hv => hder v (hsub2 hv)) hlow
        (hl2.trans hlenA) s ⟨hst, hs.2⟩
  have hderB : ∀ s ∈ Icc a b, s ∉ S → B < u s → |deriv u s| ≤ K * u s ^ 2 :=
    fun s hs hsS hBs => hder s hs hsS (lt_of_lt_of_le (by linarith) hBs.le)
  have hupper : ∀ s ∈ Icc a b, u s ≤ 2 * B := by
    intro s hs
    rcases le_total s t₀ with hst | hst
    · exact le_two_mul_of_abs_deriv_le_mul_sq_of_right_le_of_finite hS hB hK
        (fun v hv => hdiff v (hsub1 hv)) (fun v hv => hderB v (hsub1 hv)) hup
        (hl1.trans hlen) s ⟨hs.1, hst⟩
    · exact le_two_mul_of_abs_deriv_le_mul_sq_of_left_le_of_finite hS hB hK
        (fun v hv => hdiff v (hsub2 hv)) (fun v hv => hderB v (hsub2 hv)) hup
        (hl2.trans hlen) s ⟨hst, hs.2⟩
  have hbound : ∀ s ∈ Icc a b, s ∉ S → |deriv u s| ≤ K * (2 * B) ^ 2 := by
    intro s hs hsS
    refine (hder s hs hsS (hlower s hs)).trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h0 : 0 ≤ u s := (half_pos hA).le.trans (hlower s hs).le
    exact pow_le_pow_left₀ h0 (hupper s hs) 2
  have hmain : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' →
      |u s' - u s| ≤ K * (2 * B) ^ 2 * (s' - s) := by
    intro s hs s' hs' hss'
    exact abs_sub_le_mul_of_abs_deriv_le_of_finite hS hss'
      (fun v hv => hdiff v ⟨hs.1.trans hv.1, hv.2.trans hs'.2⟩)
      (fun v hv hvS => hbound v ⟨hs.1.trans hv.1.le, hv.2.le.trans hs'.2⟩ hvS)
  intro s hs s' hs'
  rcases le_total s s' with h | h
  · rw [abs_sub_comm, abs_of_nonpos (by linarith : s - s' ≤ 0), neg_sub]
    exact hmain s hs s' hs' h
  · rw [abs_of_nonneg (by linarith : 0 ≤ s - s')]
    exact hmain s' hs' s hs h

section PointedLimit

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem abs_derivWithin_scalar_le_of_local_flow_limit
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    {V : ℕ → Opens P.M} (hVmono : Monotone V) (hVcover : ∀ x : P.M, ∃ k, x ∈ V k)
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    {G : ℝ → SmoothRiemannianMetric I3 P.M}
    (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
      ancientTimeInterval))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := I3) (M := W k n)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _)))))
    {E : ℕ → Set ℝ} (hE : ∀ n, (E n).Finite) {q Ctime : ℝ}
    (hderiv : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E n →
      ∀ z : W k n, q < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ctime * metricScalarAt (h k n s) z ^ 2) :
    ∀ t < 0, ∀ x : P.M, 4 * max q 1 < metricScalarAt (G t) x →
      |derivWithin (fun v => metricScalarAt (G v) x) (Iic t) t| ≤
        16 * max Ctime 0 * metricScalarAt (G t) x ^ 2 := by
  intro t ht x hxq
  set a := metricScalarAt (G t) x with ha_def
  set K := max Ctime 0 with hK_def
  have hK : 0 ≤ K := le_max_right _ _
  have hq1 : 1 ≤ max q 1 := le_max_right _ _
  have hqq : q ≤ max q 1 := le_max_left _ _
  have ha : 0 < a := by linarith
  obtain ⟨k₁, hk₁⟩ := hVcover x
  obtain ⟨l, hl⟩ := exists_nat_gt (-t)
  set k := max k₁ l with hk_def
  have hxk : x ∈ V k := hVmono (le_max_left _ _) hk₁
  have hlk : (l : ℝ) ≤ k := by exact_mod_cast le_max_right k₁ l
  have htk : -((k + 1 : ℕ) : ℝ) < t := by push_cast; linarith
  set δ := min (min (1 / (8 * (K + 1) * a)) ((t + ((k + 1 : ℕ) : ℝ)) / 2)) (-t / 2)
    with hδ_def
  have hδ1 : δ ≤ 1 / (8 * (K + 1) * a) := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ (t + ((k + 1 : ℕ) : ℝ)) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ -t / 2 := min_le_right _ _
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by linarith)) (by linarith)
  let J := Icc (t - δ) (t + δ)
  have hJwin : J ⊆ Icc (-((k + 1 : ℕ) : ℝ)) 0 :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJreg : J ⊆ Ioo (-((k + 2 : ℕ) : ℝ)) 0 := fun s hs =>
    ⟨by push_cast at hδ2 ⊢; linarith [hs.1], by linarith [hs.2]⟩
  let _ : SigmaCompactSpace (V k) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 (V k).isOpen)
  let xk : V k := ⟨x, hxk⟩
  let seq : ℕ → ℝ → SmoothRiemannianMetric I3 (V k) := fun i s =>
    if hi : N k ≤ ψ i then localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G s).restrictOpen (V k)
  let F : ℕ → ℝ → ℝ := fun i s => metricScalarAt (seq i s) xk
  have hlim : ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      Tendsto (fun i => F i s) atTop (𝓝 (metricScalarAt (G s) x)) := by
    intro s hs
    have hcp : MetricCPConvergenceOn {xk} 2 (fun i => seq i s) ((G s).restrictOpen (V k))
        (P.metric.restrictOpen (V k)) := by
      intro η hη
      obtain ⟨j₀, hj₀⟩ := hconv k {xk} isCompact_singleton 2 η hη
      refine ⟨j₀, fun i hi => ?_⟩
      obtain ⟨hi', hb⟩ := hj₀ i hi
      change metricDerivNormSupOn {xk} 2 (if hi : N k ≤ ψ i then _ else _) _ _ < η
      rw [dite_eq_left hi']
      exact hb s hs
    have hu := (hcp.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at
      (mem_singleton xk)
    rwa [metricScalarAt_restrictOpen] at hu
  have hFeq : ∀ i (hi : N k ≤ ψ i) (s : ℝ),
      F i s = metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi xk) := by
    intro i hi s
    change metricScalarAt (if hi : N k ≤ ψ i then _ else _) xk = _
    rw [dite_eq_left hi, metricScalarAt_localPull]
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  have hta : Tendsto (fun i => F i t) atTop (𝓝 a) := hlim t ⟨htk.le, ht.le⟩
  have hev : ∀ᶠ i in atTop, ∃ hi : N k ≤ ψ i,
      IsSolutionOn ({ base.metric := h k (f (ψ i)) } : SolutionOn (I := I3)
        (M := W k (f (ψ i))) (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
          (neg_nonpos.mpr (Nat.cast_nonneg _)))) ∧
      (∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E (f (ψ i)) → ∀ z : W k (f (ψ i)),
        q < metricScalarAt (h k (f (ψ i)) s) z →
          |derivWithin (fun v => metricScalarAt (h k (f (ψ i)) v) z) (Iic s) s| ≤
            Ctime * metricScalarAt (h k (f (ψ i)) s) z ^ 2) ∧
      a / 2 ≤ F i t ∧ F i t ≤ 2 * a := by
    filter_upwards [hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k)),
      hfψ.eventually (hsol k), hfψ.eventually (hderiv k),
      hta.eventually (Icc_mem_nhds (by linarith : a / 2 < a) (by linarith : a < 2 * a))]
      with i hi hs hd hF
    exact ⟨hi, hs, hd, hF.1, hF.2⟩
  have hlip_i : ∀ᶠ i in atTop, ∀ s ∈ J, ∀ s' ∈ J,
      |F i s - F i s'| ≤ K * (2 * (2 * a)) ^ 2 * |s - s'| := by
    filter_upwards [hev] with i ⟨hi, hs, hd, hlow, hup⟩
    have hFe := hFeq i hi
    set z := φ k (ψ i) hi xk
    have hfun : (fun v => F i v) = fun v => metricScalarAt (h k (f (ψ i)) v) z :=
      funext fun v => hFe v
    have hdiff : ∀ s ∈ J, DifferentiableAt ℝ (fun v => F i v) s := by
      intro s hsJ
      have h1 := hs.scalarTime (K := Ioo (-((k + 2 : ℕ) : ℝ)) 0) (t := s) (hJreg hsJ)
        Ioo_subset_Icc_self z
      rw [hfun]
      exact h1.differentiableAt (Ioo_mem_nhds (hJreg hsJ).1 (hJreg hsJ).2)
    have hder : ∀ s ∈ J, s ∉ E (f (ψ i)) → a / 2 / 2 < F i s →
        |deriv (fun v => F i v) s| ≤ K * F i s ^ 2 := by
      intro s hsJ hsE hs2
      have hderiv' : deriv (fun v => F i v) s =
          derivWithin (fun v => metricScalarAt (h k (f (ψ i)) v) z) (Iic s) s := by
        have hd' := hdiff s hsJ
        rw [hfun] at hd' ⊢
        exact (hd'.derivWithin (uniqueDiffWithinAt_Iic s)).symm
      rw [hderiv', hFe s]
      rw [hFe s] at hs2
      exact (hd s (hJreg hsJ) hsE z (by linarith)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have hlen : K * (t + δ - (t - δ)) ≤ 1 / (2 * (2 * a)) := by
      have h1 : K * (t + δ - (t - δ)) = 2 * K * δ := by ring
      rw [h1]
      have h2 : 2 * K * δ ≤ 2 * (K + 1) * (1 / (8 * (K + 1) * a)) :=
        mul_le_mul (by linarith) hδ1 hδ.le (by positivity)
      have h3 : 2 * (K + 1) * (1 / (8 * (K + 1) * a)) = 1 / (4 * a) := by
        field_simp
        ring
      have h4 : 1 / (2 * (2 * a)) = 1 / (4 * a) := by ring
      linarith
    exact abs_sub_le_of_abs_deriv_le_mul_sq_of_finite (u := fun v => F i v) (A := a / 2)
      (B := 2 * a) (hE (f (ψ i))) (by positivity) (by linarith) hK hdiff hder
      ⟨by linarith, by linarith⟩ hlow hup hlen
  have hlip : ∀ s ∈ J, ∀ s' ∈ J, |metricScalarAt (G s) x - metricScalarAt (G s') x| ≤
      K * (2 * (2 * a)) ^ 2 * |s - s'| := by
    intro s hs s' hs'
    have ht1 := ((hlim s (hJwin hs)).sub (hlim s' (hJwin hs'))).abs
    exact le_of_tendsto ht1 (hlip_i.mono fun i hi => hi s hs s' hs')
  have hLip : LipschitzOnWith (Real.toNNReal (K * (2 * (2 * a)) ^ 2))
      (fun v => metricScalarAt (G v) x) J := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact hlip s hs s' hs'
  have hnorm := norm_deriv_le_of_lipschitzOn
    (Icc_mem_nhds (show t - δ < t by linarith) (show t < t + δ by linarith)) hLip
  have hdiffG : DifferentiableAt ℝ (fun v => metricScalarAt (G v) x) t := by
    have h := hG.scalarTime (K := Iio 0) (t := t) ht (fun s hs => by
      rw [ancientTimeInterval_carrier]
      exact mem_Iic.mpr hs.le) x
    exact h.differentiableAt (Iio_mem_nhds ht)
  rw [hdiffG.derivWithin (uniqueDiffWithinAt_Iic t)]
  rw [Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)] at hnorm
  exact hnorm.trans (le_of_eq (by ring))

end PointedLimit

universe v

theorem exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧ ∀ {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
      (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g →
      (∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      ∀ {eta C q : ℝ}, eta ≤ eta₀ →
      (∀ x : M, q < metricScalarAt g x →
        Nonempty (SpatialNeck g eta x) ∨
          (∃ w : M, Nonempty (SpatialNeck g eta w) ∧
            metricScalarAt g x ≤ C * metricScalarAt g w) ∨
          ∀ y : M, metricScalarAt g y ≤ C * metricScalarAt g x) →
      ∃ C' : ℝ, ∀ x : M, metricScalarAt g x ≤ C' := by
  obtain ⟨eta₀, heta₀, hneck⟩ := exists_spatialNeck_scalar_upper_bound.{v}
  refine ⟨eta₀, heta₀, ?_⟩
  intro M _ _ _ _ _ _ g hg hcone eta C q heta halt
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g :=
    (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff g).mpr fun x v w =>
      (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        g x hdim).mp (hcone x) v w
  obtain ⟨Cn, hCn⟩ := hneck M g hg hsec
  by_cases hglob : ∃ x : M, q < metricScalarAt g x ∧
      ∀ y : M, metricScalarAt g y ≤ C * metricScalarAt g x
  · obtain ⟨x, -, hx⟩ := hglob
    exact ⟨C * metricScalarAt g x, hx⟩
  push Not at hglob
  refine ⟨max q (max Cn (max C 0 * max Cn 0)), fun x => ?_⟩
  by_cases hx : metricScalarAt g x ≤ q
  · exact hx.trans (le_max_left _ _)
  have hxq := lt_of_not_ge hx
  rcases halt x hxq with hnk | ⟨w, hnk, hw⟩ | hall
  · obtain ⟨nk⟩ := hnk
    exact (hCn x eta heta nk).trans ((le_max_left _ _).trans (le_max_right _ _))
  · obtain ⟨nk⟩ := hnk
    have hRw := hCn w eta heta nk
    have hRw0 : 0 ≤ metricScalarAt g w :=
      metricScalarAt_nonnegative_of_curvatureOperator_nonnegative g w (hcone w)
    have h1 : C * metricScalarAt g w ≤ max C 0 * max Cn 0 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hRw0).trans
        (mul_le_mul_of_nonneg_left (hRw.trans (le_max_left _ _)) (le_max_right _ _))
    exact hw.trans (h1.trans ((le_max_right _ _).trans (le_max_right _ _)))
  · obtain ⟨y, hy⟩ := hglob x hxq
    exact absurd (hall y) (not_le.mpr hy)

theorem neck_alternatives_of_spatialCanonicalWitness {M : Type v} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {x : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (hW : W.capTubeHasNeckChart eps) :
    Nonempty (SpatialNeck g eps x) ∨
      (∃ w ∈ W.domain.carrier, Nonempty (SpatialNeck g eps w) ∧
        metricScalarAt g x ≤ C2 * metricScalarAt g w ∧
          metricScalarAt g w ≤ C2 * metricScalarAt g x) ∨
      (W.domain.carrier = connectedComponent x ∧
        ∀ y ∈ W.domain.carrier, metricScalarAt g y ≤ C2 * metricScalarAt g x) := by
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  cases halt : W.alternative with
  | neck data => exact Or.inl ⟨data.neck⟩
  | cap data deep =>
    obtain ⟨v, nk, hmap⟩ := hW data deep halt
    have hvtube : v ∈ data.tube := by
      rw [← data.tube_eq]
      refine ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, ?_⟩
      rw [hmap]
      exact nk.center_eq
    have hv : v ∈ W.domain.carrier := by
      rw [data.union_eq]
      exact Or.inr hvtube
    have hlow := (W.scalar_bounds v hv).1
    have hx' : metricScalarAt g x ≤ C2 * metricScalarAt g v := by
      have h1 := mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ C2)
      rwa [← mul_assoc, mul_inv_cancel₀ (by linarith : C2 ≠ 0), one_mul] at h1
    exact Or.inr (Or.inl ⟨v, hv, ⟨nk⟩, hx', (W.scalar_bounds v hv).2⟩)
  | positive whole data sec => exact Or.inr (Or.inr ⟨whole, fun y hy => (W.scalar_bounds y hy).2⟩)
  | round whole data => exact Or.inr (Or.inr ⟨whole, fun y hy => (W.scalar_bounds y hy).2⟩)

theorem SpatialNeck.exists_uniform_transport_tolerance {alpha r₀ r₁ : ℝ} (ha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) (hr₀ : 0 < r₀) :
    ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧
      ∀ {P : Type v} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
        [T2Space P] [SigmaCompactSpace P] {g : SmoothRiemannianMetric I3 P} {p : P}
        (nk : SpatialNeck g (neckModelTolerance alpha) p),
        r₀ ≤ metricScalarAt g p → metricScalarAt g p ≤ r₁ →
        ∀ (U : TopologicalSpace.Opens P),
          (∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ U) →
        ∀ {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
          [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
          (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
          MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} ⌈(2 * alpha)⁻¹⌉₊ delta →
          |metricScalarAt g' (F p) - metricScalarAt g p| < eta →
          Nonempty (SpatialNeck g' (2 * alpha) (F p)) := by
  set order := ⌈(2 * alpha)⁻¹⌉₊
  set target := neckSourceTolerance alpha
  have ht : 0 < target := neckSourceTolerance_pos ha
  set n : ℝ := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  set B : ℝ := (∑ a ∈ Finset.range (order + 1), Real.sqrt (r₀⁻¹ ^ (a + 2))) + 1
  have hBsum : 0 ≤ ∑ a ∈ Finset.range (order + 1), Real.sqrt (r₀⁻¹ ^ (a + 2)) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hB : 0 < B := by linarith
  have hr₁ : 0 < max r₁ r₀ := lt_max_of_lt_right hr₀
  set eta := min (r₀ / 2) (r₀ * target / (2 * (n + 1)))
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  refine ⟨target / (4 * max r₁ r₀ * B), eta, by positivity, heta, ?_⟩
  intro P _ _ _ _ _ g p nk hq0 hq1 U hout N _ _ _ _ _ g' F hUF C hclose
  set q := metricScalarAt g p
  have hq : 0 < q := nk.Q_pos
  have hqinv : q⁻¹ ≤ r₀⁻¹ := inv_anti₀ hr₀ hq0
  have hweight (a : ℕ) (ha' : a ≤ order) : Real.sqrt (q⁻¹ ^ (a + 2)) ≤ B := by
    have h0 := Finset.single_le_sum (fun b (_ : b ∈ Finset.range (order + 1)) =>
      Real.sqrt_nonneg (r₀⁻¹ ^ (b + 2))) (Finset.mem_range.mpr (by omega : a < order + 1))
    have h1 : Real.sqrt (q⁻¹ ^ (a + 2)) ≤ Real.sqrt (r₀⁻¹ ^ (a + 2)) :=
      Real.sqrt_le_sqrt (pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hqinv _)
    linarith
  set c := metricScalarAt g' (F p)
  have hlow := (abs_lt.mp hclose).1
  have hupp := (abs_lt.mp hclose).2
  have hetaq : eta ≤ q / 2 := (min_le_left _ _).trans (by linarith)
  have hc : 0 < c := by linarith
  have hc2 : c ≤ 2 * max r₁ r₀ := by linarith [le_max_left r₁ r₀]
  have hratio : |c / q - 1| * n ≤ target / 2 := by
    have he : c / q - 1 = (c - q) / q := by field_simp
    rw [he, abs_div, abs_of_pos hq]
    have h1 : |c - q| / q ≤ target / (2 * (n + 1)) := by
      rw [div_le_iff₀ hq]
      have h2 := hclose.le.trans (min_le_right (r₀ / 2) (r₀ * target / (2 * (n + 1))))
      have h3 : r₀ * target / (2 * (n + 1)) ≤ q * target / (2 * (n + 1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hq0 ht.le
      calc |c - q| ≤ q * target / (2 * (n + 1)) := h2.trans h3
        _ = target / (2 * (n + 1)) * q := by ring
    calc |c - q| / q * n ≤ target / (2 * (n + 1)) * n :=
          mul_le_mul_of_nonneg_right h1 hn
      _ ≤ target / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hcmp := C.staticRescale (t := 0) rfl q c hq hc ht.le (fun a ha' => by
    have h1 : Real.sqrt (q⁻¹ ^ (a + 2)) * c * (target / (4 * max r₁ r₀ * B)) ≤
        B * (2 * max r₁ r₀) * (target / (4 * max r₁ r₀ * B)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hweight a ha') hc2 hc.le hB.le) (by positivity)
    have h2 : B * (2 * max r₁ r₀) * (target / (4 * max r₁ r₀ * B)) = target / 2 := by
      field_simp
      ring
    linarith)
  obtain ⟨nk', -⟩ := nk.exists_transport_of_local_comparisons hc F hcmp ha hsmall ht.le le_rfl
    le_rfl rfl hout hUF
  exact ⟨nk'⟩

theorem nonempty_metricComparisonOn_refl_of_metricDerivNorm_le {M : Type v}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    [SigmaCompactSpace M] (g g' : SmoothRiemannianMetric I3 M) {K : Set M} (hK : IsCompact K)
    (order : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hbound : ∀ x ∈ K, ∀ a : ℕ, a ≤ order →
      CheegerGromovCompactness.metricDerivNorm a g' g g x ≤ delta) :
    Nonempty (MetricComparisonOn (fun _ => g) (fun _ => g') (PartialDiffeomorph.refl (I := I3) M)
      K {0} order delta) := by
  let U : TopologicalSpace.Opens M := ⊤
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  refine exists_static_metricComparisonOn_of_local_metric g g'
    (PartialDiffeomorph.refl (I := I3) M) U (g'.restrictOpen U) ?_ K hK
    (fun x _ => trivial) order hdelta ?_ {0}
  · intro x v w
    have hid : (PartialDiffeomorph.refl (I := I3) M : M → M) = id := rfl
    rw [hid, mfderiv_id, SmoothRiemannianMetric.restrictOpen_inner]
    rfl
  · intro x hx a ha
    rw [CheegerGromovCompactness.metricDerivNorm_restrictOpen]
    exact hbound x hx a ha

theorem mfderiv_apply_mfderiv_symm_apply_of_mem_target {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ThreeSpace A] [TopologicalSpace B] [ChartedSpace ThreeSpace B]
    (e : PartialDiffeomorph I3 I3 A B ∞)
    {z : B} (hz : z ∈ e.target) (v : TangentSpace I3 z) :
    mfderiv I3 I3 e (e.symm z) (mfderiv I3 I3 e.symm z v) = v := by
  have hsrc : e.symm z ∈ e.source := e.map_target hz
  have hloc : (fun q => e (e.symm q)) =ᶠ[nhds z] id :=
    Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hz) fun q hq => e.right_inv' hq
  have hcomp := mfderiv_comp z (e.mdifferentiableAt (by decide) hsrc)
    (e.symm.mdifferentiableAt (by decide) hz)
  have h1 : mfderiv I3 I3 (fun q => e (e.symm q)) z v =
      mfderiv I3 I3 e (e.symm z) (mfderiv I3 I3 e.symm z v) :=
    DFunLike.congr_fun hcomp v
  rw [hloc.mfderiv_eq, mfderiv_id] at h1
  exact h1.symm

theorem isometryOn_symm_of_isometryOn {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ThreeSpace A] [IsManifold I3 ∞ A] [TopologicalSpace B]
    [ChartedSpace ThreeSpace B] [IsManifold I3 ∞ B] (e : PartialDiffeomorph I3 I3 A B ∞)
    {gA : SmoothRiemannianMetric I3 A} {gB : SmoothRiemannianMetric I3 B}
    (hiso : ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      gB.inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = gA.inner z v w) :
    ∀ z ∈ e.symm.source, ∀ v w : TangentSpace I3 z,
      gA.inner (e.symm z) (mfderiv I3 I3 e.symm z v) (mfderiv I3 I3 e.symm z w) =
        gB.inner z v w := by
  intro z hz v w
  have hz' : z ∈ e.target := hz
  have hsrc : e.symm z ∈ e.source := e.map_target hz'
  have h := hiso (e.symm z) hsrc (mfderiv I3 I3 e.symm z v) (mfderiv I3 I3 e.symm z w)
  rw [mfderiv_apply_mfderiv_symm_apply_of_mem_target e hz',
    mfderiv_apply_mfderiv_symm_apply_of_mem_target e hz'] at h
  have hez : e (e.symm z) = z := e.right_inv' hz'
  rw [← h]
  generalize e (e.symm z) = y at hez ⊢
  subst hez
  rfl

theorem exists_uniform_neck_transfer_tolerance {alpha r₀ r₁ : ℝ} (ha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) (hr₀ : 0 < r₀) :
    ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧
      ∀ {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M),
        RiemannianMetricComplete g → ∀ (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
        {Wm : Type v} [TopologicalSpace Wm] [ChartedSpace ThreeSpace Wm] [IsManifold I3 ∞ Wm]
        [T2Space Wm] [SigmaCompactSpace Wm] (h : SmoothRiemannianMetric I3 Wm) (φ : V → Wm)
        (hφ : IsLocalDiffeomorph I3 I3 ∞ φ), Function.Injective φ →
        ∀ (x : V) {R : ℝ}, 0 < R → riemannianClosedBallOf g (x : M) (2 * R) ⊆ V →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ v : TangentSpace I3 y,
          (g.restrictOpen V).inner y v v ≤ 2 * (localPullMetric h φ hφ).inner y v v) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ a : ℕ,
          a ≤ ⌈(2 * alpha)⁻¹⌉₊ → CheegerGromovCompactness.metricDerivNorm a
            (g.restrictOpen V) (localPullMetric h φ hφ) (localPullMetric h φ hφ) y ≤ delta) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) →
          |metricScalarAt (g.restrictOpen V) y - metricScalarAt (localPullMetric h φ hφ) y| <
            eta) →
        ∀ {p : Wm} (nk : SpatialNeck h (neckModelTolerance alpha) p),
          r₀ ≤ metricScalarAt h p → metricScalarAt h p ≤ r₁ →
          (∀ y ∈ univ ×ˢ Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹,
            nk.map y ∈ riemannianBallOf h (φ x) (R / Real.sqrt 2)) →
          ∃ w : V, φ w = p ∧ (w : M) ∈ riemannianClosedBallOf g (x : M) R ∧
            Nonempty (SpatialNeck g (2 * alpha) (w : M)) := by
  obtain ⟨delta, eta, hdelta, heta, htr⟩ :=
    SpatialNeck.exists_uniform_transport_tolerance (r₁ := r₁) ha hsmall hr₀
  refine ⟨delta, eta, hdelta, heta, ?_⟩
  intro M _ _ _ _ _ g hg V _ Wm _ _ _ _ _ h φ hφ hinj x R hR hball hquad hjet hscal p nk hp0 hp1
    hregion
  set gh := localPullMetric h φ hφ with hgh
  obtain ⟨Φ, hΦs, -, hΦf⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hφ.isLocalDiffeomorphOn univ) isOpen_univ ⟨x, trivial⟩ hinj.injOn
  have hΦ : ∀ z : V, Φ z = φ z := fun z => congrFun hΦf z
  have hisoΦ : ∀ z ∈ Φ.source, ∀ v w : TangentSpace I3 z,
      h.inner (Φ z) (mfderiv I3 I3 Φ z v) (mfderiv I3 I3 Φ z w) = gh.inner z v w := by
    intro z _ v w
    rw [hgh, localPullMetric_inner, hΦf]
  have hcptM : IsCompact (riemannianClosedBallOf g (x : M) (2 * R)) :=
    RiemannianMetricComplete.closedEBall_isCompact hg (x : M) (2 * R)
  have hRR : R ≤ 2 * R := by linarith
  let Kbig : Set V := Subtype.val ⁻¹' riemannianClosedBallOf g (x : M) (2 * R)
  have hKbig : IsCompact Kbig := by
    rw [Subtype.isCompact_iff]
    change IsCompact (Subtype.val '' (Subtype.val ⁻¹' riemannianClosedBallOf g (x : M) (2 * R)))
    rw [Set.image_preimage_eq_of_subset (by
      intro z hz
      exact ⟨⟨z, hball hz⟩, rfl⟩)]
    exact hcptM
  let Kin := riemannianClosedBallOf (g.restrictOpen V) x R
  have hKin_sub : ∀ y ∈ Kin, (y : M) ∈ riemannianClosedBallOf g (x : M) R := fun y hy =>
    (riemannianEDistOf_le_restrictOpen g V x y).trans hy
  have hKin_big : Kin ⊆ Kbig := fun y hy =>
    riemannianClosedBallOf_mono _ _ hRR (hKin_sub y hy)
  have hKin : IsCompact Kin := by
    refine hKbig.of_isClosed_subset ?_ hKin_big
    exact isClosed_le (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
  have hcapture := ball_subset_image_of_metric_lower_crossModel (g.restrictOpen V) h Φ x
    (R := R) (L := Real.sqrt 2) hR (Real.sqrt_pos.mpr (by norm_num)) hKin
    (fun y _ => hΦs ▸ mem_univ y) (fun y hy v => by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hisoΦ y (hΦs ▸ mem_univ y)]
      exact hquad y (hKin_big hy) v)
  rw [hΦ] at hcapture
  have hpt : ∀ y ∈ univ ×ˢ Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹,
      ∃ z ∈ Kin, Φ z = nk.map y := fun y hy => hcapture (hregion y hy)
  have hwin : ∀ y ∈ univ ×ˢ Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹,
      nk.map y ∈ Φ.symm.source := by
    intro y hy
    obtain ⟨z, -, hz⟩ := hpt y hy
    rw [← hz]
    exact Φ.map_source (hΦs ▸ mem_univ z)
  have hsymm : ∀ y ∈ univ ×ˢ Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹,
      Φ.symm (nk.map y) ∈ Kin := by
    intro y hy
    obtain ⟨z, hzK, hz⟩ := hpt y hy
    rw [← hz]
    convert hzK using 1
    exact Φ.left_inv' (hΦs ▸ mem_univ z)
  let nkV := nk.pushforward Φ.symm (isometryOn_symm_of_isometryOn Φ hisoΦ) hwin
  have hnmt : neckModelTolerance alpha ≤ alpha := neckModelTolerance_le alpha
  have hnmt0 : 0 < neckModelTolerance alpha := neckModelTolerance_pos ha
  have hinv : alpha⁻¹ ≤ (neckModelTolerance alpha)⁻¹ := inv_anti₀ hnmt0 hnmt
  have hsub : univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹ ⊆
      (univ ×ˢ Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹ : Set Cylinder) :=
    fun y hy => ⟨hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hcen : nk.map (nk.center, 0) = p := nk.center_eq
  have hcenwin : ((nk.center, 0) : Cylinder) ∈
      (univ ×ˢ Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹ : Set Cylinder) :=
    ⟨trivial, neg_neg_of_pos (inv_pos.mpr hnmt0), inv_pos.mpr hnmt0⟩
  have hpKin : Φ.symm p ∈ Kin := hcen ▸ hsymm _ hcenwin
  have hptarget : p ∈ Φ.target := hcen ▸ hwin _ hcenwin
  have hφp : φ (Φ.symm p) = p := by rw [← hΦ]; exact Φ.right_inv' hptarget
  let U : TopologicalSpace.Opens V :=
    ⟨Subtype.val ⁻¹' riemannianBallOf g (x : M) (2 * R), (isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const).preimage
      continuous_subtype_val⟩
  have hUK : (U : Set V) ⊆ Kbig := fun y hy =>
    le_of_lt (show riemannianEDistOf g (x : M) (y : M) < ENNReal.ofReal (2 * R) from hy)
  have hout : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nkV.map y ∈ U := by
    intro y hy
    change Φ.symm (nk.map y) ∈ U
    have h1 := hKin_sub _ (hsymm y (hsub hy))
    change riemannianEDistOf g (x : M) _ < ENNReal.ofReal (2 * R)
    exact lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  obtain ⟨C⟩ := nonempty_metricComparisonOn_refl_of_metricDerivNorm_le gh (g.restrictOpen V)
    hKbig ⌈(2 * alpha)⁻¹⌉₊ hdelta.le (fun y hy a ha' => hjet y hy a ha')
  have hscalar_p : metricScalarAt gh (Φ.symm p) = metricScalarAt h p := by
    rw [hgh, metricScalarAt_localPull, hφp]
  have hclose : |metricScalarAt (g.restrictOpen V)
      (PartialDiffeomorph.refl (I := I3) V (Φ.symm p)) - metricScalarAt gh (Φ.symm p)| < eta :=
    hscal _ (hKin_big hpKin)
  obtain ⟨nk2⟩ := htr (P := V) (g := gh) nkV (by rw [hscalar_p]; exact hp0)
    (by rw [hscalar_p]; exact hp1) U hout (g.restrictOpen V)
    (PartialDiffeomorph.refl (I := I3) V) (fun _ _ => trivial) (C.mono hUK le_rfl le_rfl) hclose
  have hisoV : ∀ z ∈ (Manifold.openSubtypePartialDiffeomorph I3 V ⟨x⟩).source,
      ∀ v w : TangentSpace I3 z,
        g.inner (Manifold.openSubtypePartialDiffeomorph I3 V ⟨x⟩ z)
          (mfderiv I3 I3 (Manifold.openSubtypePartialDiffeomorph I3 V ⟨x⟩) z v)
          (mfderiv I3 I3 (Manifold.openSubtypePartialDiffeomorph I3 V ⟨x⟩) z w) =
        (g.restrictOpen V).inner z v w := by
    intro z _ v w
    have hfun : (Manifold.openSubtypePartialDiffeomorph I3 V ⟨x⟩ : V → M) = Subtype.val := rfl
    rw [hfun, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
      SmoothRiemannianMetric.restrictOpen_inner]
  let nk3 := nk2.pushforward (Manifold.openSubtypePartialDiffeomorph I3 V ⟨x⟩) hisoV
    (fun _ _ => trivial)
  exact ⟨Φ.symm p, hφp, hKin_sub _ hpKin, ⟨nk3⟩⟩

theorem exists_spatialNeck_window_edist_le :
    ∃ D : ℝ, 0 < D ∧ ∀ {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {p : M}
      (nk : SpatialNeck g eps p), ∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹,
        riemannianEDistOf g p (nk.map y) ≤
          ENNReal.ofReal ((D + 2 * eps⁻¹) / Real.sqrt (metricScalarAt g p)) := by
  obtain ⟨D, hD, hsh⟩ := exists_transverse_shortcuts_uniform_in_manifold.{v}
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ g eps p nk y hy
  obtain ⟨σ, z⟩ := y
  have hz : z ∈ Ioo (-eps⁻¹) eps⁻¹ := hy.2
  have heps0 : 0 < eps := nk.eps_pos
  have heps1 : eps ≤ 1 := by linarith [nk.eps_small]
  set Q := metricScalarAt g p
  have hQ : 0 < Q := nk.Q_pos
  let sg := scaleMetric Q hQ g
  let U : Set Cylinder := univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
  have hlevel : ∀ w : Sphere 2, ((w, (0 : ℝ)) : Cylinder) ∈ U :=
    fun w => ⟨trivial, neg_neg_of_pos (inv_pos.mpr heps0), inv_pos.mpr heps0⟩
  obtain ⟨gamma, hstart, hend, hgamma, -, hlen⟩ := hsh M nk.cylinder
    (fun _ => nk.cylinder.metric 0) (fun _ => sg) nk.map U {0} ⌈eps⁻¹⌉₊ eps 0
    nk.comparison rfl heps0.le heps1 (mem_singleton 0) nk.domain hlevel nk.center σ
  have h1 : riemannianEDistOf sg (nk.map (nk.center, 0)) (nk.map (σ, 0)) ≤ ENNReal.ofReal D := by
    have hd := edistOf_le_metricPathELength sg (by norm_num : (0 : ℝ) ≤ 1) hgamma
    rw [hstart, hend] at hd
    exact hd.trans hlen
  have hzlt : |z| < eps⁻¹ := abs_lt.mpr ⟨hz.1, hz.2⟩
  have hslab : univ ×ˢ Icc (-|z|) |z| ⊆ U := fun w hw =>
    ⟨trivial, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have h2 := collar_axial_edist_le nk.cylinder (fun _ => sg) nk.map nk.comparison rfl heps0.le
    (mem_singleton 0) nk.domain hslab σ ⟨neg_abs_le z, le_abs_self z⟩
  have hzabs : |z| ≤ eps⁻¹ := hzlt.le
  have hsq : Real.sqrt (1 + eps) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  have h2' : riemannianEDistOf sg (nk.map (σ, 0)) (nk.map (σ, z)) ≤
      ENNReal.ofReal (2 * eps⁻¹) := by
    rw [DifferentialGeometry.riemannianEDistOf_comm]
    exact h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul hsq hzabs (abs_nonneg z)
      (by norm_num)))
  have htri := (DifferentialGeometry.riemannianEDistOf_triangle sg (nk.map (nk.center, 0))
    (nk.map (σ, 0))
    (nk.map (σ, z))).trans (add_le_add h1 h2')
  rw [← ENNReal.ofReal_add hD.le (by positivity), nk.center_eq] at htri
  change riemannianEDistOf (scaleMetric Q hQ g) p (nk.map (σ, z)) ≤ _ at htri
  rw [edistOf_scale] at htri
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  rw [ENNReal.ofReal_div_of_pos hs, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact htri

theorem eventually_metricDerivNorm_swap_le {M : Type v} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    {gs : ℕ → SmoothRiemannianMetric I3 M} {g gRef : SmoothRiemannianMetric I3 M}
    (hconv : CheegerGromovCompactness.MetricCInfConvergenceOnCompacts gs g gRef)
    {K : Set M} (hK : IsCompact K) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ K, ∀ q : ℕ, q ≤ p →
      CheegerGromovCompactness.metricDerivNorm q g (gs i) (gs i) x ≤ ε := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  obtain ⟨u, hu, hKu, hcl⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨δ, hδ, hδ1, hdim, hbudget⟩ :=
    CheegerGromovCompactness.exists_metric_reference_change_delta (E := ThreeSpace) p hε
  obtain ⟨N, hN⟩ := (hconv.change_reference g) (closure u) hcl p δ hδ
  filter_upwards [eventually_ge_atTop N] with n hn x hx q hq
  apply CheegerGromovCompactness.metric_deriv_norm_reference_change_le hu g (gs n) g p hδ.le
    hδ1.le hdim hbudget
  · intro y _ r _
    rw [CheegerGromovCompactness.metricDerivNorm_self]
    exact hδ.le
  · intro y hy r hr
    exact (CheegerGromovCompactness.derivNorm_le_sup hcl hr (gs n) g g (subset_closure hy)).trans
      (hN n hn).le
  · exact hKu hx
  · exact hq

section PointedWitnessTransfer

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance opensSigmaCompactTransfer {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem monotone_and_cover_of_riemannianBallOf_eq {P : PointedRiemannianManifold.{w, 0, 0} I3}
    (hconn : ConnectedSpace P.M) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) :
    Monotone V ∧ ∀ x : P.M, ∃ k, x ∈ V k := by
  refine ⟨fun k l hkl z hz => ?_, fun x => ?_⟩
  · change z ∈ (V l : Set P.M)
    have hz' : z ∈ (V k : Set P.M) := hz
    rw [hV] at hz' ⊢
    refine riemannianBallOf_mono _ _ ?_ hz'
    have : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hkl 1
    linarith
  · have hne := riemannianEDistOf_ne_top P.metric P.basepoint x
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (riemannianEDistOf P.metric P.basepoint x).toReal)
    refine ⟨k, ?_⟩
    change x ∈ (V k : Set P.M)
    rw [hV]
    refine (ENNReal.lt_ofReal_iff_toReal_lt hne).mpr ?_
    push_cast
    linarith

theorem exists_mem_connectedComponent_of_monotone_cover {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] {V : ℕ → Opens Y} (hmono : Monotone V) (hcover : ∀ x : Y, ∃ k, x ∈ V k)
    (x y : Y) (k₀ : ℕ) :
    ∃ k, k₀ ≤ k ∧ ∃ (hx : x ∈ V k) (hy : y ∈ V k),
      (⟨y, hy⟩ : V k) ∈ connectedComponent (⟨x, hx⟩ : V k) := by
  let γ := PathConnectedSpace.somePath x y
  have hcpt : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨k₁, hk₁⟩ := hcpt.elim_directed_cover (fun k => (V k : Set Y)) (fun k => (V k).isOpen)
    (fun z _ => mem_iUnion.mpr (hcover z)) hmono.directed_le
  set k := max k₀ k₁
  have hsub : range γ ⊆ V k := hk₁.trans (hmono (le_max_right _ _))
  have hx : x ∈ V k := hsub ⟨0, γ.source⟩
  have hy : y ∈ V k := hsub ⟨1, γ.target⟩
  refine ⟨k, le_max_left _ _, hx, hy, ?_⟩
  let S : Set (V k) := Subtype.val ⁻¹' range γ
  have hS : IsPreconnected S := by
    apply (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
    have himg : Subtype.val '' S = range γ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hsub hz⟩, hz, rfl⟩
    exact himg.symm ▸ isPreconnected_range γ.continuous
  exact hS.subset_connectedComponent (show (⟨x, hx⟩ : V k) ∈ S from ⟨0, γ.source⟩)
    (show (⟨y, hy⟩ : V k) ∈ S from ⟨1, γ.target⟩)

theorem metricCInfConvergenceOnCompacts_localPull_of_local_flow_limit
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} {V : ℕ → Opens P.M}
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    {G : ℝ → SmoothRiemannianMetric I3 P.M} {ψ : ℕ → ℕ}
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (k : ℕ) {s : ℝ} (hs : s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0) :
    MetricCInfConvergenceOnCompacts (fun i => if hi : N k ≤ ψ i then
        localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi)
      else (G s).restrictOpen (V k))
      ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
  intro K hK p η hη
  obtain ⟨j₀, hj₀⟩ := hconv k K hK p η hη
  refine ⟨j₀, fun i hi => ?_⟩
  obtain ⟨hi', hb⟩ := hj₀ i hi
  simp only [dite_eq_left hi']
  exact hb s hs

end PointedWitnessTransfer

theorem neckAlternatives_of_spatialCanonicalWitness {M : Type v} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I3 M} {eps C1 C2 : ℝ} {x : M}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (hW : W.capTubeHasNeckChart eps) :
    Nonempty (SpatialNeck g eps x) ∨
      (∃ w : M, Nonempty (SpatialNeck g eps w) ∧
        metricScalarAt g x ≤ max (2 * |C1|) C2 * metricScalarAt g w ∧
        metricScalarAt g w ≤ max (2 * |C1|) C2 * metricScalarAt g x ∧
        riemannianEDistOf g x w <
          ENNReal.ofReal (max (2 * |C1|) C2 / Real.sqrt (metricScalarAt g x))) ∨
      ∀ y ∈ connectedComponent x,
        metricScalarAt g y ≤ max (2 * |C1|) C2 * metricScalarAt g x := by
  have hQ := W.Q_pos
  have hC2 : C2 ≤ max (2 * |C1|) C2 := le_max_right _ _
  rcases neck_alternatives_of_spatialCanonicalWitness W hW with h1 | ⟨w, hw, hnk, hxw, hwx⟩ |
    ⟨hdom, hb⟩
  · exact Or.inl h1
  · have hw0 : 0 ≤ metricScalarAt g w := by
      have := (W.scalar_bounds w hw).1
      have hC21 : 1 ≤ C2 := W.one_le_comparison_constant
      have : 0 ≤ C2⁻¹ * metricScalarAt g x := mul_nonneg (by positivity) hQ.le
      linarith
    refine Or.inr (Or.inl ⟨w, hnk, hxw.trans (mul_le_mul_of_nonneg_right hC2 hw0),
      hwx.trans (mul_le_mul_of_nonneg_right hC2 hQ.le), ?_⟩)
    refine (W.inside_ball hw).trans_le (ENNReal.ofReal_le_ofReal ?_)
    have hrad := W.radius_upper
    have hs : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hQ
    have h1 : 2 * W.radius ≤ 2 * |C1| / Real.sqrt (metricScalarAt g x) := by
      have := div_le_div_of_nonneg_right (le_abs_self C1) hs.le
      rw [mul_div_assoc]
      linarith
    exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
  · refine Or.inr (Or.inr fun y hy => ?_)
    rw [← hdom] at hy
    exact (hb y hy).trans (mul_le_mul_of_nonneg_right hC2 hQ.le)

theorem exists_neck_transfer_of_edist_lt {alpha r₀ r₁ : ℝ} (halpha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) (hr₀ : 0 < r₀) :
    ∃ D delta eta : ℝ, 0 < D ∧ 0 < delta ∧ 0 < eta ∧
      ∀ {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M),
        RiemannianMetricComplete g → ∀ (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
        {Wm : Type v} [TopologicalSpace Wm] [ChartedSpace ThreeSpace Wm] [IsManifold I3 ∞ Wm]
        [T2Space Wm] [SigmaCompactSpace Wm] (hm : SmoothRiemannianMetric I3 Wm) (φ : V → Wm)
        (hφ : IsLocalDiffeomorph I3 I3 ∞ φ), Function.Injective φ →
        ∀ (x : V) {R : ℝ}, 0 < R → riemannianClosedBallOf g (x : M) (2 * R) ⊆ V →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ v : TangentSpace I3 y,
          (g.restrictOpen V).inner y v v ≤ 2 * (localPullMetric hm φ hφ).inner y v v) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ a : ℕ,
          a ≤ ⌈(2 * alpha)⁻¹⌉₊ → CheegerGromovCompactness.metricDerivNorm a
            (g.restrictOpen V) (localPullMetric hm φ hφ) (localPullMetric hm φ hφ) y ≤ delta) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) →
          |metricScalarAt (g.restrictOpen V) y - metricScalarAt (localPullMetric hm φ hφ) y| <
            eta) →
        ∀ {p : Wm}, SpatialNeck hm (neckModelTolerance alpha) p →
          r₀ ≤ metricScalarAt hm p → metricScalarAt hm p ≤ r₁ → ∀ {d : ℝ},
          riemannianEDistOf hm (φ x) p < ENNReal.ofReal d →
          d + (D + 2 * (neckModelTolerance alpha)⁻¹) / Real.sqrt r₀ ≤ R / Real.sqrt 2 →
          ∃ w : V, φ w = p ∧ (w : M) ∈ riemannianClosedBallOf g (x : M) R ∧
            Nonempty (SpatialNeck g (2 * alpha) (w : M)) := by
  obtain ⟨D, hD, hwin⟩ := exists_spatialNeck_window_edist_le.{v}
  obtain ⟨δ, η, hδ, hη, hNT⟩ :=
    exists_uniform_neck_transfer_tolerance (r₀ := r₀) (r₁ := r₁) halpha hsmall hr₀
  refine ⟨D, δ, η, hD, hδ, hη, ?_⟩
  intro M _ _ _ _ _ g hg V _ Wm _ _ _ _ _ hm φ hφ hinj x R hR hball hquad hjet hscal p nk hp0 hp1
    d hd hdR
  refine hNT g hg V hm φ hφ hinj x hR hball hquad hjet hscal nk hp0 hp1 fun y hy => ?_
  have hr0 : 0 < Real.sqrt r₀ := Real.sqrt_pos.mpr hr₀
  have h1 : riemannianEDistOf hm p (nk.map y) ≤
      ENNReal.ofReal ((D + 2 * (neckModelTolerance alpha)⁻¹) / Real.sqrt r₀) := by
    refine (hwin hm nk y hy).trans (ENNReal.ofReal_le_ofReal ?_)
    have hn0 : 0 < neckModelTolerance alpha := neckModelTolerance_pos halpha
    exact div_le_div_of_nonneg_left (by positivity) hr0 (Real.sqrt_le_sqrt hp0)
  have hd0 : 0 ≤ d := by
    by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_of_nonpos hneg.le] at hd
    exact absurd hd (not_lt.mpr zero_le)
  change riemannianEDistOf hm (φ x) (nk.map y) < ENNReal.ofReal (R / Real.sqrt 2)
  calc riemannianEDistOf hm (φ x) (nk.map y)
      ≤ riemannianEDistOf hm (φ x) p + riemannianEDistOf hm p (nk.map y) :=
        DifferentialGeometry.riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal d +
          ENNReal.ofReal ((D + 2 * (neckModelTolerance alpha)⁻¹) / Real.sqrt r₀) :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) hd h1
    _ = ENNReal.ofReal (d + (D + 2 * (neckModelTolerance alpha)⁻¹) / Real.sqrt r₀) :=
        (ENNReal.ofReal_add hd0 (by
          have hn0 : 0 < neckModelTolerance alpha := neckModelTolerance_pos halpha
          positivity)).symm
    _ ≤ ENNReal.ofReal (R / Real.sqrt 2) := ENNReal.ofReal_le_ofReal hdR

theorem le_four_mul_of_near_neck_scalars {a z v w ε C : ℝ} (ha : 0 < a) (hC : 1 ≤ C)
    (hz : |a - z| < ε) (hzv : z ≤ C * v) (hvw : |w - v| < ε) (hv : a / (2 * C) ≤ v)
    (hε : ε ≤ a / (8 * C)) : a ≤ 4 * C * w := by
  have hwv := (abs_lt.mp hvw).1
  have hvw' := (abs_lt.mp hvw).2
  have hRw : 3 * a / (8 * C) ≤ w := by
    have h1 : a / (2 * C) - a / (8 * C) = 3 * a / (8 * C) := by
      field_simp
      ring
    linarith
  have hεw : ε ≤ w / 3 := by
    have : a / (8 * C) = (3 * a / (8 * C)) / 3 := by ring
    linarith
  have hw0 : 0 ≤ w := le_trans (by positivity) hRw
  have hA1 : a < z + ε := by linarith [(abs_lt.mp hz).2]
  have h1 : C * v ≤ C * (w + ε) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (C + 1) * ε ≤ (C + 1) * (w / 3) := mul_le_mul_of_nonneg_left hεw (by linarith)
  have h3 : (C + 1) * (w / 3) ≤ C * w := by
    have h4 := mul_le_mul_of_nonneg_right (show C + 1 ≤ 2 * C by linarith) hw0
    linarith
  have h5 : C * w ≤ 3 * C * w := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ C) hw0
    linarith
  have h6 : C * (w + ε) + ε = C * w + (C + 1) * ε := by ring
  linarith

theorem exists_neck_alternatives_transfer_constants {alpha : ℝ} (halpha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) {C : ℝ} (hC : 1 ≤ C) {a : ℝ} (ha : 0 < a) :
    ∃ R delta ε : ℝ, 0 < R ∧ 0 < delta ∧ 0 < ε ∧ ε ≤ a / 8 ∧
      ∀ {M : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
        [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M),
        RiemannianMetricComplete g → ∀ (V : TopologicalSpace.Opens M) [SigmaCompactSpace V]
        {Wm : Type v} [TopologicalSpace Wm] [ChartedSpace ThreeSpace Wm] [IsManifold I3 ∞ Wm]
        [T2Space Wm] [SigmaCompactSpace Wm] (hm : SmoothRiemannianMetric I3 Wm) (φ : V → Wm)
        (hφ : IsLocalDiffeomorph I3 I3 ∞ φ), Function.Injective φ → ∀ x : V,
        metricScalarAt g (x : M) = a →
        riemannianClosedBallOf g (x : M) (2 * R) ⊆ V →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ v : TangentSpace I3 y,
          (g.restrictOpen V).inner y v v ≤ 2 * (localPullMetric hm φ hφ).inner y v v) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) → ∀ r : ℕ,
          r ≤ ⌈(2 * alpha)⁻¹⌉₊ → CheegerGromovCompactness.metricDerivNorm r
            (g.restrictOpen V) (localPullMetric hm φ hφ) (localPullMetric hm φ hφ) y ≤ delta) →
        (∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) →
          |metricScalarAt (g.restrictOpen V) y - metricScalarAt (localPullMetric hm φ hφ) y| <
            ε) →
        (Nonempty (SpatialNeck hm (neckModelTolerance alpha) (φ x)) ∨
          (∃ w : Wm, Nonempty (SpatialNeck hm (neckModelTolerance alpha) w) ∧
            metricScalarAt hm (φ x) ≤ C * metricScalarAt hm w ∧
            metricScalarAt hm w ≤ C * metricScalarAt hm (φ x) ∧
            riemannianEDistOf hm (φ x) w <
              ENNReal.ofReal (C / Real.sqrt (metricScalarAt hm (φ x)))) ∨
          ∀ y ∈ connectedComponent (φ x), metricScalarAt hm y ≤ C * metricScalarAt hm (φ x)) →
        Nonempty (SpatialNeck g (2 * alpha) (x : M)) ∨
          (∃ w : M, Nonempty (SpatialNeck g (2 * alpha) w) ∧
            metricScalarAt g (x : M) ≤ 4 * max C 1 * metricScalarAt g w) ∨
          ∀ y ∈ connectedComponent (φ x), metricScalarAt hm y ≤ C * metricScalarAt hm (φ x) := by
  set C' := max C 1 with hC'_def
  have hC' : 1 ≤ C' := le_max_right _ _
  have hCle : C ≤ C' := le_max_left _ _
  set r₀ := a / (2 * C') with hr₀_def
  set r₁ := 2 * C' * a with hr₁_def
  have hr₀ : 0 < r₀ := by positivity
  obtain ⟨D, δ, η, hD, hδ, hη, hNT⟩ :=
    exists_neck_transfer_of_edist_lt (r₀ := r₀) (r₁ := r₁) halpha hsmall hr₀
  set ε := min η (a / (8 * C')) with hε_def
  have hε : 0 < ε := lt_min hη (by positivity)
  have hεη : ε ≤ η := min_le_left _ _
  have hεa : ε ≤ a / (8 * C') := min_le_right _ _
  have hεa' : ε ≤ a / 8 := hεa.trans (div_le_div_of_nonneg_left ha.le (by norm_num)
    (by linarith))
  set eps := neckModelTolerance alpha with heps_def
  have heps0 : 0 < eps := neckModelTolerance_pos halpha
  set Dn := (D + 2 * eps⁻¹) / Real.sqrt r₀ with hDn_def
  have hDn : 0 ≤ Dn := by positivity
  set d := |C| / Real.sqrt (a / 2) with hd_def
  have hd : 0 ≤ d := by positivity
  set R := Real.sqrt 2 * (d + Dn + 1) with hR_def
  have hR : 0 < R := by positivity
  have hRρ : R / Real.sqrt 2 = d + Dn + 1 := by
    rw [hR_def]
    field_simp
  refine ⟨R, δ, ε, hR, hδ, hε, hεa', ?_⟩
  intro M _ _ _ _ _ g hg V _ Wm _ _ _ _ _ hm φ hφ hinj x hxa hball hquad hjet hscal halt
  have hscV : ∀ y : V, (y : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) →
      |metricScalarAt (g.restrictOpen V) y - metricScalarAt (localPullMetric hm φ hφ) y| < η :=
    fun y hy => (hscal y hy).trans_le hεη
  have hxball : (x : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) := by
    change riemannianEDistOf g (x : M) (x : M) ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hax : |a - metricScalarAt hm (φ x)| < ε := by
    have := hscal x hxball
    rwa [CheegerGromovCompactness.metricScalarAt_restrictOpen, metricScalarAt_localPull,
      hxa] at this
  have hz_lo : 7 * a / 8 < metricScalarAt hm (φ x) := by linarith [(abs_lt.mp hax).2]
  have hz_hi : metricScalarAt hm (φ x) < 9 * a / 8 := by linarith [(abs_lt.mp hax).1]
  have hr0a : r₀ ≤ a / 2 := div_le_div_of_nonneg_left ha.le (by norm_num) (by linarith)
  rcases halt with hnk | ⟨v, hnkv, hzv, hvz, hdist⟩ | hwhole
  · obtain ⟨nk⟩ := hnk
    have hzr1 : metricScalarAt hm (φ x) ≤ r₁ := by nlinarith
    obtain ⟨w, hwz, -, hnkw⟩ := hNT g hg V hm φ hφ hinj x hR hball hquad hjet hscV nk
      (by linarith) hzr1 (d := 1) (by
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.mpr one_pos) (by rw [hRρ]; linarith)
    left
    rw [hinj hwz] at hnkw
    exact hnkw
  · obtain ⟨nk⟩ := hnkv
    have hv0 : 0 ≤ metricScalarAt hm v :=
      (pos_of_mul_pos_right (lt_of_lt_of_le (by linarith) hzv) (by linarith)).le
    have hzC : metricScalarAt hm (φ x) ≤ C' * metricScalarAt hm v :=
      hzv.trans (mul_le_mul_of_nonneg_right hCle hv0)
    have hvr0 : r₀ ≤ metricScalarAt hm v := by
      rw [hr₀_def, div_le_iff₀ (by positivity)]
      nlinarith
    have hvr1 : metricScalarAt hm v ≤ r₁ := by
      have h1 : metricScalarAt hm v ≤ C' * metricScalarAt hm (φ x) :=
        hvz.trans (mul_le_mul_of_nonneg_right hCle (by linarith))
      rw [hr₁_def]
      nlinarith
    have hdist' : riemannianEDistOf hm (φ x) v < ENNReal.ofReal d := by
      refine hdist.trans_le (ENNReal.ofReal_le_ofReal ?_)
      have hsa : Real.sqrt (a / 2) ≤ Real.sqrt (metricScalarAt hm (φ x)) :=
        Real.sqrt_le_sqrt (by linarith)
      have hsa0 : 0 < Real.sqrt (a / 2) := Real.sqrt_pos.mpr (by positivity)
      exact (div_le_div_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left (abs_nonneg C) hsa0 hsa)
    obtain ⟨w, hwv, hwball, hnkw⟩ := hNT g hg V hm φ hφ hinj x hR hball hquad hjet hscV nk
      hvr0 hvr1 hdist' (by rw [hRρ]; linarith)
    right
    left
    refine ⟨(w : M), hnkw, ?_⟩
    have hwK : (w : M) ∈ riemannianClosedBallOf g (x : M) (2 * R) :=
      riemannianClosedBallOf_mono _ _ (by linarith) hwball
    have hw_sc := hscal w hwK
    rw [CheegerGromovCompactness.metricScalarAt_restrictOpen, metricScalarAt_localPull,
      hwv] at hw_sc
    rw [hxa]
    exact le_four_mul_of_near_neck_scalars ha hC' hax hzC hw_sc hvr0 hεa
  · exact Or.inr (Or.inr hwhole)

section PointedWitnessTransferMain

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance opensSigmaCompactTransferMain {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem neck_alternatives_of_local_flow_limit {alpha : ℝ} (halpha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11)
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) (hconn : ConnectedSpace P.M) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j)
    {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hcomplete : ∀ t ≤ 0, RiemannianMetricComplete (G t)) {E : ℕ → Set ℝ}
    (hEreg : ∀ s ≤ 0, ∀ᶠ n in atTop, s ∉ E n) {q C2 : ℝ} (hC2 : 1 ≤ C2)
    (hW : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n → ∀ z : W k n,
      (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      q < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        ∀ y ∈ connectedComponent z, metricScalarAt (h k n s) y ≤ C2 * metricScalarAt (h k n s) z) :
    ∀ s ≤ 0, ∀ x : P.M, 4 * max q 1 < metricScalarAt (G s) x →
      Nonempty (SpatialNeck (G s) (2 * alpha) x) ∨
      (∃ w : P.M, Nonempty (SpatialNeck (G s) (2 * alpha) w) ∧
        metricScalarAt (G s) x ≤ 4 * max C2 1 * metricScalarAt (G s) w) ∨
      ∀ y : P.M, metricScalarAt (G s) y ≤ 4 * max C2 1 * metricScalarAt (G s) x := by
  intro s hs x hxq
  set a := metricScalarAt (G s) x with ha_def
  set C2' := max C2 1 with hC2'_def
  have hC2' : 1 ≤ C2' := le_max_right _ _
  have hC2le : C2 ≤ C2' := le_max_left _ _
  have ha : 0 < a := by linarith [le_max_right q 1]
  have hqa : q < a / 4 := by linarith [le_max_left q 1]
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hgs := hcomplete s hs
  obtain ⟨R, δ, ε, hR, hδ, hε, hεa, hcore⟩ :=
    exists_neck_alternatives_transfer_constants.{w} halpha hsmall hC2 ha
  have hcpt2R : IsCompact (riemannianClosedBallOf (G s) x (2 * R)) :=
    RiemannianMetricComplete.closedEBall_isCompact hgs x (2 * R)
  obtain ⟨k₁, hk₁⟩ := hcpt2R.elim_directed_cover (fun k => (V k : Set P.M))
    (fun k => (V k).isOpen) (fun z _ => mem_iUnion.mpr (hVcover z)) hVmono.directed_le
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge (-s)
  set k₀ := max k₁ k₂ with hk₀_def
  have hball_k : ∀ k, k₀ ≤ k → riemannianClosedBallOf (G s) x (2 * R) ⊆ V k :=
    fun k hk => hk₁.trans (hVmono ((le_max_left _ _).trans hk))
  have hxself : x ∈ riemannianClosedBallOf (G s) x (2 * R) := by
    change riemannianEDistOf (G s) x x ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hxmem : ∀ k, k₀ ≤ k → x ∈ V k := fun k hk => hball_k k hk hxself
  have hs_k : ∀ k, k₀ ≤ k → s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 := by
    intro k hk
    refine ⟨?_, hs⟩
    have : (k₂ : ℝ) ≤ k := by exact_mod_cast (le_max_right k₁ k₂).trans hk
    push_cast
    linarith
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  let seq : ∀ k, ℕ → SmoothRiemannianMetric I3 (V k) := fun k i =>
    if hi : N k ≤ ψ i then localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    else (G s).restrictOpen (V k)
  have hseq_eq : ∀ k i (hi : N k ≤ ψ i),
      seq k i = localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi) :=
    fun k i hi => dite_eq_left hi
  have hconvk : ∀ k, k₀ ≤ k → MetricCInfConvergenceOnCompacts (seq k)
      ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := fun k hk =>
    metricCInfConvergenceOnCompacts_localPull_of_local_flow_limit hconv k (hs_k k hk)
  have hlimpt : ∀ k (hk : k₀ ≤ k) (y : V k), Tendsto (fun i => metricScalarAt (seq k i) y)
      atTop (𝓝 (metricScalarAt (G s) y)) := by
    intro k hk y
    have hu := ((hconvk k hk {y} isCompact_singleton 2).tendstoUniformlyOn_metricScalarAt
      isCompact_singleton).tendsto_at (mem_singleton y)
    rwa [metricScalarAt_restrictOpen] at hu
  have hinj : ∀ k j (hj : N k ≤ j), Function.Injective (φ k j hj) := by
    intro k j hj z z' hzz
    have h1 : F.map j z = F.map j z' := by
      rw [← hφF k j hj z, ← hφF k j hj z', hzz]
    exact Subtype.ext ((F.partialDiffeomorph j).injOn (hVF k j hj z.2) (hVF k j hj z'.2) h1)
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  let WholeType : ∀ k, V k → ℕ → Prop := fun k xk i => ∃ hi : N k ≤ ψ i,
    ∀ y ∈ connectedComponent xk, metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi y) ≤
      C2' * metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi xk)
  by_cases hwhole : ∀ k (hk : k₀ ≤ k), ∀ᶠ i in atTop, WholeType k ⟨x, hxmem k hk⟩ i
  · refine Or.inr (Or.inr fun y => ?_)
    let _ : PathConnectedSpace P.M := by
      let _ : LocallyPathConnectedSpace P.M :=
        ChartedSpace.locallyPathConnectedSpace ThreeSpace P.M
      exact pathConnectedSpace_iff_connectedSpace.mpr hconn
    obtain ⟨k, hk, hxk, hyk, hcomp⟩ :=
      exists_mem_connectedComponent_of_monotone_cover hVmono hVcover x y k₀
    have hle : metricScalarAt (G s) y ≤ C2' * a := by
      refine le_of_tendsto_of_tendsto (hlimpt k hk ⟨y, hyk⟩)
        ((hlimpt k hk ⟨x, hxk⟩).const_mul C2') ?_
      filter_upwards [hwhole k hk] with i ⟨hi, hbound⟩
      rw [hseq_eq k i hi, metricScalarAt_localPull, metricScalarAt_localPull]
      exact hbound ⟨y, hyk⟩ hcomp
    have h4 : C2' * a ≤ 4 * C2' * a := by nlinarith
    exact hle.trans h4
  push Not at hwhole
  obtain ⟨k, hk, hfreq⟩ := hwhole
  set xk : V k := ⟨x, hxmem k hk⟩ with hxk_def
  let Kbig : Set (V k) := Subtype.val ⁻¹' riemannianClosedBallOf (G s) x (2 * R)
  have hKbig : IsCompact Kbig := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' Kbig = riemannianClosedBallOf (G s) x (2 * R) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hball_k k hk hz⟩, hz, rfl⟩
    rw [himg]
    exact hcpt2R
  have hunif := (hconvk k hk Kbig hKbig 2).tendstoUniformlyOn_metricScalarAt hKbig
  have hquad := (hconvk k hk Kbig hKbig 0).eventually_quadratic_bounds hKbig
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hjet := eventually_metricDerivNorm_swap_le (hconvk k hk) hKbig ⌈(2 * alpha)⁻¹⌉₊ hδ
  have hkr : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := by positivity
  have himage := F.eventually_image_closed_ball_subset Cd href hPc P.basepoint hkr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  have hxball : x ∈ riemannianClosedBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2) := by
    have hx' : x ∈ (V k : Set P.M) := xk.2
    rw [hV] at hx'
    exact (show riemannianEDistOf P.metric P.basepoint x < _ from hx').le
  obtain ⟨i, hnot, hi, ⟨hWi, hsE⟩, himg, hsc, hq2, hj⟩ := (hfreq.and_eventually
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      ((hfψ.eventually ((hW k).and (hEreg s hs))).and ((hψ.tendsto_atTop.eventually himage).and
        ((Metric.tendstoUniformlyOn_iff.mp hunif ε hε).and (hquad.and hjet)))))).exists
  have hseq := hseq_eq k i hi
  have hzball : ((φ k (ψ i) hi xk : W k (f (ψ i))) : (X.obj (f (ψ i))).M) ∈
      riemannianClosedBallOf (X.obj (f (ψ i))).metric (X.obj (f (ψ i))).basepoint
        ((k + 1 : ℕ) : ℝ) := by
    rw [hφF]
    have h1 := himg.2 ⟨x, hxball, rfl⟩
    have hb : F.map (ψ i) P.basepoint = (X.obj (f (ψ i))).basepoint := F.basepoint_map (ψ i)
    rw [hb] at h1
    exact riemannianClosedBallOf_mono _ _ (by linarith) h1
  have hzpos : a / 2 < metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi xk) := by
    have h1 := hsc xk hxself
    rw [Real.dist_eq, hseq, metricScalarAt_localPull, metricScalarAt_restrictOpen] at h1
    have h2 := (abs_lt.mp h1).2
    have h3 : metricScalarAt (G s) x = a := rfl
    linarith
  have hzq : q < metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi xk) := by linarith
  have halt := hWi s (hs_k k hk) hsE _ hzball hzq
  have hcases := hcore (G s) hgs (V k) (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi)
    (hinj k (ψ i) hi) xk rfl (hball_k k hk)
    (fun y hy v => by
      have h1 := ((hq2 y hy v).1)
      rw [hseq] at h1
      linarith)
    (fun y hy r hr => by
      have h1 := hj y hy r hr
      rw [hseq] at h1
      exact h1)
    (fun y hy => by
      have h1 := hsc y hy
      rw [Real.dist_eq, hseq] at h1
      exact h1)
    halt
  rcases hcases with h1 | h2 | hdomb
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine absurd ⟨hi, fun y hy => ?_⟩ hnot
    have hy' : φ k (ψ i) hi y ∈ connectedComponent (φ k (ψ i) hi xk) :=
      ((isPreconnected_connectedComponent.image _
        (hφ k (ψ i) hi).contMDiff.continuous.continuousOn).subset_connectedComponent
          ⟨xk, mem_connectedComponent, rfl⟩) ⟨y, hy, rfl⟩
    have hz0 : 0 ≤ metricScalarAt (h k (f (ψ i)) s) (φ k (ψ i) hi xk) := by linarith
    exact (hdomb _ hy').trans (mul_le_mul_of_nonneg_right hC2le hz0)

end PointedWitnessTransferMain

section PointedBoundedCurvature

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

universe w

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance opensSigmaCompactBounded {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : Opens Y) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)

theorem exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ {X : PointedRiemannianSeq.{w, 0, 0} I3}
      {P : PointedRiemannianManifold.{w, 0, 0} I3} {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ}, StrictMono f →
      ∀ (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F),
      (∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n) →
      MetricComplete P → ConnectedSpace P.M → ∀ {V : ℕ → Opens P.M},
      (∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) →
      ∀ {N : ℕ → ℕ}, (∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) →
      ∀ {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
        {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)},
      (∀ k j (hj : N k ≤ j) (z : V k),
        ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z) →
      ∀ {G : ℝ → SmoothRiemannianMetric I3 P.M}, G 0 = P.metric →
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.infiniteClosed 0 0 le_rfl)) →
      ∀ {ψ : ℕ → ℕ}, StrictMono ψ →
      (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) →
      (∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
        SolutionOn (I := I3) (M := W k n)
          (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
            (neg_nonpos.mpr (Nat.cast_nonneg _))))) →
      ∀ {Q : ℕ → ℝ}, Tendsto Q atTop atTop → ∀ {Phi : ℝ → ℝ}, AdmissiblePinchingFunction Phi →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
          (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x))) →
      ∀ {E : ℕ → Set ℝ}, (∀ n, (E n).Finite) → (∀ s ≤ 0, ∀ᶠ n in atTop, s ∉ E n) →
      ∀ {eps qW C2 qD Ctime : ℝ}, 0 < eps → eps ≤ epsW → 1 ≤ C2 →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n → ∀ z : W k n,
        (z : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
        qW < metricScalarAt (h k n s) z →
        Nonempty (SpatialNeck (h k n s) eps z) ∨
          (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
            metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
            metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
            riemannianEDistOf (h k n s) z w <
              ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
          ∀ y ∈ connectedComponent z,
            metricScalarAt (h k n s) y ≤ C2 * metricScalarAt (h k n s) z) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-((k + 2 : ℕ) : ℝ)) 0, s ∉ E n → ∀ z : W k n,
        qD < metricScalarAt (h k n s) z →
          |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
            Ctime * metricScalarAt (h k n s) z ^ 2) →
      ∃ C : ℝ, ∀ t ≤ 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C := by
  obtain ⟨η₀, hη₀, hslice⟩ :=
    exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives.{w}
  set alpha := min (η₀ / 2) (1 / 44) with halpha_def
  have halpha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have h2α : 2 * alpha ≤ η₀ := by
    have := min_le_left (η₀ / 2) (1 / 44 : ℝ)
    linarith
  have hsmall : 2 * alpha < 1 / 11 := by
    have := min_le_right (η₀ / 2) (1 / 44 : ℝ)
    linarith
  have hnmt : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  refine ⟨neckModelTolerance alpha, neckModelTolerance_pos halpha, ?_⟩
  intro X P W h f hf F Cd hcan hPc hconn V hV N hVF φ hφ hφF G hG0 hGsol ψ hψ hconv hsol Q hQ
    Phi hPhi hpinch E hEfin hEreg eps qW C2 qD Ctime heps hle hC2 hW hderiv
  obtain ⟨hcone, hcomplete⟩ :=
    ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete hf hPc hconn hV hG0
      hGsol hψ hconv hQ hPhi hpinch
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hW' : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, s ∉ E n →
      ∀ z : W k n, (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 1 : ℕ) : ℝ) →
      qW < metricScalarAt (h k n s) z →
      Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) z) ∨
        (∃ w : W k n, Nonempty (SpatialNeck (h k n s) (neckModelTolerance alpha) w) ∧
          metricScalarAt (h k n s) z ≤ C2 * metricScalarAt (h k n s) w ∧
          metricScalarAt (h k n s) w ≤ C2 * metricScalarAt (h k n s) z ∧
          riemannianEDistOf (h k n s) z w <
            ENNReal.ofReal (C2 / Real.sqrt (metricScalarAt (h k n s) z))) ∨
        ∀ y ∈ connectedComponent z,
          metricScalarAt (h k n s) y ≤ C2 * metricScalarAt (h k n s) z := by
    intro k
    filter_upwards [hW k] with n hn s hs hsE z hz hq
    rcases hn s hs hsE z hz hq with hnk | ⟨w, hnk, h1⟩ | h3
    · obtain ⟨nk⟩ := hnk
      exact Or.inl ⟨nk.mono hle hnmt⟩
    · obtain ⟨nk⟩ := hnk
      exact Or.inr (Or.inl ⟨w, ⟨nk.mono hle hnmt⟩, h1⟩)
    · exact Or.inr (Or.inr h3)
  have halt := neck_alternatives_of_local_flow_limit halpha hsmall hf F Cd hcan hPc hconn hV
    hVF hφF hψ hconv hcomplete hEreg hC2 hW'
  let _ : ConnectedSpace P.M := hconn
  have hslices : ∀ t ≤ 0, ∃ C : ℝ, ∀ x : P.M, metricScalarAt (G t) x ≤ C := fun t ht =>
    hslice (G t) (hcomplete t ht) (hcone t ht) h2α (halt t ht)
  have hder := abs_derivWithin_scalar_le_of_local_flow_limit hf hVmono hVcover hGsol hψ hconv
    hsol hEfin hderiv
  exact exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_slice_bounds hGsol
    hcomplete hcone hslices hder

end PointedBoundedCurvature

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
