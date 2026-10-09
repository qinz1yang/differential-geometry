import DifferentialGeometry.Geometry.Comparison.AngleShortening
import DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngle

set_option autoImplicit false

open Set Filter Topology
open DifferentialGeometry.Toponogov (positiveRectangleValues CoordinatewiseNonincreasingOn
  tendsto_sSup_positiveRectangle)

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def limitingComparisonAngle {X : Type*} [MetricSpace X]
    (κ R S : ℝ) (γ β : ℝ → X) : ℝ :=
  sSup (positiveRectangleValues R S
    (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (β t))))

theorem comparisonAngleNegCurvature_antitone_on_segments
    {X : Type*} [MetricSpace X] {κ R S : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) {γ β : ℝ → X}
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist p (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist p (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|)
    (hγmem : ∀ s ∈ Ioc (0 : ℝ) R, γ s ∈ Ω)
    (hβmem : ∀ t ∈ Ioc (0 : ℝ) S, β t ∈ Ω) :
    CoordinatewiseNonincreasingOn R S
      (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (β t))) := by
  constructor
  · intro s₁ s₂ t hs₁ hs₂ ht hle
    have h := comparisonAngleNegCurvature_le_of_shortening_left hκ hcomp hp
      (hγmem s₁ hs₁) (hγmem s₂ hs₂) (hβmem t ht)
      (by rw [hγrad s₁ hs₁]; exact hs₁.1)
      (dist_pos.mp (show 0 < dist p (β t) by rw [hβrad t ht]; exact ht.1)).symm
      (by rw [hγrad s₁ hs₁, hγrad s₂ hs₂, hγmin s₁ hs₁ s₂ hs₂,
          abs_of_nonpos (sub_nonpos.mpr hle)]; ring)
    simpa only [hγrad s₁ hs₁, hγrad s₂ hs₂, hβrad t ht] using h
  · intro s t₁ t₂ hs ht₁ ht₂ hle
    have h := comparisonAngleNegCurvature_le_of_shortening_right hκ hcomp hp
      (hβmem t₁ ht₁) (hβmem t₂ ht₂) (hγmem s hs)
      (by rw [hβrad t₁ ht₁]; exact ht₁.1)
      (dist_pos.mp (show 0 < dist p (γ s) by rw [hγrad s hs]; exact hs.1)).symm
      (by rw [hβrad t₁ ht₁, hβrad t₂ ht₂, hβmin t₁ ht₁ t₂ ht₂,
          abs_of_nonpos (sub_nonpos.mpr hle)]; ring)
    simpa only [hβrad t₁ ht₁, hβrad t₂ ht₂, hγrad s hs] using h

theorem limitingComparisonAngle_mem_Icc {X : Type*} [MetricSpace X]
    {κ R S : ℝ} (γ β : ℝ → X) (hR : 0 < R) (hS : 0 < S) :
    limitingComparisonAngle κ R S γ β ∈ Icc (0 : ℝ) Real.pi := by
  let T := positiveRectangleValues R S
    (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (β t)))
  have hne : T.Nonempty := ⟨_, R, ⟨hR, le_rfl⟩, S, ⟨hS, le_rfl⟩, rfl⟩
  have hB : BddAbove T := ⟨Real.pi, by
    rintro v ⟨s, hs, t, ht, rfl⟩
    exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2⟩
  exact ⟨(comparisonAngleNegCurvature_mem_Icc κ R S _).1.trans
    (le_csSup hB ⟨R, ⟨hR, le_rfl⟩, S, ⟨hS, le_rfl⟩, rfl⟩),
    csSup_le hne (by
      rintro v ⟨s, hs, t, ht, rfl⟩
      exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2)⟩

theorem comparisonAngleNegCurvature_le_limitingComparisonAngle
    {X : Type*} [MetricSpace X] {κ R S s t : ℝ} (γ β : ℝ → X)
    (hs : s ∈ Ioc (0 : ℝ) R) (ht : t ∈ Ioc (0 : ℝ) S) :
    comparisonAngleNegCurvature κ s t (dist (γ s) (β t)) ≤
      limitingComparisonAngle κ R S γ β := by
  apply le_csSup (show BddAbove (positiveRectangleValues R S
    (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (β t)))) from ?_)
    ⟨s, hs, t, ht, rfl⟩
  exact ⟨Real.pi, by rintro v ⟨u, hu, w, hw, rfl⟩
                     exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2⟩

theorem tendsto_limitingComparisonAngle_of_fourPointComparison
    {X : Type*} [MetricSpace X] {κ R S : ℝ} (hκ : 0 ≤ κ)
    (hR : 0 < R) (hS : 0 < S) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) {γ β : ℝ → X}
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist p (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist p (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|)
    (hγmem : ∀ s ∈ Ioc (0 : ℝ) R, γ s ∈ Ω)
    (hβmem : ∀ t ∈ Ioc (0 : ℝ) S, β t ∈ Ω) :
    Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (limitingComparisonAngle κ R S γ β)) := by
  apply tendsto_sSup_positiveRectangle hR hS
    (comparisonAngleNegCurvature_antitone_on_segments hκ hcomp hp
      hγrad hβrad hγmin hβmin hγmem hβmem)
  exact ⟨Real.pi, by rintro v ⟨s, hs, t, ht, rfl⟩
                     exact (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2⟩

theorem limitingComparisonAngle_comm {X : Type*} [MetricSpace X]
    (κ R S : ℝ) (γ β : ℝ → X) :
    limitingComparisonAngle κ R S γ β = limitingComparisonAngle κ S R β γ := by
  apply congrArg sSup
  ext v
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨t, ht, s, hs, by dsimp only; rw [comparisonAngleNegCurvature_comm, dist_comm]⟩
  · rintro ⟨t, ht, s, hs, rfl⟩
    exact ⟨s, hs, t, ht, by dsimp only; rw [comparisonAngleNegCurvature_comm, dist_comm]⟩

theorem limitingComparisonAngle_zero_eq_limitingRadialAngle
    {X : Type*} [MetricSpace X] {ι : Type*} (L : ι → ℝ) (γ : ι → ℝ → X) (i j : ι) :
    limitingComparisonAngle 0 (L i) (L j) (γ i) (γ j) =
      DifferentialGeometry.Toponogov.limitingRadialAngle L γ i j := by
  simp only [limitingComparisonAngle, comparisonAngleNegCurvature_zero,
    DifferentialGeometry.Toponogov.limitingRadialAngle]
  rfl

theorem limitingComparisonAngle_self {X : Type*} [MetricSpace X]
    {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) {γ : ℝ → X}
    (hmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|) :
    limitingComparisonAngle κ R R γ γ = 0 := by
  have heq : positiveRectangleValues R R
      (fun s t => comparisonAngleNegCurvature κ s t (dist (γ s) (γ t))) = {0} := by
    ext v
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      dsimp only
      rw [hmin s hs t ht, comparisonAngleNegCurvature_abs_sub hκ hs.1 ht.1]
      exact mem_singleton 0
    · intro hv
      rw [mem_singleton_iff] at hv
      subst v
      refine ⟨R, ⟨hR, le_rfl⟩, R, ⟨hR, le_rfl⟩, ?_⟩
      dsimp only
      rw [hmin R ⟨hR, le_rfl⟩ R ⟨hR, le_rfl⟩,
        comparisonAngleNegCurvature_abs_sub hκ hR hR]
  rw [limitingComparisonAngle, heq, csSup_singleton]

theorem limitingComparisonAngle_opposite {X : Type*} [MetricSpace X]
    {κ R S : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S) {γ β : ℝ → X}
    (hopp : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (γ s) (β t) = s + t) :
    limitingComparisonAngle κ R S γ β = Real.pi := by
  apply le_antisymm (limitingComparisonAngle_mem_Icc γ β hR hS).2
  have h := comparisonAngleNegCurvature_le_limitingComparisonAngle (κ := κ) γ β
    (show R ∈ Ioc (0 : ℝ) R from ⟨hR, le_rfl⟩)
    (show S ∈ Ioc (0 : ℝ) S from ⟨hS, le_rfl⟩)
  rwa [hopp R ⟨hR, le_rfl⟩ S ⟨hS, le_rfl⟩,
    comparisonAngleNegCurvature_add hκ hR hS] at h

theorem limitingComparisonAngle_restrict_of_fourPointComparison
    {X : Type*} [MetricSpace X] {κ R S r s : ℝ} (hκ : 0 ≤ κ)
    (hr : 0 < r) (hs : 0 < s) (hrR : r ≤ R) (hsS : s ≤ S) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) {γ β : ℝ → X}
    (hγrad : ∀ u ∈ Ioc (0 : ℝ) R, dist p (γ u) = u)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist p (β t) = t)
    (hγmin : ∀ u ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ u) (γ t) = |u - t|)
    (hβmin : ∀ u ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β u) (β t) = |u - t|)
    (hγmem : ∀ u ∈ Ioc (0 : ℝ) R, γ u ∈ Ω)
    (hβmem : ∀ t ∈ Ioc (0 : ℝ) S, β t ∈ Ω) :
    limitingComparisonAngle κ r s γ β = limitingComparisonAngle κ R S γ β := by
  have hsubR : Ioc (0 : ℝ) r ⊆ Ioc (0 : ℝ) R := Ioc_subset_Ioc_right hrR
  have hsubS : Ioc (0 : ℝ) s ⊆ Ioc (0 : ℝ) S := Ioc_subset_Ioc_right hsS
  exact tendsto_nhds_unique
    (tendsto_limitingComparisonAngle_of_fourPointComparison hκ hr hs hcomp hp
      (fun u hu => hγrad u (hsubR hu)) (fun t ht => hβrad t (hsubS ht))
      (fun u hu t ht => hγmin u (hsubR hu) t (hsubR ht))
      (fun u hu t ht => hβmin u (hsubS hu) t (hsubS ht))
      (fun u hu => hγmem u (hsubR hu)) (fun t ht => hβmem t (hsubS ht)))
    (tendsto_limitingComparisonAngle_of_fourPointComparison hκ (hr.trans_le hrR)
      (hs.trans_le hsS) hcomp hp hγrad hβrad hγmin hβmin hγmem hβmem)

theorem limitingComparisonAngle_sum_le_two_pi
    {X : Type*} [MetricSpace X] {ι : Type*} {κ : ℝ} (hκ : 0 ≤ κ)
    {L : ι → ℝ} (hL : ∀ i, 0 < L i) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) {γ : ι → ℝ → X}
    (hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), dist p (γ i s) = s)
    (hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t|)
    (hmem : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), γ i s ∈ Ω) (i j k : ι) :
    limitingComparisonAngle κ (L i) (L j) (γ i) (γ j) +
      limitingComparisonAngle κ (L j) (L k) (γ j) (γ k) +
      limitingComparisonAngle κ (L k) (L i) (γ k) (γ i) ≤ 2 * Real.pi := by
  have ht (a b : ι) : Tendsto (fun s : ℝ =>
      comparisonAngleNegCurvature κ s s (dist (γ a s) (γ b s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (limitingComparisonAngle κ (L a) (L b) (γ a) (γ b))) :=
    by
      have hjoint := tendsto_limitingComparisonAngle_of_fourPointComparison hκ (hL a) (hL b)
        hcomp hp (hrad a) (hrad b) (hmin a) (hmin b) (hmem a) (hmem b)
      have hdiag : Tendsto (fun s : ℝ => (s, s)) (𝓝[>] (0 : ℝ))
          (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) := tendsto_id.prodMk tendsto_id
      simpa only [Function.comp_def] using hjoint.comp hdiag
  apply le_of_tendsto (((ht i j).add (ht j k)).add (ht k i))
  filter_upwards [Ioc_mem_nhdsGT (hL i), Ioc_mem_nhdsGT (hL j), Ioc_mem_nhdsGT (hL k)]
    with s hi hj hk
  have hne (a : ι) (ha : s ∈ Ioc (0 : ℝ) (L a)) : γ a s ≠ p :=
    (dist_pos.mp (show 0 < dist p (γ a s) by rw [hrad a s ha]; exact ha.1)).symm
  have h := hcomp p hp (γ i s) (hmem i s hi) (γ j s) (hmem j s hj)
    (γ k s) (hmem k s hk) (hne i hi) (hne j hj) (hne k hk)
  simpa only [hrad i s hi, hrad j s hj, hrad k s hk] using h

theorem limitingComparisonAngle_adjacent_sum_le_pi
    {X : Type*} [MetricSpace X] {ι : Type*} {κ : ℝ} (hκ : 0 ≤ κ)
    {L : ι → ℝ} (hL : ∀ i, 0 < L i) {Ω : Set X}
    (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) {γ : ι → ℝ → X}
    (hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), dist p (γ i s) = s)
    (hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t|)
    (hmem : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), γ i s ∈ Ω) (i j k : ι)
    (hopp : ∀ s ∈ Ioc (0 : ℝ) (L k), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ k s) (γ i t) = s + t) :
    limitingComparisonAngle κ (L i) (L j) (γ i) (γ j) +
      limitingComparisonAngle κ (L j) (L k) (γ j) (γ k) ≤ Real.pi := by
  have h := limitingComparisonAngle_sum_le_two_pi hκ hL hcomp hp hrad hmin hmem i j k
  rw [limitingComparisonAngle_opposite hκ (hL k) (hL i) hopp] at h
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
