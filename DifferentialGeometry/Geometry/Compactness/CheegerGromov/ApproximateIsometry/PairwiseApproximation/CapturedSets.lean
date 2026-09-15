import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Relative
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

universe u uQ uE uF uH uH'
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {Q : Type uQ} [TopologicalSpace Q] [ChartedSpace H Q] [T2Space Q]
  [IsManifold I ∞ Q] [LocallyCompactSpace Q]
  {Y : ℕ → Type u} [∀ k, TopologicalSpace (Y k)] [∀ k, ChartedSpace H' (Y k)]
  [∀ k, T2Space (Y k)] [∀ k, IsManifold J ∞ (Y k)] [∀ k, SigmaCompactSpace (Y k)]

theorem eventually_pairwise_approximation_on_captured_sets
    (V U : TopologicalSpace.Opens Q) [SigmaCompactSpace U]
    (hV : IsCompact (closure (V : Set Q))) (hVU : closure (V : Set Q) ⊆ U)
    (q : Q) (hq : q ∈ V) (b : ∀ k, Y k)
    (g : ∀ k, SmoothRiemannianMetric J (Y k)) (gInf : SmoothRiemannianMetric I U)
    (G : ℕ → SmoothRiemannianMetric I U) (f : ∀ k, Q → Y k) (K : ∀ k, Set (Y k))
    (hG : ∀ᶠ k in atTop, ∀ (x : U) (v w : TangentSpace I x),
      (G k).inner x v w = (g k).inner (f k x)
        (mfderiv I J (f k) (x : Q) v) (mfderiv I J (f k) (x : Q) w))
    (hconv : MetricCInfConvergenceOnCompacts G gInf gInf)
    (hPhi : ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph I J Q (Y k) ∞,
      closure (U : Set Q) ⊆ Φ.source ∧ EqOn Φ (f k) Φ.source ∧
      Φ q = b k ∧ K k ⊆ Φ '' closure (V : Set Q)) :
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ p : ℕ,
      ∃ n₀ : ℕ, ∀ k l : ℕ, n₀ ≤ k → n₀ ≤ l →
        ∃ R : PartialDiffeomorph J J (Y k) (Y l) ∞,
          R (b k) = b l ∧ Nonempty (PartialDiffeomorphMetricApproximation (K k) eps p R (g k) (g l)) := by
  let L : Set U := Subtype.val ⁻¹' closure (V : Set Q)
  have hL : IsCompact L :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hV (by
      intro x hx
      exact ⟨⟨x, hVU hx⟩, rfl⟩)
  obtain ⟨T, hT, hVT, hTU⟩ := exists_compact_between hV U.isOpen hVU
  intro eps heps heps1 p
  obtain ⟨n₀, hn₀⟩ := hconv.eventually_relative_partial_diffeomorph_metric_approximation
    U G gInf g hL p heps heps1
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (hG.and hPhi)
  refine ⟨max n₀ n₁, ?_⟩
  intro k l hk hl
  have hk₀ : n₀ ≤ k := (Nat.le_max_left n₀ n₁).trans hk
  have hl₀ : n₀ ≤ l := (Nat.le_max_left n₀ n₁).trans hl
  have hk₁ : n₁ ≤ k := (Nat.le_max_right n₀ n₁).trans hk
  have hl₁ : n₁ ≤ l := (Nat.le_max_right n₀ n₁).trans hl
  obtain ⟨hGk, Φ, hclUΦ, hΦf, hΦq, hcapΦ⟩ := hn₁ k hk₁
  obtain ⟨hGl, Ψ, hclUΨ, hΨf, hΨq, hcapΨ⟩ := hn₁ l hl₁
  have hUΦ : (U : Set Q) ⊆ Φ.source := subset_closure.trans hclUΦ
  have hUΨ : (U : Set Q) ⊆ Ψ.source := subset_closure.trans hclUΨ
  have hGΦ : ∀ (z : U) (v w : TangentSpace I z),
      (G k).inner z v w = (g k).inner (Φ z)
        (mfderiv I J (Φ : Q → Y k) (z : Q) v) (mfderiv I J (Φ : Q → Y k) (z : Q) w) := by
    intro z v w
    have heq : (Φ : Q → Y k) =ᶠ[𝓝 (z : Q)] f k :=
      Filter.eventuallyEq_of_mem (Φ.open_source.mem_nhds (hUΦ z.property)) hΦf
    rw [heq.eq_of_nhds, heq.mfderiv_eq]
    exact hGk z v w
  have hGΨ : ∀ (z : U) (v w : TangentSpace I z),
      (G l).inner z v w = (g l).inner (Ψ z)
        (mfderiv I J (Ψ : Q → Y l) (z : Q) v) (mfderiv I J (Ψ : Q → Y l) (z : Q) w) := by
    intro z v w
    have heq : (Ψ : Q → Y l) =ᶠ[𝓝 (z : Q)] f l :=
      Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds (hUΨ z.property)) hΨf
    rw [heq.eq_of_nhds, heq.mfderiv_eq]
    exact hGl z v w
  have hK' : IsCompact ((Φ : Q → Y k) '' T) :=
    hT.image_of_continuousOn (Φ.contMDiffOn.continuousOn.mono (hTU.trans hUΦ))
  have hKK' : K k ⊆ interior ((Φ : Q → Y k) '' T) :=
    hcapΦ.trans ((image_mono hVT).trans
      (interior_maximal (image_mono interior_subset)
        (Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
          (interior_subset.trans (hTU.trans hUΦ)))))
  have hsrc : (Φ : Q → Y k) '' T ⊆ (Φ.symm.trans Ψ).source := by
    rintro y ⟨x, hx, rfl⟩
    change Φ x ∈ Φ.target ∧ Φ.symm (Φ x) ∈ Ψ.source
    refine ⟨Φ.map_source (hUΦ (hTU hx)), ?_⟩
    rw [_root_.PartialDiffeomorph.symm_apply_apply Φ (hUΦ (hTU hx))]
    exact hUΨ (hTU hx)
  have hcapture : K k ⊆ (fun z : U => (Φ : Q → Y k) z) '' L := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hcapΦ hy
    exact ⟨⟨z, hVU hz⟩, hz, rfl⟩
  refine ⟨Φ.symm.trans Ψ, ?_, hn₀ k hk₀ l hl₀ Φ Ψ hUΦ hUΨ hGΦ hGΨ
    (K k) ((Φ : Q → Y k) '' T) hK' hKK' hsrc hcapture⟩
  rw [← hΦq, _root_.PartialDiffeomorph.trans_apply,
    _root_.PartialDiffeomorph.symm_apply_apply Φ (hUΦ (hVU (subset_closure hq))), hΨq]

end DifferentialGeometry.CheegerGromovCompactness
