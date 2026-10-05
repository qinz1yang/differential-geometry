import DifferentialGeometry.Topology.VectorBundle.FrameTrivialization
import DifferentialGeometry.Topology.VectorBundle.NormPreservingDisc
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport

/-!
# Consumers of the LFR51 bundle kernels: the point row on the actual sublevel

Frozen blueprint master207A, LFR51 (lines 29309–29378), row `{*} | ℝ³ | D³`, as consumed by LFR54
(lines 29526–29565): the actual radial sublevel `D_T = {‖(e⁻¹ x).2‖ ≤ T}` of a carrier `N` that is
identified with a smooth Riemannian bundle over a one-point soul is diffeomorphic, with boundary,
to the closed unit disc bundle of the trivial bundle `{*} × ℝᵏ`, through the SAME map `e`
(`exists_discCore_diffeomorph_trivial_of_subsingleton`). The bundle-level form is
`exists_normClosedDisc_diffeomorph_trivial_of_subsingleton`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]

/-- The trivial model `B × ℝᵏ` has the total dimension of the bundle. -/
theorem finrank_prod_euclidean_eq {m k : ℕ} (hk : Module.finrank ℝ F = k)
    (hd : Module.finrank ℝ (EB × F) = m + 1) :
    Module.finrank ℝ (EB × EuclideanSpace ℝ (Fin k)) = m + 1 := by
  rw [← hd, Module.finrank_prod, Module.finrank_prod, finrank_euclideanSpace_fin, hk]

/-- **LFR51 point row, disc form.** Over a base with at most one point, the closed unit disc
bundle of any smooth Riemannian bundle is diffeomorphic, with boundary, to that of the trivial
bundle `B × ℝᵏ`, fibrewise over the base. -/
theorem exists_normClosedDisc_diffeomorph_trivial_of_subsingleton [Subsingleton B] {m k : ℕ}
    (hk : Module.finrank ℝ F = k) (hd : Module.finrank ℝ (EB × F) = m + 1) :
    letI := normClosedDiscBundleChartedSpace (IB := IB)
      (V := Trivial B (EuclideanSpace ℝ (Fin k))) (finrank_prod_euclidean_eq hk hd) 1 one_pos
    letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace (EuclideanSpace ℝ (Fin k)) (Trivial B (EuclideanSpace ℝ (Fin k))) //
        ‖z.2‖ ≤ 1}
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞,
      ∀ z, (Ψ z).val.proj = z.val.proj ∧ ‖(Ψ z).val.2‖ = ‖z.val.2‖ := by
  obtain ⟨Φ, hΦp, hΦn⟩ :=
    exists_normPreserving_trivialization_of_subsingleton (IB := IB) (V := V) hk
  obtain ⟨Ψ, hΨ, -⟩ := exists_normClosedDisc_diffeomorph_of_norm_eq
    (finrank_prod_euclidean_eq hk hd) hd Φ hΦn 1 one_pos
  refine ⟨Ψ, fun z => ?_⟩
  rw [hΨ]
  exact ⟨hΦp z.val, hΦn z.val⟩

/-- **LFR51 point row on the actual sublevel (LFR54 consumer).** If `e` identifies a carrier `N`
with a smooth Riemannian bundle over a one-point base, every actual sublevel
`D_T = {‖(e⁻¹ x).2‖ ≤ T}`, `T > 0`, with its transported boundary charts, is diffeomorphic to the
closed unit disc bundle of `{*} × ℝᵏ`; the transported radius is `T` times the model radius. -/
theorem exists_discCore_diffeomorph_trivial_of_subsingleton [Subsingleton B] {m k : ℕ}
    (hk : Module.finrank ℝ F = k) (hd : Module.finrank ℝ (EB × F) = m + 1)
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T) :
    letI := normClosedDiscBundleChartedSpace (IB := IB)
      (V := Trivial B (EuclideanSpace ℝ (Fin k))) (finrank_prod_euclidean_eq hk hd) 1 one_pos
    letI := discCoreChartedSpace e hd T hT
    ∃ Ψ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {z : TotalSpace (EuclideanSpace ℝ (Fin k)) (Trivial B (EuclideanSpace ℝ (Fin k))) //
        ‖z.2‖ ≤ 1}
      {x : N // ‖(e.symm x).2‖ ≤ T} ∞,
      ∀ z, ‖(e.symm (Ψ z).val).2‖ = T * ‖z.val.2‖ := by
  let := normClosedDiscBundleChartedSpace (IB := IB)
    (V := Trivial B (EuclideanSpace ℝ (Fin k))) (finrank_prod_euclidean_eq hk hd) 1 one_pos
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
  let := discCoreChartedSpace e hd T hT
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_normClosedDisc_diffeomorph_trivial_of_subsingleton
    (IB := IB) (V := V) hk hd
  refine ⟨Ψ₀.trans (unitDiscCoreDiffeomorph e hd T hT), fun z => ?_⟩
  change ‖(e.symm (unitDiscCoreDiffeomorph e hd T hT (Ψ₀ z)).val).2‖ = _
  rw [unitDiscCoreDiffeomorph_apply, e.symm_apply_apply]
  change ‖T • (Ψ₀ z).val.2‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT, (hΨ₀ z).2]

end DifferentialGeometry.Topology.VectorBundle
