import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierComparisonMaps
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierRechartApplications

/-!
# LFR49 noncompact branch, item (a): the carrier package (lane LFR49-FIN, group G1)

The binding interface (a) of LFR49's assembly (`build-logs/scratch/LFR49/Assembly.lean`), frozen
by LFR49-A with `6 ≤ r` (the original `3 ≤ r` is false: `e^*G` is only `C^{r-3}`).

`lfr49A_carrier_package`: for a finite model `(N, G)` over `E3` (`G ∈ C^{r+1}`, `6 ≤ r`, a
Riemannian manifold for `G`, proper) with smooth comparison maps `jN` in T4's shape (LFR48's
output), a smooth Riemannian bundle `V → B` with `dim EB + dim F = 3`, LFR46's `C^{r-2}`
diffeomorphism `e : TotalSpace F V ≃ N` and LFR47's smooth generator `W` on
`TransportedCarrier e` with `du(W) = 1` beyond `ℓ`: the re-charted carrier `N'` over `E3`
(LFR49-A's `CarrierRechart e Λ` for a linear `Λ : EB × F ≃L E3`) with the transported metric
`G' ∈ C^{(r-4)+1}`, the isometry `κ : N' ≃ᵢ N` (`C¹`, `G' = κ^* G`), the SMOOTH
`D' : TotalSpace F V ≃ N'` with `κ ∘ D' = e`, the smooth push-forward `W'` of `W` with
`dκ W' = d(id) W` and `du'(W') = 1` beyond `ℓ`, and SMOOTH comparison maps `jt` from `N'` with
`jt i (κ⁻¹ q) = jN i q` for every `i` and T4's clauses.

Deviation from the frozen form (strengthening): the hypothesis `hcover` on `jN` and the instance
arguments `[CompactSpace B]`, `[IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]` are not used (the
coverage of `jt` comes from LFR48) and are dropped; the verbatim frozen form is the `example` in
`CarrierPackageApplications.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology (TransportedCarrier)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section Package

variable {X : ℕ → Type} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
  [∀ i, IsManifold I3 ∞ (X i)] [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **(a) of LFR49's assembly: the carrier package** (`6 ≤ r`; the unused `hcover`,
`[CompactSpace B]` and `[IsContMDiffRiemannianBundle …]` of the frozen form dropped). -/
theorem lfr49A_carrier_package
    {N : Type} [MetricSpace N] [ProperSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace I3 x)] [IsRiemannianManifold I3 N]
    {r : ℕ∞} (hr : 6 ≤ r)
    (G : ContMDiffRiemannianMetric I3 ((r : ℕ∞ω) + 1) E3 (TangentSpace I3 : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I3 x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (jN : ∀ i, PartialDiffeomorph I3 I3 N (X i) ∞)
    (hexh : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ (jN i).source)
    (hconv : ∀ (x : N) (L : Set E3), IsCompact L → L ⊆ (extChartAt I3 x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((jN i : N → X i) ∘ (extChartAt I3 x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (jN i x) (jN i y) - dist x y| < ε)
    {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]
    (hdimP : Module.finrank ℝ EB + Module.finrank ℝ F = 3)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I3⟯ N)
    (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y)
    (hW : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)).tangent ∞
      (fun y => (⟨y, W y⟩ :
        TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph))))
    {ℓ : ℝ}
    (hdu : ∀ y, ℓ < ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        e.toHomeomorph).symm y).2‖ →
      mvfderiv (I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        (fun y' => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
          e.toHomeomorph).symm y').2‖) y (W y) = 1) :
    ∃ (N' : Type) (mN' : MetricSpace N') (cN' : ChartedSpace E3 N'),
      letI := mN'
      letI := cN'
      ∃ (_ : IsManifold I3 ∞ N') (_ : RiemannianBundle (fun y : N' => TangentSpace I3 y))
        (_ : IsRiemannianManifold I3 N') (r' : ℕ∞) (_ : 2 ≤ r')
        (G' : ContMDiffRiemannianMetric I3 ((r' : ℕ∞ω) + 1) E3 (TangentSpace I3 : N' → Type _))
        (κ : N' ≃ᵢ N) (D' : Diffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N' ∞)
        (W' : (y : N') → TangentSpace I3 y) (jt : ∀ i, PartialDiffeomorph I3 I3 N' (X i) ∞),
        ProperSpace N' ∧
        (∀ (y : N') (w : TangentSpace I3 y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G'.inner y w w))) ∧
        ContMDiff I3 I3 1 (κ : N' → N) ∧
        (∀ (y : N') (v w : TangentSpace I3 y), G'.inner y v w =
          G.inner (κ y) (mfderiv I3 I3 (κ : N' → N) y v) (mfderiv I3 I3 (κ : N' → N) y w)) ∧
        (∀ z, κ (D' z) = e z) ∧
        ContMDiff I3 (ModelWithCorners.tangent I3) ∞ (fun y => (⟨y, W' y⟩ : TangentBundle I3 N')) ∧
        (∀ y : N', mfderiv I3 I3 (κ : N' → N) y (W' y) =
          mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I3 (TransportedCarrier.identity e) ⟨κ y⟩
            (W ⟨κ y⟩)) ∧
        (∀ y : N', ℓ < ‖(D'.symm y).2‖ →
          mvfderiv (I := I3) (fun y' => ‖(D'.symm y').2‖) y (W' y) = 1) ∧
        (∀ i, κ.symm q ∈ (jt i).source ∧ jt i (κ.symm q) = jN i q) ∧
        (∀ K : Set N', IsCompact K → ∀ᶠ i in atTop, K ⊆ (jt i).source) ∧
        (∀ (x : N') (L : Set E3), IsCompact L → L ⊆ (extChartAt I3 x).target →
          MapCPConvergenceOn L 1
            (fun i => pullbackMetricCoefficients (g i) ((jt i : N' → X i) ∘ (extChartAt I3 x).symm))
            (chartCoeff G' x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball (κ.symm q) R, ∀ y ∈ ball (κ.symm q) R,
          |dist (jt i x) (jt i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (jt i (κ.symm q)) a ⊆ (jt i : N' → X i) '' ball (κ.symm q) b) := by
  -- the linear identification of the models
  have hfin : Module.finrank ℝ (EB × F) = Module.finrank ℝ E3 := by
    rw [Module.finrank_prod, hdimP, finrank_euclideanSpace_fin]
  obtain ⟨Λ⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hfin
  have instNZ_LFR49FIN : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  -- the carrier, its metric and its isometry onto `N`
  have hmn := carrierRechart_order_le r
  have hms := carrierRechart_order_add_one_le (le_trans (by norm_num) hr : (4 : ℕ∞) ≤ r)
  set G' := CarrierRechart.metric Λ e G hmn hms with hG'
  let rb : RiemannianBundle
      (fun y : CarrierRechart e.toHomeomorph Λ => TangentSpace I3 y) := ⟨G'.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I3 (CarrierRechart e.toHomeomorph Λ) :=
    CarrierRechart.isRiemannianManifold Λ e G hmn hms hGnorm
  have hκ : (CarrierRechart.isometryEquiv e.toHomeomorph Λ : CarrierRechart e.toHomeomorph Λ → N) =
      CarrierRechart.identity Λ e := rfl
  have h1 : (1 : ℕ∞ω) ≤ ((r - 2 : ℕ∞) : ℕ∞ω) := le_trans le_add_self hms
  have hκ1 : ContMDiff I3 I3 1 (CarrierRechart.identity Λ e) :=
    (CarrierRechart.identity Λ e).contMDiff.of_le h1
  -- the comparison maps (LFR48 on the carrier)
  obtain ⟨jt, hjtpt, hjtexh, hjtconv, hjtdist, hjtcov⟩ :=
    CarrierRechart.exists_smooth_comparison_maps Λ e G hmn hms le_add_self g hmetric
      (WithTop.coe_le_coe.mpr le_top) jN q hexh hconv hdist
  -- the field
  set Ψ := CarrierRechart.ofTransported e.toHomeomorph Λ with hΨ
  have hinf : (∞ : ℕ∞ω) ≠ 0 := by simp
  refine ⟨CarrierRechart e.toHomeomorph Λ, inferInstance, inferInstance, inferInstance, rb, hRM,
    r - 4, carrierRechart_two_le_order hr, G', CarrierRechart.isometryEquiv e.toHomeomorph Λ,
    CarrierRechart.diffeomorph e.toHomeomorph Λ, pushField Ψ W, jt, inferInstance,
    CarrierRechart.enorm_eq Λ e G hmn hms, ?_, fun y v w => ?_, fun z => rfl,
    contMDiff_pushField Ψ hW, fun y => ?_, fun y hy => ?_, hjtpt, hjtexh, hjtconv, hjtdist,
    hjtcov⟩
  · rw [hκ]
    exact hκ1
  · rw [hκ]
    rfl
  · rw [hκ]
    have hd : MDifferentiableAt I3 I3 (CarrierRechart.identity Λ e) (Ψ ⟨y.point⟩) :=
      (hκ1 _).mdifferentiableAt one_ne_zero
    have hcomp : (CarrierRechart.identity Λ e : CarrierRechart e.toHomeomorph Λ → N) ∘ Ψ =
        TransportedCarrier.identity e := funext fun _ => rfl
    have h := mfderiv_pushField hinf Ψ W (CarrierRechart.identity Λ e) ⟨y.point⟩ hd
    rw [hcomp] at h
    exact h
  · set uT : TransportedCarrier e.toHomeomorph → ℝ := fun y' =>
      ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        e.toHomeomorph).symm y').2‖ with huT
    have h1' := hdu ⟨y.point⟩ hy
    have hdiff : MDifferentiableAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) uT ⟨y.point⟩ := by
      by_contra hnd
      have h0 := mfderiv_zero_of_not_mdifferentiableAt hnd
      rw [mvfderiv, ContinuousLinearMap.comp_apply, h0, zero_apply, map_zero] at h1'
      exact zero_ne_one h1'
    have hu : MDifferentiableAt I3 𝓘(ℝ, ℝ)
        (fun y' : CarrierRechart e.toHomeomorph Λ =>
          ‖((CarrierRechart.diffeomorph e.toHomeomorph Λ).symm y').2‖) (Ψ ⟨y.point⟩) := by
      have heq : (fun y' : CarrierRechart e.toHomeomorph Λ =>
          ‖((CarrierRechart.diffeomorph e.toHomeomorph Λ).symm y').2‖) = uT ∘ Ψ.symm :=
        funext fun _ => rfl
      have hs : MDifferentiableAt I3 (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) Ψ.symm (Ψ ⟨y.point⟩) :=
        Ψ.symm.mdifferentiable hinf _
      have hdiff' : MDifferentiableAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) uT
          (Ψ.symm (Ψ ⟨y.point⟩)) := by
        rw [Ψ.symm_apply_apply]
        exact hdiff
      rw [heq]
      exact hdiff'.comp (Ψ ⟨y.point⟩) hs
    have h := mvfderiv_pushField hinf Ψ W _ ⟨y.point⟩ hu
    exact h.trans h1'

end Package

end DifferentialGeometry.Geometry.Collapse
