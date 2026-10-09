import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionIntertwiner
import DifferentialGeometry.Analysis.InnerProductSpace.RealSpectralProjectionRegularity
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# S-BUNDLE: norm-preserving smoothing of a `C^k` field of orthogonal projections

Lane CMS-BUN (finite soul package, binding G3; consumed by row LFR47). Corrected interface after the
external review (§7 S-BUNDLE) and disposition D7:
* the base `S` is a HAUSDORFF (`[T2Space S]`) smooth manifold, σ-compact (compact in the frozen form);
* the smooth projection field `P̂` is within any prescribed `δ > 0` of `P` (`‖P̂ s - P s‖ < δ`);
* `P̂` is the spectral (Riesz) projection of a smooth self-adjoint approximant `A`, onto the
  eigenvalues in `ball 1 (1/2)` (the tree's `ContDiffOn.real_starProjection_eigenspace_ball_of_norm_sub_le`);
* the isometry is the WHOLE-SPACE orthogonal operator `B = T (T* T)^{-1/2}`,
  `T = P̂ P + (1 - P̂)(1 - P)` (`projIntertwiner`), of class `C^k`, with `B P = P̂ B`.

Main results: `exists_smooth_projection_and_orthogonal_intertwiner` (corrected, full output) and
`exists_smooth_projection_and_isometry` (the frozen D-CMS conclusions, with `[T2Space S]` added).
-/

set_option autoImplicit false

noncomputable section

open Metric Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Analysis.NearOneSqrt DifferentialGeometry.Analysis.ProjectionIntertwiner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A self-adjoint idempotent operator is the orthogonal projection onto its range. -/
theorem eq_starProjection_range_of_comp_self {P : F →L[ℝ] F} (hidem : P ∘L P = P)
    (hsymm : P.adjoint = P) : P = (LinearMap.range (P : F →ₗ[ℝ] F)).starProjection := by
  have hP : IsStarProjection P := ⟨hidem, ContinuousLinearMap.isSelfAdjoint_iff'.mpr hsymm⟩
  obtain ⟨_, h⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  exact h

/-- The spectral projection of an operator onto its eigenvalues in `ball 1 (1/2)`. -/
def spectralProjNearOne (A : F →L[ℝ] F) : F →L[ℝ] F :=
  (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace A.toLinearMap μ).starProjection

theorem spectralProjNearOne_comp_self (A : F →L[ℝ] F) :
    spectralProjNearOne A ∘L spectralProjNearOne A = spectralProjNearOne A :=
  Submodule.isIdempotentElem_starProjection _

theorem adjoint_spectralProjNearOne (A : F →L[ℝ] F) :
    (spectralProjNearOne A).adjoint = spectralProjNearOne A :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection _)

/-- Quantitative closeness of the spectral projection (tree supplier
`norm_real_starProjection_eigenspace_ball_sub_le`). -/
theorem norm_spectralProjNearOne_sub_le {A P : F →L[ℝ] F} (hA : A.adjoint = A)
    (hidem : P ∘L P = P) (hsymm : P.adjoint = P) (hclose : ‖A - P‖ ≤ 1 / 4) :
    ‖spectralProjNearOne A - P‖ ≤ 4 * ‖A - P‖ := by
  have hPK := eq_starProjection_range_of_comp_self hidem hsymm
  have hAsym : A.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (ContinuousLinearMap.isSelfAdjoint_iff'.mpr hA)
  rw [hPK] at hclose ⊢
  exact norm_real_starProjection_eigenspace_ball_sub_le A hAsym _ hclose

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {S : Type*} [TopologicalSpace S] [ChartedSpace HB S]

/-- Adapter of the tree's Riesz spectral projection to a manifold parameter: no Hausdorff or
compactness hypothesis is needed, only `‖A s - P s‖ < 1/8` against a continuous projection field. -/
theorem contMDiff_spectralProjNearOne {n : ℕ∞ω} {A P : S → F →L[ℝ] F}
    (hA : ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) n A) (hAs : ∀ s, (A s).adjoint = A s)
    (hP : Continuous P) (hidem : ∀ s, P s ∘L P s = P s) (hsymm : ∀ s, (P s).adjoint = P s)
    (hclose : ∀ s, ‖A s - P s‖ < 1 / 8) :
    ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) n (fun s => spectralProjNearOne (A s)) := by
  intro s₀
  set K := LinearMap.range (P s₀ : F →ₗ[ℝ] F) with hK
  have hPK : P s₀ = K.starProjection := eq_starProjection_range_of_comp_self (hidem s₀) (hsymm s₀)
  set t : Set (F →L[ℝ] F) :=
    {B | B.toLinearMap.IsSymmetric ∧ ‖B - K.starProjection‖ ≤ 1 / 4} with ht
  have hg : ContDiffOn ℝ n spectralProjNearOne t :=
    ContDiffOn.real_starProjection_eigenspace_ball_of_norm_sub_le (f := id) contDiffOn_id
      (fun B hB => hB.1) K (fun B hB => hB.2)
  set U : Set S := P ⁻¹' ball (P s₀) (1 / 8) with hU
  have hUn : U ∈ 𝓝 s₀ := hP.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (by norm_num))
  have hmaps : U ⊆ A ⁻¹' t := by
    intro s hs
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ContinuousLinearMap.isSelfAdjoint_iff'.mpr (hAs s)), ?_⟩
    rw [← hPK]
    have h1 := hclose s
    have h2 : ‖P s - P s₀‖ < 1 / 8 := by
      rw [← dist_eq_norm]
      exact hs
    calc ‖A s - P s₀‖ = ‖(A s - P s) + (P s - P s₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖A s - P s‖ + ‖P s - P s₀‖ := norm_add_le _ _
      _ ≤ 1 / 4 := by linarith
  have hs₀ : s₀ ∈ U := mem_ball_self (by norm_num)
  have hgA := (hg (A s₀) (hmaps hs₀)).comp_contMDiffWithinAt (hA s₀).contMDiffWithinAt hmaps
  exact hgA.contMDiffAt hUn

/-- Smooth self-adjoint uniform approximation of a continuous self-adjoint operator field on a
σ-compact Hausdorff smooth manifold (Mathlib's smooth partitions of unity). -/
theorem exists_contMDiff_selfAdjoint_approx [FiniteDimensional ℝ EB] [IsManifold IB ∞ S]
    [T2Space S] [SigmaCompactSpace S] {P : S → F →L[ℝ] F} (hP : Continuous P)
    (hsymm : ∀ s, (P s).adjoint = P s) {θ : ℝ} (hθ : 0 < θ) :
    ∃ A : S → F →L[ℝ] F, ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) ∞ A ∧ (∀ s, (A s).adjoint = A s) ∧
      ∀ s, ‖A s - P s‖ < θ := by
  have hconvSA : Convex ℝ {A : F →L[ℝ] F | IsSelfAdjoint A} := by
    intro x hx y hy a b _ _ _
    exact ((IsSelfAdjoint.all a).smul hx).add ((IsSelfAdjoint.all b).smul hy)
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const IB (n := ⊤)
    (t := fun s => ball (P s) θ ∩ {A : F →L[ℝ] F | IsSelfAdjoint A})
    (fun s => (convex_ball _ _).inter hconvSA)
    (fun s₀ => ⟨P s₀, by
      filter_upwards [hP.continuousAt (ball_mem_nhds (P s₀) hθ)] with s hs
      exact ⟨by rw [mem_ball, dist_comm]; exact hs,
        ContinuousLinearMap.isSelfAdjoint_iff'.mpr (hsymm s₀)⟩⟩)
  refine ⟨g, g.contMDiff, fun s => ContinuousLinearMap.isSelfAdjoint_iff'.mp (hg s).2, fun s => ?_⟩
  rw [← dist_eq_norm]
  exact (hg s).1

/-- **S-BUNDLE, corrected interface.** A `C^k` field of orthogonal projections on a σ-compact
Hausdorff smooth manifold has, for every `δ > 0`, a smooth field of orthogonal projections `P̂`
with `‖P̂ - P‖ < δ`, and a `C^k` field `B` of orthogonal operators of the whole space with
`B P = P̂ B` (hence equal ranks, norm preservation, and `B` maps `range P` onto `range P̂`). -/
theorem exists_smooth_projection_and_orthogonal_intertwiner [FiniteDimensional ℝ EB]
    [IsManifold IB ∞ S] [T2Space S] [SigmaCompactSpace S] {k : ℕ} (P : S → F →L[ℝ] F)
    (hP : ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) k P) (hidem : ∀ s, P s ∘L P s = P s)
    (hsymm : ∀ s, (P s).adjoint = P s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Phat : S → F →L[ℝ] F) (Bmap : S → F →L[ℝ] F),
      ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) ∞ Phat ∧ ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) k Bmap ∧
      (∀ s, ‖Phat s - P s‖ < δ) ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Bmap s ∘L P s = Phat s ∘L Bmap s) ∧
      (∀ s, (Bmap s).adjoint ∘L Bmap s = 1) ∧ (∀ s, Bmap s ∘L (Bmap s).adjoint = 1) ∧
      (∀ s v, ‖Bmap s v‖ = ‖v‖) ∧
      (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : F →ₗ[ℝ] F)) =
        Module.finrank ℝ (LinearMap.range (P s : F →ₗ[ℝ] F))) ∧
      (∀ s v, P s v = v → Phat s (Bmap s v) = Bmap s v) ∧
      (∀ s w, Phat s w = w → ∃ v, P s v = v ∧ Bmap s v = w) := by
  have hη : 0 < sqrtRadius (F →L[ℝ] F) := sqrtRadius_pos
  set c : ℝ := min (min δ 1) (Real.sqrt (sqrtRadius (F →L[ℝ] F))) with hc
  have hc0 : 0 < c := lt_min (lt_min hδ one_pos) (Real.sqrt_pos.mpr hη)
  obtain ⟨A, hA, hAs, hAP⟩ := exists_contMDiff_selfAdjoint_approx (IB := IB) hP.continuous hsymm
    (θ := min (1 / 8) (c / 4)) (lt_min (by norm_num) (by linarith))
  have hAP8 : ∀ s, ‖A s - P s‖ < 1 / 8 := fun s => lt_of_lt_of_le (hAP s) (min_le_left _ _)
  set Phat : S → F →L[ℝ] F := fun s => spectralProjNearOne (A s) with hPhatdef
  have hPhat : ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) ∞ Phat :=
    contMDiff_spectralProjNearOne hA hAs hP.continuous hidem hsymm hAP8
  have hclose : ∀ s, ‖Phat s - P s‖ < c := fun s => by
    have h4 := lt_of_lt_of_le (hAP s) (min_le_right _ _)
    calc ‖Phat s - P s‖ ≤ 4 * ‖A s - P s‖ :=
          norm_spectralProjNearOne_sub_le (hAs s) (hidem s) (hsymm s) (by linarith [hAP8 s])
      _ < c := by linarith
  have hδs : ∀ s, ‖Phat s - P s‖ < δ := fun s =>
    lt_of_lt_of_le (hclose s) ((min_le_left _ _).trans (min_le_left _ _))
  have h1s : ∀ s, ‖Phat s - P s‖ < 1 := fun s =>
    lt_of_lt_of_le (hclose s) ((min_le_left _ _).trans (min_le_right _ _))
  have hηs : ∀ s, ‖Phat s - P s‖ ^ 2 < sqrtRadius (F →L[ℝ] F) := fun s =>
    (Real.lt_sqrt (norm_nonneg _)).mp (lt_of_lt_of_le (hclose s) (min_le_right _ _))
  have hPi : ∀ s, Phat s ∘L Phat s = Phat s := fun s => spectralProjNearOne_comp_self (A s)
  have hPs : ∀ s, (Phat s).adjoint = Phat s := fun s => adjoint_spectralProjNearOne (A s)
  have hspec := fun s =>
    projIntertwiner_spec (hidem s) (hsymm s) (hPi s) (hPs s) (h1s s) (hηs s)
  refine ⟨Phat, fun s => projIntertwiner (P s) (Phat s), hPhat, ?_, hδs, hPi, hPs,
    fun s => (hspec s).1, fun s => (hspec s).2.1, fun s => (hspec s).2.2.1,
    fun s => (hspec s).2.2.2.1, fun s => ?_, fun s v hv => ?_, fun s w hw => ?_⟩
  · intro s
    exact ContMDiffAt.projIntertwiner (n := (k : ℕ∞)) (hP s)
      ((hPhat s).of_le (WithTop.coe_le_coe.mpr le_top)) (hηs s)
  · exact finrank_range_eq_of_projIntertwiner (hidem s) (hsymm s) (hPi s) (hPs s) (h1s s) (hηs s)
  · exact projIntertwiner_mapsTo (hidem s) (hsymm s) (hPi s) (hPs s) (h1s s) (hηs s) hv
  · exact exists_projIntertwiner_eq (hidem s) (hsymm s) (hPi s) (hPs s) (h1s s) (hηs s) hw

/-- **S-BUNDLE, frozen form** (D-CMS interface `exists_smooth_projection_and_isometry`, conclusions
verbatim) with the review's correction `[T2Space S]`. -/
theorem exists_smooth_projection_and_isometry [FiniteDimensional ℝ EB] [IsManifold IB ∞ S]
    [CompactSpace S] [T2Space S] {k : ℕ} (P : S → F →L[ℝ] F)
    (hP : ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) k P) (hidem : ∀ s, P s ∘L P s = P s)
    (hsymm : ∀ s, (P s).adjoint = P s) :
    ∃ (Phat : S → F →L[ℝ] F) (Bmap : S → F →L[ℝ] F),
      ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) ∞ Phat ∧ ContMDiff IB 𝓘(ℝ, F →L[ℝ] F) k Bmap ∧
      (∀ s, Phat s ∘L Phat s = Phat s) ∧ (∀ s, (Phat s).adjoint = Phat s) ∧
      (∀ s, Module.finrank ℝ (LinearMap.range (Phat s : F →ₗ[ℝ] F)) =
        Module.finrank ℝ (LinearMap.range (P s : F →ₗ[ℝ] F))) ∧
      (∀ s v, P s v = v → Phat s (Bmap s v) = Bmap s v ∧ ‖Bmap s v‖ = ‖v‖) ∧
      (∀ s w, Phat s w = w → ∃ v, P s v = v ∧ Bmap s v = w) := by
  obtain ⟨Phat, Bmap, hPhat, hB, -, hPi, hPs, -, -, -, hnorm, hrank, hmaps, hsurj⟩ :=
    exists_smooth_projection_and_orthogonal_intertwiner P hP hidem hsymm one_pos
  exact ⟨Phat, Bmap, hPhat, hB, hPi, hPs, hrank, fun s v hv => ⟨hmaps s v hv, hnorm s v⟩, hsurj⟩

end DifferentialGeometry.Geometry.FiniteSoul
