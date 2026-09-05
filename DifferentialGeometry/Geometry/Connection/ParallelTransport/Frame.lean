import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Existence
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

private theorem exists_parallel_frame_of_contMDiff
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, e i 0 = v i) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i) t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (e i t) (e j t) = if i = j then 1 else 0) := by
  classical
  have htransport : ∀ i, ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v i ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) :=
    fun i =>
      Variation.exists_parallel_transport_on_Icc
        (I := I) g γ hN hγ hL (v i)
  choose Vfun hV0 hVdiff hVpar using htransport
  refine ⟨Vfun, hV0, hVdiff, hVpar, ?_⟩
  intro t ht i j
  have hconst :=
    Variation.parallel_transport_preserves_inner_product
      (I := I) g γ hN hγ (Vfun i) (Vfun j)
      (hVdiff i) (hVdiff j) (hVpar i) (hVpar j) t ht
  rw [hconst, hV0 i, hV0 j]
  exact hON0 i j

theorem exists_parallel_frame_on_Icc
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {U : Set ℝ} {L : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hU : IsOpen U) (hL : 0 ≤ L) (hseg : Icc (0 : ℝ) L ⊆ U)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ F : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, F i 0 = v i) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ (F i) t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0) := by
  obtain ⟨Γ, hΓ, hgerm⟩ := hγ.exists_extension_uIcc (a := 0) (b := L) hU
    (by simpa only [uIcc_of_le hL] using hseg)
  rw [uIcc_of_le hL] at hgerm
  let w : ι → TangentSpace I (Γ 0) := fun i => show TangentSpace I (Γ 0) from (v i : E)
  have hbase : Γ 0 = γ 0 := (hgerm 0 ⟨le_rfl, hL⟩).eq_of_nhds
  have hONw : ∀ i j, g.inner (Γ 0) (w i) (w j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    change g.inner (Γ 0) (show TangentSpace I (Γ 0) from (v i : E))
      (show TangentSpace I (Γ 0) from (v j : E)) = _
    rw [hbase]
    exact hON0 i j
  obtain ⟨FG, hFG0, hFGdiff, hFGpar, hFGON⟩ :=
    exists_parallel_frame_of_contMDiff (I := I) g Γ (N := 2) (by norm_num) hΓ
      (lt_of_lt_of_le zero_lt_one (le_max_right L 1)) w hONw
  let F : ι → ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i t => show TangentSpace I (γ t) from (FG i t : E)
  have hfield : ∀ i t,
      (fun s : ℝ => (F i s : E)) =ᶠ[𝓝 t] fun s : ℝ => (FG i s : E) :=
    fun _ _ => Filter.Eventually.of_forall fun _ => rfl
  have hsub : Icc (0 : ℝ) L ⊆ Icc (0 : ℝ) (max L 1) :=
    Icc_subset_Icc_right (le_max_left L 1)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hFG0 i
  · intro i t ht
    have hrep := chartRep_congr_curve (I := I) (F i) (FG i)
      (hgerm t ht).symm (hfield i t)
    exact hrep.differentiableAt_iff.mpr (hFGdiff i t (hsub ht))
  · intro i t ht
    have hcongr := covDerivAlong_congr_curve (I := I) g (F i) (FG i)
      (hgerm t ht).symm (hfield i t)
    exact hcongr.trans (hFGpar i t (hsub ht))
  · intro t ht i j
    have hpoint : Γ t = γ t := (hgerm t ht).eq_of_nhds
    change g.inner (γ t) (show TangentSpace I (γ t) from (FG i t : E))
      (show TangentSpace I (γ t) from (FG j t : E)) = _
    rw [← hpoint]
    exact hFGON t (hsub ht) i j

theorem exists_parallel_frame
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, e i 0 = v i) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i) t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (e i t) (e j t) = if i = j then 1 else 0) := by
  exact exists_parallel_frame_on_Icc (I := I) g γ
    (hγ.of_le (by exact_mod_cast hN)).contMDiffOn isOpen_univ hL.le
    (subset_univ _) v hON0

end DifferentialGeometry.Geometry.Riemannian
