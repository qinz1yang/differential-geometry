import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

noncomputable def parallelTransportSectionOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∀ t, TangentSpace I (γ t) :=
  Classical.choose (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)

@[simp]
theorem parallelTransportSectionOnIcc_initial [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀ 0 = v₀ :=
  (Classical.choose_spec
    (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)).1

theorem parallelTransportSectionOnIcc_differentiableAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀) t) t :=
  (Classical.choose_spec
    (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)).2.1 t ht

theorem parallelTransportSectionOnIcc_covDerivAlong [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    covDerivAlong (I := I) g γ
      (parallelTransportSectionOnIcc (I := I) g γ hγ hL v₀) t = 0 :=
  (Classical.choose_spec
    (exists_parallel_transport_on_Icc (I := I) g γ le_rfl hγ hL v₀)).2.2 t ht

theorem parallelTransportSectionOnIcc_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL (v + w) t =
      parallelTransportSectionOnIcc (I := I) g γ hγ hL v t +
        parallelTransportSectionOnIcc (I := I) g γ hγ hL w t := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL (v + w)
  let Vv := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let Vw := parallelTransportSectionOnIcc (I := I) g γ hγ hL w
  let W : ∀ s, TangentSpace I (γ s) := fun s ↦ Vv s + Vw s
  refine parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
    ?_ ?_ ?_ ?_ (t₀ := 0) ?_ ?_ t ht
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL (v + w) hs
  · intro s hs
    rw [show chartRepAt (I := I) γ W s =
      fun r ↦ chartRepAt (I := I) γ Vv s r + chartRepAt (I := I) γ Vw s r by
        simpa [W] using chartRepAt_add (I := I) γ Vv Vw s]
    exact (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL v hs).add
      (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL w hs)
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL (v + w) hs
  · intro s hs
    change covDerivAlong (I := I) g γ (fun r ↦ Vv r + Vw r) s = 0
    rw [covDerivAlong_add (I := I) g γ Vv Vw s
      (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL v hs)
      (parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL w hs)]
    rw [parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL v hs,
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL w hs]
    simp
  · exact ⟨le_rfl, le_of_lt hL⟩
  · simp [V, W, Vv, Vw]

theorem parallelTransportSectionOnIcc_smul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (c : ℝ) (v : TangentSpace I (γ 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    parallelTransportSectionOnIcc (I := I) g γ hγ hL (c • v) t =
      c • parallelTransportSectionOnIcc (I := I) g γ hγ hL v t := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL (c • v)
  let Vv := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let W : ∀ s, TangentSpace I (γ s) := fun s ↦ c • Vv s
  refine parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
    ?_ ?_ ?_ ?_ (t₀ := 0) ?_ ?_ t ht
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL (c • v) hs
  · intro s hs
    rw [show chartRepAt (I := I) γ W s =
      fun r ↦ c • chartRepAt (I := I) γ Vv s r by
        simpa [W] using chartRepAt_smul (I := I) γ c Vv s]
    exact (parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL v hs).const_smul c
  · intro s hs
    simpa [V] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL (c • v) hs
  · intro s hs
    change covDerivAlong (I := I) g γ (fun r ↦ c • Vv r) s = 0
    rw [covDerivAlong_smul (I := I) g γ c Vv s]
    rw [parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL v hs]
    simp
  · exact ⟨le_rfl, le_of_lt hL⟩
  · simp [V, W, Vv]

noncomputable def parallelTransportLinearMapOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ L) where
  toFun v := parallelTransportSectionOnIcc (I := I) g γ hγ hL v L
  map_add' v w := parallelTransportSectionOnIcc_add (I := I) g γ hγ hL v w
    ⟨le_of_lt hL, le_rfl⟩
  map_smul' c v := parallelTransportSectionOnIcc_smul (I := I) g γ hγ hL c v
    ⟨le_of_lt hL, le_rfl⟩

@[simp]
theorem parallelTransportLinearMapOnIcc_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0)) :
    parallelTransportLinearMapOnIcc (I := I) g γ hγ hL v =
      parallelTransportSectionOnIcc (I := I) g γ hγ hL v L :=
  rfl

theorem parallelTransportLinearMapOnIcc_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (γ 0)) :
    g.inner (γ L) (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL v)
        (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL w) =
      g.inner (γ 0) v w := by
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let W := parallelTransportSectionOnIcc (I := I) g γ hγ hL w
  have h := parallel_transport_preserves_inner_product (I := I) g γ le_rfl hγ V W
    (fun t ht ↦ parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL v ht)
    (fun t ht ↦ parallelTransportSectionOnIcc_differentiableAt
      (I := I) g γ hγ hL w ht)
    (fun t ht ↦ parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g γ hγ hL v ht)
    (fun t ht ↦ parallelTransportSectionOnIcc_covDerivAlong
      (I := I) g γ hγ hL w ht) L ⟨le_of_lt hL, le_rfl⟩
  simpa [V, W] using h

theorem parallelTransportLinearMapOnIcc_injective [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    Function.Injective (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL) := by
  intro v w hvw
  let V := parallelTransportSectionOnIcc (I := I) g γ hγ hL v
  let W := parallelTransportSectionOnIcc (I := I) g γ hγ hL w
  have h := parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ V W
    (fun t ht ↦ by simpa [V] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL v ht)
    (fun t ht ↦ by simpa [W] using
      parallelTransportSectionOnIcc_differentiableAt (I := I) g γ hγ hL w ht)
    (fun t ht ↦ by simpa [V] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL v ht)
    (fun t ht ↦ by simpa [W] using
      parallelTransportSectionOnIcc_covDerivAlong (I := I) g γ hγ hL w ht)
    (t₀ := L) ⟨le_of_lt hL, le_rfl⟩ (by simpa [V, W] using hvw)
    0 ⟨le_rfl, le_of_lt hL⟩
  simpa [V, W] using h

theorem parallelTransportLinearMapOnIcc_surjective [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    Function.Surjective (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL) := by
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)]
  exact parallelTransportLinearMapOnIcc_injective (I := I) g γ hγ hL

noncomputable def parallelTransportLinearEquivOnIcc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) :
    TangentSpace I (γ 0) ≃ₗ[ℝ] TangentSpace I (γ L) :=
  LinearEquiv.ofBijective (parallelTransportLinearMapOnIcc (I := I) g γ hγ hL)
    ⟨parallelTransportLinearMapOnIcc_injective (I := I) g γ hγ hL,
      parallelTransportLinearMapOnIcc_surjective (I := I) g γ hγ hL⟩

@[simp]
theorem parallelTransportLinearEquivOnIcc_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v : TangentSpace I (γ 0)) :
    parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL v =
      parallelTransportSectionOnIcc (I := I) g γ hγ hL v L :=
  rfl

theorem parallelTransportLinearEquivOnIcc_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v w : TangentSpace I (γ 0)) :
    g.inner (γ L) (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL v)
        (parallelTransportLinearEquivOnIcc (I := I) g γ hγ hL w) =
      g.inner (γ 0) v w :=
  parallelTransportLinearMapOnIcc_inner (I := I) g γ hγ hL v w

noncomputable def parallelTransportLinearEquivBetween [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) :
    TangentSpace I (γ a) ≃ₗ[ℝ] TangentSpace I (γ b) := by
  have hshift : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (fun s ↦ γ (s + a)) :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  exact parallelTransportLinearEquivOnIcc (I := I) g (fun s ↦ γ (s + a))
    hshift (sub_pos.mpr hab)

theorem parallelTransportLinearEquivBetween_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ)
    {a b : ℝ} (hab : a < b) (v w : TangentSpace I (γ a)) :
    g.inner (γ b) (parallelTransportLinearEquivBetween (I := I) g γ hγ hab v)
        (parallelTransportLinearEquivBetween (I := I) g γ hγ hab w) =
      g.inner (γ a) v w := by
  have hshift : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (fun s ↦ γ (s + a)) :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  change g.inner (γ b)
      (parallelTransportLinearEquivOnIcc (I := I) g (fun s ↦ γ (s + a))
        hshift (sub_pos.mpr hab) v)
      (parallelTransportLinearEquivOnIcc (I := I) g (fun s ↦ γ (s + a))
        hshift (sub_pos.mpr hab) w) =
    g.inner (γ a) v w
  convert parallelTransportLinearEquivOnIcc_inner (I := I) g
    (fun s ↦ γ (s + a)) hshift (sub_pos.mpr hab) v w using 1
  · rw [sub_add_cancel]
  · rw [zero_add]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
