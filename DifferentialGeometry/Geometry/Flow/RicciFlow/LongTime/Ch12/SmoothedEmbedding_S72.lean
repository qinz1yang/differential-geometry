import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompImmersion_S60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceInBall_S61
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false

/-! # CH12-S72 G1a: the smoothed map `f ∘ e` is a smooth embedding on an open subset of `B(ρ)`

`e = E_j(μ, ·)` is a smooth bijection that is the identity off `B(ρ)`; `f` is a smooth injective map
on `B(4ρ)`; both have order-0 `ckErr_S45` error `< 1` (hence injective differential, S60).  Then
`f ∘ e` restricted to any open `U ⊆ B(ρ)` is smooth and a smooth embedding (injective local
diffeomorphism; `isSmoothEmbedding_of_injective_mfderiv`).  Also: `PersistentModelPatch` is monotone
in the start time and in the accuracy `α` (only the speed clause involves `α`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Topology.Manifold
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

/-- a bijection that is the identity off `B(ρ)` preserves `B(ρ)`. -/
theorem ball_mapsTo_of_supp_S72 (H : FiniteVolumeHyperbolicModel.{u}) (ρ : ℝ)
    (e : H.Carrier → H.Carrier) (hinj : Function.Injective e)
    (hsupp : ∀ p, p ∉ riemannianBallOf H.metric H.basepoint ρ → e p = p) :
    ∀ p ∈ riemannianBallOf H.metric H.basepoint ρ, e p ∈ riemannianBallOf H.metric H.basepoint ρ := by
  intro p hp
  by_contra h
  have h1 : e (e p) = e p := hsupp _ h
  exact h (by rw [hinj h1]; exact hp)

theorem smoothedMap_embedding_S72 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (e : H.Carrier → H.Carrier)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) (hbij : Function.Bijective e)
    (hsupp : ∀ p, p ∉ riemannianBallOf H.metric H.basepoint ρ → e p = p)
    (he0 : ∀ p ∈ riemannianBallOf H.metric H.basepoint ρ, ckErr_S45 H H.metric 1 e 0 p < 1)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (riemannianBallOf H.metric H.basepoint (4 * ρ)))
    (hfinj : Set.InjOn f (riemannianBallOf H.metric H.basepoint (4 * ρ)))
    (hf0 : ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ), ckErr_S45 H g' c f 0 p < 1)
    (U : TopologicalSpace.Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ riemannianBallOf H.metric H.basepoint ρ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => f (e x)) U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f (e x)) := by
  have hmaps := ball_mapsTo_of_supp_S72 H ρ e hbij.1 hsupp
  have hsub : riemannianBallOf H.metric H.basepoint ρ ⊆ riemannianBallOf H.metric H.basepoint (4 * ρ) :=
    riemannianBallOf_mono _ _ (by linarith)
  have hopen : IsOpen (riemannianBallOf H.metric H.basepoint (4 * ρ)) := isOpen_riemannianBallOf_S61 H _
  have hUe : ∀ x ∈ (U : Set H.Carrier), e x ∈ riemannianBallOf H.metric H.basepoint (4 * ρ) :=
    fun x hx => hsub (hmaps x (hU hx))
  have hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => f (e x)) U :=
    hf.comp he.contMDiffOn hUe
  refine ⟨hsm, ?_⟩
  have hcm : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => f (e x)) :=
    (hf.comp_contMDiff (g := f) (f := fun x : U => e x.val)
      (he.comp contMDiff_subtype_val) (fun x => hUe x.val x.2))
  have hinj : Function.Injective (fun x : U => f (e x)) := by
    intro x y hxy
    have hx := hsub (hmaps x.val (hU x.2))
    have hy := hsub (hmaps y.val (hU y.2))
    exact Subtype.ext (hbij.1 (hfinj hx hy hxy))
  refine isSmoothEmbedding_of_injective_mfderiv hcm hinj ?_ rfl
  intro x
  have hxB := hU x.2
  have hmdf : MDifferentiableAt (𝓡 3) (𝓡 3) f (e x.val) :=
    (hf.mdifferentiableOn (by simp) _ (hUe x.val x.2)).mdifferentiableAt (hopen.mem_nhds (hUe x.val x.2))
  have hmde : MDifferentiableAt (𝓡 3) (𝓡 3) e x.val := he.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : U → H.Carrier) x :=
    (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
  have hevl : MDifferentiableAt (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : U → H.Carrier)) x :=
    MDifferentiableAt.comp x hmde hval
  have h1 : mfderiv (𝓡 3) (𝓡 3) (f ∘ (e ∘ (Subtype.val : U → H.Carrier))) x =
      (mfderiv (𝓡 3) (𝓡 3) f (e x.val)).comp (mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : U → H.Carrier)) x) :=
    mfderiv_comp x hmdf hevl
  have h2 : mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : U → H.Carrier)) x =
      (mfderiv (𝓡 3) (𝓡 3) e x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → H.Carrier) x) :=
    mfderiv_comp x hmde hval
  have hI1 := (ckErr0_immersion_S60 H g' c f (e x.val) (hf0 _ (hUe x.val x.2))).2
  have hI2 := (ckErr0_immersion_S60 H H.metric 1 e x.val (he0 _ hxB)).2
  change Function.Injective (mfderiv (𝓡 3) (𝓡 3) (f ∘ (e ∘ (Subtype.val : U → H.Carrier))) x)
  rw [h1, h2]
  intro u v huv
  simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply] at huv
  exact hI2 (hI1 huv)

/-- `smoothedMap_embedding_S72` v2 (S8 v6 support radius, [FROZEN v2] CH12-O40): the isotopy is the
identity off `B(4ρ)` and has `ckErr` order 0 `< 1` on `B(4ρ)`; `f` is controlled on `B(4ρ)` only
(`e` preserves `B(4ρ)` by bijectivity + support, so `f ∘ e` only sees `f` on `B(4ρ)`); the open
`U ⊆ B(ρ)` is unchanged.  Same conclusion as the v1. -/
theorem smoothedMap_embedding_v2_S72 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (e : H.Carrier → H.Carrier)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) (hbij : Function.Bijective e)
    (hsupp : ∀ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ) → e p = p)
    (he0 : ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ), ckErr_S45 H H.metric 1 e 0 p < 1)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (riemannianBallOf H.metric H.basepoint (4 * ρ)))
    (hfinj : Set.InjOn f (riemannianBallOf H.metric H.basepoint (4 * ρ)))
    (hf0 : ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ), ckErr_S45 H g' c f 0 p < 1)
    (U : TopologicalSpace.Opens H.Carrier) (hU : (U : Set H.Carrier) ⊆ riemannianBallOf H.metric H.basepoint ρ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => f (e x)) U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f (e x)) := by
  have hmaps := ball_mapsTo_of_supp_S72 H (4 * ρ) e hbij.1 hsupp
  have hsub : riemannianBallOf H.metric H.basepoint ρ ⊆ riemannianBallOf H.metric H.basepoint (4 * ρ) :=
    riemannianBallOf_mono _ _ (by linarith)
  have hopen : IsOpen (riemannianBallOf H.metric H.basepoint (4 * ρ)) := isOpen_riemannianBallOf_S61 H _
  have hUe : ∀ x ∈ (U : Set H.Carrier), e x ∈ riemannianBallOf H.metric H.basepoint (4 * ρ) :=
    fun x hx => hmaps x (hsub (hU hx))
  have hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => f (e x)) U :=
    hf.comp he.contMDiffOn hUe
  refine ⟨hsm, ?_⟩
  have hcm : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => f (e x)) :=
    (hf.comp_contMDiff (g := f) (f := fun x : U => e x.val)
      (he.comp contMDiff_subtype_val) (fun x => hUe x.val x.2))
  have hinj : Function.Injective (fun x : U => f (e x)) := by
    intro x y hxy
    have hx := hUe x.val x.2
    have hy := hUe y.val y.2
    exact Subtype.ext (hbij.1 (hfinj hx hy hxy))
  refine isSmoothEmbedding_of_injective_mfderiv hcm hinj ?_ rfl
  intro x
  have hxB := hsub (hU x.2)
  have hmdf : MDifferentiableAt (𝓡 3) (𝓡 3) f (e x.val) :=
    (hf.mdifferentiableOn (by simp) _ (hUe x.val x.2)).mdifferentiableAt (hopen.mem_nhds (hUe x.val x.2))
  have hmde : MDifferentiableAt (𝓡 3) (𝓡 3) e x.val := he.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : U → H.Carrier) x :=
    (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
  have hevl : MDifferentiableAt (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : U → H.Carrier)) x :=
    MDifferentiableAt.comp x hmde hval
  have h1 : mfderiv (𝓡 3) (𝓡 3) (f ∘ (e ∘ (Subtype.val : U → H.Carrier))) x =
      (mfderiv (𝓡 3) (𝓡 3) f (e x.val)).comp (mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : U → H.Carrier)) x) :=
    mfderiv_comp x hmdf hevl
  have h2 : mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : U → H.Carrier)) x =
      (mfderiv (𝓡 3) (𝓡 3) e x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → H.Carrier) x) :=
    mfderiv_comp x hmde hval
  have hI1 := (ckErr0_immersion_S60 H g' c f (e x.val) (hf0 _ (hUe x.val x.2))).2
  have hI2 := (ckErr0_immersion_S60 H H.metric 1 e x.val (he0 _ hxB)).2
  change Function.Injective (mfderiv (𝓡 3) (𝓡 3) (f ∘ (e ∘ (Subtype.val : U → H.Carrier))) x)
  rw [h1, h2]
  intro u v huv
  simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply] at huv
  exact hI2 (hI1 huv)

/-- `PersistentModelPatch` is monotone in the start time and in `α` (only the speed clause involves `α`). -/
theorem patch_mono_S72 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {H : FiniteVolumeHyperbolicModel.{u}} {T T' : ℝ} {α α' : ℝ → ℝ}
    (hTT' : T ≤ T') (hα0 : ∀ t, T' ≤ t → 0 ≤ α t) (hαα' : ∀ t, T' ≤ t → α t ≤ α' t)
    {domain : ℝ → TopologicalSpace.Opens H.Carrier}
    {m : (t : ℝ) → T ≤ t → H.Carrier → (postStage F.observation t).Carrier} {t₀ : ℝ} {x₀ : H.Carrier}
    (Pt : PersistentModelPatch F H T α domain m t₀ x₀) :
    Nonempty (PersistentModelPatch F H T' α' domain (fun t ht => m t (hTT'.trans ht)) t₀ x₀) := by
  refine ⟨{ Pt with
    in_domain := fun t ht hT => Pt.in_domain t ht (hTT'.trans hT)
    agrees := fun t ht hT x hx => Pt.agrees t ht (hTT'.trans hT) x hx
    speed := fun t ht hT x hx => ?_ }⟩
  have h := Pt.speed t ht (hTT'.trans hT) x hx
  refine lt_of_lt_of_le h ?_
  have h0 := hα0 t hT
  have h1 := hαα' t hT
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  exact div_le_div_of_nonneg_right (by nlinarith) ht0

end GC.LongTime.Ch12
