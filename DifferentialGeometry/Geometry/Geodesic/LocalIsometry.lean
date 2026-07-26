import DifferentialGeometry.Geometry.Coordinates.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Geodesic.ChartRegularity
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype
import DifferentialGeometry.Geometry.Geodesic.PullbackCross
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Topology.SigmaCompactOpen

set_option autoImplicit false

/-!
# Local isometries preserve geodesics

A smooth local diffeomorphism whose differential preserves a pair of smooth
Riemannian metrics sends geodesics to geodesics.  The proof chooses a local
partial diffeomorphism at the time under consideration, restricts it to open
subtypes, and reuses the cross-model diffeomorphism naturality theorem.

No separate local-isometry predicate is introduced: the public theorem takes
the standard `IsLocalDiffeomorph` hypothesis and the fiberwise metric identity
directly.
-/

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open Bundle Filter Manifold Set TopologicalSpace
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] in
private theorem metric_ext
    {g₁ g₂ : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₂.inner x v w) :
    g₁ = g₂ := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
  have hi : i₁ = i₂ :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

/-- A metric-preserving local diffeomorphism transports the geodesic equation
at a time where the source curve is smooth. -/
theorem geoEq_map_localIso
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N)
    {f : M → N}
    (hld : IsLocalDiffeomorph I J ∞ f)
    (hpres : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w =
        g'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (γ : ℝ → M) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : HasGeodesicEquationAt (I := I) g γ t) :
    HasGeodesicEquationAt (I := J) g' (fun s => f (γ s)) t := by
  classical
  obtain ⟨Φ, htΦ, hfΦ⟩ := hld (γ t)
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  have hUΦ : (U : Set M) ⊆ Φ.source := fun _ hx => hx
  let V : Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hUΦ⟩
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen J V.isOpen)
  let Ψ : Diffeomorph I J U V ∞ :=
    PartialDiffeomorph.toOpensDiffeoCross Φ hUΦ
  let γtU : U := ⟨γ t, htΦ⟩
  let γU : ℝ → U := fun s =>
    if hs : γ s ∈ (U : Set M) then ⟨γ s, hs⟩ else γtU
  have hmem : ∀ᶠ s in 𝓝 t, γ s ∈ (U : Set M) :=
    hγ.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds htΦ)
  have hγU_val : (fun s => ((γU s : U) : M)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hmem] with s hs
    simp only [γU, dif_pos hs]
  have hγU_smooth : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γU t := by
    have hamb : ContMDiffAt 𝓘(ℝ, ℝ) I ∞
        (fun s => ((γU s : U) : M)) t :=
      hγ.congr_of_eventuallyEq hγU_val
    have hcod := codRestr_contMDiffAt
      (I := 𝓘(ℝ, ℝ)) (J := I) (V := U)
      (f := fun s => ((γU s : U) : M))
      (fun s => (γU s).property) hamb
    simpa only [Subtype.coe_eta] using hcod
  have hgeo_amb :
      HasGeodesicEquationAt (I := I) g (fun s => ((γU s : U) : M)) t :=
    HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (I := I) (g := g) hγU_val.eq_of_nhds hγU_val hgeo
  have hgeo_U :
      HasGeodesicEquationAt (I := I) (g.restrictOpen (I := I) U) γU t := by
    have hOn : IsGeodesicOn (I := I) g
        (fun s => ((γU s : U) : M)) ({t} : Set ℝ) := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hgeo_amb
    have hOnU :=
      (geodesicOn_open_iff (I := I) g U γU ({t} : Set ℝ)).mpr hOn
    exact hOnU t (Set.mem_singleton t)
  have hΦmfd :
      ∀ (x : U),
        mfderiv I J (Φ : M → N) (x : M) =
          mfderiv I J f (x : M) := by
    intro x
    have heq : f =ᶠ[𝓝 (x : M)] (Φ : M → N) :=
      Filter.eventuallyEq_of_mem
        (Φ.open_source.mem_nhds x.property) hfΦ
    exact heq.mfderiv_eq.symm
  have hmetric :
      g.restrictOpen (I := I) U =
        Diffeomorph.pullbackMetricCross
          (g'.restrictOpen (I := J) V) Ψ := by
    apply metric_ext
    intro x v w
    dsimp only [Ψ]
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner,
      PartialDiffeomorph.opensDiffeo_mfd,
      PartialDiffeomorph.opensDiffeo_mfd,
      hΦmfd x]
    change g.inner (x : M) v w =
      g'.inner ((Ψ x : V) : N)
        (mfderiv I J f (x : M) v)
        (mfderiv I J f (x : M) w)
    have hval : ((Ψ x : V) : N) = f (x : M) := by
      change (Φ : M → N) (x : M) = f (x : M)
      exact (hfΦ x.property).symm
    rw [hval]
    exact hpres (x : M) v w
  have hgeo_pull :
      HasGeodesicEquationAt (I := I)
        (Diffeomorph.pullbackMetricCross
          (g'.restrictOpen (I := J) V) Ψ) γU t := by
    rw [← hmetric]
    exact hgeo_U
  have hgeo_V :
      HasGeodesicEquationAt (I := J)
        (g'.restrictOpen (I := J) V) (fun s => Ψ (γU s)) t :=
    geoEq_mapCrossAt (I := I) (J := J)
      (g'.restrictOpen (I := J) V) Ψ γU t hγU_smooth hgeo_pull
  have hgeo_target :
      HasGeodesicEquationAt (I := J) g'
        (fun s => ((Ψ (γU s) : V) : N)) t := by
    have hOnV : IsGeodesicOn (I := J)
        (g'.restrictOpen (I := J) V)
        (fun s => Ψ (γU s)) ({t} : Set ℝ) := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hgeo_V
    have hOn :=
      (geodesicOn_open_iff (I := J) g' V
        (fun s => Ψ (γU s)) ({t} : Set ℝ)).mp hOnV
    exact hOn t (Set.mem_singleton t)
  have hmap_eq :
      (fun s => f (γ s)) =ᶠ[𝓝 t]
        (fun s => ((Ψ (γU s) : V) : N)) := by
    filter_upwards [hmem] with s hs
    dsimp only [Ψ]
    have hγUs : ((γU s : U) : M) = γ s := by
      simp only [γU, dif_pos hs]
    change f (γ s) =
      (Φ : M → N) ((γU s : U) : M)
    rw [hγUs]
    exact hfΦ hs
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (I := J) (g := g') hmap_eq.eq_of_nhds hmap_eq hgeo_target

/-- A metric-preserving local diffeomorphism sends a continuous geodesic on
an open time set to a geodesic on the same set. -/
theorem geoOn_map_localIso
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N)
    {f : M → N}
    (hld : IsLocalDiffeomorph I J ∞ f)
    (hpres : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w =
        g'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s) (hcont : ContinuousOn γ s)
    (hgeo : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := J) g' (fun t => f (γ t)) s := by
  intro t ht
  exact geoEq_map_localIso (I := I) (J := J) g g' hld hpres γ t
    (isGeodesicOn_contMDiffAt_infty (I := I) g hs ht hgeo hcont)
    (hgeo t ht)

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
