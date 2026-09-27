import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CoverCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ProductCurve

variable (c : ProductCurve M)

def Field.SmoothOn {c : ProductCurve M} (V : c.Field (I := I)) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
    (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem coverLift_contMDiffAt {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun z => c.coverLift z t) x := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hcover : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.coverLift p.1 p.2) (univ ×ˢ J) (x, t) :=
    (hc.1 (x, t) hmem).prodMk (hc.2 (x, t) hmem).contMDiffWithinAt
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  exact contMDiffWithinAt_univ.mp (hcover.comp x hz hto)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem chartRepAt_differentiableAt_of_field_smooth {J : Set ℝ} (V : c.Field (I := I))
    (hV : V.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    DifferentiableAt ℝ (chartRepAt (I := I.prod 𝓘(ℝ, ℝ))
      (fun z => c.coverLift z t) (fun z => V z t) x) x := by
  have hsec : ContMDiffWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun z : ℝ => (⟨c.coverLift z t, V z t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) univ x :=
    ((hV t ht).contMDiffAt).contMDiffWithinAt
  have hdiff := chartRepAtBase_differentiableWithinAt (I := I.prod 𝓘(ℝ, ℝ))
    (γ := fun z => c.coverLift z t) (V := fun z => V z t) (J := univ) (t := x) hsec
  rw [differentiableWithinAt_univ] at hdiff
  exact hdiff

end ProductCurve

omit [CompleteSpace E] in
theorem covDerivAlong_productCoverProjection (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (γ : ℝ → M × ℝ) (V : ∀ s, TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ s)) (x : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ γ x)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I.prod 𝓘(ℝ, ℝ)) γ V x) x) :
    letI := A.charts
    letI := A.smoothManifold
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection (γ x)
        (covDerivAlong (I := I.prod 𝓘(ℝ, ℝ)) (coverProductMetric g lambda hlambda) γ V x) =
      covDerivAlong (I := I.prod 𝓘(ℝ, ℝ)) (quotientProductMetric A g lambda hlambda)
        (fun s => productCoverProjection (γ s))
        (fun s => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection
          (γ s) (V s)) x := by
  let := A.charts
  let := A.smoothManifold
  let : NeZero (Module.finrank ℝ (E × ℝ)) :=
    ⟨by rw [Module.finrank_prod, Module.finrank_self]; exact Nat.succ_ne_zero _⟩
  exact covDerivAlong_map_of_eq_localPullMetric (I := I.prod 𝓘(ℝ, ℝ))
    (J := I.prod 𝓘(ℝ, ℝ))
    (g := quotientProductMetric A g lambda hlambda)
    (f := productCoverProjection (M := M))
    (isLocalDiffeomorph_productCoverProjection A)
    (k := coverProductMetric g lambda hlambda)
    (quotientProductMetric_localPull A g lambda hlambda) γ V x hγ hV

namespace ProductCurve

variable (c : ProductCurve M)

omit [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
theorem map_curvatureVector_eq (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection (c.coverLift x t)
        (c.curvatureVector g lambda x t) =
      c.map.curvatureVector (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t := by
  let := A.charts
  let := A.smoothManifold
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun z => c.coverLift z t) x :=
    c.coverLift_contMDiffAt (I := I) hc x t ht
  have hV : DifferentiableAt ℝ (chartRepAt (I := I.prod 𝓘(ℝ, ℝ))
      (fun z => c.coverLift z t) (fun z => c.unitTangent g lambda z t) x) x :=
    c.chartRepAt_differentiableAt_of_field_smooth (I := I) (c.unitTangent g lambda) hU x t ht
  have hnat := covDerivAlong_productCoverProjection (I := I) (M := M) A (g t) lambda hlambda
    (fun z => c.coverLift z t) (fun z => c.unitTangent g lambda z t) x hγ hV
  have hcover := ProductCurve.cover_covariantDerivative_of_boundaryless (I := I) c g lambda hlambda
    t (c.unitTangent g lambda) (hU t ht) x
  have hcurve : (fun s => c.map.lift s t) =
      fun s => productCoverProjection (c.coverLift s t) := by
    funext s
    exact (c.coverProjection_lift s t).symm
  have hfield : (fun s => c.map.unitTangent (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) s t) =
      fun s => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection
        (c.coverLift s t) (c.unitTangent g lambda s t) := by
    funext s
    exact c.map_unitTangent_eq (I := I) A g lambda hlambda hc s t ht
  have hmap : covDerivAlong (I := I.prod 𝓘(ℝ, ℝ))
        (quotientProductMetric A (g t) lambda hlambda)
        (fun s => productCoverProjection (c.coverLift s t))
        (fun s => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) productCoverProjection
          (c.coverLift s t) (c.unitTangent g lambda s t)) x =
      c.map.Dx (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda)
        (c.map.unitTangent (I := I.prod 𝓘(ℝ, ℝ))
          (fun s => quotientProductMetric A (g s) lambda hlambda)) x t := by
    simp only [CurveMap.Dx]
    rw [hcurve, hfield]
  have hcur : c.curvatureVector g lambda x t =
      (c.speed g lambda x t)⁻¹ • c.Dx (I := I) g (c.unitTangent g lambda) x t := rfl
  have hmapcur : c.map.curvatureVector (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      (c.map.speed (I := I.prod 𝓘(ℝ, ℝ))
          (fun s => quotientProductMetric A (g s) lambda hlambda) x t)⁻¹ •
        c.map.Dx (I := I.prod 𝓘(ℝ, ℝ))
          (fun s => quotientProductMetric A (g s) lambda hlambda)
          (c.map.unitTangent (I := I.prod 𝓘(ℝ, ℝ))
            (fun s => quotientProductMetric A (g s) lambda hlambda)) x t := rfl
  rw [hcur, hmapcur, map_smul, ← hcover, hnat, hmap,
    c.map_speed_eq (I := I) A g lambda hlambda hc x t ht]

omit [CompleteSpace E] in
theorem map_isSolutionOn_of_isSolutionOn (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t)
    (hc : c.IsSolutionOn g lambda J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun s => quotientProductMetric A (g s) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  refine ⟨c.smoothOn_map (I := I) A hc.smooth,
    (c.map_immersedOn_iff (I := I) A hc.smooth).mpr hc.immersed, ?_⟩
  intro x t ht
  rw [c.map_velocity_eq (I := I) A J hc.smooth x t ht (huniq t ht),
    hc.equation x t ht,
    c.map_curvatureVector_eq (I := I) A g lambda hlambda hc.smooth hU x t ht]

omit [CompleteSpace E] in
theorem map_isSolutionOn_of_isSolutionOn_of_interval (A : QuotientProductAtlas I M)
    [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {s u : ℝ} (hsu : s < u) {J : Set ℝ} (hJ : J = Ico s u ∨ J = Icc s u)
    (hc : c.IsSolutionOn g lambda J)
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  refine c.map_isSolutionOn_of_isSolutionOn (I := I) A g lambda hlambda ?_ hc hU
  intro t ht
  rcases hJ with hJ | hJ
  · rw [hJ] at ht ⊢
    exact uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((uniqueDiffOn_Ico s u) t ht)
  · rw [hJ] at ht ⊢
    exact uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((uniqueDiffOn_Icc hsu) t ht)

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
