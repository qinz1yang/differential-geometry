import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product

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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem coverLift_space_mdifferentiableAt {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.coverLift z t) x := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz' : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.projection.lift z t) x := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞
        ((fun p : ℝ × ℝ => c.projection.lift p.1 p.2) ∘ fun z : ℝ => (z, t)) univ x :=
      (hc.1 (x, t) hmem).comp x hz' hto
    exact (contMDiffWithinAt_univ.mp hcomp).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => c.y z t) x := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        ((fun p : ℝ × ℝ => c.y p.1 p.2) ∘ fun z : ℝ => (z, t)) univ x :=
      ((hc.2 (x, t) hmem).contMDiffWithinAt).comp x hz' hto
    exact (contMDiffWithinAt_univ.mp hcomp).mdifferentiableAt (by simp)
  exact h1.prodMk h2

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem map_X_eq (A : QuotientProductAtlas I M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.X (I := I.prod 𝓘(ℝ, ℝ)) x t =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (c.coverLift x t) (c.X (I := I) x t) := by
  let := A.charts
  let := A.smoothManifold
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun z => c.coverLift z t) x :=
    c.coverLift_space_mdifferentiableAt (I := I) hc x t ht
  have hf : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (productCoverProjection (M := M)) (c.coverLift x t) :=
    (A.cover_smooth.mdifferentiable (by simp)).mdifferentiableAt
  have hcongr : (fun y : ℝ => c.map (y : Surgery.Topology.Circle) t)
      = productCoverProjection (M := M) ∘ fun y => c.coverLift y t := by
    funext y
    exact (c.coverProjection_lift y t).symm
  have hcomp : (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (fun y : ℝ => c.map (y : Surgery.Topology.Circle) t) x) (1 : ℝ) =
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (c.coverLift x t)) ((mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (fun y : ℝ => c.coverLift y t) x) (1 : ℝ)) := by
    rw [hcongr, mfderiv_comp x hf hγ]
    rfl
  exact hcomp.trans (congrArg (fun z =>
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (productCoverProjection (M := M)) (c.coverLift x t)) z)
    (c.cover_spatial_derivative (I := I) J hc x t ht))

omit [CompleteSpace E] in
theorem map_speed_eq [T2Space M] (A : QuotientProductAtlas I M) [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.speed (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      c.speed g lambda x t := by
  let := A.charts
  let := A.smoothManifold
  have hstep : (quotientProductMetric A (g t) lambda hlambda).inner
        (productCoverProjection (M := M) (c.coverLift x t))
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t) (c.X (I := I) x t))
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t) (c.X (I := I) x t)) =
      c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) := by
    refine (localPullMetric_inner (quotientProductMetric A (g t) lambda hlambda)
      (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
      (c.coverLift x t) (c.X (I := I) x t) (c.X (I := I) x t)).symm.trans ?_
    rw [quotientProductMetric_localPull A (g t) lambda hlambda]
    exact coverProductMetric_inner (g t) lambda hlambda (c.coverLift x t)
      (c.X (I := I) x t) (c.X (I := I) x t)
  rw [CurveMap.speed, ProductCurve.speed]
  simp only [CurveMap.lift]
  rw [← c.coverProjection_lift x t, c.map_X_eq A hc x t ht]
  exact congrArg Real.sqrt hstep

omit [CompleteSpace E] in
theorem map_unitTangent_eq [T2Space M] (A : QuotientProductAtlas I M) [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.unitTangent (I := I.prod 𝓘(ℝ, ℝ))
        (fun s => quotientProductMetric A (g s) lambda hlambda) x t =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (c.coverLift x t) (c.unitTangent g lambda x t) := by
  let := A.charts
  let := A.smoothManifold
  rw [CurveMap.unitTangent, ProductCurve.unitTangent,
    c.map_speed_eq A g lambda hlambda hc x t ht, c.map_X_eq A hc x t ht]
  exact (ContinuousLinearMap.map_smul
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
      (c.coverLift x t)) ((c.speed g lambda x t)⁻¹) (c.X (I := I) x t)).symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem map_X_eq_zero_iff [T2Space M] (A : QuotientProductAtlas I M) [I.Boundaryless]
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.X (I := I.prod 𝓘(ℝ, ℝ)) x t = 0 ↔ c.X (I := I) x t = 0 := by
  let := A.charts
  let := A.smoothManifold
  constructor
  · intro h
    have h' : (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t)) (c.X (I := I) x t) =
        (0 : TangentSpace (I.prod 𝓘(ℝ, ℝ))
          (productCoverProjection (M := M) (c.coverLift x t))) := by
      rw [← c.map_X_eq A hc x t ht]
      exact h
    exact (A.cover_derivative_bijective (c.coverLift x t)).injective
      (h'.trans (map_zero (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (c.coverLift x t))).symm)
  · intro h
    have h'' : (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
          (c.coverLift x t)) (c.X (I := I) x t) =
        (0 : TangentSpace (I.prod 𝓘(ℝ, ℝ))
          (productCoverProjection (M := M) (c.coverLift x t))) := by
      rw [h]
      exact map_zero _
    rw [c.map_X_eq A hc x t ht]
    exact h''

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem map_immersedOn_iff [T2Space M] (A : QuotientProductAtlas I M) [I.Boundaryless]
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.ImmersedOn (I := I.prod 𝓘(ℝ, ℝ)) J ↔ c.ImmersedOn (I := I) J := by
  let := A.charts
  let := A.smoothManifold
  constructor
  · intro h x t ht
    by_contra hx
    exact h x t ht ((c.map_X_eq_zero_iff A hc x t ht).mpr hx)
  · intro h x t ht
    by_contra hx
    exact h x t ht ((c.map_X_eq_zero_iff A hc x t ht).mp hx)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem smoothOn_map (A : QuotientProductAtlas I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.SmoothOn (I := I.prod 𝓘(ℝ, ℝ)) J := by
  let := A.charts
  let := A.smoothManifold
  have hcover : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.coverLift p.1 p.2) (univ ×ˢ J) := by
    intro p hp
    exact (hc.1 p hp).prodMk (hc.2 p hp).contMDiffWithinAt
  refine (A.cover_smooth.comp_contMDiffOn hcover).congr (fun p _ => ?_)
  exact (c.coverProjection_lift p.1 p.2).symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem coverLift_time_mdifferentiableWithinAt {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun s => c.coverLift x s) J t := by
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (x, s)) J t := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hto : Set.MapsTo (fun s : ℝ => (x, s)) J ((univ : Set ℝ) ×ˢ J) :=
    fun s hs => ⟨mem_univ x, hs⟩
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun s => c.projection.lift x s) J t :=
    (c.projection.time_slice_contMDiffWithinAt (I := I) J hc.1 x t ht).mdifferentiableWithinAt
      (by simp)
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => c.y x s) J t := by
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        ((fun p : ℝ × ℝ => c.y p.1 p.2) ∘ fun s : ℝ => (x, s)) J t :=
      ((hc.2 (x, t) ⟨mem_univ x, ht⟩).contMDiffWithinAt).comp t hz hto
    exact hcomp.mdifferentiableWithinAt (by simp)
  exact h1.prodMk h2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem cover_time_derivative {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J)
    (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t) :
    mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun s => c.coverLift x s) J t (1 : ℝ) =
      c.velocity (I := I) J x t := by
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun s => c.projection.lift x s) J t :=
    (c.projection.time_slice_contMDiffWithinAt (I := I) J hc.1 x t ht).mdifferentiableWithinAt
      (by simp)
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => c.y x s) J t := by
    have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (x, s)) J t := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
    have hto : Set.MapsTo (fun s : ℝ => (x, s)) J ((univ : Set ℝ) ×ˢ J) :=
      fun s hs => ⟨mem_univ x, hs⟩
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        ((fun p : ℝ × ℝ => c.y p.1 p.2) ∘ fun s : ℝ => (x, s)) J t :=
      ((hc.2 (x, t) ⟨mem_univ x, ht⟩).contMDiffWithinAt).comp t hz hto
    exact hcomp.mdifferentiableWithinAt (by simp)
  have hpair := mfderivWithin_prodMk h1 h2 huniq
  have hy : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => c.y x s) J t (1 : ℝ) =
      derivWithin (c.y x) J t := by
    rw [mfderivWithin_eq_fderivWithin]
    rfl
  rw [show (fun s => c.coverLift x s) = fun s => (c.projection.lift x s, c.y x s) from rfl,
    hpair]
  exact Prod.ext rfl hy

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem map_velocity_eq [T2Space M] (A : QuotientProductAtlas I M) [I.Boundaryless]
    (J : Set ℝ) (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J)
    (huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (c.coverLift x t) (c.velocity (I := I) J x t) := by
  let := A.charts
  let := A.smoothManifold
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
      (fun s => c.coverLift x s) J t :=
    c.coverLift_time_mdifferentiableWithinAt (I := I) hc x t ht
  have hf : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (productCoverProjection (M := M)) (c.coverLift x t) :=
    (A.cover_smooth.mdifferentiable (by simp)).mdifferentiableAt
  have hcongr : c.map.lift x = productCoverProjection (M := M) ∘ fun s => c.coverLift x s := by
    funext s
    exact (c.coverProjection_lift x s).symm
  have hvel : c.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t =
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (c.coverLift x t)) ((mfderivWithin 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (fun s => c.coverLift x s) J t) (1 : ℝ)) := by
    rw [CurveMap.velocity, hcongr,
      mfderivWithin_comp t hf hγ (fun s _ => Set.mem_univ (c.coverLift x s)) huniq,
      mfderivWithin_univ]
    rfl
  rw [hvel, c.cover_time_derivative hc x t ht huniq]

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
