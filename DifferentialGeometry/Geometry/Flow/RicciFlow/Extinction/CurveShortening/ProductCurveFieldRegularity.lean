import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringDerivative

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ProductCurve

variable (c : ProductCurve M)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem field_smoothOn_X {J : Set ℝ} (hc : c.SmoothOn (I := I) J) :
    (c.X (I := I)).SmoothOn (I := I) J := by
  have hcover_self : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.coverLift p.1 p.2) (univ ×ˢ J) :=
    fun p hp => (hc.1 p hp).prodMk (hc.2 p hp).contMDiffWithinAt
  have hcover : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.coverLift p.1 p.2) (univ ×ˢ J) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcover_self
    exact hcover_self
  have h := ContMDiffOn.time_mfderivWithin (I := 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, ℝ))
    (N := M × ℝ) (γ := fun x t => c.coverLift x t) (s := univ) (u := J)
    (n := ∞) (m := ∞) hcover uniqueDiffOn_univ le_rfl
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  intro t ht x
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  have hslice := (h (x, t) hmem).comp x hz hto
  rw [contMDiffWithinAt_univ] at hslice
  refine hslice.congr_of_eventuallyEq (Eventually.of_forall (fun z => ?_))
  simp only [Function.comp_apply, mfderivWithin_univ]
  rw [show ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm (1 : ℝ) :
      TangentSpace 𝓘(ℝ, ℝ) z) = 1 from rfl]
  exact congrArg
    (fun v => (⟨c.coverLift z t, v⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)))
    (ProductCurve.cover_spatial_derivative (I := I) c J hc z t ht).symm

omit [CompleteSpace E] in
theorem field_smoothOn_inner [T2Space M] {J : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (V W : c.Field (I := I))
    (hV : V.SmoothOn (I := I) J) (hW : W.SmoothOn (I := I) J) :
    ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x => c.inner g lambda x t (V x t) (W x t)) := by
  intro t ht x
  have hb : ContMDiffWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ => c.coverLift z t) univ x :=
    (Bundle.contMDiffAt_totalSpace.mp (hV t ht x)).1.contMDiffWithinAt
  have hψ : ContMDiffAt 𝓘(ℝ, ℝ)
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ →L[ℝ] E × ℝ →L[ℝ] ℝ)) ∞
      (fun z : ℝ => (⟨c.coverLift z t,
        (coverProductMetric (g t) lambda hlambda).inner (c.coverLift z t)⟩ :
        TotalSpace (E × ℝ →L[ℝ] E × ℝ →L[ℝ] ℝ)
          (fun p : M × ℝ =>
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) x :=
    ((coverProductMetric (g t) lambda hlambda).contMDiff.contMDiffAt).comp_contMDiffWithinAt x hb
  have htotal := ContMDiffAt.clm_bundle_apply₂ (F₁ := E × ℝ) (F₂ := E × ℝ) (F₃ := ℝ)
    (E₁ := fun p : M × ℝ => TangentSpace (I.prod 𝓘(ℝ, ℝ)) p)
    (E₂ := fun p : M × ℝ => TangentSpace (I.prod 𝓘(ℝ, ℝ)) p)
    (E₃ := fun _ : M × ℝ => ℝ) hψ (hV t ht x) (hW t ht x)
  rw [contMDiffAt_totalSpace] at htotal
  have hinner : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ => (coverProductMetric (g t) lambda hlambda).inner
        (c.coverLift z t) (V z t) (W z t)) x := htotal.2
  refine hinner.congr_of_eventuallyEq (Eventually.of_forall (fun z => ?_))
  simp only [ProductCurve.inner]
  exact (coverProductMetric_inner (g t) lambda hlambda (c.coverLift z t)
    (V z t) (W z t)).symm


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem field_smoothOn_const_smul {J : Set ℝ} (a : ℝ → ℝ → ℝ)
    (ha : ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x => a x t))
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) :
    Field.SmoothOn (I := I) (fun x t => a x t • V x t) J := by
  intro t ht x
  let e := trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) (c.coverLift x t)
  have hbase : c.coverLift x t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hV' : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun z : ℝ => (⟨c.coverLift z t, V z t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) x := hV t ht x
  have hb' : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun z : ℝ => c.coverLift z t) x :=
    (Bundle.contMDiffAt_totalSpace.mp hV').1
  have hVrep : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E × ℝ) ∞
      (fun z : ℝ => (e (⟨c.coverLift z t, V z t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))).2) x :=
    (Bundle.contMDiffAt_totalSpace.mp hV').2
  have hsm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E × ℝ) ∞
      (fun z : ℝ => a z t • (e (⟨c.coverLift z t, V z t⟩ :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))).2) x :=
    contMDiffAt_iff_contDiffAt.mpr
      ((contMDiffAt_iff_contDiffAt.mp (ha t ht x)).smul
        (contMDiffAt_iff_contDiffAt.mp hVrep))
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hb', ?_⟩
  refine hsm.congr_of_eventuallyEq ?_
  filter_upwards [hb'.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)] with z hz
  exact (e.linear ℝ hz).map_smul (a z t) (V z t)


omit [CompleteSpace E] in
theorem field_smoothOn_invSpeed [T2Space M] {J : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) :
    ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x => (c.speed g lambda x t)⁻¹) := by
  intro t ht x
  have hX : (c.X (I := I)).SmoothOn (I := I) J := c.field_smoothOn_X (I := I) hc
  have hinner := c.field_smoothOn_inner (I := I) g lambda hlambda (c.X (I := I)) (c.X (I := I))
    hX hX t ht x
  have hmet : c.inner g lambda x t (c.X x t) (c.X x t) =
      (coverProductMetric (g t) lambda hlambda).inner (c.coverLift x t)
        (c.X x t) (c.X x t) :=
    (coverProductMetric_inner (g t) lambda hlambda (c.coverLift x t) (c.X x t) (c.X x t)).symm
  have hpos : 0 < c.inner g lambda x t (c.X x t) (c.X x t) := by
    rw [hmet]
    exact (coverProductMetric (g t) lambda hlambda).pos (c.coverLift x t) (c.X x t) (hi x t ht)
  have hs : ContDiffAt ℝ ∞ (fun x => c.speed g lambda x t) x := by
    change ContDiffAt ℝ ∞
      (fun x => Real.sqrt (c.inner g lambda x t (c.X x t) (c.X x t))) x
    exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp x (contMDiffAt_iff_contDiffAt.mp hinner)
  exact contMDiffAt_iff_contDiffAt.mpr (hs.inv (ne_of_gt (Real.sqrt_pos.2 hpos)))

omit [CompleteSpace E] in
theorem field_smoothOn_unitTangent [T2Space M] {J : Set ℝ} (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) :
    (c.unitTangent g lambda).SmoothOn (I := I) J := by
  have hX : (c.X (I := I)).SmoothOn (I := I) J := c.field_smoothOn_X (I := I) hc
  have hinv := c.field_smoothOn_invSpeed (I := I) g lambda hlambda hc hi
  have hsm := c.field_smoothOn_const_smul (I := I) (fun x t => (c.speed g lambda x t)⁻¹)
    hinv (c.X (I := I)) hX
  change Field.SmoothOn (I := I) (fun x t => (c.speed g lambda x t)⁻¹ • c.X x t) J
  exact hsm


omit [CompleteSpace E] in
theorem map_isSolutionOn_of_interval_of_isSolutionOn (A : QuotientProductAtlas I M) [T2Space M]
    [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {s u : ℝ} (hsu : s < u) {J : Set ℝ} (hJ : J = Ico s u ∨ J = Icc s u)
    (hc : c.IsSolutionOn g lambda J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  have hU : (c.unitTangent g lambda).SmoothOn (I := I) J :=
    c.field_smoothOn_unitTangent (I := I) g lambda hlambda hc.smooth hc.immersed
  exact c.map_isSolutionOn_of_isSolutionOn_of_interval A g lambda hlambda hsu hJ hc hU

end ProductCurve


omit [CompleteSpace E] in
theorem product_solution_lift_of_smoothBase_of_localLift (A : QuotientProductAtlas I M)
    [T2Space M] [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (hlambda : 0 < lambda) (c : CurveMap (M × Surgery.Topology.Circle)) {s u : ℝ} (hsu : s < u)
    {J : Set ℝ} (hJ : J = Ico s u ∨ J = Icc s u)
    (hbase : CurveMap.SmoothOn (I := I) (fun z t => (c z t).1) J)
    (hcircle : ∀ x t, ∃ localLift : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ localLift (univ ×ˢ univ) (x, t) ∧
      ∀ᶠ p in 𝓝[univ ×ˢ univ] (x, t),
        (localLift p : Surgery.Topology.Circle) = (c (p.1 : Surgery.Topology.Circle) p.2).2)
    (hc : letI := A.charts
      letI := A.smoothManifold
      c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    ∃ ĉ : ProductCurve M, ĉ.IsSolutionOn g lambda J ∧
      ∀ z t, t ∈ J → ĉ.map z t = c z t := by
  let := A.charts
  let := A.smoothManifold
  set f : ℝ × ℝ → Surgery.Topology.Circle :=
    fun p => (c (p.1 : Surgery.Topology.Circle) p.2).2 with hf
  have hper : ∀ p : ℝ × ℝ, f (p.1 + 1, p.2) = f p := by
    intro p
    have h1 : ((p.1 + 1 : ℝ) : Surgery.Topology.Circle) = (p.1 : Surgery.Topology.Circle) := by
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
    simp only [f]
    rw [h1]
  have hloc : ∀ q ∈ (univ : Set ℝ) ×ˢ (univ : Set ℝ), ∃ φ : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ φ ((univ : Set ℝ) ×ˢ univ) q ∧
      (fun p => (φ p : Surgery.Topology.Circle)) =ᶠ[𝓝[(univ : Set ℝ) ×ˢ univ] q] f :=
    fun q _ => hcircle q.1 q.2
  obtain ⟨y, d, hy_smooth, hy_lift, hy_inc⟩ :=
    DifferentialGeometry.Topology.exists_contDiffOn_addCircle_lift_of_periodic
      convex_univ univ_nonempty f hper hloc
  let yfun : ℝ → ℝ → ℝ := fun x t => y (x, t)
  let ĉ : ProductCurve M :=
    { map := c, y := yfun, degree := d,
      lift_eq := fun x t => hy_lift (x, t) ⟨trivial, trivial⟩,
      increment := fun x t => hy_inc (x, t) ⟨trivial, trivial⟩ }
  have hĉsm : ĉ.SmoothOn (I := I) J := by
    refine ⟨?_, ?_⟩
    · change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => (c (p.1 : Surgery.Topology.Circle) p.2).1) (univ ×ˢ J)
      exact hbase
    · change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => yfun p.1 p.2) (univ ×ˢ J)
      exact hy_smooth.mono fun p _ => ⟨mem_univ p.1, mem_univ p.2⟩
  have huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t := by
    intro t ht
    rcases hJ with hJ | hJ
    · rw [hJ] at ht ⊢
      exact (uniqueDiffOn_Ico s u t ht).uniqueMDiffWithinAt
    · rw [hJ] at ht ⊢
      exact (uniqueDiffOn_Icc hsu t ht).uniqueMDiffWithinAt
  have himm : ĉ.ImmersedOn (I := I) J := by
    intro x t ht
    have hXeq := ĉ.map_X_eq (I := I) A hĉsm x t ht
    have hne : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (ĉ.coverLift x t) (ĉ.X (I := I) x t) ≠ 0 := by
      rw [← hXeq]
      exact hc.immersed x t ht
    exact fun hzero => hne (by rw [hzero]; exact map_zero _)
  have hU : (ĉ.unitTangent g lambda).SmoothOn (I := I) J :=
    ĉ.field_smoothOn_unitTangent (I := I) g lambda hlambda hĉsm himm
  have heq : ∀ x t, t ∈ J → ĉ.velocity (I := I) J x t = ĉ.curvatureVector g lambda x t := by
    intro x t ht
    have h1 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (ĉ.coverLift x t) (ĉ.velocity (I := I) J x t) =
        ĉ.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t :=
      (ĉ.map_velocity_eq (I := I) A J hĉsm x t ht (huniq t ht)).symm
    have h2 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (productCoverProjection (M := M))
        (ĉ.coverLift x t) (ĉ.curvatureVector g lambda x t) =
        ĉ.map.velocity (I := I.prod 𝓘(ℝ, ℝ)) J x t :=
      (ĉ.map_curvatureVector_eq (I := I) A g lambda hlambda hĉsm hU x t ht).trans
        (hc.equation x t ht).symm
    exact (A.cover_derivative_bijective (ĉ.coverLift x t)).injective (h1.trans h2.symm)
  exact ⟨ĉ, ⟨hĉsm, himm, heq⟩, fun _ _ _ => rfl⟩

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem X_eq_zero_of_lift_eq {c : CurveMap M} {x t : ℝ}
    (h : ∀ y : ℝ, c.lift y t = c.lift x t) : c.X (I := I) x t = 0 := by
  have hfun : (fun y : ℝ => c.lift y t) = fun _ : ℝ => c.lift x t := funext h
  rw [CurveMap.X, hfun, mfderiv_const]
  exact IsZeroApply.zero_apply _

omit [CompleteSpace E] in
theorem not_isSolutionOn_of_eq_const {c : CurveMap M} {p : M} (h : ∀ x t, c.lift x t = p)
    {J : Set ℝ} (hJ : J.Nonempty) (g : ℝ → SmoothRiemannianMetric I M) :
    ¬ c.IsSolutionOn (I := I) g J := by
  obtain ⟨t, ht⟩ := hJ
  exact fun hc => hc.immersed 0 t ht
    (X_eq_zero_of_lift_eq (I := I) fun y => (h y t).trans (h 0 t).symm)

end CurveMap


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
