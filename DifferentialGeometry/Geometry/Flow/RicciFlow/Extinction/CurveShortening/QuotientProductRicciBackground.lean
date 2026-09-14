import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveSmoothLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductGeometry
import DifferentialGeometry.Topology.Covering.AddCircleLift
import DifferentialGeometry.Topology.Manifold.AddCircle
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Topology

private theorem isInvertible_of_injective_realLine (f : ℝ →L[ℝ] ℝ)
    (hf : Function.Injective f) : f.IsInvertible := by
  have hf1 : f 1 ≠ 0 := by
    intro h
    refine one_ne_zero (hf ?_)
    rw [h, map_zero]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (f 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · refine ContinuousLinearMap.ext fun x => ?_
    have hx : ∀ y : ℝ, f y = y * f 1 := fun y => by
      simpa [smul_eq_mul] using f.map_smul y (1 : ℝ)
    have hgy : ∀ y : ℝ, ((f 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) y = (f 1)⁻¹ * y :=
      fun y => rfl
    rw [ContinuousLinearMap.comp_apply, hgy, hx ((f 1)⁻¹ * x),
      ContinuousLinearMap.id_apply]
    field_simp
  · refine ContinuousLinearMap.ext fun x => ?_
    have hx : ∀ y : ℝ, f y = y * f 1 := fun y => by
      simpa [smul_eq_mul] using f.map_smul y (1 : ℝ)
    have hgy : ∀ y : ℝ, ((f 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) y = (f 1)⁻¹ * y :=
      fun y => rfl
    rw [ContinuousLinearMap.comp_apply, hx x, hgy, ContinuousLinearMap.id_apply]
    field_simp

private theorem isLocalDiffeomorphAt_addCircle_coe (t : ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun s : ℝ => (s : AddCircle (1 : ℝ))) t := by
  have hinv : ∀ y ∈ (univ : Set ℝ),
      (fderiv ℝ
        (writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) y
          (fun s : ℝ => (s : AddCircle (1 : ℝ))))
        (extChartAt 𝓘(ℝ, ℝ) y y)).IsInvertible := by
    intro y _
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun s : ℝ => (s : AddCircle (1 : ℝ))) y :=
      AddCircle.contMDiff_coe.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
    have hderiv : fderiv ℝ
          (writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) y
            (fun s : ℝ => (s : AddCircle (1 : ℝ))))
          (extChartAt 𝓘(ℝ, ℝ) y y) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) y := by
      rw [hmd.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
    rw [hderiv]
    exact isInvertible_of_injective_realLine _
      (AddCircle.bijective_mfderiv_coe y).1
  obtain ⟨Φ, htΦ, -, hEq⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)) (M := ℝ) (N := AddCircle (1 : ℝ))
      (x := t) isOpen_univ (mem_univ t) AddCircle.contMDiff_coe.contMDiffOn hinv
  exact ⟨Φ, htΦ, hEq⟩

theorem exists_contDiffWithinAt_addCircle_lift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set E} {q : E} {f : E → AddCircle (1 : ℝ)}
    (hf : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U q) :
    ∃ φ : E → ℝ, ContDiffWithinAt ℝ ∞ φ U q ∧
      (fun p => (φ p : AddCircle (1 : ℝ))) =ᶠ[𝓝[U] q] f := by
  obtain ⟨r₀, hr₀⟩ : ∃ r : ℝ, (r : AddCircle (1 : ℝ)) = f q :=
    ⟨_, AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))⟩
  obtain ⟨Φ, hqΦ, hΦ⟩ := isLocalDiffeomorphAt_addCircle_coe r₀
  have hΦq : Φ r₀ = f q := (hΦ hqΦ).symm.trans hr₀
  have hfq : f q ∈ Φ.target := by
    rw [← hΦq]
    exact Φ.toPartialEquiv.map_source hqΦ
  refine ⟨fun p => (Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p), ?_, ?_⟩
  · have hsymm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (Φ.symm : AddCircle (1 : ℝ) → ℝ) (f q) :=
      Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hfq)
    have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        ((Φ.symm : AddCircle (1 : ℝ) → ℝ) ∘ f) U q :=
      hsymm.contMDiffWithinAt.comp q hf (fun _ _ => mem_univ _)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp hcomp
  · filter_upwards
      [(hf.continuousWithinAt).preimage_mem_nhdsWithin (Φ.open_target.mem_nhds hfq)]
      with p hfp
    have h1 : Φ ((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) = f p :=
      Φ.toPartialEquiv.right_inv' hfp
    have h2 : (((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) : AddCircle (1 : ℝ)) =
        Φ ((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) :=
      hΦ (Φ.toPartialEquiv.map_target hfp)
    exact h2.trans h1

theorem contMDiffWithinAt_of_exists_addCircle_lift {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set E} {q : E} {f : E → AddCircle (1 : ℝ)} (hq : q ∈ U)
    (h : ∃ φ : E → ℝ, ContDiffWithinAt ℝ ∞ φ U q ∧
      (fun p => (φ p : AddCircle (1 : ℝ))) =ᶠ[𝓝[U] q] f) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U q := by
  obtain ⟨φ, hφ, hφf⟩ := h
  have hφ' : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ U q :=
    contMDiffWithinAt_iff_contDiffWithinAt.mpr hφ
  have hcoe : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun p => (φ p : AddCircle (1 : ℝ))) U q :=
    (AddCircle.contMDiff_coe.contMDiffAt).comp_contMDiffWithinAt q hφ'
  exact hcoe.congr_of_eventuallyEq hφf.symm (hφf.symm.eq_of_nhdsWithin hq)

theorem exists_contDiffOn_addCircle_lift_of_contMDiffOn {s : Set ℝ} (hs : Convex ℝ s)
    (hne : s.Nonempty) (f : ℝ × ℝ → AddCircle (1 : ℝ))
    (hper : ∀ p : ℝ × ℝ, f (p.1 + 1, p.2) = f p)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ f ((univ : Set ℝ) ×ˢ s)) :
    ∃ (g : ℝ × ℝ → ℝ) (d : ℤ), ContDiffOn ℝ ∞ g ((univ : Set ℝ) ×ˢ s) ∧
      (∀ q ∈ (univ : Set ℝ) ×ˢ s, (g q : AddCircle (1 : ℝ)) = f q) ∧
      (∀ q ∈ (univ : Set ℝ) ×ˢ s, g (q.1 + 1, q.2) = g q + d) := by
  have hloc : ∀ q ∈ (univ : Set ℝ) ×ˢ s, ∃ φ : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ φ ((univ : Set ℝ) ×ˢ s) q ∧
      (fun p => (φ p : AddCircle (1 : ℝ))) =ᶠ[𝓝[(univ : Set ℝ) ×ˢ s] q] f :=
    fun q hq => exists_contDiffWithinAt_addCircle_lift (hf q hq)
  exact exists_contDiffOn_addCircle_lift_of_periodic hs hne f hper hloc

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem iterCov_metricRicci_one_eq_totalNabla0SFun [T2Space M]
    (g : SmoothRiemannianMetric I M) (x : M) :
    iterCov (I := I) g 2 (metricRicci (I := I) g) 1 x =
      totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g)
        (metricRicci (I := I) g) x := by
  have hcov : (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
      (I := I) g).ContMDiffCovariantDerivativeLocally (∞ : WithTop ℕ∞) :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g
  have h1 := DifferentialGeometry.PDE.RicciFlow.iterCov_realizes (I := I) g
    (metricRicci (I := I) g) 0
  have h2 := totalNabla0S_realizes (𝕜 := ℝ) 2
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g)
    (metricRicci (I := I) g)
    (totalNabla0S_regularity 2 _ hcov (metricRicci (I := I) g))
  exact congrArg (fun T => T x) (Tensor0SBundle.totalNabla0SRealizes_unique h1 h2)

theorem exists_ricciBackground_quotientProduct_of_isSolutionOn (A : QuotientProductAtlas I M)
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda)
    (hflow : letI := A.charts
      letI := A.smoothManifold
      IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
        (show SolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D from
          ⟨quotientProductFamily A B.family lambda hlambda⟩)) :
    letI := A.charts
    letI := A.smoothManifold
    ∃ Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D a b,
      Bhat.family = quotientProductFamily A B.family lambda hlambda ∧
      Bhat.B₀ = B.B₀ ∧ Bhat.B₁ = B.B₁ ∧ Bhat.B₂ = B.B₂ := by
  let := A.charts
  let := A.smoothManifold
  have hricci : ∀ t ∈ Icc a b, ∀ p : M × Surgery.Topology.Circle,
      normSq0S (quotientProductMetric A (B.family.metric t) lambda hlambda) p 2
        (iterCov (quotientProductMetric A (B.family.metric t) lambda hlambda) 2
          (metricRicci (quotientProductMetric A (B.family.metric t) lambda hlambda)) 0 p) ≤
        B.B₀ ^ 2 := by
    intro t ht p
    rw [(quotientProduct_iterCov_normSq A (B.family.metric t) lambda hlambda 0 p).2]
    exact B.ricci_bound t ht p.1
  have hriemann : ∀ t ∈ Icc a b, ∀ p : M × Surgery.Topology.Circle,
      normSq0S (quotientProductMetric A (B.family.metric t) lambda hlambda) p 4
        (iterCov (quotientProductMetric A (B.family.metric t) lambda hlambda) 4
          (metricRm04 (quotientProductMetric A (B.family.metric t) lambda hlambda)) 0 p) ≤
        B.B₁ ^ 2 := by
    intro t ht p
    rw [(quotientProduct_iterCov_normSq A (B.family.metric t) lambda hlambda 0 p).1]
    exact B.riemann_bound t ht p.1
  have hnabla : ∀ t ∈ Icc a b, ∀ p : M × Surgery.Topology.Circle,
      normSq0S (quotientProductMetric A (B.family.metric t) lambda hlambda) p 3
        (iterCov (quotientProductMetric A (B.family.metric t) lambda hlambda) 2
          (metricRicci (quotientProductMetric A (B.family.metric t) lambda hlambda)) 1 p) ≤
        B.B₂ ^ 2 := by
    intro t ht p
    have hb := iterCov_metricRicci_one_eq_totalNabla0SFun (I := I) (B.family.metric t) p.1
    rw [(quotientProduct_iterCov_normSq A (B.family.metric t) lambda hlambda 1 p).2, hb]
    exact B.nablaRicci_bound t ht p.1
  refine ⟨{ family := quotientProductFamily A B.family lambda hlambda
            smooth := hflow.smoothMetric
            lt := B.lt
            regular := B.regular
            equation := hflow
            B₀ := B.B₀
            B₁ := B.B₁
            B₂ := B.B₂
            B₀_nonneg := B.B₀_nonneg
            B₁_nonneg := B.B₁_nonneg
            B₂_nonneg := B.B₂_nonneg
            ricci_bound := ?_
            riemann_bound := ?_
            nablaRicci_bound := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro t ht p
    exact hricci t ht p
  · intro t ht p
    exact hriemann t ht p
  · intro t ht p
    exact hnabla t ht p

private theorem ricciTensor_scaleEuclideanReal_eq_zero (lambda : ℝ) (hlambda : 0 < lambda)
    (y : ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ) y) :
    ricciTensor (I := 𝓘(ℝ, ℝ)) (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2)
      (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ))) y v w = 0 := by
  rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor
    (g := DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2) (pow_pos hlambda 2)
      (DifferentialGeometry.euclideanMetric (E := ℝ))) (x := y) v w]
  exact DifferentialGeometry.PDE.RicciFlow.metricRicciAt_scaleMetric_euclideanMetric (lambda ^ 2)
    (pow_pos hlambda 2) y (vec2 (I := 𝓘(ℝ, ℝ)) (x := y) v w)

omit [CompleteSpace E] in
private theorem ricciTensor_quotientProductMetric_eq_zero [T2Space M] [I.Boundaryless]
    [BoundarylessManifold I M] (A : QuotientProductAtlas I M) (g : SmoothRiemannianMetric I M)
    (hflat : ∀ (y : M) (v w : TangentSpace I y), ricciTensor g y v w = 0)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∀ (q : M × Surgery.Topology.Circle), ∀ X Y : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q,
      ricciTensor (I := I.prod 𝓘(ℝ, ℝ)) (quotientProductMetric A g lambda hlambda) q X Y = 0 := by
  let := A.charts
  let := A.smoothManifold
  intro q X Y
  obtain ⟨p, rfl⟩ := surjective_productCoverProjection (M := M) q
  obtain ⟨V, hV⟩ := (A.cover_derivative_bijective p).2 X
  obtain ⟨W, hW⟩ := (A.cover_derivative_bijective p).2 Y
  rw [← hV, ← hW, ← ricciTensor_localPull (g := quotientProductMetric A g lambda hlambda)
    (Phi := productCoverProjection (M := M))
    (hPhi := isLocalDiffeomorph_productCoverProjection A) p V W]
  have hcover : coverProductMetric g lambda hlambda =
      g.prod (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2)
        (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ))) := rfl
  rw [quotientProductMetric_localPull, hcover, ricciTensor_productMetric, hflat p.1 V.1 W.1,
    zero_add]
  exact ricciTensor_scaleEuclideanReal_eq_zero lambda hlambda p.2 V.2 W.2

theorem isSolutionOn_const_quotientProductFamily_of_ricciTensor_eq_zero [T2Space M]
    [I.Boundaryless] [BoundarylessManifold I M] (A : QuotientProductAtlas I M)
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    (hflat : ∀ (y : M) (v w : TangentSpace I y), ricciTensor g y v w = 0)
    (lambda : ℝ) (hlambda : 0 < lambda) (D : RealTimeInterval) :
    letI := A.charts
    letI := A.smoothManifold
    IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
      (show SolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D from
        ⟨quotientProductFamily A
          (show SolutionFamily (I := I) (M := M) from ⟨fun _ => g⟩) lambda hlambda⟩) := by
  let := A.charts
  let := A.smoothManifold
  exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_const_of_ricciTensor_eq_zero
    (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
    (quotientProductMetric A g lambda hlambda)
    (fun q X Y => ricciTensor_quotientProductMetric_eq_zero A g hflat lambda hlambda q X Y) D

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
