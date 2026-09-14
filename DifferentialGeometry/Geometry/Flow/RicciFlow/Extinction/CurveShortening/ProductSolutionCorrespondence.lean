import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveFieldRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveSmoothLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionReduction

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

private theorem exists_contDiffWithinAt_addCircle_lift {U : Set (ℝ × ℝ)} {q : ℝ × ℝ}
    {f : ℝ × ℝ → AddCircle (1 : ℝ)}
    (hf : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ f U q) :
    ∃ φ : ℝ × ℝ → ℝ, ContDiffWithinAt ℝ ∞ φ U q ∧
      (fun p => (φ p : AddCircle (1 : ℝ))) =ᶠ[𝓝[U] q] f := by
  let r₀ : ℝ := ((AddCircle.equivIco (1 : ℝ) 0 (f q) : Ico (0 : ℝ) (0 + 1)) : ℝ)
  have hr₀ : (r₀ : AddCircle (1 : ℝ)) = f q :=
    AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
  obtain ⟨Φ, hqΦ, hΦ⟩ := isLocalDiffeomorphAt_addCircle_coe r₀
  have hΦq : Φ (r₀) = f q := (hΦ hqΦ).symm.trans hr₀
  have hfq : f q ∈ Φ.target := by
    rw [← hΦq]
    exact Φ.toPartialEquiv.map_source hqΦ
  refine ⟨fun p => (Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p), ?_, ?_⟩
  · have hsymm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (Φ.symm : AddCircle (1 : ℝ) → ℝ) (f q) :=
      Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hfq)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp
      (hsymm.contMDiffWithinAt.comp q hf (fun _ _ => mem_univ _))
  · filter_upwards [(hf.continuousWithinAt).preimage_mem_nhdsWithin (Φ.open_target.mem_nhds hfq)]
      with p hfp
    have h1 : Φ ((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) = f p :=
      Φ.toPartialEquiv.right_inv' hfp
    have h2 : (((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) : AddCircle (1 : ℝ)) =
        Φ ((Φ.symm : AddCircle (1 : ℝ) → ℝ) (f p)) :=
      hΦ (Φ.toPartialEquiv.map_target hfp)
    exact h2.trans h1

omit [CompleteSpace E] in
private theorem contMDiff_fst_quotientProductAtlas (A : QuotientProductAtlas I M) [I.Boundaryless] :
    letI := A.charts
    letI := A.smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
      (Prod.fst : M × Surgery.Topology.Circle → M) := by
  let := A.charts
  let := A.smoothManifold
  intro z
  obtain ⟨w, hw⟩ := surjective_productCoverProjection (M := M) z
  obtain ⟨Φ, hwΦ, hEqΦ⟩ := isLocalDiffeomorph_productCoverProjection (I := I) (M := M) A w
  have hzΦ : z ∈ Φ.target := by
    rw [← hw, hEqΦ hwΦ]
    exact Φ.toPartialEquiv.map_source hwΦ
  have hsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
      (Prod.fst : M × Surgery.Topology.Circle → M) Φ.target := by
    refine ((contMDiff_fst (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).comp_contMDiffOn
      Φ.symm.contMDiffOn_toFun).congr (fun z' hz' => ?_)
    have h1 : Φ (Φ.symm z') = z' := Φ.toPartialEquiv.right_inv hz'
    have h2 : productCoverProjection (Φ.symm z') = Φ (Φ.symm z') :=
      hEqΦ (Φ.toPartialEquiv.map_target hz')
    change Prod.fst z' = Prod.fst ((Φ.symm : M × Surgery.Topology.Circle → M × ℝ) z')
    calc Prod.fst z' = Prod.fst (Φ (Φ.symm z')) := by rw [h1]
      _ = Prod.fst (productCoverProjection (Φ.symm z')) := by rw [h2]
      _ = Prod.fst (Φ.symm z') := rfl
  exact hsmooth.contMDiffAt (Φ.open_target.mem_nhds hzΦ)

omit [CompleteSpace E] in
private theorem contMDiff_snd_quotientProductAtlas (A : QuotientProductAtlas I M) [I.Boundaryless] :
    letI := A.charts
    letI := A.smoothManifold
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : M × Surgery.Topology.Circle → Surgery.Topology.Circle) := by
  let := A.charts
  let := A.smoothManifold
  intro z
  obtain ⟨w, hw⟩ := surjective_productCoverProjection (M := M) z
  obtain ⟨Φ, hwΦ, hEqΦ⟩ := isLocalDiffeomorph_productCoverProjection (I := I) (M := M) A w
  have hzΦ : z ∈ Φ.target := by
    rw [← hw, hEqΦ hwΦ]
    exact Φ.toPartialEquiv.map_source hwΦ
  have hsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : M × Surgery.Topology.Circle → Surgery.Topology.Circle) Φ.target := by
    refine (AddCircle.contMDiff_coe.comp_contMDiffOn
      ((contMDiff_snd (I := I) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).comp_contMDiffOn
        Φ.symm.contMDiffOn_toFun)).congr (fun z' hz' => ?_)
    have h1 : Φ (Φ.symm z') = z' := Φ.toPartialEquiv.right_inv hz'
    have h3 : productCoverProjection (Φ.symm z') = Φ (Φ.symm z') :=
      hEqΦ (Φ.toPartialEquiv.map_target hz')
    calc (Prod.snd : M × Surgery.Topology.Circle → Surgery.Topology.Circle) z'
        = Prod.snd (Φ (Φ.symm z')) := by rw [h1]
      _ = Prod.snd (productCoverProjection (Φ.symm z')) := by rw [h3]
      _ = (((Φ.symm : M × Surgery.Topology.Circle → M × ℝ) z').2 :
          Surgery.Topology.Circle) := rfl
  exact hsmooth.contMDiffAt (Φ.open_target.mem_nhds hzΦ)

variable (A : QuotientProductAtlas I M)

omit [CompleteSpace E] in
theorem product_solution_iff [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : ProductCurve M) {s u : ℝ} (hsu : s < u)
    (J : Set ℝ) (hJ : J = Ico s u ∨ J = Icc s u)
    (hylift : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (univ ×ˢ J)) :
    letI := A.charts
    letI := A.smoothManifold
    c.IsSolutionOn g lambda J ↔
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J := by
  let := A.charts
  let := A.smoothManifold
  have huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t :=
    fun _ ht => uniqueMDiffWithinAt_of_mem_Ico_or_Icc hsu hJ ht
  constructor
  · intro hc
    exact c.map_isSolutionOn_of_interval_of_isSolutionOn A g lambda hlambda hsu hJ hc
  · intro hm
    have hsm : c.SmoothOn (I := I) J :=
      (c.coverSmoothLift_of_continuousOn_height A J hylift) hm.smooth
    have himm : c.ImmersedOn (I := I) J :=
      (c.map_immersedOn_iff A hsm).mp hm.immersed
    have hU : (c.unitTangent g lambda).SmoothOn (I := I) J :=
      c.field_smoothOn_unitTangent (I := I) g lambda hlambda hsm himm
    exact c.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift A g lambda hlambda
      hylift hU huniq hm

omit [CompleteSpace E] in
theorem product_solution_lift [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) (c : CurveMap (M × Surgery.Topology.Circle)) {s u : ℝ}
    (hsu : s < u)
    (J : Set ℝ) (hJ : J = Ico s u ∨ J = Icc s u)
    (hc : letI := A.charts
      letI := A.smoothManifold
      c.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J) :
    ∃ ĉ : ProductCurve M, ĉ.IsSolutionOn g lambda J ∧
      ∀ z t, t ∈ J → ĉ.map z t = c z t := by
  classical
  let := A.charts
  let := A.smoothManifold
  set f : ℝ × ℝ → Surgery.Topology.Circle :=
    fun p => (c (p.1 : Surgery.Topology.Circle) p.2).2 with hf
  have hconvJ : Convex ℝ J := by
    rcases hJ with rfl | rfl
    · exact convex_Ico s u
    · exact convex_Icc s u
  have hneJ : J.Nonempty := by
    rcases hJ with rfl | rfl
    · exact ⟨s, left_mem_Ico.mpr hsu⟩
    · exact ⟨s, left_mem_Icc.mpr hsu.le⟩
  have hper : ∀ p : ℝ × ℝ, f (p.1 + 1, p.2) = f p := by
    intro p
    have h1 : ((p.1 + 1 : ℝ) : Surgery.Topology.Circle) = (p.1 : Surgery.Topology.Circle) := by
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
    simp only [f]
    rw [h1]
  have hloc : ∀ q ∈ (univ : Set ℝ) ×ˢ J, ∃ φ : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ φ ((univ : Set ℝ) ×ˢ J) q ∧
      (fun p => (φ p : Surgery.Topology.Circle)) =ᶠ[𝓝[(univ : Set ℝ) ×ˢ J] q] f := by
    intro q hq
    have hfcont : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ f
        ((univ : Set ℝ) ×ˢ J) q := by
      have h := ContMDiffWithinAt.comp q
        (contMDiff_snd_quotientProductAtlas (I := I) (M := M) A).contMDiffAt (hc.smooth q hq)
        (fun _ _ => mem_univ _)
      exact h
    exact exists_contDiffWithinAt_addCircle_lift hfcont
  obtain ⟨y, d, hy_smooth, hy_lift, hy_inc⟩ :=
    DifferentialGeometry.Topology.exists_contDiffOn_addCircle_lift_of_periodic
      hconvJ hneJ f hper hloc
  have hdclean : ∀ x : ℝ,
      (((d : ℝ) * (⌊x⌋ : ℝ) : ℝ) : Surgery.Topology.Circle) = 0 := by
    intro x
    have hcast : (d : ℝ) * (⌊x⌋ : ℝ) = ((d * ⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
    rw [hcast, ← zsmul_one (d * ⌊x⌋), AddCircle.coe_zsmul (p := (1 : ℝ)) (x := (1 : ℝ)),
      AddCircle.coe_period, smul_zero]
  let yfun : ℝ → ℝ → ℝ :=
    fun x t => if t ∈ J then y (x, t) else (d : ℝ) * (⌊x⌋ : ℝ)
  let map : CurveMap (M × Surgery.Topology.Circle) :=
    fun z t => if t ∈ J then c z t else ((c 0 0).1, 0)
  have hyfun_on : ∀ x t, t ∈ J → yfun x t = y (x, t) := by
    intro x t ht
    change (if t ∈ J then y (x, t) else (d : ℝ) * (⌊x⌋ : ℝ)) = y (x, t)
    rw [if_pos ht]
  have hyfun_off : ∀ x t, t ∉ J → yfun x t = (d : ℝ) * (⌊x⌋ : ℝ) := by
    intro x t ht
    change (if t ∈ J then y (x, t) else (d : ℝ) * (⌊x⌋ : ℝ)) = (d : ℝ) * (⌊x⌋ : ℝ)
    rw [if_neg ht]
  have hmap_eq : ∀ z t, t ∈ J → map z t = c z t := by
    intro z t ht
    change (if t ∈ J then c z t else ((c 0 0).1, 0)) = c z t
    rw [if_pos ht]
  have hmap_off : ∀ z t, t ∉ J → map z t = ((c 0 0).1, 0) := by
    intro z t ht
    change (if t ∈ J then c z t else ((c 0 0).1, 0)) = ((c 0 0).1, 0)
    rw [if_neg ht]
  have hlift_eq : ∀ x t,
      (yfun x t : Surgery.Topology.Circle) = (map (x : Surgery.Topology.Circle) t).2 := by
    intro x t
    by_cases ht : t ∈ J
    · rw [hyfun_on x t ht, hmap_eq (x : Surgery.Topology.Circle) t ht]
      exact hy_lift (x, t) ⟨trivial, ht⟩
    · rw [hyfun_off x t ht, hmap_off (x : Surgery.Topology.Circle) t ht]
      exact hdclean x
  have hinc : ∀ x t, yfun (x + 1) t = yfun x t + d := by
    intro x t
    by_cases ht : t ∈ J
    · rw [hyfun_on (x + 1) t ht, hyfun_on x t ht]
      exact hy_inc (x, t) ⟨trivial, ht⟩
    · rw [hyfun_off (x + 1) t ht, hyfun_off x t ht]
      rw [Int.floor_add_one]
      push_cast
      ring
  let ĉ : ProductCurve M :=
    { map := map, y := yfun, degree := d, lift_eq := hlift_eq, increment := hinc }
  have hĉsm : ĉ.SmoothOn (I := I) J := by
    refine ⟨?_, ?_⟩
    · change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => (map (p.1 : Surgery.Topology.Circle) p.2).1) (univ ×ˢ J)
      have h2 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
          (fun p : ℝ × ℝ => (c.lift p.1 p.2).1) (univ ×ˢ J) :=
        (contMDiff_fst_quotientProductAtlas (I := I) (M := M) A).comp_contMDiffOn hc.smooth
      refine h2.congr (fun p hp => ?_)
      change ((if p.2 ∈ J then c (p.1 : Surgery.Topology.Circle) p.2
          else ((c 0 0).1, 0)) : M × Surgery.Topology.Circle).1 = (c.lift p.1 p.2).1
      rw [if_pos hp.2]
      rfl
    · change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => yfun p.1 p.2) (univ ×ˢ J)
      exact hy_smooth.congr (fun p hp => hyfun_on p.1 p.2 hp.2)
  have himm : ĉ.ImmersedOn (I := I) J := by
    intro x t ht
    have hXeq := ĉ.map_X_eq (I := I) A hĉsm x t ht
    have hmapX : map.X (I := I.prod 𝓘(ℝ, ℝ)) x t = c.X (I := I.prod 𝓘(ℝ, ℝ)) x t :=
      CurveMap.X_congr (I := I.prod 𝓘(ℝ, ℝ)) (c := map) (d := c) (t := t)
        (fun z => hmap_eq z t ht) x
    have hne : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (ĉ.coverLift x t) (ĉ.X (I := I) x t) ≠ 0 := by
      rw [← hXeq, hmapX]
      exact hc.immersed x t ht
    exact fun hzero => hne (by rw [hzero]; exact map_zero _)
  have hU : (ĉ.unitTangent g lambda).SmoothOn (I := I) J :=
    ĉ.field_smoothOn_unitTangent (I := I) g lambda hlambda hĉsm himm
  have hyc : ContinuousOn (fun p : ℝ × ℝ => ĉ.y p.1 p.2) (univ ×ˢ J) := by
    refine hy_smooth.continuousOn.congr (fun p hp => ?_)
    change yfun p.1 p.2 = y (p.1, p.2)
    exact hyfun_on p.1 p.2 hp.2
  have hm : ĉ.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (g t) lambda hlambda) J :=
    CurveMap.isSolutionOn_congr (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
      (fun x t ht => hmap_eq _ _ ht) hc
  have huniq : ∀ t ∈ J, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) J t :=
    fun _ ht => uniqueMDiffWithinAt_of_mem_Ico_or_Icc hsu hJ ht
  exact ⟨ĉ, ĉ.isSolutionOn_of_map_isSolutionOn_of_coverSmoothLift A g lambda hlambda
    hyc hU huniq hm, hmap_eq⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
