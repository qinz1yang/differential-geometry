import DifferentialGeometry.Topology.VectorBundle.CircleBase.FrameAlong
import DifferentialGeometry.Topology.Manifold.SmoothOrientation
import DifferentialGeometry.Topology.VectorBundle.CircleBase.OrientationSign

/-!
# Orientation of the total space along the zero section over the circle (P1a, holonomy)

`V` is a smooth rank-two bundle over `S¹ = AddCircle 1`, `oV` a smooth orientation of its total
space (`DifferentialGeometry.Topology.Manifold.SmoothOrientation`). Along the zero section, a frame
`u` along the covering line gives the tangent frame `(∂_t 0, vertical u₀, vertical u₁)`
(`zeroSectionFrame`). In the chart at any zero-section point it has block form
(`mfderiv_extChartAt_comp_zeroSectionFrame`), so whether its sign matches `oV` is locally constant
(`eventually_orientation_sign_iff`). Comparing a frame with its own shift by one period
(`frameShift`), which has the same tangent frame one period later (`zeroSectionFrame_frameShift`),
gives the orientation relation: the holonomy of a frame along the line is a rotation
(`planeDet_frameShift_pos`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, InnerProductSpace ℝ (V b)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
theorem mem_chartAt_source_totalSpace (p z : TotalSpace F V)
    (he : z.proj ∈ (trivializationAt F V p.proj).baseSet)
    (hc : z.proj ∈ (chartAt ℝ p.proj).source) :
    z ∈ (chartAt (ModelProd ℝ F) p).source := by
  rw [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.trans_source]
  refine ⟨(trivializationAt F V p.proj).mem_source.mpr he, ?_⟩
  simp only [mem_preimage, OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source,
    mem_prod, mem_univ, and_true]
  rw [Trivialization.coe_coe, (trivializationAt F V p.proj).coe_fst' he]
  exact hc

omit [FiniteDimensional ℝ F] [∀ b, InnerProductSpace ℝ (V b)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
theorem extChartAt_totalSpace_apply (p z : TotalSpace F V)
    (he : z.proj ∈ (trivializationAt F V p.proj).baseSet) :
    extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p z =
      (extChartAt 𝓘(ℝ, ℝ) p.proj z.proj, ((trivializationAt F V p.proj) z).2) := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.coe_trans, Function.comp_apply, PartialEquiv.prod_coe,
    PartialEquiv.refl_coe, id]
  change (extChartAt 𝓘(ℝ, ℝ) p.proj ((trivializationAt F V p.proj) z).1,
    ((trivializationAt F V p.proj) z).2) = _
  rw [(trivializationAt F V p.proj).coe_fst' he]

variable (F V) in
/-- The velocity at `t` of the zero section along the covering line. -/
def circleZeroTangent (t : ℝ) : ℝ × F :=
  mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
    (fun s : ℝ => zeroSection F V (s : AddCircle (1 : ℝ))) t (1 : ℝ)

variable (F) in
/-- The vertical tangent vector at the zero of the fibre `V b` given by `v ∈ V b`. -/
def verticalTangent (b : AddCircle (1 : ℝ)) (v : V b) : ℝ × F :=
  mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (fun s : ℝ => (⟨b, s • v⟩ : TotalSpace F V)) 0 (1 : ℝ)

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
theorem mfderiv_extChartAt_circleZeroTangent (p : TotalSpace F V) (t : ℝ)
    (he : ((t : ℝ) : AddCircle (1 : ℝ)) ∈ (trivializationAt F V p.proj).baseSet)
    (hc : ((t : ℝ) : AddCircle (1 : ℝ)) ∈ (chartAt ℝ p.proj).source) :
    mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ × F) (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p)
        (zeroSection F V ((t : ℝ) : AddCircle (1 : ℝ))) (circleZeroTangent F V t) =
      (deriv (fun s : ℝ => extChartAt 𝓘(ℝ, ℝ) p.proj ((s : ℝ) : AddCircle (1 : ℝ))) t, 0) := by
  let γ : ℝ → TotalSpace F V := fun s => zeroSection F V ((s : ℝ) : AddCircle (1 : ℝ))
  let ψ : ℝ → ℝ := fun s => extChartAt 𝓘(ℝ, ℝ) p.proj ((s : ℝ) : AddCircle (1 : ℝ))
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) γ t :=
    ((contMDiff_zeroSection ℝ V).comp AddCircle.contMDiff_coe).mdifferentiableAt (by simp)
  have hmem : γ t ∈ (chartAt (ModelProd ℝ F) p).source :=
    mem_chartAt_source_totalSpace p _ he hc
  have hext := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) hmem
  have hψ : DifferentiableAt ℝ ψ t := by
    have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ t :=
      ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℝ)) (n := ∞) hc).comp t
        (AddCircle.contMDiff_coe t)).mdifferentiableAt (by simp)
    exact mdifferentiableAt_iff_differentiableAt.mp h1
  have heq : (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p ∘ γ) =ᶠ[𝓝 t] fun s => (ψ s, (0 : F)) := by
    have hbase : ∀ᶠ s in 𝓝 t, ((s : ℝ) : AddCircle (1 : ℝ)) ∈
        (trivializationAt F V p.proj).baseSet :=
      AddCircle.contMDiff_coe.continuous.continuousAt.preimage_mem_nhds
        ((trivializationAt F V p.proj).open_baseSet.mem_nhds he)
    filter_upwards [hbase] with s hs
    simp only [Function.comp_apply, γ, ψ]
    rw [extChartAt_totalSpace_apply p _ hs, (trivializationAt F V p.proj).zeroSection ℝ hs]
    rfl
  have hd : HasDerivAt (fun s => (ψ s, (0 : F))) (deriv ψ t, 0) t :=
    hψ.hasDerivAt.prodMk (hasDerivAt_const t (0 : F))
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × F) (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p ∘ γ) t (1 : ℝ) =
      (deriv ψ t, 0) := by
    rw [heq.mfderiv_eq, hd.hasFDerivAt.hasMFDerivAt.mfderiv]
    exact one_smul ℝ _
  rw [mfderiv_comp t hext hγ] at h1
  exact h1

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
theorem mfderiv_extChartAt_verticalTangent (p : TotalSpace F V) {b : AddCircle (1 : ℝ)}
    (he : b ∈ (trivializationAt F V p.proj).baseSet) (hc : b ∈ (chartAt ℝ p.proj).source)
    (v : V b) :
    mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ × F) (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p)
        (zeroSection F V b) (verticalTangent F b v) =
      (0, ((trivializationAt F V p.proj) ⟨b, v⟩).2) := by
  let γ : ℝ → TotalSpace F V := fun s => ⟨b, s • v⟩
  have hγ0 : γ 0 = zeroSection F V b := by simp [γ, zeroSection]
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) γ 0 :=
    ((DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul (IB := 𝓘(ℝ, ℝ))
      (F := F) (V := V)).comp (contMDiff_id.prodMk
        (contMDiff_const (c := (⟨b, v⟩ : TotalSpace F V))))).mdifferentiableAt (by simp)
  have hmem : γ 0 ∈ (chartAt (ModelProd ℝ F) p).source :=
    mem_chartAt_source_totalSpace p _ he hc
  have hext := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) hmem
  have heq : (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p ∘ γ) =
      fun s => (extChartAt 𝓘(ℝ, ℝ) p.proj b, s • ((trivializationAt F V p.proj) ⟨b, v⟩).2) := by
    funext s
    simp only [Function.comp_apply, γ]
    rw [extChartAt_totalSpace_apply p _ he]
    congr 1
    exact ((trivializationAt F V p.proj).linear ℝ he).map_smul s v
  have hd : HasDerivAt (fun s : ℝ => (extChartAt 𝓘(ℝ, ℝ) p.proj b,
      s • ((trivializationAt F V p.proj) ⟨b, v⟩).2))
      (0, ((trivializationAt F V p.proj) ⟨b, v⟩).2) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (extChartAt 𝓘(ℝ, ℝ) p.proj b)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const ((trivializationAt F V p.proj) ⟨b, v⟩).2)
    simpa using h
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × F) (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p ∘ γ) 0 (1 : ℝ) =
      (0, ((trivializationAt F V p.proj) ⟨b, v⟩).2) := by
    rw [heq, hd.hasFDerivAt.hasMFDerivAt.mfderiv]
    exact one_smul ℝ _
  rw [mfderiv_comp 0 hext hγ, hγ0] at h1
  exact h1

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The chart derivative of the covering line does not vanish. -/
theorem deriv_extChartAt_coe_ne_zero (b₀ : AddCircle (1 : ℝ)) {t : ℝ}
    (hc : ((t : ℝ) : AddCircle (1 : ℝ)) ∈ (chartAt ℝ b₀).source) :
    deriv (fun s : ℝ => extChartAt 𝓘(ℝ, ℝ) b₀ ((s : ℝ) : AddCircle (1 : ℝ))) t ≠ 0 := by
  let ψ : ℝ → ℝ := fun s => extChartAt 𝓘(ℝ, ℝ) b₀ ((s : ℝ) : AddCircle (1 : ℝ))
  have hext : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) b₀)
      ((t : ℝ) : AddCircle (1 : ℝ)) := mdifferentiableAt_extChartAt hc
  have hq : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => ((s : ℝ) : AddCircle (1 : ℝ))) t :=
    AddCircle.contMDiff_coe.mdifferentiableAt (by simp)
  have hψ : DifferentiableAt ℝ ψ t := mdifferentiableAt_iff_differentiableAt.mp (hext.comp t hq)
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ t (1 : ℝ) = deriv ψ t := by
    rw [hψ.hasDerivAt.hasFDerivAt.hasMFDerivAt.mfderiv]
    exact one_smul ℝ _
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ t = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) b₀)
      ((t : ℝ) : AddCircle (1 : ℝ))).comp
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => ((s : ℝ) : AddCircle (1 : ℝ))) t) :=
    mfderiv_comp t hext hq
  intro h0
  rw [← h1, hcomp] at h0
  have h0' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) b₀) ((t : ℝ) : AddCircle (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => ((s : ℝ) : AddCircle (1 : ℝ))) t (1 : ℝ)) = 0 := h0
  have hinj1 := (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, ℝ)) (x := b₀)
    (by rwa [extChartAt_source])).injective
  have hinj2 := (AddCircle.bijective_mfderiv_coe t).1
  have h10 : ((1 : ℝ) : ℝ) = 0 :=
    hinj2 ((hinj1 (h0'.trans (map_zero _).symm)).trans (map_zero _).symm)
  exact one_ne_zero h10

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The chart derivative of the covering line is continuous where it is defined. -/
theorem continuousOn_deriv_extChartAt_coe (b₀ : AddCircle (1 : ℝ)) :
    ContinuousOn (deriv (fun s : ℝ => extChartAt 𝓘(ℝ, ℝ) b₀ ((s : ℝ) : AddCircle (1 : ℝ))))
      ((fun s : ℝ => ((s : ℝ) : AddCircle (1 : ℝ))) ⁻¹' (chartAt ℝ b₀).source) := by
  have hO : IsOpen ((fun s : ℝ => ((s : ℝ) : AddCircle (1 : ℝ))) ⁻¹' (chartAt ℝ b₀).source) :=
    (chartAt ℝ b₀).open_source.preimage AddCircle.contMDiff_coe.continuous
  refine ContDiffOn.continuousOn_deriv_of_isOpen (n := ∞) ?_ hO (by simp)
  intro s hs
  exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℝ)) (n := ∞) hs).comp s
    (AddCircle.contMDiff_coe s)).contDiffAt.contDiffWithinAt

omit [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Vertical tangent vectors along equal base points agree. -/
theorem verticalTangent_cast {b b' : AddCircle (1 : ℝ)} (h : b = b') (v : V b) :
    verticalTangent F b' (cast (congrArg V h) v) = verticalTangent F b v := by
  subst h
  rfl

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The vertical tangent vector is linear in the fibre vector. -/
theorem verticalTangent_add_smul (b : AddCircle (1 : ℝ)) (a a' : ℝ) (v w : V b) :
    verticalTangent F b (a • v + a' • w) =
      a • verticalTangent F b v + a' • verticalTangent F b w := by
  let p : TotalSpace F V := zeroSection F V b
  have he : b ∈ (trivializationAt F V p.proj).baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hc : b ∈ (chartAt ℝ p.proj).source := mem_chart_source ℝ b
  have hinj := (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (x := p)
    (mem_extChartAt_source (I := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p)).injective
  apply hinj
  have hlin := (trivializationAt F V p.proj).linear ℝ he
  let L : (ℝ × F) →L[ℝ] (ℝ × F) := mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ × F)
    (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p) (zeroSection F V b)
  have k : ∀ x : V b, L (verticalTangent F b x) = (0, ((trivializationAt F V p.proj) ⟨b, x⟩).2) :=
    fun x => mfderiv_extChartAt_verticalTangent p he hc x
  change L (verticalTangent F b (a • v + a' • w)) =
    L (a • verticalTangent F b v + a' • verticalTangent F b w)
  rw [L.map_add, L.map_smul, L.map_smul, k, k, k, hlin.map_add, hlin.map_smul, hlin.map_smul]
  simp

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The zero-section velocity is periodic. -/
theorem circleZeroTangent_add_one (t : ℝ) :
    circleZeroTangent F V (t + 1) = circleZeroTangent F V t := by
  let γ : ℝ → TotalSpace F V := fun s => zeroSection F V ((s : ℝ) : AddCircle (1 : ℝ))
  have hper : γ ∘ (fun s : ℝ => s + 1) = γ := by
    funext s
    simp only [Function.comp_apply, γ, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) γ (t + 1) :=
    ((contMDiff_zeroSection ℝ V).comp AddCircle.contMDiff_coe).mdifferentiableAt (by simp)
  have hτ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + 1) t :=
    ((contDiff_id.add contDiff_const : ContDiff ℝ ∞ (fun s : ℝ => s + 1)).contMDiff).mdifferentiableAt
      (by simp)
  have hτd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + 1) t (1 : ℝ) = 1 := by
    rw [((hasDerivAt_id' t).add_const 1).hasFDerivAt.hasMFDerivAt.mfderiv]
    exact one_smul ℝ _
  have h := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) t hγ hτ
  rw [hper] at h
  have h1 : mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) γ t (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) γ (t + 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + 1) t (1 : ℝ)) :=
    congrArg (fun L => L (1 : ℝ)) h
  rw [hτd] at h1
  exact h1.symm

omit [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- A block family `(c, 0), (0, f₀), (0, f₁)` with `c ≠ 0` and `f` independent has nonzero
determinant. -/
theorem det_block_ne_zero (b3 : Module.Basis (Fin 3) ℝ (ℝ × F)) {c : ℝ} (hc : c ≠ 0)
    {f₀ f₁ : F} (hf : ∀ s₀ s₁ : ℝ, s₀ • f₀ + s₁ • f₁ = 0 → s₀ = 0 ∧ s₁ = 0) :
    b3.det ![((c, 0) : ℝ × F), (0, f₀), (0, f₁)] ≠ 0 := by
  have hli : LinearIndependent ℝ ![((c, 0) : ℝ × F), (0, f₀), (0, f₁)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_zero, add_zero, Prod.fst_zero, Prod.snd_zero, smul_zero, zero_add] at h1 h2
    have hg0 : g 0 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hc
    obtain ⟨hg1, hg2⟩ := hf (g 1) (g 2) h2
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  have hsp := hli.span_eq_top_of_card_eq_finrank'
    (by rw [Module.finrank_eq_card_basis b3])
  exact ((b3.is_basis_iff_det).mp ⟨hli, hsp⟩).ne_zero

omit [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The determinant of a continuously varying family is continuous. -/
theorem continuousAt_basis_det {X : Type*} [TopologicalSpace X]
    (b3 : Module.Basis (Fin 3) ℝ (ℝ × F)) {W : X → Fin 3 → ℝ × F} {x₀ : X}
    (hW : ∀ i, ContinuousAt (fun x => W x i) x₀) :
    ContinuousAt (fun x => b3.det (W x)) x₀ := by
  have heq : (fun x => b3.det (W x)) = fun x => Matrix.det (b3.toMatrix (W x)) :=
    funext fun x => b3.det_apply _
  rw [heq]
  have hent : ContinuousAt (fun x => b3.toMatrix (W x)) x₀ := by
    refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
    have h : (fun x => b3.toMatrix (W x) i j) = fun x => b3.coord i (W x j) := by
      funext x
      rw [Module.Basis.toMatrix_apply, Module.Basis.coord_apply]
    rw [h]
    exact (b3.coord i).continuous_of_finiteDimensional.continuousAt.comp (hW j)
  exact (continuous_id.matrix_det).continuousAt.comp hent

/-- The tangent frame `(∂_t 0, vertical u₀, vertical u₁)` at the zero of the fibre over `t`. -/
def zeroSectionFrame (u : Fin 2 → (t : ℝ) → V t) (t : ℝ) : Fin 3 → ℝ × F :=
  ![circleZeroTangent F V t, verticalTangent F (t : AddCircle (1 : ℝ)) (u 0 t),
    verticalTangent F (t : AddCircle (1 : ℝ)) (u 1 t)]

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- In the chart at `p`, the tangent frame along the zero section has block form. -/
theorem mfderiv_extChartAt_comp_zeroSectionFrame (p : TotalSpace F V)
    (u : Fin 2 → (t : ℝ) → V t) {t : ℝ}
    (he : ((t : ℝ) : AddCircle (1 : ℝ)) ∈ (trivializationAt F V p.proj).baseSet)
    (hc : ((t : ℝ) : AddCircle (1 : ℝ)) ∈ (chartAt ℝ p.proj).source) :
    (fun i => mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ × F)
        (extChartAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p) (zeroSection F V ((t : ℝ) : AddCircle (1 : ℝ)))
        (zeroSectionFrame u t i)) =
      ![((deriv (fun s : ℝ => extChartAt 𝓘(ℝ, ℝ) p.proj ((s : ℝ) : AddCircle (1 : ℝ))) t, 0) :
          ℝ × F),
        (0, ((trivializationAt F V p.proj) ⟨t, u 0 t⟩).2),
        (0, ((trivializationAt F V p.proj) ⟨t, u 1 t⟩).2)] := by
  funext i
  fin_cases i
  · exact mfderiv_extChartAt_circleZeroTangent p t he hc
  · exact mfderiv_extChartAt_verticalTangent p he hc (u 0 t)
  · exact mfderiv_extChartAt_verticalTangent p he hc (u 1 t)

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- A trivialization keeps an orthonormal pair independent. -/
theorem trivialization_pair_independent (b' : AddCircle (1 : ℝ)) {b : AddCircle (1 : ℝ)}
    (hb : b ∈ (trivializationAt F V b').baseSet) {y : Fin 2 → V b} (hy : Orthonormal ℝ y) :
    ∀ s₀ s₁ : ℝ, s₀ • ((trivializationAt F V b') ⟨b, y 0⟩).2 +
      s₁ • ((trivializationAt F V b') ⟨b, y 1⟩).2 = 0 → s₀ = 0 ∧ s₁ = 0 := by
  intro s₀ s₁ h
  let L := (trivializationAt F V b').linearEquivAt ℝ b hb
  have hL : L (s₀ • y 0 + s₁ • y 1) = 0 := by
    rw [map_add, map_smul, map_smul]
    exact h
  have h0 : s₀ • y 0 + s₁ • y 1 = 0 := by
    rw [← map_zero L] at hL
    exact L.injective hL
  have hli := hy.linearIndependent
  have hfam : y = ![y 0, y 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hfam] at hli
  exact LinearIndependent.pair_iff.mp hli s₀ s₁ h0

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- **Local constancy of the orientation sign along the zero section.** For a smooth orthonormal
frame `u` along the line on an open `U` and `t₀ ∈ U`, the tangent frame
`(∂_t 0, vertical u₀, vertical u₁)` at the zero over `t₀` is a basis, and whether its sign agrees
with the total-space orientation does not change near `t₀`. -/
theorem eventually_orientation_sign_iff
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V))
    (β₀ : Module.Basis (Fin (Module.finrank ℝ (ℝ × F))) ℝ (ℝ × F))
    (b3 : Module.Basis (Fin 3) ℝ (ℝ × F)) {U : Set ℝ} (hU : IsOpen U)
    {u : Fin 2 → (t : ℝ) → V t}
    (hu : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) U)
    (hon : ∀ t ∈ U, Orthonormal ℝ (fun i => u i t)) {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    b3.det (zeroSectionFrame u t₀) ≠ 0 ∧
    ∀ᶠ t : ℝ in 𝓝 t₀,
      ((oV.1 (zeroSection F V ((t : ℝ) : AddCircle (1 : ℝ))) = β₀.orientation ↔
          0 < b3.det (zeroSectionFrame u t)) ↔
        (oV.1 (zeroSection F V ((t₀ : ℝ) : AddCircle (1 : ℝ))) = β₀.orientation ↔
          0 < b3.det (zeroSectionFrame u t₀))) := by
  let q : ℝ → AddCircle (1 : ℝ) := fun s => (s : AddCircle (1 : ℝ))
  have hq : Continuous q := AddCircle.contMDiff_coe.continuous
  let p : TotalSpace F V := zeroSection F V (q t₀)
  let e := trivializationAt F V p.proj
  let ψ : ℝ → ℝ := fun s => extChartAt 𝓘(ℝ, ℝ) p.proj (q s)
  let O₁ : Set ℝ := q ⁻¹' e.baseSet
  let O₂ : Set ℝ := q ⁻¹' (chartAt ℝ p.proj).source
  have hO₁ : IsOpen O₁ := e.open_baseSet.preimage hq
  have hO₂ : IsOpen O₂ := (chartAt ℝ p.proj).open_source.preimage hq
  have ht₀1 : t₀ ∈ O₁ := FiberBundle.mem_baseSet_trivializationAt' (q t₀)
  have ht₀2 : t₀ ∈ O₂ := mem_chart_source ℝ (q t₀)
  have hmem : ∀ t, t ∈ O₁ → t ∈ O₂ →
      zeroSection F V (q t) ∈ (chartAt (ModelProd ℝ F) p).source :=
    fun t h1 h2 => mem_chartAt_source_totalSpace p _ h1 h2
  let W : ℝ → Fin 3 → ℝ × F := fun t =>
    ![((deriv ψ t, 0) : ℝ × F), (0, (e ⟨q t, u 0 t⟩).2), (0, (e ⟨q t, u 1 t⟩).2)]
  have hW : ∀ t, t ∈ U → t ∈ O₁ → t ∈ O₂ → b3.det (W t) ≠ 0 := fun t ht h1 h2 =>
    det_block_ne_zero b3 (deriv_extChartAt_coe_ne_zero p.proj h2)
      (trivialization_pair_independent p.proj h1 (hon t ht))
  let D : ∀ t, t ∈ O₁ → t ∈ O₂ → (ℝ × F) ≃L[ℝ] (ℝ × F) := fun t h1 h2 =>
    DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) p
      (zeroSection F V (q t)) (hmem t h1 h2)
  have hcomp : ∀ t (h1 : t ∈ O₁) (h2 : t ∈ O₂),
      ⇑(D t h1 h2).toLinearEquiv ∘ zeroSectionFrame u t = W t := fun t h1 h2 =>
    mfderiv_extChartAt_comp_zeroSectionFrame p u h1 h2
  have hY : ∀ t, t ∈ U → ∀ (h1 : t ∈ O₁) (h2 : t ∈ O₂), b3.det (zeroSectionFrame u t) ≠ 0 := by
    intro t ht h1 h2 h0
    apply hW t ht h1 h2
    have := Module.Basis.det_comp b3 ((D t h1 h2).toLinearEquiv : (ℝ × F) →ₗ[ℝ] (ℝ × F))
      (zeroSectionFrame u t)
    rw [← hcomp t h1 h2]
    exact this.trans (by rw [h0, mul_zero])
  have hR : ∀ t, t ∈ U → ∀ (h1 : t ∈ O₁) (h2 : t ∈ O₂),
      ((oV.1 (zeroSection F V (q t)) = β₀.orientation ↔ 0 < b3.det (zeroSectionFrame u t)) ↔
        (Orientation.map (Fin (Module.finrank ℝ (ℝ × F))) (D t h1 h2).toLinearEquiv
          (oV.1 (zeroSection F V (q t))) = β₀.orientation ↔ 0 < b3.det (W t))) := by
    intro t ht h1 h2
    have := orientation_sign_iff_map (β₀ := β₀) (D t h1 h2).toLinearEquiv
      (o := oV.1 (zeroSection F V (q t))) (hY t ht h1 h2)
    rwa [hcomp t h1 h2] at this
  -- the chart orientation is locally constant
  have hlc := oV.2 p
  have hev := hlc.eventually_eq ⟨zeroSection F V (q t₀), hmem t₀ ht₀1 ht₀2⟩
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at hev
  have hzs : Continuous (fun t : ℝ => zeroSection F V (q t)) :=
    (contMDiff_zeroSection ℝ V (n := ∞) (IB := 𝓘(ℝ, ℝ))).continuous.comp hq
  have hevΩ := (hzs.tendsto t₀).eventually hev
  -- the sign of the chart determinant is locally constant
  have hgcont : ContinuousAt (fun t => b3.det (W t)) t₀ := by
    refine continuousAt_basis_det b3 fun i => ?_
    have hsec : ∀ j, ContinuousAt (fun t : ℝ => e (⟨q t, u j t⟩ : TotalSpace F V)) t₀ := by
      intro j
      have hs : ContinuousAt (fun t : ℝ => (⟨q t, u j t⟩ : TotalSpace F V)) t₀ :=
        ((hu j).continuousOn).continuousAt (hU.mem_nhds ht₀)
      exact ContinuousAt.comp (f := fun t : ℝ => (⟨q t, u j t⟩ : TotalSpace F V))
        (e.continuousOn.continuousAt (e.open_source.mem_nhds
          ((e.mem_source (x := (⟨q t₀, u j t₀⟩ : TotalSpace F V))).mpr ht₀1))) hs
    fin_cases i
    · exact ((continuousOn_deriv_extChartAt_coe p.proj).continuousAt
        (hO₂.mem_nhds ht₀2)).prodMk continuousAt_const
    · exact continuousAt_const.prodMk (continuous_snd.continuousAt.comp (hsec 0))
    · exact continuousAt_const.prodMk (continuous_snd.continuousAt.comp (hsec 1))
  have hg0 := hW t₀ ht₀ ht₀1 ht₀2
  have hsign : ∀ᶠ t in 𝓝 t₀, (0 < b3.det (W t) ↔ 0 < b3.det (W t₀)) := by
    rcases lt_or_gt_of_ne hg0 with hneg | hpos
    · filter_upwards [hgcont.eventually (gt_mem_nhds hneg)] with t ht
      exact ⟨fun h => absurd ht (not_lt.mpr h.le), fun h => absurd hneg (not_lt.mpr h.le)⟩
    · filter_upwards [hgcont.eventually (lt_mem_nhds hpos)] with t ht
      exact ⟨fun _ => hpos, fun _ => ht⟩
  refine ⟨hY t₀ ht₀ ht₀1 ht₀2, ?_⟩
  filter_upwards [hU.mem_nhds ht₀, hO₁.mem_nhds ht₀1, hO₂.mem_nhds ht₀2, hevΩ, hsign]
    with t ht h1 h2 hΩt hgt
  rw [hR t ht h1 h2, hR t₀ ht₀ ht₀1 ht₀2, hgt]
  have hΩ := hΩt ⟨zeroSection F V (q t), hmem t h1 h2⟩ rfl
  rw [show Orientation.map (Fin (Module.finrank ℝ (ℝ × F))) (D t h1 h2).toLinearEquiv
      (oV.1 (zeroSection F V (q t))) = Orientation.map (Fin (Module.finrank ℝ (ℝ × F)))
      (D t₀ ht₀1 ht₀2).toLinearEquiv (oV.1 (zeroSection F V (q t₀))) from hΩ]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℝ (V b)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Transport along an equality of base points does not change the total-space point. -/
theorem totalSpace_mk_cast {b b' : AddCircle (1 : ℝ)} (h : b = b') (v : V b) :
    (⟨b', cast (congrArg V h) v⟩ : TotalSpace F V) = ⟨b, v⟩ := by
  subst h
  rfl

omit [FiniteDimensional ℝ F] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Transport along an equality of base points preserves inner products. -/
theorem inner_cast_cast {b b' : AddCircle (1 : ℝ)} (h : b = b') (v w : V b) :
    ⟪cast (congrArg V h) v, cast (congrArg V h) w⟫_ℝ = ⟪v, w⟫_ℝ := by
  subst h
  rfl

theorem coe_sub_one_eq (t : ℝ) :
    (((t - 1 : ℝ) : ℝ) : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]

variable (V) in
/-- The frame along the line shifted by one period: `(shift u)(t) = u(t - 1)`, transported to the
fibre over `t`. -/
def frameShift (u : Fin 2 → (t : ℝ) → V t) : Fin 2 → (t : ℝ) → V t :=
  fun i t => cast (congrArg V (coe_sub_one_eq t)) (u i (t - 1))

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
theorem totalSpace_frameShift (u : Fin 2 → (t : ℝ) → V t) (i : Fin 2) (t : ℝ) :
    (⟨(t : AddCircle (1 : ℝ)), frameShift V u i t⟩ : TotalSpace F V) =
      ⟨((t - 1 : ℝ) : AddCircle (1 : ℝ)), u i (t - 1)⟩ :=
  totalSpace_mk_cast (coe_sub_one_eq t) (u i (t - 1))

omit [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The shifted frame is smooth and orthonormal on the shifted set. -/
theorem frameShift_smooth {U : Set ℝ} {u : Fin 2 → (t : ℝ) → V t}
    (hu : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) U)
    (hon : ∀ t ∈ U, Orthonormal ℝ (fun i => u i t)) :
    (∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), frameShift V u i t⟩ : TotalSpace F V))
      ((fun t => t - 1) ⁻¹' U)) ∧
    ∀ t ∈ (fun t => t - 1) ⁻¹' U, Orthonormal ℝ (fun i => frameShift V u i t) := by
  refine ⟨fun i => ?_, fun t ht => ?_⟩
  · have h := (hu i).comp ((contDiff_id.sub contDiff_const :
      ContDiff ℝ ∞ (fun t : ℝ => t - 1)).contMDiff.contMDiffOn) (Set.mapsTo_preimage _ U)
    refine h.congr fun t _ => ?_
    exact totalSpace_frameShift u i t
  · have h := hon (t - 1) ht
    refine orthonormal_of_inner ?_ ?_ ?_
    · exact (inner_cast_cast (coe_sub_one_eq t) _ _).trans (inner_self_of_orthonormal h 0)
    · exact (inner_cast_cast (coe_sub_one_eq t) _ _).trans (inner_self_of_orthonormal h 1)
    · exact (inner_cast_cast (coe_sub_one_eq t) _ _).trans (inner_zero_one_of_orthonormal h)

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- The tangent frame of the shifted frame one period later is the original tangent frame. -/
theorem zeroSectionFrame_frameShift (u : Fin 2 → (t : ℝ) → V t) (t : ℝ) :
    zeroSectionFrame (F := F) (frameShift V u) (t + 1) = zeroSectionFrame (F := F) u t := by
  have key : ∀ (j : Fin 2) (r : ℝ), r = t →
      ∀ h : ((r : ℝ) : AddCircle (1 : ℝ)) = ((t + 1 : ℝ) : AddCircle (1 : ℝ)),
      verticalTangent F ((t + 1 : ℝ) : AddCircle (1 : ℝ)) (cast (congrArg V h) (u j r)) =
        verticalTangent F ((t : ℝ) : AddCircle (1 : ℝ)) (u j t) := by
    intro j r hr h
    subst hr
    exact verticalTangent_cast h (u j r)
  funext i
  fin_cases i
  · exact circleZeroTangent_add_one t
  · change verticalTangent F ((t + 1 : ℝ) : AddCircle (1 : ℝ)) (frameShift V u 0 (t + 1)) =
      verticalTangent F ((t : ℝ) : AddCircle (1 : ℝ)) (u 0 t)
    exact key 0 (t + 1 - 1) (by ring) (coe_sub_one_eq (t + 1))
  · change verticalTangent F ((t + 1 : ℝ) : AddCircle (1 : ℝ)) (frameShift V u 1 (t + 1)) =
      verticalTangent F ((t : ℝ) : AddCircle (1 : ℝ)) (u 1 t)
    exact key 1 (t + 1 - 1) (by ring) (coe_sub_one_eq (t + 1))

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- **Comparison of two frames at one point.** If the orientation-sign statements of two orthonormal
frames at the same point agree, their orientation determinant is positive. -/
theorem planeDet_pos_of_sign_iff (hF : Module.finrank ℝ F = 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (β₀ : Module.Basis ι ℝ (ℝ × F))
    (b3 : Module.Basis (Fin 3) ℝ (ℝ × F)) (o : Orientation ℝ (ℝ × F) ι)
    {u v : Fin 2 → (t : ℝ) → V t} {t : ℝ} (hu : Orthonormal ℝ (fun i => u i t))
    (hv : Orthonormal ℝ (fun i => v i t)) (hdet : b3.det (zeroSectionFrame u t) ≠ 0)
    (h : (o = β₀.orientation ↔ 0 < b3.det (zeroSectionFrame u t)) ↔
      (o = β₀.orientation ↔ 0 < b3.det (zeroSectionFrame v t))) :
    0 < planeDet (fun i => v i t) (fun i => u i t) := by
  have hfd_LFR54P1 := finiteDimensional_fiber_of_two (V := V) hF (t : AddCircle (1 : ℝ))
  have h2 := finrank_fiber_eq_two (V := V) hF (t : AddCircle (1 : ℝ))
  have e0 := eq_inner_smul_add_of_orthonormal h2 hu (v 0 t)
  have e1 := eq_inner_smul_add_of_orthonormal h2 hu (v 1 t)
  have hframe : zeroSectionFrame v t =
      ![circleZeroTangent F V t,
        ⟪u 0 t, v 0 t⟫_ℝ • verticalTangent F (t : AddCircle (1 : ℝ)) (u 0 t) +
          ⟪u 1 t, v 0 t⟫_ℝ • verticalTangent F (t : AddCircle (1 : ℝ)) (u 1 t),
        ⟪u 0 t, v 1 t⟫_ℝ • verticalTangent F (t : AddCircle (1 : ℝ)) (u 0 t) +
          ⟪u 1 t, v 1 t⟫_ℝ • verticalTangent F (t : AddCircle (1 : ℝ)) (u 1 t)] := by
    rw [← verticalTangent_add_smul, ← verticalTangent_add_smul, ← e0, ← e1]
    rfl
  have hdetv : b3.det (zeroSectionFrame v t) =
      planeDet (fun i => v i t) (fun i => u i t) * b3.det (zeroSectionFrame u t) := by
    rw [hframe, alternatingMap_vec3_combo]
    simp only [planeDet, real_inner_comm (u 0 t), real_inner_comm (u 1 t)]
    rfl
  have hδ := planeDet_ne_zero h2 hv hu
  rw [hdetv] at h
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · exfalso
    have hflip : (0 < planeDet (fun i => v i t) (fun i => u i t) * b3.det (zeroSectionFrame u t)) ↔
        ¬ (0 < b3.det (zeroSectionFrame u t)) := by
      constructor
      · intro hp hy
        have := mul_neg_of_neg_of_pos hneg hy
        linarith
      · intro hy
        exact mul_pos_of_neg_of_neg hneg (lt_of_le_of_ne (not_lt.mp hy) hdet)
    rw [hflip] at h
    tauto
  · exact hpos

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- **The holonomy of a frame along the line is a rotation.** If the total space of the rank-two
bundle is orientable, a smooth orthonormal frame `u` along the covering line on `(a, T)` returns
after one period with positive orientation determinant: for `a < t₁` and `t₁ + 1 < T`, the frame
`u(t₁)`, transported to `t₁ + 1`, and `u(t₁ + 1)` have `planeDet > 0`. -/
theorem planeDet_frameShift_pos (hF : Module.finrank ℝ F = 2)
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V))
    {a T : ℝ} {u : Fin 2 → (t : ℝ) → V t}
    (hu : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u i t⟩ : TotalSpace F V)) (Ioo a T))
    (hon : ∀ t ∈ Ioo a T, Orthonormal ℝ (fun i => u i t)) {t₁ : ℝ} (ha : a < t₁)
    (hT : t₁ + 1 < T) :
    0 < planeDet (fun i => frameShift V u i (t₁ + 1)) (fun i => u i (t₁ + 1)) := by
  have h3 : Module.finrank ℝ (ℝ × F) = 3 := by
    rw [Module.finrank_prod, hF, Module.finrank_self]
  let β₀ := Module.finBasis ℝ (ℝ × F)
  let b3 := Module.finBasisOfFinrankEq ℝ (ℝ × F) h3
  let R : ℝ → Prop := fun t =>
    (oV.1 (zeroSection F V ((t : ℝ) : AddCircle (1 : ℝ))) = β₀.orientation ↔
      0 < b3.det (zeroSectionFrame u t))
  have ht₁ : t₁ ∈ Ioo a T := ⟨ha, by linarith⟩
  have ht₂ : t₁ + 1 ∈ Ioo a T := ⟨by linarith, hT⟩
  have hlc : IsLocallyConstant (fun t : Ioo a T => R t.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx := (eventually_orientation_sign_iff oV β₀ b3 isOpen_Ioo hu hon x.2).2
    rw [nhds_subtype_eq_comap]
    exact (hx.comap Subtype.val).mono fun y hy => propext hy
  have : PreconnectedSpace (Ioo a T) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hconst : R t₁ = R (t₁ + 1) :=
    hlc.apply_eq_of_preconnectedSpace ⟨t₁, ht₁⟩ ⟨t₁ + 1, ht₂⟩
  have hshift := frameShift_smooth hu hon
  have hv : Orthonormal ℝ (fun i => frameShift V u i (t₁ + 1)) :=
    hshift.2 (t₁ + 1) (by simpa using ht₁)
  have hdet := (eventually_orientation_sign_iff oV β₀ b3 isOpen_Ioo hu hon ht₂).1
  have hq : ((t₁ + 1 : ℝ) : AddCircle (1 : ℝ)) = ((t₁ : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  refine planeDet_pos_of_sign_iff hF β₀ b3 (oV.1 (zeroSection F V ((t₁ + 1 : ℝ) :
    AddCircle (1 : ℝ)))) (hon (t₁ + 1) ht₂) hv hdet ?_
  rw [zeroSectionFrame_frameShift]
  change R (t₁ + 1) ↔ _
  rw [← hconst]
  change _ ↔ (oV.1 (zeroSection F V ((t₁ + 1 : ℝ) : AddCircle (1 : ℝ))) = β₀.orientation ↔ _)
  rw [hq]

end DifferentialGeometry.Topology.VectorBundle
