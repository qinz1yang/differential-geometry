import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PartialDataCompositionForward
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

private theorem add_sub_add_sub_eq_sub_sub {A : Type*} [AddCommGroup A] (a b c d : A) :
    (a - d) + (b - c) = (b - d) - (c - a) := by
  abel

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialDataComp

open TopologicalSpace

omit [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
theorem partialData_comp_reverse [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {P : Type u} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space N] [SigmaCompactSpace N] [T2Space P] [SigmaCompactSpace P]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [IsManifold I 1 P] [IsManifold I 2 P] [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {U₁ : Opens M} [Nonempty U₁] (hU₁ : (U₁ : Set M) ⊆ Φ.source)
    {K₂ : Opens N} [Nonempty K₂] (hK₂ : (K₂ : Set N) ⊆ Φ'.source)
    (himg : (Φ : M → N) '' (U₁ : Set M) ⊆ (K₂ : Set N))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U₁ : Set M))
    {ε ε' : ℝ} {p : ℕ} (hε'2 : ε' ≤ 1 / 2)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
      [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
      [IsManifold I 1 M'] [IsManifold I 2 M']
      [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
      {u : Set M'}, IsOpen u →
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoPartialData (I := I) (U₁ : Set M) ε p Φ g h)
    (D₂ : BookApproxIsoPartialData (I := I) (K₂ : Set N) ε' p Φ' h h') :
    ∀ ε'' : ℝ,
      ε' / (1 - ε') + ε * max C 2 ≤ ε'' →
      ε'' < 1 →
      Nonempty (PreApproxIsoDataOn (I := I)
        ((PartialDiffeomorph.trans (I := I) Φ Φ' : M → P) '' K) ε'' p
        ((PartialDiffeomorph.trans (I := I) Φ Φ').symm : P → M) h' g) := by
  classical
  set Ψ := PartialDiffeomorph.trans (I := I) Φ Φ' with hΨdef
  have hsrcU : (U₁ : Set M) ⊆ Ψ.source := by
    intro y hy
    exact ⟨hU₁ hy, hK₂ (himg (Set.mem_image_of_mem _ hy))⟩
  have hKsrc : K ⊆ Ψ.source := fun y hy => hsrcU (hKU hy)
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨KG, hKGcpt, hKKG, hKGU⟩ := exists_compact_between hK U₁.2 hKU
  set V : Opens M := ⟨interior KG, isOpen_interior⟩ with hVdef
  have hKV : K ⊆ (V : Set M) := hKKG
  have hVKG : (V : Set M) ⊆ KG := interior_subset
  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H N
  have hε0 : 0 < ε := D₁.forward.eps_pos
  have hΨcont : ContinuousOn (Ψ : M → P) KG :=
    Ψ.contMDiffOn_toFun.continuousOn.mono (fun y hy => hsrcU (hKGU hy))
  have hΨKG_cpt : IsCompact ((Ψ : M → P) '' KG) := hKGcpt.image_of_continuousOn hΨcont
  have hΨKG_tgt : (Ψ : M → P) '' KG ⊆ Ψ.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact Ψ.map_source' (hsrcU (hKGU hy))
  obtain ⟨Pr, Gr, hPGr, hGrinner, hPrapply⟩ :=
    exists_pullbackField (I := I) Ψ.symm hΨKG_cpt hΨKG_tgt g h'
  have hKimg : (Ψ : M → P) '' K ⊆ (Ψ : M → P) '' KG :=
    Set.image_mono (fun y hy => hVKG (hKV hy))
  have hVsrc : (V : Set M) ⊆ Ψ.source := fun y hy => hsrcU (hKGU (hVKG hy))
  set VP : Opens P := ⟨(Ψ : M → P) '' (V : Set M), image_opens_isOpen (I := I) Ψ hVsrc⟩
    with hVPdef
  have hVPKG : (VP : Set P) ⊆ (Ψ : M → P) '' KG := Set.image_mono hVKG
  have hΨKG_tgt' : (Ψ : M → P) '' KG ⊆ Φ'.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    have : (Φ : M → N) y ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ (hKGU hy))
    exact Φ'.map_source' (hK₂ this)
  obtain ⟨P₂r, G₂r, hPG₂r, hG₂rinner, hP₂rapply⟩ :=
    exists_pullbackField (I := I) Φ'.symm hΨKG_cpt hΨKG_tgt' h h'
  have hε'0' : 0 < ε' := D₂.forward.eps_pos
  set ε₀' : ℝ := ε' / (1 - ε') with hε₀'def
  obtain ⟨h1ε', hε₀'0', hε₀'1', hε'ε₀'', hε₀'2ε''⟩ :=
    ratio_div_one_sub_bounds_of_le_half hε'0' hε'2
  have hε₀'0 : 0 ≤ ε₀' := by rw [hε₀'def]; exact hε₀'0'
  have hε₀'1 : ε₀' ≤ 1 := by rw [hε₀'def]; exact hε₀'1'
  have hε'ε₀' : ε' ≤ ε₀' := by rw [hε₀'def]; exact hε'ε₀''
  have hε₀'2ε' : ε₀' ≤ 2 * ε' := by rw [hε₀'def]; exact hε₀'2ε''
  set δ₀r := D₂.reverse.pullback - Tensor0SBundle.metricTensorField (I := I) h'
    with hδ₀rdef
  set δ₁r := Pr - P₂r with hδ₁rdef
  set δN₁r := D₁.reverse.pullback - Tensor0SBundle.metricTensorField (I := I) h
    with hδN₁rdef
  have hVPmem : ∀ y ∈ (VP : Set P), ∃ m ∈ (V : Set M), (Ψ : M → P) m = y := by
    rintro y ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  have hVPimgK₂ : ∀ y ∈ (VP : Set P), (Φ'.symm : P → N) y ∈ (K₂ : Set N) ∧
      (Φ'.symm : P → N) y ∈ (Φ : M → N) '' (U₁ : Set M) ∧ y ∈ Φ'.target := by
    rintro y ⟨m, hm, rfl⟩
    have hmU : m ∈ (U₁ : Set M) := hKGU (hVKG hm)
    have hΦm : (Φ : M → N) m ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ hmU)
    have hyt : ((Ψ : M → P) m) ∈ Φ'.target := by
      have : (Ψ : M → P) m = (Φ' : N → P) ((Φ : M → N) m) := rfl
      rw [this]
      exact Φ'.map_source' (hK₂ hΦm)
    have hsymm : (Φ'.symm : P → N) ((Ψ : M → P) m) = (Φ : M → N) m := by
      have : (Ψ : M → P) m = (Φ' : N → P) ((Φ : M → N) m) := rfl
      rw [this]
      exact Φ'.left_inv' (hK₂ hΦm)
    refine ⟨?_, ?_, hyt⟩
    · rw [hsymm]; exact hΦm
    · rw [hsymm]; exact Set.mem_image_of_mem _ hmU
  have hc0Tr : ∀ y ∈ (VP : Set P),
      metricTensorErrorNorm (I := I) P₂r h' y ≤ ε' := by
    intro y hyVP
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyKG : y ∈ (Ψ : M → P) '' KG := hVPKG hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) := by
      refine ⟨(Φ'.symm : P → N) y, hyK₂, ?_⟩
      exact Φ'.right_inv' hyt
    have hval : P₂r y = D₂.reverse.pullback y := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₂rapply y hyKG w, D₂.reverse.pullback_apply y hyΦ'K₂ w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₂.reverse.c0_small y hyΦ'K₂
  have hG₂rc0 : ∀ y ∈ (VP : Set P), metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₂r) h' y ≤ ε' := by
    intro y hy
    rw [← hPG₂r]
    exact hc0Tr y hy
  have hEqG₂r := inner_le_of_c0 (I := I) G₂r h' hG₂rc0
  have hchainr : ∀ y ∈ (VP : Set P), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ.symm : P → M) y v
        = mfderiv I I (Φ.symm : N → M) ((Φ'.symm : P → N) y)
            (mfderiv I I (Φ'.symm : P → N) y v) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hΦ'sd : MDifferentiableAt I I (Φ'.symm : P → N) y :=
      (Φ'.symm.contMDiffOn_toFun.contMDiffAt
        (Φ'.symm.open_source.mem_nhds hyt)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦst : (Φ'.symm : P → N) y ∈ Φ.target := by
      obtain ⟨m, hmU, hmeq⟩ := hyU₁img
      rw [← hmeq]
      exact Φ.map_source' (hU₁ hmU)
    have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ'.symm : P → N) y) :=
      (Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds hΦst)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h := mfderiv_comp y hΦsd hΦ'sd
    have happ := DFunLike.congr_fun h v
    simpa [ContinuousLinearMap.comp_apply] using happ
  have hδ₁rpt : ∀ y ∈ (VP : Set P), ∀ v : Fin 2 → TangentSpace I y,
      δ₁r y v = δN₁r ((Φ'.symm : P → N) y)
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyKG : y ∈ (Ψ : M → P) '' KG := hVPKG hyVP
    have hL : δ₁r y v = Pr y v - P₂r y v := by
      simp [hδ₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₁r ((Φ'.symm : P → N) y)
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))
        = D₁.reverse.pullback ((Φ'.symm : P → N) y)
            (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))
          - Tensor0SBundle.metricTensorField (I := I) h ((Φ'.symm : P → N) y)
              (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
      simp [hδN₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hL, hR, hPrapply y hyKG v, hP₂rapply y hyKG v,
      D₁.reverse.pullback_apply ((Φ'.symm : P → N) y) hyU₁img
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)),
      Tensor0SBundle.metricTensorField_apply]
    rw [hchainr y hyVP (v 0), hchainr y hyVP (v 1)]
    rfl
  have hG₂rV : ∀ y ∈ (VP : Set P), ∀ v w : TangentSpace I y,
      G₂r.inner y v w = h.inner ((Φ'.symm : P → N) y)
        (mfderiv I I (Φ'.symm : P → N) y v) (mfderiv I I (Φ'.symm : P → N) y w) :=
    fun y hy v w => hG₂rinner y (hVPKG hy) v w
  haveI : LocallyCompactSpace P := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H P
  haveI : LocallyCompactSpace (VP : Set P) := VP.2.locallyCompactSpace
  haveI : SigmaCompactSpace (VP : Set P) := inferInstance
  haveI : LocallyCompactSpace ((Φ'.symm : P → N) '' (VP : Set P) : Set N) :=
    (image_opens_isOpen (I := I) Φ'.symm
      (fun y hy => (hVPimgK₂ y hy).2.2)).locallyCompactSpace
  haveI : SigmaCompactSpace ((Φ'.symm : P → N) '' (VP : Set P) : Set N) := inferInstance
  have hδ₁rtow : ∀ (hNVP : Nonempty VP) (a : ℕ) (y : P) (hy : y ∈ (VP : Set P)),
      tensor02CovDerivNormWith (I := I) a δ₁r G₂r G₂r y
        = tensor02CovDerivNormWith (I := I) a δN₁r h h ((Φ'.symm : P → N) y) := by
    intro hNVP a y hy
    exact covNormWith_pd_zone (I := I) Φ'.symm (V := VP)
      (fun z hz => (hVPimgK₂ z hz).2.2) h δN₁r δ₁r G₂r hδ₁rpt hG₂rV a y hy
  have hgptr : ∀ y ∈ (VP : Set P), ∀ v : Fin 2 → TangentSpace I y,
      Tensor0SBundle.metricTensorField (I := I) h' y v
        = D₂.forward.pullback ((Φ'.symm : P → N) y)
            (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hfg : (Φ' : N → P) ∘ (Φ'.symm : P → N) =ᶠ[nhds y] id := by
      filter_upwards [Φ'.open_target.mem_nhds hyt] with z hz
      exact Φ'.right_inv' hz
    have hΦ'sd : MDifferentiableAt I I (Φ'.symm : P → N) y :=
      (Φ'.symm.contMDiffOn_toFun.contMDiffAt
        (Φ'.symm.open_source.mem_nhds hyt)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ'.symm : P → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds (Φ'.map_target' hyt))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp : (mfderiv I I (Φ' : N → P) ((Φ'.symm : P → N) y)).comp
        (mfderiv I I (Φ'.symm : P → N) y) = ContinuousLinearMap.id ℝ (TangentSpace I y) := by
      rw [← mfderiv_comp y hΦ'd hΦ'sd, hfg.mfderiv_eq]
      exact mfderiv_id
    have happ : ∀ w : TangentSpace I y,
        mfderiv I I (Φ' : N → P) ((Φ'.symm : P → N) y)
          (mfderiv I I (Φ'.symm : P → N) y w) = w := by
      intro w
      simpa using DFunLike.congr_fun hcomp w
    rw [D₂.forward.pullback_apply ((Φ'.symm : P → N) y) hyK₂
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))]
    rw [Tensor0SBundle.metricTensorField_apply]
    have hr : (Φ' : N → P) ((Φ'.symm : P → N) y) = y := Φ'.right_inv' hyt
    rw [happ (v 0), happ (v 1), hr]
  have hgKrtow : ∀ (hNVP : Nonempty VP) (a : ℕ) (y : P) (hy : y ∈ (VP : Set P)),
      tensor02CovDerivNormWith (I := I) a
          (Tensor0SBundle.metricTensorField (I := I) h') G₂r G₂r y
        = tensor02CovDerivNormWith (I := I) a D₂.forward.pullback h h
            ((Φ'.symm : P → N) y) := by
    intro hNVP a y hy
    exact covNormWith_pd_zone (I := I) Φ'.symm (V := VP)
      (fun z hz => (hVPimgK₂ z hz).2.2) h D₂.forward.pullback
      (Tensor0SBundle.metricTensorField (I := I) h') G₂r hgptr hG₂rV a y hy
  have hequivF5r : ∀ y ∈ (VP : Set P), ∀ v : TangentSpace I y,
      (1 + ε₀')⁻¹ * G₂r.inner y v v ≤ h'.inner y v v ∧
        h'.inner y v v ≤ (1 + ε₀') * G₂r.inner y v v := by
    intro y hy v
    have hE := hEqG₂r y hy v
    have hnn : 0 ≤ h'.inner y v v := metricInner_nonneg (I := I) h' y v
    exact metric_equiv_of_one_sub_bounds hε'0' hε'2 hε₀'def hnn hE
  have hδ₀rF5 : ∀ y ∈ (VP : Set P), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y (2 + r)
        (iterCov (I := I) h' 2 δ₀r r y)) ≤ ε₀' := by
    intro y hyVP r hr0 hrp
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) :=
      ⟨(Φ'.symm : P → N) y, hyK₂, Φ'.right_inv' hyt⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hsub := iterCov_sub (I := I) h' 2 D₂.reverse.pullback
      (Tensor0SBundle.metricTensorField (I := I) h') (r' + 1)
    rw [hδ₀rdef, hsub, iterCov_metric_zero, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    rw [← t02Norm_eq_iterCov (I := I) D₂.reverse.pullback h' (r' + 1) basis hinv]
    calc tensor02CovDerivNormWith (I := I) (r' + 1) D₂.reverse.pullback h' h' y
        ≤ ε' := D₂.reverse.cov_deriv_small (r' + 1) (by omega) hrp y hyΦ'K₂
      _ ≤ ε₀' := hε'ε₀'
  have hgKrF5 : ∀ (hNVP : Nonempty VP), ∀ y ∈ (VP : Set P), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y (2 + j)
        (iterCov (I := I) G₂r 2 (Tensor0SBundle.metricTensorField (I := I) h') j y))
        ≤ ε₀' := by
    intro hNVP y hyVP j hj1 hjp
    obtain ⟨hyK₂, _, _⟩ := hVPimgK₂ y hyVP
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) G₂r y
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) G₂r basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) h') G₂r j basis hinv]
    rw [hgKrtow hNVP j y hyVP]
    calc tensor02CovDerivNormWith (I := I) j D₂.forward.pullback h h
          ((Φ'.symm : P → N) y)
        ≤ ε' := D₂.forward.cov_deriv_small j hj1 hjp ((Φ'.symm : P → N) y) hyK₂
      _ ≤ ε₀' := hε'ε₀'
  have hδ₁rF5 : ∀ (hNVP : Nonempty VP), ∀ y ∈ (VP : Set P), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y (2 + k)
        (iterCov (I := I) G₂r 2 δ₁r k y)) ≤ ε := by
    intro hNVP y hyVP k hkp
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) G₂r y
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) G₂r basis hON
    rw [← t02Norm_eq_iterCov (I := I) δ₁r G₂r k basis hinv]
    rw [hδ₁rtow hNVP k y hyVP]
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hc0 := D₁.reverse.c0_small ((Φ'.symm : P → N) y) hyU₁img
      calc tensor02CovDerivNormWith (I := I) 0 δN₁r h h ((Φ'.symm : P → N) y)
          = metricTensorErrorNorm (I := I) D₁.reverse.pullback h
              ((Φ'.symm : P → N) y) := by
            unfold tensor02CovDerivNormWith metricTensorErrorNorm
            congr 1
        _ ≤ ε := hc0
    · calc tensor02CovDerivNormWith (I := I) k δN₁r h h ((Φ'.symm : P → N) y)
          = tensor02CovDerivNormWith (I := I) k D₁.reverse.pullback h h
              ((Φ'.symm : P → N) y) := by
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have hfield : tensor02CovDeriv (I := I) δN₁r h (k' + 1)
                = tensor02CovDeriv (I := I) D₁.reverse.pullback h (k' + 1) := by
              rw [hδN₁rdef, tensor02_eq_covDOF, tensor02_eq_covDOF, covDerivOfField_sub,
                covDerivOfField_eq_iterCov (I := I) h
                  (Tensor0SBundle.metricTensorField (I := I) h) (k' + 1),
                iterCov_metric_zero]
              simp
            unfold tensor02CovDerivNormWith
            rw [hfield]
        _ ≤ ε := D₁.reverse.cov_deriv_small k hk1 hkp ((Φ'.symm : P → N) y) hyU₁img
  have hCpr := hC (M' := P) (u := (VP : Set P)) VP.2 h' G₂r
    δ₀r δ₁r ε₀' ε hε₀'0 hε₀'1 hε0.le
    hequivF5r
    (fun y hy j hj1 hjp => hgKrF5 ⟨⟨y, hy⟩⟩ y hy j hj1 hjp)
    hδ₀rF5
    (fun y hy k hkp => hδ₁rF5 ⟨⟨y, hy⟩⟩ y hy k hkp)
  have hgermzr : ∀ (a : ℕ) (y : P), y ∈ (VP : Set P) →
      ∀ slots : Fin (a + 2) → TangentSpace I y,
      covDerivOfField (I := I) h' (P₂r - D₂.reverse.pullback) a y slots = 0 := by
    intro a y hyVP slots
    haveI : Nonempty VP := ⟨⟨y, hyVP⟩⟩
    have hA0 : ∀ (q : VP) (w : Fin 2 → TangentSpace I q),
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := VP) (n := (∞ : WithTop ℕ∞)) 2) q w
          = (P₂r - D₂.reverse.pullback) (q : P) w := by
      intro q w
      obtain ⟨hqK₂, _, hqt⟩ := hVPimgK₂ (q : P) q.2
      have hqΦ'K₂ : (q : P) ∈ (Φ' : N → P) '' (K₂ : Set N) :=
        ⟨(Φ'.symm : P → N) q, hqK₂, Φ'.right_inv' hqt⟩
      have hv : P₂r (q : P) w = D₂.reverse.pullback (q : P) w := by
        rw [hP₂rapply _ (hVPKG q.2) w, D₂.reverse.pullback_apply _ hqΦ'K₂ w]
      simp [ContMDiffSection.coe_sub, Pi.sub_apply, hv]
    have hres := covDerivOfField_restrictOpen (I := I) h' VP
      (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := VP) (n := (∞ : WithTop ℕ∞)) 2)
      (P₂r - D₂.reverse.pullback) hA0 a ⟨y, hyVP⟩ slots
    rw [← hres, covDOF_zero]
    simp
  have hcovPr : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ (Ψ : M → P) '' K,
      tensor02CovDerivNormWith (I := I) a Pr h' h' y ≤ ε₀' + ε * C := by
    intro a ha1 hap y hyK
    have hyVP : y ∈ (VP : Set P) := by
      obtain ⟨m, hm, rfl⟩ := hyK
      exact ⟨m, hKV hm, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hgermzrI : ∀ slots : Fin (2 + (a' + 1)) → TangentSpace I y,
        iterCov (I := I) h' 2 (P₂r - D₂.reverse.pullback) (a' + 1) y slots = 0 := by
      intro slots
      have hfe := covDerivOfField_eq_iterCov (I := I) h'
        (P₂r - D₂.reverse.pullback) (a' + 1)
      have hx1 := DFunLike.congr_fun hfe y
      have hx2 := DFunLike.congr_fun hx1
        (fun q => slots ((acEquiv (a' + 1)).symm q))
      change _ = (ContinuousMultilinearMap.domDomCongr
        (acEquiv (a' + 1)) _) _ at hx2
      rw [ContinuousMultilinearMap.domDomCongr_apply] at hx2
      have hslots : (fun q => slots ((acEquiv (a' + 1)).symm
          ((acEquiv (a' + 1)) q))) = slots := by
        funext q
        rw [Equiv.symm_apply_apply]
      rw [hslots] at hx2
      exact hx2.symm.trans (hgermzr (a' + 1) y hyVP _)
    have hdecI : iterCov (I := I) h' 2 Pr (a' + 1) y
        = iterCov (I := I) h' 2 (δ₀r + δ₁r) (a' + 1) y := by
      have hsplit : (δ₀r + δ₁r : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E)
          (H := H) (I := I) (M := P) (n := (∞ : WithTop ℕ∞)) 2)
          = (Pr - Tensor0SBundle.metricTensorField (I := I) h')
            - (P₂r - D₂.reverse.pullback) := by
        rw [hδ₀rdef, hδ₁rdef]
        exact add_sub_add_sub_eq_sub_sub D₂.reverse.pullback Pr P₂r
          (Tensor0SBundle.metricTensorField (I := I) h')
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      rw [hsplit, iterCov_sub, iterCov_sub, iterCov_metric_zero, sub_zero]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [Tensor0SBundle.Tensor0SSpace.sub_apply, hgermzrI slots, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    rw [t02Norm_eq_iterCov (I := I) Pr h' (a' + 1) basis hinv, hdecI]
    exact hCpr y hyVP (a' + 1) (by omega) hap
  have hc0Pr : ∀ y ∈ (Ψ : M → P) '' K,
      metricTensorErrorNorm (I := I) Pr h' y ≤ ε' + ε * (1 + ε₀') := by
    intro y hyK
    have hyVP : y ∈ (VP : Set P) := by
      obtain ⟨m, hm, rfl⟩ := hyK
      exact ⟨m, hKV hm, rfl⟩
    obtain ⟨hyK₂, _, hyt⟩ := hVPimgK₂ y hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) :=
      ⟨(Φ'.symm : P → N) y, hyK₂, Φ'.right_inv' hyt⟩
    have h3 : P₂r y = D₂.reverse.pullback y := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₂rapply _ (hVPKG hyVP) w, D₂.reverse.pullback_apply _ hyΦ'K₂ w]
    have hval : Pr y - Tensor0SBundle.metricTensorField (I := I) h' y
        = δ₀r y + δ₁r y := by
      simp only [hδ₀rdef, hδ₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [← h3]
      abel
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    have htri := sqrt_normSq0S_add_le (I := I) h' (δ₀r y) (δ₁r y) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y)) ≤ ε' := by
      have hc := D₂.reverse.c0_small y hyΦ'K₂
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀r y = D₂.reverse.pullback y
          - Tensor0SBundle.metricTensorField (I := I) h' y := by
        simp [hδ₀rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y))
        ≤ (1 + ε₀') * ε := by
      have hMUE : MetricUniformEquivalentOn (I := I) (VP : Set P) G₂r h' (1 + ε₀') :=
        ⟨by linarith, fun z hz v => hequivF5r z hz v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hyVP (δ₁r y)
      have hG₂δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) ≤ ε := by
        have h := hδ₁rF5 ⟨⟨y, hyVP⟩⟩ y hyVP 0 (Nat.zero_le p)
        simpa using h
      have hsq : Real.sqrt ((1 + ε₀') ^ 2) = 1 + ε₀' := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y))
          ≤ Real.sqrt ((1 + ε₀') ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) := hcompn
        _ = (1 + ε₀') * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) := by
            rw [hsq]
        _ ≤ (1 + ε₀') * ε := mul_le_mul_of_nonneg_left hG₂δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y + δ₁r y))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y)) := htri
      _ ≤ ε' + (1 + ε₀') * ε := add_le_add ht0 ht1
      _ = ε' + ε * (1 + ε₀') := by ring
  intro ε'' hlb hub
  have hCm0 : (0 : ℝ) ≤ max C 2 := le_trans hC0 (le_max_left _ _)
  have hC_le : C ≤ max C 2 := le_max_left _ _
  have h1ε₀'le : 1 + ε₀' ≤ max C 2 := by
    have htwo : 1 + ε₀' ≤ 2 := by nlinarith [hε₀'2ε', hε'2]
    exact htwo.trans (le_max_right _ _)
  have hlb' : ε₀' + ε * max C 2 ≤ ε'' := by
    rw [hε₀'def]
    exact hlb
  have harithc0r : ε' + ε * (1 + ε₀') ≤ ε'' :=
    (add_le_add hε'ε₀' (mul_le_mul_of_nonneg_left h1ε₀'le hε0.le)).trans hlb'
  have harithcovr : ε₀' + ε * C ≤ ε'' :=
    (add_le_add (le_refl ε₀') (mul_le_mul_of_nonneg_left hC_le hε0.le)).trans hlb'
  have hε₀'pos : 0 < ε₀' := by
    rw [hε₀'def]
    exact div_pos hε'0' h1ε'
  have hε''0 : 0 < ε'' :=
    (add_pos_of_pos_of_nonneg hε₀'pos (mul_nonneg hε0.le hCm0)).trans_le hlb'
  exact ⟨
    { eps_pos := hε''0
      eps_lt_one := hub
      smoothOn := Ψ.symm.contMDiffOn_toFun.mono
        (fun y hy => hΨKG_tgt (hKimg hy))
      pullback := Pr
      pullback_apply := fun y hy v => hPrapply y (hKimg hy) v
      c0_small := fun y hy => le_trans (hc0Pr y hy) harithc0r
      cov_deriv_small := fun a h1 h2 y hy =>
        le_trans (hcovPr a h1 h2 y hy) harithcovr }⟩

end PartialDataComp

end HCGCompactness
end DifferentialGeometry
