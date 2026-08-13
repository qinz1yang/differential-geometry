import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PartialDataComposition
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

private theorem sub_eq_sub_add_sub {A : Type*} [AddCommGroup A] (a b c : A) :
    a - c = (b - c) + (a - b) := by
  abel

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialDataComp

open TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
noncomputable def compSepFwd [I.Boundaryless] [NeZero (Module.finrank Real E)]
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
    {c0 cov c0' cov' q e1 c0'' cov'' : Real} {p : Nat}
    (hc0_half : c0 ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq_c0 : c0 / (1 - c0) ≤ q) (hq_cov : cov ≤ q)
    (he1_0 : 0 ≤ e1) (he1_c0 : c0' ≤ e1) (he1_cov : cov' ≤ e1)
    (C : Real) (hC0 : 0 ≤ C)
    (hc0_out : c0 + c0' * (1 + q) ≤ c0'')
    (hcov_out : q + e1 * C ≤ cov'')
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
            (iterCov (I := I) g₀ 2
              (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoSep (I := I) (U₁ : Set M) c0 cov p Φ g h)
    (D₂ : BookApproxIsoSep (I := I) (K₂ : Set N) c0' cov' p Φ' h h') :
    PreApproxIsoSep (I := I) K c0'' cov'' p
      (PartialDiffeomorph.trans (I := I) Φ Φ' : M → P) g h' := by
  classical
  set Ψ := PartialDiffeomorph.trans (I := I) Φ Φ' with hΨdef
  have hsrcU : (U₁ : Set M) ⊆ Ψ.source := by
    intro y hy
    exact ⟨hU₁ hy, hK₂ (himg (Set.mem_image_of_mem _ hy))⟩
  have hKsrc : K ⊆ Ψ.source := fun y hy => hsrcU (hKU hy)
  have hchain : ∀ y ∈ (U₁ : Set M), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ : M → P) y v
        = mfderiv I I (Φ' : N → P) ((Φ : M → N) y)
            (mfderiv I I (Φ : M → N) y v) := by
    intro y hy v
    have hΦd : MDifferentiableAt I I (Φ : M → N) y :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hU₁ hy))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ : M → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds
          (hK₂ (himg (Set.mem_image_of_mem _ hy))))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp := mfderiv_comp y hΦ'd hΦd
    have happ := DFunLike.congr_fun hcomp v
    simpa [ContinuousLinearMap.comp_apply] using happ
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let KG : Set M := Classical.choose (exists_compact_between hK U₁.2 hKU)
  have hKGspec := Classical.choose_spec (exists_compact_between hK U₁.2 hKU)
  have hKGcpt : IsCompact KG := hKGspec.1
  have hKKG : K ⊆ interior KG := hKGspec.2.1
  have hKGU : KG ⊆ (U₁ : Set M) := hKGspec.2.2
  set V : Opens M := ⟨interior KG, isOpen_interior⟩ with hVdef
  have hKV : K ⊆ (V : Set M) := hKKG
  have hVKG : (V : Set M) ⊆ KG := interior_subset
  let pull1 := exists_pullbackField (I := I) Φ hKGcpt
    (fun y hy => hU₁ (hKGU hy)) h g
  let P₁ := Classical.choose pull1
  let G₁ := Classical.choose (Classical.choose_spec pull1)
  have hP₁spec := Classical.choose_spec (Classical.choose_spec pull1)
  have hPG₁ : P₁ = Tensor0SBundle.metricTensorField (I := I) G₁ := hP₁spec.1
  have hG₁inner : ∀ x ∈ KG, ∀ v w : TangentSpace I x,
      G₁.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) :=
    hP₁spec.2.1
  have hP₁apply : ∀ x ∈ KG, ∀ v : Fin 2 → TangentSpace I x,
      P₁ x v = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x (v 0)) (mfderiv I I (Φ : M → N) x (v 1)) :=
    hP₁spec.2.2
  let pullComp := exists_pullbackField (I := I) Ψ hKGcpt
    (fun y hy => hsrcU (hKGU hy)) h' g
  let P'' := Classical.choose pullComp
  let G'' := Classical.choose (Classical.choose_spec pullComp)
  have hP''spec := Classical.choose_spec (Classical.choose_spec pullComp)
  have hPG'' : P'' = Tensor0SBundle.metricTensorField (I := I) G'' := hP''spec.1
  have hG''inner : ∀ x ∈ KG, ∀ v w : TangentSpace I x,
      G''.inner x v w = h'.inner ((Ψ : M → P) x)
        (mfderiv I I (Ψ : M → P) x v) (mfderiv I I (Ψ : M → P) x w) :=
    hP''spec.2.1
  have hP''apply : ∀ x ∈ KG, ∀ v : Fin 2 → TangentSpace I x,
      P'' x v = h'.inner ((Ψ : M → P) x)
        (mfderiv I I (Ψ : M → P) x (v 0)) (mfderiv I I (Ψ : M → P) x (v 1)) :=
    hP''spec.2.2
  have hc0T : ∀ x ∈ KG, metricTensorErrorNorm (I := I) P₁ g x ≤ c0 := by
    intro x hxKG
    have hval : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₁.forward.c0_small x (hKGU hxKG)
  have hG₁c0 : ∀ x ∈ KG, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₁) g x ≤ c0 := by
    intro x hx
    rw [← hPG₁]
    exact hc0T x hx
  have hEqG₁ := inner_le_of_c0 (I := I) G₁ g hG₁c0
  set δ₀ := D₁.forward.pullback - Tensor0SBundle.metricTensorField (I := I) g with hδ₀def
  set δ₁ := P'' - P₁ with hδ₁def
  set δN₂ := D₂.forward.pullback - Tensor0SBundle.metricTensorField (I := I) h with hδN₂def
  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H M
  haveI : LocallyCompactSpace (V : Set M) := V.2.locallyCompactSpace
  haveI : SigmaCompactSpace (V : Set M) := inferInstance
  have hδ₁pt : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      δ₁ x v = δN₂ ((Φ : M → N) x)
        (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
    intro x hxV v
    have hxKG : x ∈ KG := hVKG hxV
    have hxU : x ∈ (U₁ : Set M) := hKGU hxKG
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
      himg (Set.mem_image_of_mem _ hxU)
    have hL : δ₁ x v = P'' x v - P₁ x v := by
      simp [hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₂ ((Φ : M → N) x) (fun q => mfderiv I I (Φ : M → N) x (v q))
        = D₂.forward.pullback ((Φ : M → N) x)
            (fun q => mfderiv I I (Φ : M → N) x (v q))
          - Tensor0SBundle.metricTensorField (I := I) h ((Φ : M → N) x)
              (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
      simp [hδN₂def, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hL, hR, hP''apply x hxKG v, hP₁apply x hxKG v,
      D₂.forward.pullback_apply ((Φ : M → N) x) hΦxK₂
        (fun q => mfderiv I I (Φ : M → N) x (v q)),
      Tensor0SBundle.metricTensorField_apply]
    rw [hchain x hxU (v 0), hchain x hxU (v 1)]
    rfl
  have hG₁V : ∀ x ∈ (V : Set M), ∀ v w : TangentSpace I x,
      G₁.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) :=
    fun x hx v w => hG₁inner x (hVKG hx) v w
  haveI : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H N
  haveI : LocallyCompactSpace ((Φ : M → N) '' (V : Set M) : Set N) :=
    (image_opens_isOpen (I := I) Φ
      (fun y hy => hU₁ (hKGU (hVKG hy)))).locallyCompactSpace
  haveI : SigmaCompactSpace ((Φ : M → N) '' (V : Set M) : Set N) := inferInstance
  have hδ₁tow : ∀ (hNV : Nonempty V) (a : ℕ) (x : M) (hx : x ∈ (V : Set M)),
      tensor02CovDerivNormWith (I := I) a δ₁ G₁ G₁ x
        = tensor02CovDerivNormWith (I := I) a δN₂ h h ((Φ : M → N) x) := by
    intro hNV a x hx
    exact covNormWith_pd_zone (I := I) Φ (V := V)
      (fun y hy => hU₁ (hKGU (hVKG hy))) h δN₂ δ₁ G₁ hδ₁pt hG₁V a x hx
  have hgpt : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) g x v
        = D₁.reverse.pullback ((Φ : M → N) x)
            (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
    intro x hxV v
    have hxU : x ∈ (U₁ : Set M) := hKGU (hVKG hxV)
    have hxs : x ∈ Φ.source := hU₁ hxU
    have hΦxImg : (Φ : M → N) x ∈ (Φ : M → N) '' (U₁ : Set M) :=
      Set.mem_image_of_mem _ hxU
    have hfg : (Φ.symm : N → M) ∘ (Φ : M → N) =ᶠ[nhds x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxs] with y hy
      exact Φ.left_inv' hy
    have hΦd : MDifferentiableAt I I (Φ : M → N) x :=
      ((Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hxs))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ : M → N) x) :=
      ((Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds (Φ.map_source' hxs)))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp : (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).comp
        (mfderiv I I (Φ : M → N) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      rw [← mfderiv_comp x hΦsd hΦd, hfg.mfderiv_eq]
      exact mfderiv_id
    have happ : ∀ w : TangentSpace I x,
        mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x w) = w := by
      intro w
      simpa using DFunLike.congr_fun hcomp w
    rw [D₁.reverse.pullback_apply ((Φ : M → N) x) hΦxImg
        (fun q => mfderiv I I (Φ : M → N) x (v q))]
    rw [Tensor0SBundle.metricTensorField_apply]
    have hl : (Φ.symm : N → M) ((Φ : M → N) x) = x := Φ.left_inv' hxs
    rw [happ (v 0), happ (v 1), hl]
  have hgKtow : ∀ (hNV : Nonempty V) (a : ℕ) (x : M) (hx : x ∈ (V : Set M)),
      tensor02CovDerivNormWith (I := I) a
          (Tensor0SBundle.metricTensorField (I := I) g) G₁ G₁ x
        = tensor02CovDerivNormWith (I := I) a D₁.reverse.pullback h h ((Φ : M → N) x) := by
    intro hNV a x hx
    exact covNormWith_pd_zone (I := I) Φ (V := V)
      (fun y hy => hU₁ (hKGU (hVKG hy))) h D₁.reverse.pullback
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ hgpt hG₁V a x hx
  have hc0_nonneg : 0 ≤ c0 := D₁.forward.c0_nonneg
  have hc0'_nonneg : 0 ≤ c0' := D₂.forward.c0_nonneg
  have hequivF5 : ∀ x ∈ (V : Set M), ∀ v : TangentSpace I x,
      (1 + q)⁻¹ * G₁.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + q) * G₁.inner x v v := by
    intro x hxV v
    exact metric_equiv_of_div_one_sub_le hc0_half hq0 hq_c0
      (metricInner_nonneg (I := I) g x v) (hEqG₁ x (hVKG hxV) v)
  have hδ₀F5 : ∀ x ∈ (V : Set M), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (2 + r)
        (iterCov (I := I) g 2 δ₀ r x)) ≤ q := by
    intro x hxV r hr0 hrp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hsub := iterCov_sub (I := I) g 2 D₁.forward.pullback
      (Tensor0SBundle.metricTensorField (I := I) g) (r' + 1)
    rw [hδ₀def, hsub, iterCov_metric_zero, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    rw [← t02Norm_eq_iterCov (I := I) D₁.forward.pullback g (r' + 1) basis hinv]
    calc tensor02CovDerivNormWith (I := I) (r' + 1) D₁.forward.pullback g g x
        ≤ cov := D₁.forward.cov_small (r' + 1) (by omega) hrp x (hKGU (hVKG hxV))
      _ ≤ q := hq_cov
  have hgKF5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + j)
        (iterCov (I := I) G₁ 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ q := by
    intro hNV x hxV j hj1 hjp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ j basis hinv]
    rw [hgKtow hNV j x hxV]
    calc tensor02CovDerivNormWith (I := I) j D₁.reverse.pullback h h ((Φ : M → N) x)
        ≤ cov := D₁.reverse.cov_small j hj1 hjp ((Φ : M → N) x)
          (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
      _ ≤ q := hq_cov
  have hδ₁F5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + k)
        (iterCov (I := I) G₁ 2 δ₁ k x)) ≤ e1 := by
    intro hNV x hxV k hkp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I) δ₁ G₁ k basis hinv]
    rw [hδ₁tow hNV k x hxV]
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
      himg (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hc0 := D₂.forward.c0_small ((Φ : M → N) x) hΦxK₂
      calc tensor02CovDerivNormWith (I := I) 0 δN₂ h h ((Φ : M → N) x)
          = metricTensorErrorNorm (I := I) D₂.forward.pullback h ((Φ : M → N) x) := by
            unfold tensor02CovDerivNormWith metricTensorErrorNorm
            congr 1
        _ ≤ c0' := hc0
        _ ≤ e1 := he1_c0
    · calc tensor02CovDerivNormWith (I := I) k δN₂ h h ((Φ : M → N) x)
          = tensor02CovDerivNormWith (I := I) k D₂.forward.pullback h h ((Φ : M → N) x) := by
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have hfield : tensor02CovDeriv (I := I) δN₂ h (k' + 1)
                = tensor02CovDeriv (I := I) D₂.forward.pullback h (k' + 1) := by
              rw [hδN₂def, tensor02_eq_covDOF, tensor02_eq_covDOF, covDerivOfField_sub,
                covDerivOfField_eq_iterCov (I := I) h
                  (Tensor0SBundle.metricTensorField (I := I) h) (k' + 1),
                iterCov_metric_zero]
              simp
            unfold tensor02CovDerivNormWith
            rw [hfield]
        _ ≤ cov' := D₂.forward.cov_small k hk1 hkp ((Φ : M → N) x) hΦxK₂
        _ ≤ e1 := he1_cov
  have hCp := hC (M' := M) (u := (V : Set M)) V.2 g G₁ δ₀ δ₁ q e1
    hq0 hq1 he1_0
    hequivF5
    (fun x hx j hj1 hjp => hgKF5 ⟨⟨x, hx⟩⟩ x hx j hj1 hjp)
    hδ₀F5
    (fun x hx k hkp => hδ₁F5 ⟨⟨x, hx⟩⟩ x hx k hkp)
  have hgermz : ∀ (a : ℕ) (x : M), x ∈ (V : Set M) →
      ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) g (P₁ - D₁.forward.pullback) a x slots = 0 := by
    intro a x hxV slots
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hA0 : ∀ (q : V) (w : Fin 2 → TangentSpace I q),
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) 2) q w
          = (P₁ - D₁.forward.pullback) (q : M) w := by
      intro q w
      have hv : P₁ (q : M) w = D₁.forward.pullback (q : M) w := by
        rw [hP₁apply _ (hVKG q.2) w, D₁.forward.pullback_apply _ (hKGU (hVKG q.2)) w]
      simp [ContMDiffSection.coe_sub, Pi.sub_apply, hv]
    have hres := covDerivOfField_restrictOpen (I := I) g V
      (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) 2)
      (P₁ - D₁.forward.pullback) hA0 a ⟨x, hxV⟩ slots
    rw [← hres, covDOF_zero]
    simp
  have hcovP'' : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a P'' g g x ≤ q + e1 * C := by
    intro a ha1 hap x hxK
    have hxV : x ∈ (V : Set M) := hKV hxK
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hgermzI : ∀ slots : Fin (2 + (a' + 1)) → TangentSpace I x,
        iterCov (I := I) g 2 (P₁ - D₁.forward.pullback) (a' + 1) x slots = 0 := by
      intro slots
      have hfe := covDerivOfField_eq_iterCov (I := I) g
        (P₁ - D₁.forward.pullback) (a' + 1)
      have hx1 := DFunLike.congr_fun hfe x
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
      exact hx2.symm.trans (hgermz (a' + 1) x hxV _)
    have hdecI : iterCov (I := I) g 2 P'' (a' + 1) x
        = iterCov (I := I) g 2 (δ₀ + δ₁) (a' + 1) x := by
      have hsplit : (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E)
          (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
          = (P'' - Tensor0SBundle.metricTensorField (I := I) g)
            - (P₁ - D₁.forward.pullback) := by
        rw [hδ₀def, hδ₁def]
        exact add_sub_add_sub_eq_sub_sub _ _ _ _
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      rw [hsplit, iterCov_sub, iterCov_sub, iterCov_metric_zero, sub_zero]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [Tensor0SBundle.Tensor0SSpace.sub_apply, hgermzI slots, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    rw [t02Norm_eq_iterCov (I := I) P'' g (a' + 1) basis hinv, hdecI]
    exact hCp x hxV (a' + 1) (by omega) hap
  have hc0P'' : ∀ x ∈ K,
      metricTensorErrorNorm (I := I) P'' g x ≤ c0 + c0' * (1 + q) := by
    intro x hxK
    have hxV : x ∈ (V : Set M) := hKV hxK
    have hxKG : x ∈ KG := hVKG hxV
    have h3 : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    have hval : P'' x - Tensor0SBundle.metricTensorField (I := I) g x
        = δ₀ x + δ₁ x := by
      simp only [hδ₀def, hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h3]
      exact sub_eq_sub_add_sub _ _ _
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    have htri := sqrt_normSq0S_add_le (I := I) g (δ₀ x) (δ₁ x) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x)) ≤ c0 := by
      have hc := D₁.forward.c0_small x (hKGU hxKG)
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀ x = D₁.forward.pullback x
          - Tensor0SBundle.metricTensorField (I := I) g x := by
        simp [hδ₀def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
        ≤ (1 + q) * c0' := by
      have hMUE : MetricUniformEquivalentOn (I := I) (V : Set M) G₁ g (1 + q) :=
        ⟨by linarith, fun y hy v => hequivF5 y hy v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hxV (δ₁ x)
      have hG₁δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) ≤ c0' := by
        change tensor02CovDerivNormWith (I := I) 0 δ₁ G₁ G₁ x ≤ c0'
        rw [hδ₁tow ⟨⟨x, hxV⟩⟩ 0 x hxV]
        have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
          himg (Set.mem_image_of_mem _ (hKGU hxKG))
        have hc := D₂.forward.c0_small ((Φ : M → N) x) hΦxK₂
        calc tensor02CovDerivNormWith (I := I) 0 δN₂ h h ((Φ : M → N) x)
            = metricTensorErrorNorm (I := I) D₂.forward.pullback h ((Φ : M → N) x) := by
              unfold tensor02CovDerivNormWith metricTensorErrorNorm
              congr 1
          _ ≤ c0' := hc
      have hsq : Real.sqrt ((1 + q) ^ 2) = 1 + q := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
          ≤ Real.sqrt ((1 + q) ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := hcompn
        _ = (1 + q) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := by
            rw [hsq]
        _ ≤ (1 + q) * c0' := mul_le_mul_of_nonneg_left hG₁δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x + δ₁ x))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x)) := htri
      _ ≤ c0 + (1 + q) * c0' := add_le_add ht0 ht1
      _ = c0 + c0' * (1 + q) := by ring
  have hc0''0 : 0 ≤ c0'' := by
    have hbase : 0 ≤ c0 + c0' * (1 + q) := by
      exact add_nonneg hc0_nonneg (mul_nonneg hc0'_nonneg (by linarith))
    exact le_trans hbase hc0_out
  have hcov''0 : 0 ≤ cov'' := by
    have hbase : 0 ≤ q + e1 * C := add_nonneg hq0 (mul_nonneg he1_0 hC0)
    exact le_trans hbase hcov_out
  exact
    { c0_nonneg := hc0''0
      cov_nonneg := hcov''0
      smoothOn := Ψ.contMDiffOn_toFun.mono hKsrc
      pullback := P''
      pullback_apply := fun x hx v => hP''apply x (hVKG (hKV hx)) v
      c0_small := fun x hx => le_trans (hc0P'' x hx) hc0_out
      cov_small := fun a h1 h2 x hx => le_trans (hcovP'' a h1 h2 x hx) hcov_out }


end PartialDataComp

end HCGCompactness
end DifferentialGeometry
