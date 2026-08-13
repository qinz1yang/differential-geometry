import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackTowerBounds
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

theorem ratio_div_one_sub_bounds_of_le_half {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    0 < 1 - ε ∧ 0 ≤ ε / (1 - ε) ∧ ε / (1 - ε) ≤ 1 ∧
      ε ≤ ε / (1 - ε) ∧ ε / (1 - ε) ≤ 2 * ε := by
  have h1ε : 0 < 1 - ε := by linarith
  refine ⟨h1ε, (div_nonneg hε0.le h1ε.le), ?_, ?_, ?_⟩
  · rw [div_le_one h1ε]
    linarith
  · rw [le_div_iff₀ h1ε]
    nlinarith
  · rw [div_le_iff₀ h1ε]
    nlinarith

theorem metric_equiv_of_one_sub_bounds
    {ε ε₀ a b : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hε₀def : ε₀ = ε / (1 - ε)) (ha : 0 ≤ a)
    (hE : (1 - ε) * a ≤ b ∧ b ≤ (1 + ε) * a) :
    (1 + ε₀)⁻¹ * b ≤ a ∧ a ≤ (1 + ε₀) * b := by
  obtain ⟨h1ε, hε₀0, _, hεε₀, _⟩ := ratio_div_one_sub_bounds_of_le_half hε0 hε2
  rw [← hε₀def] at hε₀0
  have h1ε₀ : 0 < 1 + ε₀ := by linarith
  constructor
  · rw [inv_mul_le_iff₀ h1ε₀]
    exact hE.2.trans (mul_le_mul_of_nonneg_right (by
      rw [hε₀def]
      nlinarith [hεε₀]) ha)
  · have hmul : (1 + ε₀) * ((1 - ε) * a) ≤ (1 + ε₀) * b :=
      mul_le_mul_of_nonneg_left hE.1 h1ε₀.le
    have hfactor : 1 ≤ (1 + ε₀) * (1 - ε) := by
      rw [hε₀def]
      field_simp
      ring_nf
      norm_num
    have hone : a ≤ (1 + ε₀) * ((1 - ε) * a) := by
      nlinarith
    exact hone.trans hmul

theorem metric_equiv_of_div_one_sub_le
    {c q a b : ℝ} (hc2 : c ≤ 1 / 2) (hq0 : 0 ≤ q)
    (hqc : c / (1 - c) ≤ q) (ha : 0 ≤ a)
    (hE : (1 - c) * a ≤ b ∧ b ≤ (1 + c) * a) :
    (1 + q)⁻¹ * b ≤ a ∧ a ≤ (1 + q) * b := by
  have hden : 0 < 1 - c := by linarith
  have hc_le_frac : c ≤ c / (1 - c) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg c]
  have hcq : c ≤ q := hc_le_frac.trans hqc
  have hqden : c ≤ q * (1 - c) := by
    rwa [div_le_iff₀ hden] at hqc
  have h1q : 0 < 1 + q := by linarith
  constructor
  · rw [inv_mul_le_iff₀ h1q]
    exact hE.2.trans (mul_le_mul_of_nonneg_right (by linarith) ha)
  · have hmul : (1 + q) * ((1 - c) * a) ≤ (1 + q) * b :=
      mul_le_mul_of_nonneg_left hE.1 h1q.le
    have hfactor : 1 ≤ (1 + q) * (1 - c) := by
      calc
        1 = (1 - c) + c := by ring
        _ ≤ (1 - c) + q * (1 - c) := add_le_add (le_refl _) hqden
        _ = (1 + q) * (1 - c) := by ring
    have hone : a ≤ (1 + q) * ((1 - c) * a) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfactor ha
    exact hone.trans hmul
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialDataComp

open TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
theorem partialData_comp_forward [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
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
    {ε ε' : ℝ} {p : ℕ} (hε2 : ε ≤ 1 / 2)
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
      ε / (1 - ε) + ε' * max C 2 ≤ ε'' →
      ε'' < 1 →
      Nonempty (PreApproxIsoDataOn (I := I) K ε'' p
        (PartialDiffeomorph.trans (I := I) Φ Φ' : M → P) g h') := by
  classical
  set Ψ := PartialDiffeomorph.trans (I := I) Φ Φ' with hΨdef
  have hsrcU : (U₁ : Set M) ⊆ Ψ.source := by
    intro y hy
    exact ⟨hU₁ hy, hK₂ (himg (Set.mem_image_of_mem _ hy))⟩
  have hKsrc : K ⊆ Ψ.source := fun y hy => hsrcU (hKU hy)
  have hΨcoe : ∀ y : M, (Ψ : M → P) y = (Φ' : N → P) ((Φ : M → N) y) := fun _ => rfl
  have hchain : ∀ y ∈ (U₁ : Set M), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ : M → P) y v
        = mfderiv I I (Φ' : N → P) ((Φ : M → N) y) (mfderiv I I (Φ : M → N) y v) := by
    intro y hy v
    have hΦd : MDifferentiableAt I I (Φ : M → N) y :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hU₁ hy))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ : M → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds (hK₂ (himg (Set.mem_image_of_mem _ hy))))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h := mfderiv_comp y hΦ'd hΦd
    have happ := DFunLike.congr_fun h v
    simpa [ContinuousLinearMap.comp_apply] using happ
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨KG, hKGcpt, hKKG, hKGU⟩ := exists_compact_between hK U₁.2 hKU
  set V : Opens M := ⟨interior KG, isOpen_interior⟩ with hVdef
  have hKV : K ⊆ (V : Set M) := hKKG
  have hVKG : (V : Set M) ⊆ KG := interior_subset
  obtain ⟨P₁, G₁, hPG₁, hG₁inner, hP₁apply⟩ :=
    exists_pullbackField (I := I) Φ hKGcpt
      (fun y hy => hU₁ (hKGU hy)) h g
  obtain ⟨P'', G'', hPG'', hG''inner, hP''apply⟩ :=
    exists_pullbackField (I := I) Ψ hKGcpt
      (fun y hy => hsrcU (hKGU hy)) h' g
  have hc0T : ∀ x ∈ KG, metricTensorErrorNorm (I := I) P₁ g x ≤ ε := by
    intro x hxKG
    have hval : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₁.forward.c0_small x (hKGU hxKG)
  have hG₁c0 : ∀ x ∈ KG, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₁) g x ≤ ε := by
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
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ hxU)
    have hL : δ₁ x v = P'' x v - P₁ x v := by
      simp [hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₂ ((Φ : M → N) x) (fun q => mfderiv I I (Φ : M → N) x (v q))
        = D₂.forward.pullback ((Φ : M → N) x) (fun q => mfderiv I I (Φ : M → N) x (v q))
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
  have hε0 : 0 < ε := D₁.forward.eps_pos
  set ε₀ : ℝ := ε / (1 - ε) with hε₀def
  obtain ⟨h1ε, hε₀0', hε₀1', hεε₀', hε₀2ε'⟩ :=
    ratio_div_one_sub_bounds_of_le_half hε0 hε2
  have hε₀0 : 0 ≤ ε₀ := by rw [hε₀def]; exact hε₀0'
  have hε₀1 : ε₀ ≤ 1 := by rw [hε₀def]; exact hε₀1'
  have hεε₀ : ε ≤ ε₀ := by rw [hε₀def]; exact hεε₀'
  have hequivF5 : ∀ x ∈ (V : Set M), ∀ v : TangentSpace I x,
      (1 + ε₀)⁻¹ * G₁.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + ε₀) * G₁.inner x v v := by
    intro x hxV v
    have hE := hEqG₁ x (hVKG hxV) v
    have hgnn : 0 ≤ g.inner x v v := metricInner_nonneg (I := I) g x v
    exact metric_equiv_of_one_sub_bounds hε0 hε2 hε₀def hgnn hE
  have hδ₀F5 : ∀ x ∈ (V : Set M), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (2 + r)
        (iterCov (I := I) g 2 δ₀ r x)) ≤ ε₀ := by
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
        ≤ ε := D₁.forward.cov_deriv_small (r' + 1) (by omega) hrp x (hKGU (hVKG hxV))
      _ ≤ ε₀ := hεε₀
  have hgKF5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + j)
        (iterCov (I := I) G₁ 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ ε₀ := by
    intro hNV x hxV j hj1 hjp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ j basis hinv]
    rw [hgKtow hNV j x hxV]
    calc tensor02CovDerivNormWith (I := I) j D₁.reverse.pullback h h ((Φ : M → N) x)
        ≤ ε := D₁.reverse.cov_deriv_small j hj1 hjp ((Φ : M → N) x)
          (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
      _ ≤ ε₀ := hεε₀
  have hδ₁F5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + k)
        (iterCov (I := I) G₁ 2 δ₁ k x)) ≤ ε' := by
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
        _ ≤ ε' := hc0
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
        _ ≤ ε' := D₂.forward.cov_deriv_small k hk1 hkp ((Φ : M → N) x) hΦxK₂
  have hCp := hC (M' := M) (u := (V : Set M)) V.2 g G₁ δ₀ δ₁ ε₀ ε'
    hε₀0 hε₀1 (le_of_lt D₂.forward.eps_pos)
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
      tensor02CovDerivNormWith (I := I) a P'' g g x ≤ ε₀ + ε' * C := by
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
        abel
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
      metricTensorErrorNorm (I := I) P'' g x ≤ ε + ε' * (1 + ε₀) := by
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
      abel
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Geometry.Curvature.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    have htri := sqrt_normSq0S_add_le (I := I) g (δ₀ x) (δ₁ x) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x)) ≤ ε := by
      have hc := D₁.forward.c0_small x (hKGU hxKG)
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀ x = D₁.forward.pullback x
          - Tensor0SBundle.metricTensorField (I := I) g x := by
        simp [hδ₀def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
        ≤ (1 + ε₀) * ε' := by
      have hMUE : MetricUniformEquivalentOn (I := I) (V : Set M) G₁ g (1 + ε₀) :=
        ⟨by linarith, fun y hy v => hequivF5 y hy v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hxV (δ₁ x)
      have hG₁δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) ≤ ε' := by
        have h := hδ₁F5 ⟨⟨x, hxV⟩⟩ x hxV 0 (Nat.zero_le p)
        simpa using h
      have hsq : Real.sqrt ((1 + ε₀) ^ 2) = 1 + ε₀ := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
          ≤ Real.sqrt ((1 + ε₀) ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := hcompn
        _ = (1 + ε₀) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := by
            rw [hsq]
        _ ≤ (1 + ε₀) * ε' := mul_le_mul_of_nonneg_left hG₁δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x + δ₁ x))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x)) := htri
      _ ≤ ε + (1 + ε₀) * ε' := add_le_add ht0 ht1
      _ = ε + ε' * (1 + ε₀) := by ring
  have hε₀2ε : ε₀ ≤ 2 * ε := by rw [hε₀def]; exact hε₀2ε'
  have hε'0 : 0 ≤ ε' := le_of_lt D₂.forward.eps_pos
  intro ε'' hlb hub
  have hCm0 : (0 : ℝ) ≤ max C 2 := le_trans hC0 (le_max_left _ _)
  have hC_le : C ≤ max C 2 := le_max_left _ _
  have h1ε₀le : 1 + ε₀ ≤ max C 2 := by
    have htwo : 1 + ε₀ ≤ 2 := by nlinarith [hε₀2ε, hε2]
    exact htwo.trans (le_max_right _ _)
  have hlb' : ε₀ + ε' * max C 2 ≤ ε'' := by
    rw [hε₀def]
    exact hlb
  have harithc0 : ε + ε' * (1 + ε₀) ≤ ε'' :=
    (add_le_add hεε₀ (mul_le_mul_of_nonneg_left h1ε₀le hε'0)).trans hlb'
  have harithcov : ε₀ + ε' * C ≤ ε'' :=
    (add_le_add (le_refl ε₀) (mul_le_mul_of_nonneg_left hC_le hε'0)).trans hlb'
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact div_pos hε0 h1ε
  have hε''0 : 0 < ε'' :=
    (add_pos_of_pos_of_nonneg hε₀pos (mul_nonneg hε'0 hCm0)).trans_le hlb'
  exact ⟨
    { eps_pos := hε''0
      eps_lt_one := hub
      smoothOn := Ψ.contMDiffOn_toFun.mono hKsrc
      pullback := P''
      pullback_apply := fun x hx v => hP''apply x (hVKG (hKV hx)) v
      c0_small := fun x hx => le_trans (hc0P'' x hx) harithc0
      cov_deriv_small := fun a h1 h2 x hx =>
        le_trans (hcovP'' a h1 h2 x hx) harithcov }⟩

end PartialDataComp

end HCGCompactness
end DifferentialGeometry
