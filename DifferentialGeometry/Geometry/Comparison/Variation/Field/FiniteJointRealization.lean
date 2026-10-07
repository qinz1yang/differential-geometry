import DifferentialGeometry.Geometry.Comparison.Variation.Field.LocalJointRealization
import DifferentialGeometry.Geometry.Comparison.Variation.Field.ParameterEndpointCorrection
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.RadialBump

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.Exponential

universe uM uE uH uP

/-- One finite-dimensional variation through a finite chain of actual carriers.
The seams hold for every parameter. Its final endpoint is the genuine exponential
of the chosen final metric as a germ, retaining the endpoint second jets. -/
theorem exists_compatible_joint_variation_of_linear_fields
    {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (g : (i : Fin (n + 1)) → SmoothRiemannianMetric I (M i))
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (A : (i : Fin (n + 1)) → (t : ℝ) → P →L[ℝ] TangentSpace I (alpha i t))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i < b i)
    (J : Fin (n + 1) → Set ℝ) (hJ : ∀ i, IsOpen (J i))
    (hseg : ∀ i, Icc (a i) (b i) ⊆ J i)
    (halpha : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) (alpha i) (J i))
    (hA : ∀ i z, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨alpha i t, A i t z⟩ : TangentBundle I (M i))) (J i))
    (Phi : (i : Fin n) → M i.castSucc → M i.succ)
    (U : (i : Fin n) → Set (M i.castSucc)) (hUopen : ∀ i, IsOpen (U i))
    (hPhi : ∀ i, ContMDiffOn I I (8 : ℕ) (Phi i) (U i))
    (hsource : ∀ i, alpha i.castSucc (b i.castSucc) ∈ U i)
    (hpoint : ∀ i, Phi i (alpha i.castSucc (b i.castSucc)) = alpha i.succ (a i.succ))
    (hfield : ∀ i,
      (mfderiv I I (Phi i) (alpha i.castSucc (b i.castSucc)) : E →L[ℝ] E).comp
        (A i.castSucc (b i.castSucc)) = A i.succ (a i.succ))
    (hfirst : A 0 (a 0) = 0) :
    ∃ f : (i : Fin (n + 1)) → P × ℝ → M i,
      (∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i)) ∧
      (∀ i t, t ∈ Icc (a i) (b i) →
        (fun r => f i (0, r)) =ᶠ[𝓝 t] alpha i) ∧
      (∀ i t, t ∈ Icc (a i) (b i) →
        Filter.EventuallyEq (β := P →L[ℝ] E) (𝓝 t)
          (fun r => (mfderiv 𝓘(ℝ, P) I (fun z => f i (z, r)) 0 : P →L[ℝ] E))
          (fun r => (A i r : P →L[ℝ] E))) ∧
      (∀ z, f 0 (z, a 0) = alpha 0 (a 0)) ∧
      (∀ z i, f i.castSucc (z, b i.castSucc) ∈ U i ∧
        Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ)) ∧
      (fun z => f (Fin.last n) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
        (fun z => expMap (I := I) (g (Fin.last n))
          (alpha (Fin.last n) (b (Fin.last n))) (A (Fin.last n) (b (Fin.last n)) z)) := by
  classical
  have hex (i : Fin (n + 1)) := exists_joint_variation_of_linear_fields_on
    (g i) (alpha i) (A i) (hab i) (hJ i) (hseg i) (halpha i) (hA i)
  choose f0 hf0 hcenter hderiv _hfix hexp using hex
  let beta : (i : Fin (n + 1)) → P → M i := fun i z => f0 i (z, b i)
  have hbeta (i : Fin (n + 1)) : ContMDiff 𝓘(ℝ, P) I (8 : ℕ) (beta i) :=
    (hf0 i).comp (contMDiff_id.prodMk contMDiff_const)
  have hbeta0 (i : Fin (n + 1)) : beta i 0 = alpha i (b i) :=
    (hcenter i (b i) ⟨(hab i).le, le_rfl⟩).self_of_nhds
  have hbetav (i : Fin (n + 1)) :
      (mfderiv 𝓘(ℝ, P) I (beta i) 0 : P →L[ℝ] E) = A i (b i) :=
    (hderiv i (b i) ⟨(hab i).le, le_rfl⟩).self_of_nhds
  let Q : Set P := ⋂ i : Fin n, beta i.castSucc ⁻¹' U i
  have hQopen : IsOpen Q := isOpen_iInter_of_finite fun i =>
    (hUopen i).preimage (hbeta i.castSucc).continuous
  have h0Q : (0 : P) ∈ Q := by
    apply mem_iInter.mpr
    intro i
    change beta i.castSucc 0 ∈ U i
    rw [hbeta0]
    exact hsource i
  have hbetaSource (i : Fin n) {z : P} (hz : z ∈ Q) : beta i.castSucc z ∈ U i :=
    mem_iInter.mp hz i
  let betaA : (i : Fin (n + 1)) → P → M i :=
    Fin.cases (motive := fun i => P → M i) (fun _ => alpha 0 (a 0))
      (fun i z => Phi i (beta i.castSucc z))
  have hbetaA (i : Fin (n + 1)) :
      ContMDiffOn 𝓘(ℝ, P) I (8 : ℕ) (betaA i) Q := by
    cases i using Fin.cases with
    | zero => simpa only [betaA, Fin.cases_zero] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, P) I (8 : ℕ)
          (fun _ : P => alpha 0 (a 0))).contMDiffOn
    | succ i =>
      simpa only [betaA, Fin.cases_succ, Function.comp_def] using
        (hPhi i).comp (hbeta i.castSucc).contMDiffOn (fun _ hz => hbetaSource i hz)
  have hbetaA0 (i : Fin (n + 1)) : betaA i 0 = alpha i (a i) := by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => simpa only [betaA, Fin.cases_succ, hbeta0] using hpoint i
  have hbetaAv (i : Fin (n + 1)) :
      (mfderiv 𝓘(ℝ, P) I (betaA i) 0 : P →L[ℝ] E) = A i (a i) := by
    cases i using Fin.cases with
    | zero =>
      simp only [betaA, Fin.cases_zero, mfderiv_const, hfirst]
      rfl
    | succ i =>
      have hchain := mfderiv_comp (I := 𝓘(ℝ, P)) (I' := I) (I'' := I) (0 : P)
        (((hPhi i _ (hbetaSource i h0Q)).contMDiffAt
          ((hUopen i).mem_nhds (hbetaSource i h0Q))).mdifferentiableAt (by norm_num))
        ((hbeta i.castSucc).mdifferentiableAt (by norm_num))
      change (mfderiv 𝓘(ℝ, P) I (betaA i.succ) 0 : P →L[ℝ] E) =
        (mfderiv I I (Phi i) (beta i.castSucc 0)).comp
          (mfderiv 𝓘(ℝ, P) I (beta i.castSucc) 0) at hchain
      rw [hbeta0, hbetav] at hchain
      exact hchain.trans (hfield i)
  have hcorrect (i : Fin (n + 1)) :
      ∃ V : Set P, IsOpen V ∧ (0 : P) ∈ V ∧ V ⊆ Q ∧
        ∃ G : P × ℝ → M i,
          ContMDiffOn 𝓘(ℝ, P × ℝ) I (8 : ℕ) G (V ×ˢ univ) ∧
          (∀ t, G (0, t) = f0 i (0, t)) ∧
          (∀ t, (mfderiv 𝓘(ℝ, P) I (fun z => G (z, t)) 0 : P →L[ℝ] E) =
            mfderiv 𝓘(ℝ, P) I (fun z => f0 i (z, t)) 0) ∧
          (∀ z ∈ V, G (z, a i) = betaA i z) ∧
          (∀ z ∈ V, G (z, b i) = beta i z) := by
    have hfs : ContMDiff 𝓘(ℝ, P × ℝ) I (8 : ℕ) (f0 i) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hf0 i
    apply correct_parameter_variation_endpoint (f0 i) hQopen h0Q hfs.contMDiffOn
      (betaA i) (hbetaA i) (a i) (b i) (hab i).ne
    · exact (hbetaA0 i).trans
        (hcenter i (a i) ⟨le_rfl, (hab i).le⟩).self_of_nhds.symm
    · exact (hbetaAv i).trans
        (hderiv i (a i) ⟨le_rfl, (hab i).le⟩).self_of_nhds.symm
  choose V hVopen h0V hVQ G hG hG0 hGv hGa hGb using hcorrect
  let V0 : Set P := ⋂ i, V i
  have hV0open : IsOpen V0 := isOpen_iInter_of_finite hVopen
  have h0V0 : (0 : P) ∈ V0 := mem_iInter.mpr h0V
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hV0open 0 h0V0
  let cut : ContDiffBump (0 : P) :=
    { rIn := d / 2, rOut := d, rIn_pos := half_pos hd, rIn_lt_rOut := half_lt_self hd }
  let sigma : P → P := cut.radial
  have hsigma : ContDiff ℝ ∞ sigma := cut.radial_contDiff
  have hsigmaRange (z : P) (i : Fin (n + 1)) : sigma z ∈ V i :=
    mem_iInter.mp (hball (cut.radial_mapsTo (mem_univ z))) i
  have hsigmaId : sigma =ᶠ[𝓝 (0 : P)] id := by
    filter_upwards [Metric.ball_mem_nhds (0 : P) cut.rIn_pos] with z hz
    exact cut.radial_eq_self (Metric.ball_subset_closedBall hz)
  have hsigma0 : sigma 0 = 0 := hsigmaId.self_of_nhds
  let f : (i : Fin (n + 1)) → P × ℝ → M i := fun i z => G i (sigma z.1, z.2)
  have hf (i : Fin (n + 1)) :
      ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i) := by
    have hh : ContMDiff 𝓘(ℝ, P × ℝ) I (8 : ℕ) (f i) :=
      (hG i).comp_contMDiff
        (((hsigma.comp contDiff_fst).prodMk contDiff_snd).of_le
          (WithTop.coe_le_coe.mpr le_top)).contMDiff
        (fun z => ⟨hsigmaRange z.1 i, mem_univ _⟩)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hh
    exact hh
  have hfinal0 (i : Fin (n + 1)) (t : ℝ) : f i (0, t) = f0 i (0, t) := by
    change G i (sigma 0, t) = f0 i (0, t)
    rw [hsigma0, hG0]
  have hfinalv (i : Fin (n + 1)) (t : ℝ) :
      (mfderiv 𝓘(ℝ, P) I (fun z => f i (z, t)) 0 : P →L[ℝ] E) =
        mfderiv 𝓘(ℝ, P) I (fun z => f0 i (z, t)) 0 := by
    have heq : (fun z => f i (z, t)) =ᶠ[𝓝 (0 : P)] (fun z => G i (z, t)) := by
      filter_upwards [hsigmaId] with z hz
      change G i (sigma z, t) = G i (z, t)
      rw [hz]
      rfl
    exact heq.mfderiv_eq.trans (hGv i t)
  refine ⟨f, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t ht
    filter_upwards [hcenter i t ht] with r hr
    exact (hfinal0 i r).trans hr
  · intro i t ht
    filter_upwards [hderiv i t ht] with r hr
    exact (hfinalv i r).trans hr
  · intro z
    exact hGa 0 (sigma z) (hsigmaRange z 0)
  · intro z i
    have hzQ : sigma z ∈ Q := hVQ i.castSucc (hsigmaRange z i.castSucc)
    change G i.castSucc (sigma z, b i.castSucc) ∈ U i ∧
      Phi i (G i.castSucc (sigma z, b i.castSucc)) = G i.succ (sigma z, a i.succ)
    rw [hGb i.castSucc (sigma z) (hsigmaRange z i.castSucc),
      hGa i.succ (sigma z) (hsigmaRange z i.succ)]
    exact ⟨hbetaSource i hzQ, rfl⟩
  · have hpair : Tendsto (fun z : P => (z, b (Fin.last n)))
        (𝓝 0) (𝓝 (0, b (Fin.last n))) :=
      (continuous_id.prodMk continuous_const).continuousAt
    have he := hpair.eventually
      (hexp (Fin.last n) (b (Fin.last n)) ⟨(hab (Fin.last n)).le, le_rfl⟩)
    filter_upwards [hsigmaId, he] with z hz hez
    change G (Fin.last n) (sigma z, b (Fin.last n)) = _
    rw [hGb (Fin.last n) (sigma z) (hsigmaRange z (Fin.last n))]
    change f0 (Fin.last n) (sigma z, b (Fin.last n)) = _
    rw [hz]
    exact hez.2

end DifferentialGeometry.Geometry.Riemannian.Variation
