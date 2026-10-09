import DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteJointRealization

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.Exponential

universe uM uE uH

/-- The full parameter map associated with a finite list of tangent vectors. -/
def frameParameter {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Fin d → E) : (Fin d → ℝ) →L[ℝ] E :=
  ∑ k : Fin d, (ContinuousLinearMap.proj k).smulRight (Y k)

@[simp] theorem frameParameter_apply {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : Fin d → E) (z : Fin d → ℝ) :
    frameParameter Y z = ∑ k, z k • Y k := by
  simp only [frameParameter, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

@[simp] theorem frameParameter_single {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : Fin d → E) (k : Fin d) :
    frameParameter Y (Pi.single k 1) = Y k := by
  classical
  simp [frameParameter_apply]

/-- The finite-frame receiver for simultaneous endpoint variations. In the
action application, the fields here are the same linear-cutoff adapted fields
whose index trace is computed by `FiniteTraceEnergy`. -/
theorem exists_compatible_joint_variation_of_fields
    {n d : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
    (g : (i : Fin (n + 1)) → SmoothRiemannianMetric I (M i))
    (alpha : (i : Fin (n + 1)) → ℝ → M i)
    (Y : (i : Fin (n + 1)) → Fin d → (t : ℝ) → TangentSpace I (alpha i t))
    (a b : Fin (n + 1) → ℝ) (hab : ∀ i, a i < b i)
    (J : Fin (n + 1) → Set ℝ) (hJ : ∀ i, IsOpen (J i))
    (hseg : ∀ i, Icc (a i) (b i) ⊆ J i)
    (halpha : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) I (8 : ℕ) (alpha i) (J i))
    (hY : ∀ i k, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
      (fun t => (⟨alpha i t, Y i k t⟩ : TangentBundle I (M i))) (J i))
    (Phi : (i : Fin n) → M i.castSucc → M i.succ)
    (U : (i : Fin n) → Set (M i.castSucc)) (hUopen : ∀ i, IsOpen (U i))
    (hPhi : ∀ i, ContMDiffOn I I (8 : ℕ) (Phi i) (U i))
    (hsource : ∀ i, alpha i.castSucc (b i.castSucc) ∈ U i)
    (hpoint : ∀ i, Phi i (alpha i.castSucc (b i.castSucc)) = alpha i.succ (a i.succ))
    (hfield : ∀ i k,
      (mfderiv I I (Phi i) (alpha i.castSucc (b i.castSucc))
        (Y i.castSucc k (b i.castSucc)) : E) = Y i.succ k (a i.succ))
    (hfirst : ∀ k, Y 0 k (a 0) = 0) :
    ∃ f : (i : Fin (n + 1)) → (Fin d → ℝ) × ℝ → M i,
      (∀ i, ContMDiff (𝓘(ℝ, Fin d → ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (f i)) ∧
      (∀ i t, t ∈ Icc (a i) (b i) →
        (fun r => f i (0, r)) =ᶠ[𝓝 t] alpha i) ∧
      (∀ i k t, t ∈ Icc (a i) (b i) →
        Filter.EventuallyEq (β := E) (𝓝 t)
          (fun r => (mfderiv 𝓘(ℝ, Fin d → ℝ) I (fun z => f i (z, r)) 0
            (Pi.single k 1) : E)) (fun r => (Y i k r : E))) ∧
      (∀ z, f 0 (z, a 0) = alpha 0 (a 0)) ∧
      (∀ z i, f i.castSucc (z, b i.castSucc) ∈ U i ∧
        Phi i (f i.castSucc (z, b i.castSucc)) = f i.succ (z, a i.succ)) ∧
      (fun z => f (Fin.last n) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : Fin d → ℝ)]
        (fun z => expMap (I := I) (g (Fin.last n))
          (alpha (Fin.last n) (b (Fin.last n)))
          (∑ k, z k • Y (Fin.last n) k (b (Fin.last n)))) := by
  classical
  let A (i : Fin (n + 1)) (t : ℝ) :
      (Fin d → ℝ) →L[ℝ] TangentSpace I (alpha i t) :=
    frameParameter (fun k => Y i k t)
  have hA_apply (i : Fin (n + 1)) (t : ℝ) (z : Fin d → ℝ) :
      (A i t z : E) = ∑ k, z k • Y i k t :=
    frameParameter_apply (E := TangentSpace I (alpha i t)) (fun k => Y i k t) z
  have hA (i : Fin (n + 1)) (z : Fin d → ℝ) :
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
        (fun t => (⟨alpha i t, A i t z⟩ : TangentBundle I (M i))) (J i) := by
    have hh := (halpha i).sum_bundle Finset.univ
      (fun k _ => (contMDiffOn_const (c := z k)).smul_bundle (hY i k))
    simpa only [A, frameParameter_apply] using hh
  have hmatch (i : Fin n) :
      (mfderiv I I (Phi i) (alpha i.castSucc (b i.castSucc)) : E →L[ℝ] E).comp
        (A i.castSucc (b i.castSucc)) = A i.succ (a i.succ) := by
    ext z
    change (mfderiv I I (Phi i) (alpha i.castSucc (b i.castSucc)) : E →L[ℝ] E)
      (A i.castSucc (b i.castSucc) z) = (A i.succ (a i.succ) z : E)
    rw [hA_apply, hA_apply, map_sum]
    simp only [map_smul]
    exact Finset.sum_congr rfl (fun k _ => congrArg (fun v : E => z k • v) (hfield i k))
  have hAfirst : A 0 (a 0) = 0 := by
    ext z
    simp only [A, frameParameter_apply, hfirst, smul_zero, Finset.sum_const_zero,
      zero_apply]
  obtain ⟨f, hf, hcenter, hderiv, hfix, hjoin, hend⟩ :=
    exists_compatible_joint_variation_of_linear_fields g alpha A a b hab J hJ hseg
      halpha hA Phi U hUopen hPhi hsource hpoint hmatch hAfirst
  refine ⟨f, hf, hcenter, ?_, hfix, hjoin, ?_⟩
  · intro i k t ht
    filter_upwards [hderiv i t ht] with r hr
    have hh := congrArg (fun L : (Fin d → ℝ) →L[ℝ] E => L (Pi.single k 1)) hr
    have hsingle : (A i r (Pi.single k 1) : E) = Y i k r :=
      frameParameter_single (E := TangentSpace I (alpha i r)) (fun l => Y i l r) k
    exact hh.trans hsingle
  · simpa only [A, frameParameter_apply] using hend

end DifferentialGeometry.Geometry.Riemannian.Variation
