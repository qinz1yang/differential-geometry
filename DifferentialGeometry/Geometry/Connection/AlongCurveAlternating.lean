import DifferentialGeometry.Geometry.Connection.AlongCurve
import DifferentialGeometry.Geometry.Connection.TensorNabla.Alternating

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

omit [T2Space M] [FiniteDimensional ℝ F] in
private theorem alternating_trivialization_coord_apply
    (k : ℕ) (x₀ : M) (x : M)
    (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (a : V x [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → F) :
    (trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x₀).continuousLinearMapAt ℝ x a v =
        a (fun i => (trivializationAt F V x₀).symmL ℝ x (v i)) := by
  have hxa : x ∈ (trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x₀).baseSet :=
    ⟨hx, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x⟩
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hxa,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  simp [ContinuousAlternatingMap.inCoordinates, Function.comp_def]

omit [T2Space M] [FiniteDimensional ℝ F] in
private theorem alternating_trivialization_symm_apply
    (k : ℕ) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (a : F [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → F) :
    (trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x₀).symmL ℝ x a (fun i => (trivializationAt F V x₀).symmL ℝ x (v i)) = a v := by
  rw [← alternating_trivialization_coord_apply k x₀ x hx]
  let ea := trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x₀
  have hxa : x ∈ ea.baseSet := ⟨hx, mem_univ x⟩
  exact congrArg (fun b : F [⋀^Fin k]→L[ℝ] ℝ => b v)
    (ea.continuousLinearMapAt_symmL hxa a)

private instance alternatingModelFiniteDimensional (k : ℕ) :
    FiniteDimensional ℝ (F [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
    (Module.finBasis ℝ F)).finiteDimensional_of_finite

private theorem connectionForm_alternating_apply
    (cov : CovariantDerivative I F V) (k : ℕ)
    (x₀ : M) {x : M} (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (X : TangentSpace I x) (a : F [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → F) :
    (cov.alternating k).connectionForm
      (trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x₀)
          x X a v = -∑ i, a (Function.update v i (cov.connectionForm
            (trivializationAt F V x₀) x X (v i))) := by
  let e := trivializationAt F V x₀
  let ea := trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) x₀
  have hxa : x ∈ ea.baseSet :=
    ⟨hx, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x⟩
  let τ := fun y => ea.symmL ℝ y a
  let Y := fun i y => e.symmL ℝ y (v i)
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun y => (⟨y, τ y⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) x := by
    rw [ea.mdifferentiableAt_section_iff I _ hxa]
    apply (mdifferentiableAt_const (c := a)).congr_of_eventuallyEq
    filter_upwards [ea.open_baseSet.mem_nhds hxa] with y hy
    rw [← ea.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact ea.continuousLinearMapAt_symmL hy a
  have hY : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F))
      (fun y => (⟨y, Y i y⟩ : TotalSpace F V)) x := by
    intro i
    rw [e.mdifferentiableAt_section_iff I _ hx]
    apply (mdifferentiableAt_const (c := v i)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact e.continuousLinearMapAt_symmL hy (v i)
  have heq : (fun y => τ y (fun i => Y i y)) =ᶠ[𝓝 x] fun _ => a v := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact alternating_trivialization_symm_apply k x₀ hy a v
  have hd : mvfderiv (I := I) (fun y => τ y (fun i => Y i y)) x X = 0 := by
    unfold mvfderiv
    rw [heq.mfderiv_eq, mfderiv_const]
    change (NormedSpace.fromTangentSpace _) 0 = 0
    exact map_zero _
  rw [connectionForm_apply _ _ hxa, alternating_trivialization_coord_apply k x₀ x hx]
  change cov.alternating k τ x X (fun i => Y i x) = _
  rw [alternating_apply_of_mdifferentiableAt cov k Y hτ hY X, hd, zero_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [connectionForm_apply cov e hx]
  have hh := alternating_trivialization_coord_apply k x₀ x hx (τ x)
    (Function.update v i (e.continuousLinearMapAt ℝ x (cov (Y i) x X)))
  rw [show ea.continuousLinearMapAt ℝ x (τ x) = a from
    ea.continuousLinearMapAt_symmL hxa a] at hh
  rw [hh]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    exact (e.symmL_continuousLinearMapAt hx _).symm
  · simp only [Function.update_of_ne hj]
    rfl


omit [FiniteDimensional ℝ F] in
private theorem derivWithin_alternating_apply {k : ℕ}
    {a : ℝ → F [⋀^Fin k]→L[ℝ] ℝ} {z : Fin k → ℝ → F}
    {J : Set ℝ} {t : ℝ}
    (ha : DifferentiableWithinAt ℝ a J t)
    (hz : ∀ i, DifferentiableWithinAt ℝ (z i) J t)
    (hJ : UniqueDiffWithinAt ℝ J t) :
    derivWithin (fun s => a s (fun i => z i s)) J t =
      derivWithin a J t (fun i => z i t) +
        ∑ i, a t (Function.update (fun j => z j t) i (derivWithin (z i) J t)) := by
  simpa only [derivWithin] using
    fderivWithin_continuousAlternatingMap_apply_apply ha hz hJ (1 : ℝ)


private theorem derivAlongWithin_alternating_apply_of_uniqueDiffWithinAt
    (cov : CovariantDerivative I F V) (k : ℕ)
    (γ : ℝ → M) (a : ∀ s, V (γ s) [⋀^Fin k]→L[ℝ] ℝ)
    (Z : Fin k → ∀ s, V (γ s)) {J : Set ℝ} {t : ℝ}
    (ha : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun s => (⟨γ s, a s⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) J t)
    (hZ : ∀ i, MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z i s⟩ : TotalSpace F V)) J t)
    (hJ : UniqueDiffWithinAt ℝ J t) :
    (cov.alternating k).derivAlongWithin γ a J t (fun i => Z i t) =
      derivWithin (fun s => a s (fun i => Z i s)) J t -
        ∑ i, a t (Function.update (fun j => Z j t) i (cov.derivAlongWithin γ (Z i) J t)) := by
  have hc := fun X b v => connectionForm_alternating_apply cov k (γ t)
    (mem_baseSet_trivializationAt F V (γ t)) X b v
  let e := trivializationAt F V (γ t)
  let ea := trivializationAt (F [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)) (γ t)
  have he : γ t ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ t)
  have hea : γ t ∈ ea.baseSet := ⟨he, mem_univ _⟩
  let b := fun s => ea.continuousLinearMapAt ℝ (γ s) (a s)
  let z := fun i s => e.continuousLinearMapAt ℝ (γ s) (Z i s)
  have hpre : ∀ᶠ s in 𝓝[J] t, γ s ∈ e.baseSet :=
    ((mdifferentiableWithinAt_totalSpace I _).mp ha).1.continuousWithinAt
      (e.open_baseSet.mem_nhds he)
  have hb : DifferentiableWithinAt ℝ b J t := by
    have hh := ((mdifferentiableWithinAt_totalSpace I _).mp ha).2
    apply (mdifferentiableWithinAt_iff_differentiableWithinAt.mp hh).congr_of_eventuallyEq
    · filter_upwards [hpre] with s hs
      exact ea.continuousLinearMapAt_apply_of_mem ℝ ⟨hs, mem_univ _⟩ (a s)
    · exact ea.continuousLinearMapAt_apply_of_mem ℝ hea (a t)
  have hz : ∀ i, DifferentiableWithinAt ℝ (z i) J t := by
    intro i
    have hh := ((mdifferentiableWithinAt_totalSpace I _).mp (hZ i)).2
    apply (mdifferentiableWithinAt_iff_differentiableWithinAt.mp hh).congr_of_eventuallyEq
    · filter_upwards [hpre] with s hs
      exact e.continuousLinearMapAt_apply_of_mem ℝ hs (Z i s)
    · exact e.continuousLinearMapAt_apply_of_mem ℝ he (Z i t)
  have hvalue (s : ℝ) (hs : γ s ∈ e.baseSet) :
      b s (fun i => z i s) = a s (fun i => Z i s) := by
    rw [alternating_trivialization_coord_apply k (γ t) (γ s) hs]
    congr 1
    funext i
    exact e.symmL_continuousLinearMapAt hs (Z i s)
  have hscalar : (fun s => b s (fun i => z i s)) =ᶠ[𝓝[J] t]
      fun s => a s (fun i => Z i s) := by
    filter_upwards [hpre] with s hs
    exact hvalue s hs
  have hd := derivWithin_alternating_apply hb hz hJ
  rw [hscalar.derivWithin_eq (hvalue t he)] at hd
  have hda := (cov.alternating k).derivAlongWithin_coord ea hea ha
  have hdb := congrArg (fun c : F [⋀^Fin k]→L[ℝ] ℝ => c (fun i => z i t)) hda
  rw [alternating_trivialization_coord_apply k (γ t) (γ t) he] at hdb
  have hZval : (fun i => e.symmL ℝ (γ t) (z i t)) = (fun i => Z i t) := by
    funext i
    exact e.symmL_continuousLinearMapAt he (Z i t)
  rw [hZval] at hdb
  change (cov.alternating k).derivAlongWithin γ a J t (fun i => Z i t) =
    derivWithin b J t (fun i => z i t) +
      (cov.alternating k).connectionForm ea (γ t) _ (b t) (fun i => z i t) at hdb
  rw [hc] at hdb
  rw [hdb, hd]
  have hsummand (i : Fin k) :
      a t (Function.update (fun j => Z j t) i (cov.derivAlongWithin γ (Z i) J t)) =
        b t (Function.update (fun j => z j t) i (derivWithin (z i) J t)) +
          b t (Function.update (fun j => z j t) i
            (cov.connectionForm e (γ t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ J t ((NormedSpace.fromTangentSpace t).symm 1)) (z i t))) := by
    have hzi := cov.derivAlongWithin_coord e he (hZ i)
    have hcoord := alternating_trivialization_coord_apply k (γ t) (γ t) he (a t)
      (Function.update (fun j => z j t) i
        (e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ (Z i) J t)))
    have heq : (fun j => e.symmL ℝ (γ t)
        (Function.update (fun j => z j t) i
          (e.continuousLinearMapAt ℝ (γ t) (cov.derivAlongWithin γ (Z i) J t)) j)) =
        Function.update (fun j => Z j t) i (cov.derivAlongWithin γ (Z i) J t) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self]
        exact e.symmL_continuousLinearMapAt he _
      · simp only [Function.update_of_ne hj]
        exact e.symmL_continuousLinearMapAt he _
    rw [heq] at hcoord
    rw [← hcoord, hzi]
    exact (b t).map_update_add (fun j => z j t) i _ _
  simp_rw [hsummand]
  rw [Finset.sum_add_distrib]
  ring


theorem derivAlongWithin_alternating_apply
    (cov : CovariantDerivative I F V) (k : ℕ)
    (γ : ℝ → M) (a : ∀ s, V (γ s) [⋀^Fin k]→L[ℝ] ℝ)
    (Z : Fin k → ∀ s, V (γ s)) {J : Set ℝ} {t : ℝ}
    (ha : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun s => (⟨γ s, a s⟩ : TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) J t)
    (hZ : ∀ i, MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, Z i s⟩ : TotalSpace F V)) J t) :
    (cov.alternating k).derivAlongWithin γ a J t (fun i => Z i t) =
      derivWithin (fun s => a s (fun i => Z i s)) J t -
        ∑ i, a t (Function.update (fun j => Z j t) i (cov.derivAlongWithin γ (Z i) J t)) := by
  by_cases hJ : UniqueDiffWithinAt ℝ J t
  · exact derivAlongWithin_alternating_apply_of_uniqueDiffWithinAt cov k γ a Z ha hZ hJ
  · rw [(cov.alternating k).derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ a hJ,
      derivWithin_zero_of_not_uniqueDiffWithinAt hJ]
    simp_rw [cov.derivAlongWithin_eq_zero_of_not_uniqueDiffWithinAt γ _ hJ]
    have hsum : ∑ i, a t (Function.update (fun j => Z j t) i 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (a t).map_coord_zero i (Function.update_self _ _ _)
    rw [hsum, sub_zero]
    rfl


private theorem derivAlongWithin_congrLeft_eq_zero_of_mdifferentiable
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    (cov : CovariantDerivative I F V) (k : ℕ) (γ : ℝ → M)
    (T : ∀ s, F₀ ≃L[ℝ] V (γ s)) (a : F₀ [⋀^Fin k]→L[ℝ] ℝ)
    {J : Set ℝ} {t : ℝ}
    (hT : ∀ v, MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, T s v⟩ : TotalSpace F V)) J t)
    (hpar : ∀ v, cov.derivAlongWithin γ (fun s => T s v) J t = 0)
    (ha : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ))
      (fun s => (⟨γ s, (T s).continuousAlternatingMapCongrLeft a⟩ :
        TotalSpace (F [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) F V ℝ (Bundle.Trivial M ℝ)))) J t) :
    (cov.alternating k).derivAlongWithin γ
      (fun s => (T s).continuousAlternatingMapCongrLeft a) J t = 0 := by
  ext v
  change _ = (0 : ℝ)
  let w := fun i => (T t).symm (v i)
  have hv : (fun i => T t (w i)) = v := by
    funext i
    exact (T t).apply_symm_apply (v i)
  have h := derivAlongWithin_alternating_apply cov k γ
    (fun s => (T s).continuousAlternatingMapCongrLeft a)
    (fun i s => T s (w i)) ha (fun i => hT (w i))
  have hconst : (fun s => (T s).continuousAlternatingMapCongrLeft a
      (fun i => T s (w i))) = fun _ => a w := by
    funext s
    simp [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  rw [hconst, hv] at h
  have hdconst : derivWithin (fun _ : ℝ => a w) J t = 0 := by
    exact congrFun (derivWithin_const (𝕜 := ℝ) (c := a w) (s := J)) t
  rw [hdconst] at h
  simp only [hpar] at h
  have hsum : ∑ i, (T t).continuousAlternatingMapCongrLeft a
      (Function.update v i (0 : V (γ t))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact ((T t).continuousAlternatingMapCongrLeft a).map_coord_zero i
      (Function.update_self _ _ _)
  simpa only [hsum, sub_zero] using h


theorem derivAlongWithin_alternating_congrLeft_eq_zero
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    (cov : CovariantDerivative I F V) (k : ℕ) (γ : ℝ → M)
    (T : ∀ s, F₀ ≃L[ℝ] V (γ s)) (a : F₀ [⋀^Fin k]→L[ℝ] ℝ)
    {J : Set ℝ} {t : ℝ}
    (hT : ∀ v, MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun s => (⟨γ s, T s v⟩ : TotalSpace F V)) J t)
    (hpar : ∀ v, cov.derivAlongWithin γ (fun s => T s v) J t = 0) :
    (cov.alternating k).derivAlongWithin γ
      (fun s => (T s).continuousAlternatingMapCongrLeft a) J t = 0 := by
  exact derivAlongWithin_congrLeft_eq_zero_of_mdifferentiable cov k γ T a hT hpar
    (mdifferentiableWithinAt_alternating_congrLeft_of_pointwise k γ T a hT)

end CovariantDerivative
