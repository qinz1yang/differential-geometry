import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.ClosedIntervalRegularity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [I.Boundaryless] [T2Space M] [DecidableEq Idx] in
private theorem endomorphism_isometry_of_gram
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx ℝ (TangentSpace I x))
    (ι : MatrixComp M Idx) {c t : ℝ}
    (hgram : ∀ x i j,
      movingFrameGramInFrame (metricCompInFrame S (fun k y => basisAt y k)) ι t x i j =
        (S.family.metric c).inner x (basisAt x i) (basisAt x j))
    (x : M) (v w : TangentSpace I x) :
    (S.family.metric t).inner x
      (uhlenbeckEndomorphismAt (basisAt x) ι t v)
      (uhlenbeckEndomorphismAt (basisAt x) ι t w) =
        (S.family.metric c).inner x v w := by
  let U := uhlenbeckEndomorphismAt (basisAt x) ι t
  let B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v =>
        { toFun := fun w => (S.family.metric t).inner x (U v) (U w)
          map_add' := by intro w z; simp
          map_smul' := by intro r w; simp }
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro r v; ext w; simp }
  let C : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => ((S.family.metric c).inner x v).toLinearMap
      map_add' := by intro v w; ext z; simp
      map_smul' := by intro r v; ext w; simp }
  have heq : B = C := by
    apply (basisAt x).ext
    intro i
    apply (basisAt x).ext
    intro j
    change (S.family.metric t).inner x
      (uhlenbeckEndomorphismAt (basisAt x) ι t (basisAt x i))
      (uhlenbeckEndomorphismAt (basisAt x) ι t (basisAt x j)) = _
    rw [uhlenbeckEndomorphism_gram_pair]
    exact hgram x i j
  exact congrArg (fun B => B v w) heq

omit [I.Boundaryless] [T2Space M] [DecidableEq Idx] in
private theorem endomorphism_bijective_of_gram
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis Idx ℝ (TangentSpace I x))
    (ι : MatrixComp M Idx) {c t : ℝ}
    (hgram : ∀ x i j,
      movingFrameGramInFrame (metricCompInFrame S (fun k y => basisAt y k)) ι t x i j =
        (S.family.metric c).inner x (basisAt x i) (basisAt x j)) (x : M) :
    Function.Bijective (uhlenbeckEndomorphismAt (basisAt x) ι t) := by
  have hinj : Function.Injective (uhlenbeckEndomorphismAt (basisAt x) ι t) := by
    intro v w hvw
    apply sub_eq_zero.mp
    by_contra hne
    have hpos := (S.family.metric c).pos x (v - w) hne
    have heq := endomorphism_isometry_of_gram S basisAt ι hgram x (v-w) (v-w)
    have hzero : uhlenbeckEndomorphismAt (basisAt x) ι t (v-w) = 0 := by simp [hvw]
    rw [hzero] at heq
    simp only [map_zero] at heq
    linarith
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℝ) (V := TangentSpace I x) (V₂ := TangentSpace I x) rfl
    (f := (uhlenbeckEndomorphismAt (basisAt x) ι t).toLinearMap)).mp hinj⟩

theorem exists_uhlenbeck_isometry_eq_endomorphism_on_Icc
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {c b : ℝ} (hcb : c < b)
    (basisAt : ∀ x : M, Module.Basis Idx ℝ (TangentSpace I x))
    (ι : MatrixComp M Idx)
    (hι₀ : ∀ x i k, ι c x i k = if i = k then 1 else 0)
    (hframe : ∀ t ∈ Icc c b, ∀ x i k, HasDerivWithinAt (fun s => ι s x i k)
      (∑ l : Idx, uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
        (fun j y => basisAt y j) t x l k * ι t x i l) (Icc c b) t)
    (hgram : ∀ t ∈ Icc c b, ∀ x i j,
      movingFrameGramInFrame (metricCompInFrame S (fun k y => basisAt y k)) ι t x i j =
        (S.family.metric c).inner x (basisAt x i) (basisAt x j))
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, uhlenbeckEndomorphismAt (basisAt p.2) ι p.1⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
      (Icc c b ×ˢ (univ : Set M))) :
    ∃ U : ℝ → ∀ x, TangentSpace I x ≃L[ℝ] TangentSpace I x,
      (∀ t ∈ Icc c b, ∀ x, (U t x).toContinuousLinearMap =
        uhlenbeckEndomorphismAt (basisAt x) ι t) ∧
      (∀ x, U c x = ContinuousLinearEquiv.refl ℝ (TangentSpace I x)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, (U p.1 p.2).toContinuousLinearMap⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (Icc c b ×ˢ (univ : Set M)) ∧
      (∀ t ∈ Ioo c b, ∀ x v, HasDerivAt (fun s => U s x v)
        (ricciSharp (S.family.metric t) x (U t x v)) t) ∧
      ∀ t ∈ Icc c b, ∀ x v w,
        (S.family.metric t).inner x (U t x v) (U t x w) =
          (S.family.metric c).inner x v w := by
  classical
  let U : ℝ → ∀ x, TangentSpace I x ≃L[ℝ] TangentSpace I x := fun t x =>
    if ht : t ∈ Icc c b then
      (LinearEquiv.ofBijective (uhlenbeckEndomorphismAt (basisAt x) ι t).toLinearMap
        (endomorphism_bijective_of_gram S basisAt ι (hgram t ht) x)).toContinuousLinearEquiv
    else ContinuousLinearEquiv.refl ℝ (TangentSpace I x)
  have hU (t : ℝ) (ht : t ∈ Icc c b) (x : M) :
      (U t x).toContinuousLinearMap = uhlenbeckEndomorphismAt (basisAt x) ι t := by
    dsimp only [U]
    rw [dif_pos ht]
    rfl
  have hUapp (t : ℝ) (ht : t ∈ Icc c b) (x : M) (v : TangentSpace I x) :
      U t x v = uhlenbeckEndomorphismAt (basisAt x) ι t v :=
    congrArg (fun L => L v) (hU t ht x)
  refine ⟨U, hU, ?_, ?_, ?_, ?_⟩
  · intro x
    ext v
    rw [hUapp c ⟨le_rfl, hcb.le⟩]
    have hinit := uhlenbeckEndomorphism_eq_id_of_identity_components (basisAt x)
      (fun s => ι (s + c)) (by simpa only [zero_add] using hι₀ x)
    have hinit' : uhlenbeckEndomorphismAt (basisAt x) ι c =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      simpa only [uhlenbeckEndomorphismAt, zero_add] using hinit
    rw [hinit']
    rfl
  · exact hι.congr fun p hp => congrArg (TotalSpace.mk p.2) (hU p.1 hp.1 p.2)
  · intro t ht x v
    let D₀ := RealTimeInterval.closed c b hcb.le
    let S₀ := S.timeRestrict D₀
    have hmat : FrameRicciODEInFrameOn (D := D₀) ι
        (uhlenbeckRupOfSolution S₀ (solutionInverseMetricComponents S₀ basisAt)
          (fun j y => basisAt y j)) := by
      intro s y i k
      exact hframe s ⟨s.property.1.le, s.property.2.le⟩ y i k
    have hder := uhlenbeckEndomorphism_hasDerivWithinAt S₀
      (solutionInverseMetricComponents S₀ basisAt) basisAt ι
      (solutionInverseMetricComponents_mul_metric S₀ basisAt)
      (solutionInverseMetricComponents_symm S₀ basisAt) hmat ⟨t, ht⟩ x v
    have hder' := hder.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [← hUapp t ⟨ht.1.le, ht.2.le⟩ x v] at hder'
    apply hder'.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hUapp s hs x v
  · intro t ht x v w
    rw [hUapp t ht, hUapp t ht]
    exact endomorphism_isometry_of_gram S basisAt ι (hgram t ht) x v w

end DifferentialGeometry.PDE.RicciFlow
