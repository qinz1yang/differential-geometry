import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJet
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative

/-!
# Second-order jet locality of the metric covariant derivative

For arbitrary sections whose chart representative at `x₀` is `C²` there, the first two metric
covariant derivatives at `x₀` depend only on the second-order jet of that representative. The
proof writes `∇T` near `x₀` in the fixed chart at `x₀` through the Leibniz evaluation, so no
chart change of a non-smooth section is needed.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter DifferentialGeometry.TensorLieDeriv DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
/-- The derivative at a moving point, written in a fixed chart (no boundarylessness). -/
private theorem finiteJet_mvfderiv_tangentConstInChart [IsManifold I 1 M] {f : M → ℝ}
    {x p : M} (hp : p ∈ (chartAt H x).source) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p) (v : E) :
    mvfderiv I f p (tangentConstInChart (𝕜 := ℝ) (I := I) x v p) =
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) (Set.range I) (extChartAt I x p) v := by
  let z : E := extChartAt I x p
  have hsource : p ∈ (extChartAt I x).source := by simpa [extChartAt_source] using hp
  have hz_target : z ∈ (extChartAt I x).target := by
    simpa [z] using (extChartAt I x).map_source hsource
  have hsymm : (extChartAt I x).symm z = p := by simpa [z] using (extChartAt I x).left_inv hsource
  have hsymm_mdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) z := by
    simpa [z] using mdifferentiableWithinAt_extChartAt_symm (I := I) hz_target
  have hf_univ : MDifferentiableWithinAt I 𝓘(ℝ, ℝ) f Set.univ ((extChartAt I x).symm z) := by
    rw [hsymm]
    exact hf.mdifferentiableWithinAt
  have hmaps : Set.range I ⊆ (extChartAt I x).symm ⁻¹' (Set.univ : Set M) := fun _ _ => trivial
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, E) (Set.range I) z :=
    (I.uniqueDiffOn.uniqueDiffWithinAt
      (extChartAt_target_subset_range (I := I) x hz_target)).uniqueMDiffWithinAt
  have hchain := mfderivWithin_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, ℝ)) (x := z) (g := f)
    (f := (extChartAt I x).symm) hf_univ hsymm_mdiff hmaps huniq
  have happ := congrArg (fun L => L v) hchain
  rw [mfderivWithin_univ, hsymm] at happ
  have hfield : tangentConstInChart (𝕜 := ℝ) (I := I) x v p =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) z) v := by
    have hlin := TangentBundle.symmL_trivializationAt (𝕜 := ℝ) (I := I) (x₀ := x) (x := p) hp
    change ((trivializationAt E (TangentSpace I) x).symmL ℝ p) v = _
    exact congrArg (fun L => L v) hlin
  rw [mvfderiv_real_eq_mfderiv I f p, hfield]
  have h2 : fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) (Set.range I) z v =
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (f p)
        ((mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I x).symm) (Set.range I) z) v) := by
    rw [mfderivWithin_eq_fderivWithin]
    simp [writtenInExtChartAt, NormedSpace.fromTangentSpace]
    rfl
  rw [h2, happ]
  rfl

omit [CompleteSpace E] in
private theorem finiteJet_mem_baseSet {s : ℕ} {x₀ q : M} (hq : q ∈ (chartAt H x₀).source) :
    q ∈ (trivializationAt (Tensor0SModel s ℝ E) (fun p : M => Tensor0SSpace s I p) x₀).baseSet := by
  change q ∈ (trivializationAt E (TangentSpace I) x₀).baseSet
  simpa [TangentBundle.trivializationAt_baseSet] using hq

omit [CompleteSpace E] in
/-- Chart `C²` regularity at `extChartAt x₀ q` makes the section `C²` at `q`. -/
private theorem finiteJet_section_of_chart {s : ℕ} (T : (x : M) → Tensor0SSpace s I x)
    {x₀ q : M} (hq : q ∈ (chartAt H x₀).source)
    (hT : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
      (Set.range I) (extChartAt I x₀ q)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 2
      (fun p : M => (⟨p, T p⟩ :
        TotalSpace (Tensor0SModel s ℝ E) (fun p : M => Tensor0SSpace s I p))) q := by
  let e := trivializationAt (Tensor0SModel s ℝ E) (fun p : M => Tensor0SSpace s I p) x₀
  refine (e.contMDiffAt_section_iff (finiteJet_mem_baseSet hq)).mpr ?_
  have hext : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I x₀) q :=
    (contMDiffAt_extChartAt' (I := I) (n := 2) hq)
  have hcomp : ContMDiffAt I 𝓘(ℝ, Tensor0SModel s ℝ E) 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T ∘
        extChartAt I x₀) q :=
    contMDiffWithinAt_univ.mp ((contMDiffWithinAt_iff_contDiffWithinAt.mpr hT).comp q
      hext.contMDiffWithinAt (fun p _ => Set.mem_range_self (chartAt H x₀ p)))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H x₀).open_source.mem_nhds hq] with p hp
  have hp' : p ∈ (extChartAt I x₀).source := by simpa [extChartAt_source] using hp
  change (e ⟨p, T p⟩).2 = tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀
    ((extChartAt I x₀).symm (extChartAt I x₀ p)) (T ((extChartAt I x₀).symm (extChartAt I x₀ p)))
  rw [(extChartAt I x₀).left_inv hp']
  rfl

omit [CompleteSpace E] in
/-- A `C¹` section has a differentiable representative in the chart at its own point. -/
private theorem finiteJet_chart_center_diff {r : ℕ} (β : (x : M) → Tensor0SSpace r I x)
    (x₀ : M)
    (hβ : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) 2
      (fun p : M => (⟨p, β p⟩ :
        TotalSpace (Tensor0SModel r ℝ E) (fun p : M => Tensor0SSpace r I p))) x₀) :
    DifferentiableWithinAt ℝ
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (Tensor0SModel r ℝ E) (fun p : M => Tensor0SSpace r I p) x₀
  have hx : x₀ ∈ e.baseSet := finiteJet_mem_baseSet (mem_chart_source H x₀)
  have hcoord : ContMDiffAt I 𝓘(ℝ, Tensor0SModel r ℝ E) 2 (fun p : M => (e ⟨p, β p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hβ
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I 2 (extChartAt I x₀).symm (Set.range I)
      (extChartAt I x₀ x₀) := by
    simpa using contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) x₀
  have hcenter : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center : ContMDiffAt I 𝓘(ℝ, Tensor0SModel r ℝ E) 2
      (fun p : M => (e ⟨p, β p⟩).2) ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Tensor0SModel r ℝ E) 2
      ((fun p : M => (e ⟨p, β p⟩).2) ∘ (extChartAt I x₀).symm) (Set.range I)
      (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt (x := extChartAt I x₀ x₀) hsymm
  have hmdiff : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Tensor0SModel r ℝ E) 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀) :=
    hfixed.congr_of_eventuallyEq
      (by
        filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
        simp [tensor0SModelInChart, tensor0SModelAt, e])
      (by simp [tensor0SModelInChart, tensor0SModelAt, e])
  exact hmdiff.contDiffWithinAt.differentiableWithinAt (by norm_num)

variable [T2Space M]

omit [CompleteSpace E] in
/-- Smooth global vector fields agreeing near `x₀` with the chart-constant fields of `x₀`. -/
private theorem finiteJet_exists_frame (x₀ : M) :
    ∃ X : Fin (Module.finrank ℝ E) → ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
      ∀ᶠ p in 𝓝 x₀, ∀ i, X i p =
        tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (Module.finBasis ℝ E i) p := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis ℝ E
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨X, hX⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet hx₀
  refine ⟨X, ?_⟩
  filter_upwards [hX, e.open_baseSet.mem_nhds hx₀] with p hXp hp i
  rw [hXp i, e.localFrame_apply_of_mem_baseSet (b := b) (i := i) hp]
  change e.symm p (b i) = e.symmL ℝ p (b i)
  exact (e.symmL_apply hp (b i)).symm

omit [CompleteSpace E] [T2Space M] in
private theorem finiteJet_chart_apply {s : ℕ} (A : (x : M) → Tensor0SSpace s I x) {x₀ q : M}
    (hq : q ∈ (chartAt H x₀).source) (c : Fin s → E) :
    tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ A
        (extChartAt I x₀ q) c =
      A q (fun a => tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (c a) q) := by
  have hq' : q ∈ (extChartAt I x₀).source := by simpa [extChartAt_source] using hq
  rw [tensor0SModelInChart_apply, (extChartAt I x₀).left_inv hq']
  rfl

omit [T2Space M] in
/-- **Moving-chart formula (G1.b).** Near `x₀`, the chart representative at `x₀` of `∇T`
is the derivative of the chart representative of `T` minus smooth connection terms. -/
private theorem finiteJet_moving (G : SmoothRiemannianMetric I M) {s : ℕ}
    (T : (x : M) → Tensor0SSpace s I x) (x₀ : M)
    (X : Fin (Module.finrank ℝ E) → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    {q : M} (hq : q ∈ (chartAt H x₀).source)
    (hX : ∀ᶠ p in 𝓝 q, ∀ i, X i p =
      tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (Module.finBasis ℝ E i) p)
    (hT : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
      (Set.range I) (extChartAt I x₀ q))
    (c : Fin (s + 1) → Fin (Module.finrank ℝ E)) :
    tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1) x₀
        (metricCovariantDerivative G s T) (extChartAt I x₀ q)
        (fun a => Module.finBasis ℝ E (c a)) =
      fderivWithin ℝ (fun y : E =>
          tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T y
            (fun a : Fin s => Module.finBasis ℝ E (c a.succ)))
          (Set.range I) (extChartAt I x₀ q) (Module.finBasis ℝ E (c 0)) -
        ∑ a : Fin s, ∑ i : Fin (Module.finrank ℝ E),
          (Module.finBasis ℝ E).coord i
              (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀
                (fun p : M => leviCivitaConnectionOfMetric G (fun r : M => X (c a.succ) r) p
                  (X (c 0) p)) (extChartAt I x₀ q)) *
            tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T
              (extChartAt I x₀ q)
              (fun a' : Fin s => Module.finBasis ℝ E
                (Function.update (fun a'' : Fin s => c a''.succ) a i a')) := by
  classical
  let b := Module.finBasis ℝ E
  have hsec := finiteJet_section_of_chart T hq hT
  have hXq : ∀ i, X i q = tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (b i) q := hX.self_of_nhds
  have hTq := finiteJet_chart_center_diff T q hsec
  have hpairC : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun p : M => T p (fun a : Fin s => X (c a.succ) p)) q :=
    TensorMultilinear.contMDiffAt_section_apply_one (I := I) (M := M) (n := s) (x₀ := q)
      T (hsec.of_le (by norm_num)) (fun a p => X (c a.succ) p)
      (fun a => ((X (c a.succ)).contMDiff q).of_le (by norm_num))
  have hpair : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun p : M => T p (fun a : Fin s => X (c a.succ) p)) q :=
    hpairC.mdifferentiableAt (by norm_num)
  have hG1 := metricCovariantDerivative_apply_smooth_slots G T q hTq (X (c 0))
    (fun a => X (c a.succ)) hpair
  -- left side
  have hlhs : tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1) x₀
      (metricCovariantDerivative G s T) (extChartAt I x₀ q) (fun a => b (c a)) =
      metricCovariantDerivative G s T q (Fin.cons (X (c 0) q) (fun a : Fin s => X (c a.succ) q)) := by
    rw [finiteJet_chart_apply _ hq]
    congr 1
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp [hXq]
    · simp [hXq]
  rw [hlhs, hG1]
  congr 1
  · -- the derivative term
    let F' : M → ℝ := fun p => tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      s x₀ T (extChartAt I x₀ p) (fun a : Fin s => b (c a.succ))
    have hsrc : ∀ᶠ p in 𝓝 q, p ∈ (chartAt H x₀).source :=
      (chartAt H x₀).open_source.mem_nhds hq
    have hFF : (fun p : M => T p (fun a : Fin s => X (c a.succ) p)) =ᶠ[𝓝 q] F' := by
      filter_upwards [hX, hsrc] with p hXp hp
      simp only [F']
      rw [finiteJet_chart_apply _ hp]
      simp only [hXp]
      rfl
    have hF'diff : MDifferentiableAt I 𝓘(ℝ, ℝ) F' q := hpair.congr_of_eventuallyEq hFF.symm
    have hmv : mvfderiv I (fun p : M => T p (fun a : Fin s => X (c a.succ) p)) q =
        mvfderiv I F' q := by
      unfold mvfderiv
      rw [hFF.mfderiv_eq]
      rfl
    rw [hmv, hXq (c 0), finiteJet_mvfderiv_tangentConstInChart hq hF'diff]
    have hq' : q ∈ (extChartAt I x₀).source := by simpa [extChartAt_source] using hq
    refine congrArg (fun L : E →L[ℝ] ℝ => L (b (c 0))) ?_
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _
      (extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hq'))
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem ((extChartAt I x₀).map_source hq')]
      with y hy
    simp only [writtenInExtChartAt, F', Function.comp_apply, ext_chart_model_space_apply]
    rw [(extChartAt I x₀).right_inv hy]
  · -- the connection terms
    refine Finset.sum_congr rfl fun a _ => ?_
    let W : (p : M) → TangentSpace I p := fun p =>
      leviCivitaConnectionOfMetric G (fun r : M => X (c a.succ) r) p (X (c 0) p)
    have hbase : q ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet] using hq
    have hW := (tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem (𝕜 := ℝ) (I := I)
      x₀ W hbase).self_of_nhds
    have hWq : W q = ∑ i : Fin (Module.finrank ℝ E),
        (b.coord i (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ W (extChartAt I x₀ q))) •
          tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (b i) q := hW
    have key : ∀ (m : Fin s → TangentSpace I q) (v : TangentSpace I q),
        T q (Function.update m a v) =
          ((T q : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I q) ℝ).toContinuousLinearMap
            m a) v :=
      fun m v => (ContinuousMultilinearMap.toContinuousLinearMap_apply _ m a v).symm
    change T q (Function.update (fun b' : Fin s => X (c b'.succ) q) a (W q)) = _
    rw [hWq, key, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← key, smul_eq_mul, finiteJet_chart_apply _ hq]
    congr 2
    funext a'
    by_cases ha : a' = a
    · subst ha
      simp
      rfl
    · simp [Function.update_of_ne ha, hXq]
      rfl

omit [T2Space M] in
/-- Derivative of one component of the chart representative of `∇T` at `x₀`; the derivative
is expressed through the second-order jet of the chart representative of `T` only. -/
private theorem finiteJet_component_hasFDerivWithinAt (G : SmoothRiemannianMetric I M) {s : ℕ}
    (T : (x : M) → Tensor0SSpace s I x) (x₀ : M)
    (X : Fin (Module.finrank ℝ E) → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hX : ∀ᶠ p in 𝓝 x₀, ∀ i, X i p =
      tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (Module.finBasis ℝ E i) p)
    (hT : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
      (Set.range I) (extChartAt I x₀ x₀))
    (c : Fin (s + 1) → Fin (Module.finrank ℝ E)) :
    HasFDerivWithinAt
      (fun y : E => tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1) x₀
        (metricCovariantDerivative G s T) y (fun a => Module.finBasis ℝ E (c a)))
      (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ
            (fun a : Fin s => Module.finBasis ℝ E (c a.succ))).comp
          (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) (Module.finBasis ℝ E (c 0)))).comp
          (fderivWithin ℝ (fderivWithin ℝ
            (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
            (Set.range I)) (Set.range I) (extChartAt I x₀ x₀)) -
        ∑ a : Fin s, ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).coord i
              (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀
                (fun p : M => leviCivitaConnectionOfMetric G (fun r : M => X (c a.succ) r) p
                  (X (c 0) p)) (extChartAt I x₀ x₀)) •
            ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ
              (fun a' : Fin s => Module.finBasis ℝ E
                (Function.update (fun a'' : Fin s => c a''.succ) a i a'))).comp
              (fderivWithin ℝ
                (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
                (Set.range I) (extChartAt I x₀ x₀))) +
          tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T
              (extChartAt I x₀ x₀)
              (fun a' : Fin s => Module.finBasis ℝ E
                (Function.update (fun a'' : Fin s => c a''.succ) a i a')) •
            fderivWithin ℝ (fun y : E => (Module.finBasis ℝ E).coord i
              (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀
                (fun p : M => leviCivitaConnectionOfMetric G (fun r : M => X (c a.succ) r) p
                  (X (c 0) p)) y)) (Set.range I) (extChartAt I x₀ x₀)))
      (Set.range I) (extChartAt I x₀ x₀) := by
  classical
  let b := Module.finBasis ℝ E
  let R : Set E := Set.range I
  let y₀ : E := extChartAt I x₀ x₀
  let α := tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T
  let W : Fin s → (p : M) → TangentSpace I p := fun a p =>
    leviCivitaConnectionOfMetric G (fun r : M => X (c a.succ) r) p (X (c 0) p)
  let κ : Fin s → Fin (Module.finrank ℝ E) → E → ℝ := fun a i y =>
    b.coord i (tangentFieldModelInChart (𝕜 := ℝ) (I := I) x₀ (W a) y)
  let m : Fin s → Fin (Module.finrank ℝ E) → Fin s → E := fun a i a' =>
    b (Function.update (fun a'' : Fin s => c a''.succ) a i a')
  let mt : Fin s → E := fun a => b (c a.succ)
  have hy₀R : y₀ ∈ R := extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have huniq : UniqueDiffOn ℝ R := I.uniqueDiffOn
  -- regularity
  have hTev : ∀ᶠ y in 𝓝[R] y₀, ContDiffWithinAt ℝ 2 α R y := by
    have h := hT.eventually (by simp)
    rwa [Set.insert_eq_of_mem hy₀R] at h
  have hD1 : DifferentiableWithinAt ℝ (fderivWithin ℝ α R) R y₀ :=
    (hT.fderivWithin_right (m := 1) huniq (by norm_num) hy₀R).differentiableWithinAt
      (by norm_num)
  have hα : DifferentiableWithinAt ℝ α R y₀ := hT.differentiableWithinAt (by norm_num)
  have hWsmooth : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M => (⟨p, W a p⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := fun a =>
    (covariantDeriv_vectorField_contMDiff (I := I) (leviCivitaConnectionOfMetric G)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) G) (X (c 0))
      (X (c a.succ))) x₀
  have hκ : ∀ a i, DifferentiableWithinAt ℝ (κ a i) R y₀ := fun a i =>
    (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp_differentiableWithinAt
      (x := y₀) (tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (W a) x₀ (hWsmooth a))
  -- eventual formula
  have hframe : ∀ᶠ y in 𝓝[R] y₀, ∀ᶠ p in 𝓝 ((extChartAt I x₀).symm y), ∀ i, X i p =
      tangentConstInChart (𝕜 := ℝ) (I := I) x₀ (b i) p := by
    have h := hX.eventually_nhds
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) x₀] at h
    exact h
  have hformula : (fun y : E => tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I)
        (M := M) (s + 1) x₀ (metricCovariantDerivative G s T) y (fun a => b (c a))) =ᶠ[𝓝[R] y₀]
      fun y => (fderivWithin ℝ α R y) (b (c 0)) mt -
        ∑ a : Fin s, ∑ i : Fin (Module.finrank ℝ E), κ a i y * α y (m a i) := by
    filter_upwards [hTev, hframe, extChartAt_target_mem_nhdsWithin (I := I) x₀,
      self_mem_nhdsWithin] with y hy hXy hyt hyR
    have hq : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have := (extChartAt I x₀).map_target hyt
      simpa [extChartAt_source] using this
    have hyq : extChartAt I x₀ ((extChartAt I x₀).symm y) = y := (extChartAt I x₀).right_inv hyt
    have hT' : ContDiffWithinAt ℝ 2 α R (extChartAt I x₀ ((extChartAt I x₀).symm y)) := by
      rw [hyq]; exact hy
    have hmv := finiteJet_moving G T x₀ X hq hXy hT' c
    rw [hyq] at hmv
    rw [hmv]
    congr 1
    exact fderivWithin_continuousMultilinear_apply_const_apply (huniq y hyR)
      (hy.differentiableWithinAt (by norm_num)) mt (b (c 0))
  -- derivative of the formula
  have hev : HasFDerivWithinAt (fun y : E => (fderivWithin ℝ α R y) (b (c 0)) mt)
      (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ mt).comp
          (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) (b (c 0)))).comp
        (fderivWithin ℝ (fderivWithin ℝ α R) R y₀)) R y₀ :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ mt).comp
      (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) (b (c 0)))).hasFDerivAt.comp_hasFDerivWithinAt
      y₀ hD1.hasFDerivWithinAt
  have hterm : ∀ a i, HasFDerivWithinAt (fun y : E => κ a i y * α y (m a i))
      (κ a i y₀ • ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ (m a i)).comp
          (fderivWithin ℝ α R y₀)) + α y₀ (m a i) • fderivWithin ℝ (κ a i) R y₀) R y₀ := by
    intro a i
    exact (hκ a i).hasFDerivWithinAt.mul
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ (m a i)).hasFDerivAt.comp_hasFDerivWithinAt
        y₀ hα.hasFDerivWithinAt)
  have hsum := hev.sub (HasFDerivWithinAt.fun_sum (u := Finset.univ) fun a _ =>
    HasFDerivWithinAt.fun_sum (u := Finset.univ) fun i _ => hterm a i)
  exact hsum.congr_of_eventuallyEq hformula (hformula.eq_of_nhdsWithin hy₀R)

omit [CompleteSpace E] [T2Space M] in
private theorem finiteJet_fderivWithin_eq_pi {r : ℕ} (Ψ : E → Tensor0SModel r ℝ E) {y₀ : E}
    (hy₀ : UniqueDiffWithinAt ℝ (Set.range I) y₀)
    (hΨ : ∀ c : Fin r → Fin (Module.finrank ℝ E),
      DifferentiableWithinAt ℝ (fun y => Ψ y (fun a => Module.finBasis ℝ E (c a))) (Set.range I) y₀) :
    fderivWithin ℝ Ψ (Set.range I) y₀ =
      ((Tensor.Multilinear.continuousMultilinearMapBasis (Module.finBasis ℝ E) r).equivFunL.symm :
          ((Fin r → Fin (Module.finrank ℝ E)) → ℝ) →L[ℝ] Tensor0SModel r ℝ E).comp
        (ContinuousLinearMap.pi fun c => fderivWithin ℝ
          (fun y => Ψ y (fun a => Module.finBasis ℝ E (c a))) (Set.range I) y₀) := by
  let L := (Tensor.Multilinear.continuousMultilinearMapBasis (Module.finBasis ℝ E) r).equivFunL
  have hL : (⇑L ∘ Ψ) = fun y c => Ψ y (fun a => Module.finBasis ℝ E (c a)) := by
    funext y c
    exact Tensor.Multilinear.continuousMultilinearMap_basis_repr (Module.finBasis ℝ E) r (Ψ y) c
  have h1 := L.comp_fderivWithin (f := Ψ) hy₀
  rw [hL, fderivWithin_pi hΨ hy₀] at h1
  rw [h1]
  ext v w
  change _ = (L.symm (L (fderivWithin ℝ Ψ (Set.range I) y₀ v))) w
  rw [L.symm_apply_apply]

omit [T2Space M] in
private theorem finiteJet_congr (G : SmoothRiemannianMetric I M) {r : ℕ}
    (D D' : (x : M) → Tensor0SSpace r I x) (x₀ : M)
    (hfd : fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x₀ D)
        (Set.range I) (extChartAt I x₀ x₀) =
      fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x₀ D')
        (Set.range I) (extChartAt I x₀ x₀))
    (hx : D x₀ = D' x₀) :
    metricCovariantDerivative G r D x₀ = metricCovariantDerivative G r D' x₀ := by
  unfold metricCovariantDerivative
  rw [hfd, hx]

/-- **Jet locality (G1.c).** If the chart representatives at `x₀` of two arbitrary sections are
`C²` there and have the same second-order jet, their metric covariant derivatives of order at
most two coincide at `x₀`. -/
theorem iteratedMetricCovariantDerivative_eq_of_chart_jet (G : SmoothRiemannianMetric I M)
    {s : ℕ} (T T' : (x : M) → Tensor0SSpace s I x) (x₀ : M)
    (hT : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
      (Set.range I) (extChartAt I x₀ x₀))
    (hT' : ContDiffWithinAt ℝ 2
      (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T')
      (Set.range I) (extChartAt I x₀ x₀))
    (h0 : tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T
        (extChartAt I x₀ x₀) =
      tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T'
        (extChartAt I x₀ x₀))
    (h1 : fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
        (Set.range I) (extChartAt I x₀ x₀) =
      fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T')
        (Set.range I) (extChartAt I x₀ x₀))
    (h2 : fderivWithin ℝ (fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T)
        (Set.range I)) (Set.range I) (extChartAt I x₀ x₀) =
      fderivWithin ℝ (fderivWithin ℝ
        (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x₀ T')
        (Set.range I)) (Set.range I) (extChartAt I x₀ x₀))
    {k : ℕ} (hk : k ≤ 2) :
    iteratedMetricCovariantDerivative G s T k x₀ = iteratedMetricCovariantDerivative G s T' k x₀ := by
  classical
  have hy₀R : extChartAt I x₀ x₀ ∈ Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have huniq : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
    I.uniqueDiffOn _ hy₀R
  -- order zero
  have hk0 : T x₀ = T' x₀ := by
    rw [tensor0SModelInChart_center_eq_tensor0SModelAt,
      tensor0SModelInChart_center_eq_tensor0SModelAt] at h0
    let e := trivializationAt (Tensor0SModel s ℝ E) (fun p : M => Tensor0SSpace s I p) x₀
    have hx : x₀ ∈ e.baseSet := finiteJet_mem_baseSet (mem_chart_source H x₀)
    have h := congrArg (e.symm x₀) h0
    rwa [tensor0SModelAt, tensor0SModelAt, e.symm_apply_apply_mk hx, e.symm_apply_apply_mk hx] at h
  -- order one, at the centre
  have hk1 : metricCovariantDerivative G s T x₀ = metricCovariantDerivative G s T' x₀ :=
    finiteJet_congr G T T' x₀ h1 hk0
  -- order two
  have hk2 : metricCovariantDerivative G (s + 1) (metricCovariantDerivative G s T) x₀ =
      metricCovariantDerivative G (s + 1) (metricCovariantDerivative G s T') x₀ := by
    obtain ⟨X, hX⟩ := finiteJet_exists_frame (I := I) x₀
    have hD := finiteJet_component_hasFDerivWithinAt G T x₀ X hX hT
    have hD' := finiteJet_component_hasFDerivWithinAt G T' x₀ X hX hT'
    have hcomp : ∀ c : Fin (s + 1) → Fin (Module.finrank ℝ E),
        fderivWithin ℝ (fun y : E => tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I)
          (M := M) (s + 1) x₀ (metricCovariantDerivative G s T) y
          (fun a => Module.finBasis ℝ E (c a))) (Set.range I) (extChartAt I x₀ x₀) =
        fderivWithin ℝ (fun y : E => tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I)
          (M := M) (s + 1) x₀ (metricCovariantDerivative G s T') y
          (fun a => Module.finBasis ℝ E (c a))) (Set.range I) (extChartAt I x₀ x₀) := by
      intro c
      rw [(hD c).fderivWithin huniq, (hD' c).fderivWithin huniq, h0, h1, h2]
    have hfd : fderivWithin ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I)
          (M := M) (s + 1) x₀ (metricCovariantDerivative G s T)) (Set.range I)
          (extChartAt I x₀ x₀) =
        fderivWithin ℝ (tensor0SModelInChart (𝕜 := ℝ) (E := E) (H := H) (I := I)
          (M := M) (s + 1) x₀ (metricCovariantDerivative G s T')) (Set.range I)
          (extChartAt I x₀ x₀) := by
      rw [finiteJet_fderivWithin_eq_pi _ huniq (fun c => (hD c).differentiableWithinAt),
        finiteJet_fderivWithin_eq_pi _ huniq (fun c => (hD' c).differentiableWithinAt)]
      simp_rw [hcomp]
    exact finiteJet_congr G _ _ x₀ hfd hk1
  interval_cases k
  · exact hk0
  · exact hk1
  · exact hk2

end DifferentialGeometry.Geometry.Connection
