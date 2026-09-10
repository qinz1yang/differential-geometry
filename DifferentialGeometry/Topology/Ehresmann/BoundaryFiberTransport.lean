import DifferentialGeometry.Topology.Ehresmann.BoundaryInterval
import DifferentialGeometry.Topology.Ehresmann.CompletionFiber

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Geometry.Boundary Poincare.Topology.Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

section Slice

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [HasSmoothBoundary E H I] [IsManifold I ∞ M]
  {u : M → ℝ} {a b : ℝ} [Fact (a < b)]
  [ChartedSpace E (IntervalCompletionSpace u a b)]
  [IsManifold 𝓘(ℝ, E) ∞ (IntervalCompletionSpace u a b)]

set_option backward.isDefEq.respectTransparency false in
private def productSlice
    (hu : Continuous u) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q))
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ (intervalCompletionInclusion u a b))
    (hemb : IsEmbedding (intervalCompletionInclusion u a b))
    (hj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) (intervalCompletionInclusion u a b) x))
    {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
    [TopologicalSpace HF] [TopologicalSpace F] [ChartedSpace HF F]
    {J : ModelWithCorners ℝ EF HF}
    (Θ : Diffeomorph (J.prod (𝓡∂ 1)) I (F × Icc a b) M ∞)
    (hheight : ∀ p, u (Θ p) = p.2.1) (s : Icc a b) :
    let _ := completionFiberChartedSpace hu s.2 hf (fun q _ ↦ hreg q)
    Diffeomorph J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
      F {x : M // u x = s.1} ∞ := by
  let _ := completionFiberChartedSpace hu s.2 hf (fun q _ ↦ hreg q)
  let forward : F → {x : M // u x = s.1} := fun x ↦ ⟨Θ (x, s), hheight (x, s)⟩
  let inverse : {x : M // u x = s.1} → F := fun x ↦ (Θ.symm x.1).1
  have hlevel (y : {x : M // u x = s.1}) : (Θ.symm y.1).2 = s := by
    apply Subtype.ext
    exact (hheight (Θ.symm y.1)).symm.trans ((congrArg u (Θ.apply_symm_apply y.1)).trans y.2)
  have hleft (x) : inverse (forward x) = x := congrArg Prod.fst (Θ.symm_apply_apply (x, s))
  have hright (y) : forward (inverse y) = y := by
    apply Subtype.ext
    change Θ ((Θ.symm y.1).1, s) = y.1
    have hp : ((Θ.symm y.1).1, s) = Θ.symm y.1 := by
      apply Prod.ext
      · rfl
      · exact (hlevel y).symm
    exact (congrArg Θ hp).trans (Θ.apply_symm_apply y.1)
  have hfor : ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) ∞ forward := by
    apply (contMDiff_completionFiber_iff hu s.2 hf (fun q _ ↦ hreg q) hi hemb hj forward).mpr
    exact Θ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hback : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) J ∞ inverse :=
    contMDiff_fst.comp (Θ.symm.contMDiff.comp
      (contMDiff_completionFiberInclusion hu s.2 hf (fun q _ ↦ hreg q) hi hemb hj))
  exact ⟨⟨forward, inverse, hleft, hright⟩, hfor, hback⟩

end Slice

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] [T2Space M] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_boundary_interval_fiber_transport_by_flow
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    let _ : Fact (a < b) := ⟨hab⟩
    let K := Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ
    ∃ A : ChartedSpace E (IntervalCompletionSpace u a b), let _ := A
      IsManifold 𝓘(ℝ, E) ∞ (IntervalCompletionSpace u a b) ∧
      ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
          (IntervalCompletionSpace u a b) (IntervalCompletionSpace u a b) ∞,
        ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
          (fun p : ℝ × IntervalCompletionSpace u a b ↦ D p.1 p.2) ∧
        D 0 = Diffeomorph.refl 𝓘(ℝ, E) _ ∞ ∧
        (∀ s t, (D s).trans (D t) = D (s + t)) ∧
        (∀ s, (D s).symm = D (-s)) ∧
        ∃ C : ∀ s : Icc a b, ChartedSpace K {x : M // u x = s.1},
          let _ (s : Icc a b) := C s
          (∀ s : Icc a b, IsManifold 𝓘(ℝ, K) ∞ {x : M // u x = s.1}) ∧
          (∀ s : Icc a b, ContMDiff 𝓘(ℝ, K) I ∞ (Subtype.val : {x : M // u x = s.1} → M)) ∧
          ∃ Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
              (boundaryLevel u a b hab.ne hu.continuous hboundary × Icc a b) M ∞,
            (∀ p, u (Θ p) = p.2.1) ∧
            (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) ∧
            ∃ S : ∀ s : Icc a b, Diffeomorph hI.boundaryI 𝓘(ℝ, K)
                (boundaryLevel u a b hab.ne hu.continuous hboundary) {x : M // u x = s.1} ∞,
              (∀ s x, (S s x).1 = Θ (x, s)) ∧
              ∃ T : ∀ s t : Icc a b, Diffeomorph 𝓘(ℝ, K) 𝓘(ℝ, K)
                  {x : M // u x = s.1} {x : M // u x = t.1} ∞,
                (∀ s t, T s t = (S s).symm.trans (S t)) ∧
                (∀ s t y, (T s t y).1 = Θ ((Θ.symm y.1).1, t)) ∧
                (∀ s, T s s = Diffeomorph.refl 𝓘(ℝ, K) _ ∞) ∧
                (∀ s t, (T s t).symm = T t s) ∧
                (∀ s t r, (T s t).trans (T t r) = T s r) ∧
                (∀ s t : Icc a b, ConnectedSpace {x : M // u x = s.1} ↔
                  ConnectedSpace {x : M // u x = t.1}) ∧
                (∀ p, intervalCompletionInclusion u a b (Θ p) =
                  D (p.2.1 - a) (intervalCompletionInclusion u a b p.1.1.1)) ∧
                (∀ y, intervalCompletionInclusion u a b (Θ.symm y).1.1.1 =
                  D (a - u y) (intervalCompletionInclusion u a b y)) ∧
                ∀ (s t : Icc a b) (y : {x : M // u x = s.1}),
                  intervalCompletionInclusion u a b (T s t y).1 =
                    D (t.1 - s.1) (intervalCompletionInclusion u a b y.1) := by
  let _ : Fact (a < b) := ⟨hab⟩
  let K := Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ
  obtain ⟨A, hA, D, hD, hD₀, hDadd, hDsymm, Θ, hΘ, hΘ₀, hforward, hreturn, _⟩ :=
    exists_boundary_interval_trivialization_by_flow hab hu hreg hboundary ha hb
  obtain ⟨metric⟩ := DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric (I := I) (M := M)
  obtain ⟨C₀, hm, hi, hj, hf, hr⟩ := exists_smooth_intervalCompletion metric hab hu hreg hboundary ha hb
  let := C₀
  let := hm
  have hsurj (q : IntervalCompletionSpace u a b) :
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q) := by
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ)
      (f := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q).toLinearMap)
    · exact Module.finrank_self ℝ
    · intro hz
      apply hr q
      ext v
      exact congrArg (fun L : TangentSpace 𝓘(ℝ, E) q →ₗ[ℝ]
        TangentSpace 𝓘(ℝ) (intervalCompletionHeight u a b q) ↦ L v) hz
  let C (s : Icc a b) : ChartedSpace K {x : M // u x = s.1} :=
    completionFiberChartedSpace hu.continuous s.2 hf (fun q _ ↦ hsurj q)
  have hemb := (isClosedEmbedding_intervalCompletionInclusion hu.continuous a b).isEmbedding
  let S (s : Icc a b) := productSlice hu.continuous hf hsurj hi hemb hj Θ hΘ s
  let T (s t : Icc a b) := (S s).symm.trans (S t)
  refine ⟨A, hA, D, hD, hD₀, hDadd, hDsymm, C, (fun s ↦ completionFiberIsManifold hu.continuous s.2 hf (fun q _ ↦ hsurj q)),
    (fun s ↦ contMDiff_completionFiberInclusion hu.continuous s.2 hf (fun q _ ↦ hsurj q) hi hemb hj),
    Θ, hΘ, hΘ₀, S, (fun _ _ ↦ rfl), T, (fun _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_, ?_, ?_, ?_, hforward, hreturn, ?_⟩
  · exact fun s ↦ (S s).symm_trans_self
  · intro s t
    apply Diffeomorph.ext
    intro y
    rfl
  · intro s t r
    apply Diffeomorph.ext
    intro y
    change S r ((S t).symm (S t ((S s).symm y))) = S r ((S s).symm y)
    rw [Diffeomorph.symm_apply_apply]
  · exact fun s t ↦ (T s t).toHomeomorph.connectedSpace_iff
  · intro s t y
    change intervalCompletionInclusion u a b (Θ ((Θ.symm y.1).1, t)) = _
    rw [hforward, hreturn]
    calc
      D (t.1 - a) (D (a - u y.1) (intervalCompletionInclusion u a b y.1)) =
          D ((a - u y.1) + (t.1 - a)) (intervalCompletionInclusion u a b y.1) :=
        congrArg (fun f ↦ f (intervalCompletionInclusion u a b y.1))
          (hDadd (a - u y.1) (t.1 - a))
      _ = D (t.1 - s.1) (intervalCompletionInclusion u a b y.1) := by
        have htime : (a - s.1) + (t.1 - a) = t.1 - s.1 := by ring
        rw [y.2, htime]

theorem exists_boundary_interval_fiber_transport
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    let _ : Fact (a < b) := ⟨hab⟩
    let K := Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ
    ∃ C : ∀ s : Icc a b, ChartedSpace K {x : M // u x = s.1},
      let _ (s : Icc a b) := C s
      (∀ s : Icc a b, IsManifold 𝓘(ℝ, K) ∞ {x : M // u x = s.1}) ∧
      (∀ s : Icc a b, ContMDiff 𝓘(ℝ, K) I ∞ (Subtype.val : {x : M // u x = s.1} → M)) ∧
      ∃ Θ : Diffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
          (boundaryLevel u a b hab.ne hu.continuous hboundary × Icc a b) M ∞,
        (∀ p, u (Θ p) = p.2.1) ∧
        (∀ x, Θ (x, ⟨a, le_rfl, hab.le⟩) = x.1.1) ∧
        ∃ S : ∀ s : Icc a b, Diffeomorph hI.boundaryI 𝓘(ℝ, K)
            (boundaryLevel u a b hab.ne hu.continuous hboundary) {x : M // u x = s.1} ∞,
          (∀ s x, (S s x).1 = Θ (x, s)) ∧
          ∃ T : ∀ s t : Icc a b, Diffeomorph 𝓘(ℝ, K) 𝓘(ℝ, K)
              {x : M // u x = s.1} {x : M // u x = t.1} ∞,
            (∀ s t, T s t = (S s).symm.trans (S t)) ∧
            (∀ s t y, (T s t y).1 = Θ ((Θ.symm y.1).1, t)) ∧
            (∀ s, T s s = Diffeomorph.refl 𝓘(ℝ, K) _ ∞) ∧
            (∀ s t, (T s t).symm = T t s) ∧
            (∀ s t r, (T s t).trans (T t r) = T s r) ∧
            ∀ s t : Icc a b, ConnectedSpace {x : M // u x = s.1} ↔
              ConnectedSpace {x : M // u x = t.1} := by
  obtain ⟨_, _, _, _, _, _, _, C, hm, hi, Θ, hh, hl, S, hS, T,
    hT, hformula, hid, hinv, hcomp, hconn, _⟩ :=
    exists_boundary_interval_fiber_transport_by_flow hab hu hreg hboundary ha hb
  exact ⟨C, hm, hi, Θ, hh, hl, S, hS, T, hT, hformula, hid, hinv, hcomp, hconn⟩

end Poincare.Topology.Ehresmann
