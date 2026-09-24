import DifferentialGeometry.Geometry.Metric.Family.Continuity
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [IsManifold J 1 N]

namespace tensor0SFamilyContinuousOnSet

theorem of_surjective_localPullMetric
    {s : ℕ} {K : Set ℝ}
    {k : ℝ → (x : M) → Tensor0SSpace s I x}
    {A : ℝ → (y : N) → Tensor0SSpace s J y}
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hk : tensor0SFamilyContinuousOnSet (I := I) (M := M) s K k)
    (hrel : ∀ t ∈ K, ∀ x : M, ∀ v : Fin s → TangentSpace I x,
      k t x v = A t (f x) (fun i => mfderiv I J f x (v i))) :
    tensor0SFamilyContinuousOnSet (I := J) (M := N) s K A := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp (A := A)
    (N := fun y₀ => (trivializationAt F (TangentSpace J) y₀).baseSet)
  · intro y₀
    exact (Trivialization.open_baseSet _).mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) y₀)
  · intro y₀ idx
    obtain ⟨x₀, rfl⟩ := hsurj y₀
    let B : Set N := (trivializationAt F (TangentSpace J) (f x₀)).baseSet
    have hBopen : IsOpen B := (trivializationAt F (TangentSpace J) (f x₀)).open_baseSet
    let w : Fin s → (y : N) → TangentSpace J y := fun i y =>
      DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := J) (f x₀) (idx i) y
    intro q hq
    obtain ⟨x, hx⟩ := hsurj q.2
    let Y := (hf x).localInverse
    have hxmem : f x ∈ Y.source := (hf x).localInverse_mem_source
    have hqY : q.2 ∈ Y.source := by rw [← hx]; exact hxmem
    have hYsm : ContMDiffOn J I ∞ (Y : N → M) Y.source := (hf x).localInverse_contMDiffOn
    have hYopen : IsOpen Y.source := Y.open_source
    have hYDiff : ∀ y ∈ Y.source, MDifferentiableAt J I (Y : N → M) y := fun y hy =>
      (hYsm.contMDiffAt (hYopen.mem_nhds hy)).mdifferentiableAt (by simp)
    let V : Set N := Y.source ∩ B
    have hVopen : IsOpen V := hYopen.inter hBopen
    have hVnhds : {r : {t : ℝ // t ∈ K} × N | r.2 ∈ V} ∈ 𝓝 q :=
      continuous_snd.continuousAt (hVopen.mem_nhds ⟨hqY, hq⟩)
    let Gs : {t : ℝ // t ∈ K} × N → ℝ :=
      fun r => k r.1.1 (Y r.2) (fun i => mfderiv J I Y r.2 (w i r.2))
    have hsec : ∀ i : Fin s, ContinuousOn
        (fun y : N => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Y y)
          (mfderiv J I Y y (w i y))) V := by
      intro i
      have hv : ContMDiffOn J (J.prod 𝓘(ℝ, F)) ∞
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := J) (f x₀) (idx i)) B :=
        DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (f x₀) (idx i)
      have hv' : ContMDiffOn J (J.prod 𝓘(ℝ, F)) ∞
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := J) (f x₀) (idx i)) V :=
        hv.mono inter_subset_right
      have ht : ContMDiffOn J.tangent I.tangent ∞
          (tangentMapWithin J I (Y : N → M) V) (TotalSpace.proj ⁻¹' V) :=
        (hYsm.mono inter_subset_left).contMDiffOn_tangentMapWithin (m := ∞) le_rfl
          hVopen.uniqueMDiffOn
      have ht' : ContMDiffOn J (I.prod 𝓘(ℝ, E)) ∞
          (fun y : N => tangentMapWithin J I (Y : N → M) V
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := J) (f x₀) (idx i) y)) V :=
        ht.comp hv' (fun y hy => hy)
      have ht'' : ContMDiffOn J (I.prod 𝓘(ℝ, E)) ∞
          (fun y : N => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Y y)
            (mfderiv J I (Y : N → M) y
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
                (I := J) (f x₀) (idx i) y))) V := by
        apply ht'.congr
        intro y hy
        change (⟨Y y, mfderiv J I (Y : N → M) y
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
              (I := J) (f x₀) (idx i) y)⟩ : TangentBundle I M) =
          ⟨Y y, mfderivWithin J I (Y : N → M) V y
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
              (I := J) (f x₀) (idx i) y)⟩
        rw [mfderivWithin_eq_mfderiv (hVopen.uniqueMDiffOn y hy) (hYDiff y hy.1)]
      exact ht''.continuousOn
    have hGs : ContinuousAt Gs q := by
      have hPcont : Continuous (fun p : {r : {t : ℝ // t ∈ K} × N // r.2 ∈ V} => Gs p.1) := by
        have hτc : Continuous (fun p : {r : {t : ℝ // t ∈ K} × N // r.2 ∈ V} => (p.1.1.1 : ℝ)) :=
          continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
        have hb : Continuous (fun p : {r : {t : ℝ // t ∈ K} × N // r.2 ∈ V} => Y p.1.2) :=
          (hYsm.continuousOn).comp_continuous (continuous_snd.comp continuous_subtype_val)
            (fun p => p.2.1)
        have hvec : ∀ i : Fin s, Continuous (fun p : {r : {t : ℝ // t ∈ K} × N // r.2 ∈ V} =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Y p.1.2)
              (mfderiv J I Y p.1.2 (w i p.1.2))) := fun i =>
          (hsec i).comp_continuous (continuous_snd.comp continuous_subtype_val)
            (fun p => p.2)
        have hkey := hk.eval_continuous hτc (fun p => p.1.1.2) hb hvec
        exact hkey
      have hcontOn : ContinuousOn Gs {r : {t : ℝ // t ∈ K} × N | r.2 ∈ V} :=
        continuousOn_iff_continuous_domRestrict.mpr hPcont
      exact hcontOn.continuousAt hVnhds
    have hev : (fun r : {t : ℝ // t ∈ K} × N => A r.1.1 r.2 (fun i => w i r.2)) =ᶠ[𝓝 q] Gs := by
      have hEqOn : EqOn (f ∘ (Y : N → M)) id Y.source := (hf x).localInverse_eqOn_right
      filter_upwards [hVnhds] with r hr
      have hfr : f (Y r.2) = r.2 := hEqOn hr.1
      have hYdiff : MDifferentiableAt J I (Y : N → M) r.2 := hYDiff r.2 hr.1
      have hfdiff : MDifferentiableAt I J f (Y r.2) := (hf (Y r.2)).mdifferentiableAt (by simp)
      have heveq : f ∘ (Y : N → M) =ᶠ[𝓝 r.2] id := by
        filter_upwards [hYopen.mem_nhds hr.1] with z hz
        exact hEqOn hz
      have hchain : ∀ i : Fin s,
          mfderiv I J f (Y r.2) (mfderiv J I Y r.2 (w i r.2)) = w i r.2 := by
        intro i
        have hc := mfderiv_comp (I := J) (I' := I) (I'' := J) (x := r.2)
          (f := (Y : N → M)) (g := f) hfdiff hYdiff
        have hid : mfderiv J J (f ∘ (Y : N → M)) r.2 =
            ContinuousLinearMap.id ℝ (TangentSpace J r.2) := by
          rw [heveq.mfderiv_eq, mfderiv_id]
        rw [hid] at hc
        exact congrArg (fun L : TangentSpace J r.2 →L[ℝ] TangentSpace J r.2 => L (w i r.2))
          hc.symm
      have hGs_eq : Gs r = A r.1.1 r.2 (fun i => w i r.2) := by
        change k r.1.1 (Y r.2) (fun i => mfderiv J I Y r.2 (w i r.2)) =
          A r.1.1 r.2 (fun i => w i r.2)
        rw [hrel r.1.1 r.1.2 (Y r.2) (fun i => mfderiv J I Y r.2 (w i r.2)), hfr]
        exact congrArg (fun z : Fin s → TangentSpace J r.2 => A r.1.1 r.2 z)
          (funext (fun i => hchain i))
      exact hGs_eq.symm
    have hFa : ContinuousAt (fun r : {t : ℝ // t ∈ K} × N => A r.1.1 r.2 (fun i => w i r.2)) q :=
      hGs.congr hev.symm
    exact hFa.continuousWithinAt

end tensor0SFamilyContinuousOnSet

end DifferentialGeometry.Geometry.Curvature
