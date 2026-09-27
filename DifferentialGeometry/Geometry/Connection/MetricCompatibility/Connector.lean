import DifferentialGeometry.Geometry.Connection.Connector
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {IP : ModelWithCorners ℝ E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle I 1 F V] in
private theorem mdifferentiableWithinAt_fiber_coord
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {b : P → M} {Z : ∀ p, V (b p)} {s : Set P} {p : P} (he : b p ∈ e.baseSet)
    (hZ : MDifferentiableWithinAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) s p) :
    MDifferentiableWithinAt IP 𝓘(ℝ, F)
      (fun q => e.continuousLinearMapAt ℝ (b q) (Z q)) s p := by
  have h := (e.mdifferentiableWithinAt_totalSpace_iff I
    (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ
  apply h.2.congr_of_eventuallyEq
  · filter_upwards [h.1.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he)] with q hq
    exact e.continuousLinearMapAt_apply_of_mem ℝ hq (Z q)
  · exact e.continuousLinearMapAt_apply_of_mem ℝ he (Z p)

theorem IsMetricCompatible.mvfderivWithin_inner
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    {b : P → M} {Z W : ∀ p, V (b p)} {s : Set P} {p : P}
    (hs : UniqueMDiffWithinAt IP s p)
    (hZ : MDifferentiableWithinAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) s p)
    (hW : MDifferentiableWithinAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, W q⟩ : TotalSpace F V)) s p) (U : TangentSpace IP p) :
    mvfderivWithin IP (fun q => inner ℝ (Z q) (W q)) s p U =
      inner ℝ (cov.connector (⟨b p, Z p⟩ : TotalSpace F V)
        (mfderivWithin IP (I.prod 𝓘(ℝ, F))
          (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) s p U)) (W p) +
      inner ℝ (Z p) (cov.connector (⟨b p, W p⟩ : TotalSpace F V)
        (mfderivWithin IP (I.prod 𝓘(ℝ, F))
          (fun q => (⟨b q, W q⟩ : TotalSpace F V)) s p U)) := by
  classical
  let e := trivializationAt F V (b p)
  have he : b p ∈ e.baseSet := mem_baseSet_trivializationAt F V (b p)
  let z : P → F := fun q => e.continuousLinearMapAt ℝ (b q) (Z q)
  let w : P → F := fun q => e.continuousLinearMapAt ℝ (b q) (W q)
  let B : M → F →L[ℝ] F →L[ℝ] ℝ := fun x =>
    (innerSL ℝ : V x →L[ℝ] V x →L[ℝ] ℝ).bilinearComp (e.symmL ℝ x) (e.symmL ℝ x)
  have hsection (v : F) : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun x => (⟨x, e.symmL ℝ x v⟩ : TotalSpace F V)) (b p) := by
    rw [e.contMDiffAt_section_iff he]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with x hx
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hx]
    exact e.continuousLinearMapAt_symmL hx v
  have hB : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) 1 B (b p) := by
    apply contMDiffAt_clm_of_pointwise
    intro v
    apply contMDiffAt_clm_of_pointwise
    intro u
    exact (hsection v).inner_bundle (hsection u)
  have hb : MDifferentiableWithinAt IP I b s p :=
    ((e.mdifferentiableWithinAt_totalSpace_iff I
      (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) (e.mem_source.mpr he)).mp hZ).1
  have hBdiff : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) B (b p) :=
    hB.mdifferentiableAt (by simp)
  have hBb : MDifferentiableWithinAt IP 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)
      (fun q => B (b q)) s p := hBdiff.comp_mdifferentiableWithinAt p hb
  have hz : MDifferentiableWithinAt IP 𝓘(ℝ, F) z s p :=
    mdifferentiableWithinAt_fiber_coord e he hZ
  have hw : MDifferentiableWithinAt IP 𝓘(ℝ, F) w s p :=
    mdifferentiableWithinAt_fiber_coord e he hW
  have heq : (fun q => inner ℝ (Z q) (W q)) =ᶠ[𝓝[s] p]
      (fun q => B (b q) (z q) (w q)) := by
    filter_upwards [hb.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds he)] with q hq
    simp only [B, z, w, ContinuousLinearMap.bilinearComp_apply,
      e.symmL_continuousLinearMapAt hq, innerSL_apply_apply]
  have heq₀ : inner ℝ (Z p) (W p) = B (b p) (z p) (w p) := by
    simp only [B, z, w, ContinuousLinearMap.bilinearComp_apply,
      e.symmL_continuousLinearMapAt he, innerSL_apply_apply]
  have hD : mvfderivWithin IP (fun q => inner ℝ (Z q) (W q)) s p U =
      mvfderivWithin IP (fun q => B (b q)) s p U (z p) (w p) +
        B (b p) (mvfderivWithin IP z s p U) (w p) +
        B (b p) (z p) (mvfderivWithin IP w s p U) := by
    have hd : mvfderivWithin IP (fun q => inner ℝ (Z q) (W q)) s p =
        mvfderivWithin IP (fun q => B (b q) (z q) (w q)) s p := by
      simp only [mvfderivWithin, heq.mfderivWithin_eq heq₀]
      rfl
    rw [hd, (hBb.clm_apply hz).mvfderivWithin_clm_apply hw hs,
      hBb.mvfderivWithin_clm_apply hz hs]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    ring
  let X := mfderivWithin IP I b s p U
  have hfixed : mvfderivWithin IP (fun q => B (b q)) s p U (z p) (w p) =
      mvfderiv I (fun x => B x (z p) (w p)) (b p) X := by
    have hf : MDifferentiableAt I 𝓘(ℝ) (fun x => B x (z p) (w p)) (b p) :=
      ((hsection (z p)).inner_bundle (hsection (w p))).mdifferentiableAt (by simp)
    have h := hf.mvfderiv_comp_mfderivWithin_apply (f := b) hb hs U
    change mvfderivWithin IP (fun q => B (b q) (z p) (w p)) s p U = _ at h
    rw [(hBb.clm_apply (mdifferentiableWithinAt_const (c := z p))).mvfderivWithin_clm_apply
      (mdifferentiableWithinAt_const (c := w p)) hs,
      hBb.mvfderivWithin_clm_apply (mdifferentiableWithinAt_const (c := z p)) hs] at h
    simp only [mvfderivWithin_const, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at h
    exact h
  have hcon (v : F) : cov (fun x => e.symmL ℝ x v) (b p) X =
      e.symmL ℝ (b p) (cov.connectionForm e (b p) X v) := by
    rw [cov.connectionForm_apply e he]
    exact (e.symmL_continuousLinearMapAt he _).symm
  have hmetric := hcov.mvfderiv_inner_eq
    (Function.update (fun x => (0 : TangentSpace I x)) (b p) X)
    ((hsection (z p)).mdifferentiableAt (by simp))
    ((hsection (w p)).mdifferentiableAt (by simp))
  simp only [Function.update_self, hcon] at hmetric
  change mvfderiv I (fun x => B x (z p) (w p)) (b p) X =
    B (b p) (cov.connectionForm e (b p) X (z p)) (w p) +
      B (b p) (z p) (cov.connectionForm e (b p) X (w p)) at hmetric
  have hz₀ : e.symmL ℝ (b p) (z p) = Z p := e.symmL_continuousLinearMapAt he (Z p)
  have hw₀ : e.symmL ℝ (b p) (w p) = W p := e.symmL_continuousLinearMapAt he (W p)
  rw [cov.connector_mfderivWithin_eq e he hs hZ U,
    cov.connector_mfderivWithin_eq e he hs hW U, ← hz₀, ← hw₀]
  simp only [e.continuousLinearMapAt_symmL he]
  change mvfderivWithin IP (fun q => inner ℝ (Z q) (W q)) s p U =
    B (b p) (mvfderivWithin IP z s p U + cov.connectionForm e (b p) X (z p)) (w p) +
      B (b p) (z p) (mvfderivWithin IP w s p U + cov.connectionForm e (b p) X (w p))
  rw [hD, hfixed, hmetric]
  simp only [map_add, add_apply]
  ring

theorem IsMetricCompatible.mvfderiv_inner
    {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)
    {b : P → M} {Z W : ∀ p, V (b p)} {p : P}
    (hZ : MDifferentiableAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) p)
    (hW : MDifferentiableAt IP (I.prod 𝓘(ℝ, F))
      (fun q => (⟨b q, W q⟩ : TotalSpace F V)) p) (U : TangentSpace IP p) :
    mvfderiv IP (fun q => inner ℝ (Z q) (W q)) p U =
      inner ℝ (cov.connector (⟨b p, Z p⟩ : TotalSpace F V)
        (mfderiv IP (I.prod 𝓘(ℝ, F))
          (fun q => (⟨b q, Z q⟩ : TotalSpace F V)) p U)) (W p) +
      inner ℝ (Z p) (cov.connector (⟨b p, W p⟩ : TotalSpace F V)
        (mfderiv IP (I.prod 𝓘(ℝ, F))
          (fun q => (⟨b q, W q⟩ : TotalSpace F V)) p U)) := by
  simpa only [mfderivWithin_univ, mvfderivWithin_univ] using
    hcov.mvfderivWithin_inner (uniqueMDiffWithinAt_univ IP)
      hZ.mdifferentiableWithinAt hW.mdifferentiableWithinAt U

end CovariantDerivative
