import DifferentialGeometry.Topology.Ehresmann.ProperSubmersion
import DifferentialGeometry.Topology.Manifold.SubmersionFiber
import DifferentialGeometry.Topology.Manifold.VectorField
import DifferentialGeometry.Topology.Manifold.DiffeomorphFamily

noncomputable section
open scoped ContDiff Manifold Topology
open Poincare.Topology.Manifold DifferentialGeometry.Analysis.ODE

namespace Poincare.Topology.Ehresmann

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

private theorem trivialization_of_related_diffeomorphFamily
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, Function.Surjective (mfderiv I J f x)) (y : N)
    (D : P → M ≃ₘ⟮I, I⟯ M) (d : P → N ≃ₘ⟮J, J⟯ N)
    (hD : ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun p : P × M ↦ D p.1 p.2))
    (hDi : ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun p : P × M ↦ (D p.1).symm p.2))
    (hrel : ∀ t x, f (D t x) = d t (f x))
    (hbase : IsLocalDiffeomorphAt 𝓘(ℝ, P) J ∞ (fun t ↦ d t y) 0)
    (hd0 : d 0 y = y) (hD0 : D 0 = Diffeomorph.refl I M ∞) :
    let _ := regularFiberChartedSpace f y hf (fun x _ ↦ hreg x)
    ∃ Q : TopologicalSpace.Opens N, ∃ hy : y ∈ Q,
      let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
      ∃ Θ : Diffeomorph
          (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ).prod J) I
          ({x : M // f x = y} × Q) U ∞,
        (∀ p, f (Θ p).1 = p.2.1) ∧
        (∀ x, (Θ (x, ⟨y, hy⟩)).1 = x.1) := by
  dsimp only
  let _ := regularFiberChartedSpace f y hf (fun x _ ↦ hreg x)
  let K := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let Q : TopologicalSpace.Opens N :=
    ⟨hbase.localInverse.source, hbase.localInverse_open_source⟩
  have hy : y ∈ Q := by
    change y ∈ hbase.localInverse.source
    simpa only [hd0] using hbase.localInverse_mem_source
  let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
  let σ : Q → P := fun z ↦ hbase.localInverse z.1
  have hσ : ContMDiff J 𝓘(ℝ, P) ∞ σ := by
    intro z
    apply contMDiffAt_subtype_iff.mpr
    exact (hbase.contmdiffOn_localInverse z.1 z.2).contMDiffAt (Q.isOpen.mem_nhds z.2)
  have hσy : σ ⟨y, hy⟩ = 0 := by
    have hz := hbase.localInverse_left_inv hbase.localInverse_mem_target
    simpa only [hd0] using hz
  have hσright : ∀ z : Q, d (σ z) y = z.1 := fun z ↦ hbase.localInverse_right_inv z.2
  have hreturn : ∀ z : U, f ((D (σ ⟨f z.1, z.2⟩)).symm z.1) = y := by
    intro z
    apply (d (σ ⟨f z.1, z.2⟩)).injective
    change d (σ ⟨f z.1, z.2⟩) (f ((D (σ ⟨f z.1, z.2⟩)).symm z.1)) =
      d (σ ⟨f z.1, z.2⟩) y
    rw [← hrel, Diffeomorph.apply_symm_apply, hσright]
  let forward : {x : M // f x = y} × Q → U := fun p ↦
    ⟨D (σ p.2) p.1.1, by
      change f (D (σ p.2) p.1.1) ∈ Q
      rw [hrel, p.1.2, hσright]
      exact p.2.2⟩
  let inverse : U → {x : M // f x = y} × Q := fun z ↦
    (⟨(D (σ ⟨f z.1, z.2⟩)).symm z.1, hreturn z⟩, ⟨f z.1, z.2⟩)
  have hover : ∀ p, f (forward p).1 = p.2.1 := by
    intro p
    change f (D (σ p.2) p.1.1) = p.2.1
    rw [hrel, p.1.2, hσright]
  have hleft : ∀ p, inverse (forward p) = p := by
    intro p
    have hz : (⟨f (forward p).1, (forward p).2⟩ : Q) = p.2 := Subtype.ext (hover p)
    apply Prod.ext
    · apply Subtype.ext
      change (D (σ ⟨f (forward p).1, (forward p).2⟩)).symm (D (σ p.2) p.1.1) = p.1.1
      rw [hz, Diffeomorph.symm_apply_apply]
    · exact hz
  have hright : ∀ z, forward (inverse z) = z := by
    intro z
    apply Subtype.ext
    exact (D (σ ⟨f z.1, z.2⟩)).apply_symm_apply z.1
  have hforward : ContMDiff (𝓘(ℝ, K).prod J) I ∞ forward := by
    apply (ContMDiff.subtypeVal_comp_iff U forward).mp
    exact hD.comp ((hσ.comp contMDiff_snd).prodMk
      ((contMDiff_regularFiberInclusion f y hf (fun x _ ↦ hreg x)).comp contMDiff_fst))
  have hheight : ContMDiff I J ∞ (fun z : U ↦ (⟨f z.1, z.2⟩ : Q)) := by
    apply (ContMDiff.subtypeVal_comp_iff Q _).mp
    exact hf.comp contMDiff_subtype_val
  have hinverse : ContMDiff I (𝓘(ℝ, K).prod J) ∞ inverse := by
    apply ContMDiff.prodMk _ hheight
    apply (contMDiff_regularFiber_iff f y hf (fun x _ ↦ hreg x) _).mpr
    exact hDi.comp ((hσ.comp hheight).prodMk contMDiff_subtype_val)
  let Θ : Diffeomorph (𝓘(ℝ, K).prod J) I ({x : M // f x = y} × Q) U ∞ :=
    { toEquiv := ⟨forward, inverse, hleft, hright⟩
      contMDiff_toFun := hforward
      contMDiff_invFun := hinverse }
  refine ⟨Q, hy, Θ, hover, ?_⟩
  intro x
  change D (σ ⟨y, hy⟩) x.1 = x.1
  rw [hσy, hD0]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ehresmann_local_triviality
    [T2Space M] [SigmaCompactSpace M] [T2Space N]
    (f : M → N) (hf : ContMDiff I J ∞ f) (hproper : IsProperMap f)
    (hreg : ∀ x, Function.Surjective (mfderiv I J f x)) (y : N) :
    let _ := regularFiberChartedSpace f y hf (fun x _ ↦ hreg x)
    ∃ Q : TopologicalSpace.Opens N, ∃ hy : y ∈ Q,
      let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
      ∃ Θ : Diffeomorph
          (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ).prod J) I
          ({x : M // f x = y} × Q) U ∞,
        (∀ p, f (Θ p).1 = p.2.1) ∧
        (∀ x, (Θ (x, ⟨y, hy⟩)).1 = x.1) := by
  classical
  let ι := Fin (Module.finrank ℝ F)
  let b := Module.finBasis ℝ F
  have hex : ∀ i : ι, ∃ Z : Cₛ^∞⟮J; F, TangentSpace J⟯,
      Z y = b i ∧ IsCompact (tsupport Z) := by
    intro i
    obtain ⟨Z, he, hc, -⟩ := exists_compactlySupported_vectorField_eq
      (I := J) y (b i) (U := Set.univ) Filter.univ_mem
    exact ⟨Z, he, hc⟩
  choose Z hZvalue hZcompact using hex
  have hlift := fun i : ι ↦ exists_compactlySupported_smoothDerivativeLift_of_surjective
    f hproper hf hreg (Z i) (Z i).contMDiff (hZcompact i)
  choose X hrel hsupport hXcompact using hlift
  let d : ι → ℝ → N ≃ₘ⟮J, J⟯ N := fun i ↦
    compactSupportFlowDiffeomorph (Z i) (Z i).contMDiff (hZcompact i)
  let D : ι → ℝ → M ≃ₘ⟮I, I⟯ M := fun i ↦
    compactSupportFlowDiffeomorph (X i) (X i).contMDiff (hXcompact i)
  have hd0 : ∀ i, d i 0 = Diffeomorph.refl J N ∞ := fun i ↦
    compactSupportFlowDiffeomorph_zero (Z i) (Z i).contMDiff (hZcompact i)
  have hD0 : ∀ i, D i 0 = Diffeomorph.refl I M ∞ := fun i ↦
    compactSupportFlowDiffeomorph_zero (X i) (X i).contMDiff (hXcompact i)
  have hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞
      (fun p : ℝ × N ↦ d i p.1 p.2) := fun i ↦
    contMDiff_globalFlow_joint_of_compactSupport (Z i) (Z i).contMDiff (hZcompact i)
  have hD : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ D i p.1 p.2) := fun i ↦
    contMDiff_globalFlow_joint_of_compactSupport (X i) (X i).contMDiff (hXcompact i)
  have hDi : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ (D i p.1).symm p.2) := by
    intro i
    exact (hD i).comp (contMDiff_fst.neg.prodMk contMDiff_snd)
  have hb : ∀ i, mfderiv 𝓘(ℝ, ℝ) J (fun r ↦ d i r y) 0 (1 : ℝ) = b i := by
    intro i
    have hc := (curveAt_integralCurve (Z i)
      (exists_globalIntegralCurve_of_compactSupport (Z i) (Z i).contMDiff (hZcompact i)) y) 0
    change (mfderiv 𝓘(ℝ, ℝ) J (curveAt (Z i)
      (exists_globalIntegralCurve_of_compactSupport (Z i) (Z i).contMDiff (hZcompact i)) y)
      0) (1 : ℝ) = b i
    rw [hc.mfderiv]
    change (1 : ℝ) • ((Z i) (curveAt (Z i)
      (exists_globalIntegralCurve_of_compactSupport (Z i) (Z i).contMDiff (hZcompact i)) y 0) : F) = b i
    rw [one_smul]
    exact (congrArg (fun z : N ↦ ((Z i) z : F))
      (curveAt_zero (Z i)
        (exists_globalIntegralCurve_of_compactSupport (Z i) (Z i).contMDiff (hZcompact i)) y)).trans
      (hZvalue i)
  have hrelated : ∀ (l : List ι) (t : ι → ℝ) (x : M),
      f (diffeomorphList D l t x) = diffeomorphList d l t (f x) := by
    intro l t
    induction l with
    | nil => exact fun _ ↦ rfl
    | cons i l ih =>
      intro x
      change f (diffeomorphList D l t (D i (t i) x)) =
        diffeomorphList d l t (d i (t i) (f x))
      rw [ih, compactSupportFlowDiffeomorph_map_of_mfderiv_eq
        f (hf.of_le (by norm_num)) (X i) (X i).contMDiff (hXcompact i)
        (Z i) (Z i).contMDiff (hZcompact i) (hrel i)]
  let l := List.finRange (Module.finrank ℝ F)
  have hbase := isLocalDiffeomorphAt_diffeomorphList_of_basis d hd0 hd l
    (List.nodup_finRange _) (fun i ↦ List.mem_finRange i) y b hb
  exact trivialization_of_related_diffeomorphFamily f hf hreg y
    (diffeomorphList D l) (diffeomorphList d l)
    (contMDiff_diffeomorphList D hD l) (contMDiff_diffeomorphList_symm D hDi l)
    (hrelated l) hbase (by rw [diffeomorphList_zero d hd0]; rfl)
    (diffeomorphList_zero D hD0 l)

end Poincare.Topology.Ehresmann
