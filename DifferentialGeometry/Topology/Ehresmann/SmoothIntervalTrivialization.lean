import DifferentialGeometry.Topology.Ehresmann.SmoothIntervalFlow
import DifferentialGeometry.Topology.Manifold.SubmersionFiber

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_trivialization_over_interval_of_proper
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hreg : ∀ x, Function.Surjective (mfderiv I 𝓘(ℝ) f x))
    {a b c : ℝ} (hc : c ∈ Ioo a b) :
    let _ := regularFiberChartedSpace f c hf (fun x _ ↦ hreg x)
    let Q : TopologicalSpace.Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
    let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩
    ∃ Θ : Diffeomorph
        (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ).prod 𝓘(ℝ)) I
        ({x : M // f x = c} × Q) U ∞,
      (∀ p, f (Θ p).1 = p.2.1) ∧
      ∀ x, (Θ (x, ⟨c, hc⟩)).1 = x.1 := by
  dsimp only
  let _ := regularFiberChartedSpace f c hf (fun x _ ↦ hreg x)
  let K := Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ
  let Q : TopologicalSpace.Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
  let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩
  have hnonzero (x : M) : mfderiv I 𝓘(ℝ) f x ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := hreg x (1 : ℝ)
    rw [hz] at hv
    change (0 : ℝ) = 1 at hv
    exact zero_ne_one hv
  obtain ⟨D, hD, hD0, _, hDi, hheight⟩ :=
    exists_interval_transport_of_proper f hf hp hnonzero (hc.1.trans hc.2).le
  have hforwardHeight (x : {x : M // f x = c}) (t : Q) : f (D (t.1 - c) x.1) = t.1 := by
    have hh := hheight x.1 (by rw [x.2]; exact Ioo_subset_Icc_self hc) t.1 (Ioo_subset_Icc_self t.2)
    simpa only [x.2] using hh
  have hreturnHeight (y : U) : f ((D (f y.1 - c)).symm y.1) = c := by
    rw [hDi, neg_sub]
    exact hheight y.1 (Ioo_subset_Icc_self y.2) c (Ioo_subset_Icc_self hc)
  let forward : {x : M // f x = c} × Q → U := fun p ↦
    ⟨D (p.2.1 - c) p.1.1, by
      change f (D (p.2.1 - c) p.1.1) ∈ Ioo a b
      rw [hforwardHeight]
      exact p.2.2⟩
  let inverse : U → {x : M // f x = c} × Q := fun y ↦
    (⟨(D (f y.1 - c)).symm y.1, hreturnHeight y⟩, ⟨f y.1, y.2⟩)
  have hover (p) : f (forward p).1 = p.2.1 := hforwardHeight p.1 p.2
  have hleft (p) : inverse (forward p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change (D (f (forward p).1 - c)).symm (D (p.2.1 - c) p.1.1) = p.1.1
      rw [hover, Diffeomorph.symm_apply_apply]
    · exact Subtype.ext (hover p)
  have hright (y) : forward (inverse y) = y := by
    apply Subtype.ext
    exact (D (f y.1 - c)).apply_symm_apply y.1
  have hfor : ContMDiff (𝓘(ℝ, K).prod 𝓘(ℝ)) I ∞ forward := by
    apply (ContMDiff.subtypeVal_comp_iff U forward).mp
    exact hD.comp (((contMDiff_subtype_val.comp contMDiff_snd).sub contMDiff_const).prodMk
      ((contMDiff_regularFiberInclusion f c hf (fun x _ ↦ hreg x)).comp contMDiff_fst))
  have hbase : ContMDiff I 𝓘(ℝ) ∞ (fun y : U ↦ (⟨f y.1, y.2⟩ : Q)) := by
    apply (ContMDiff.subtypeVal_comp_iff Q _).mp
    exact hf.comp contMDiff_subtype_val
  have hDinverse : ContMDiff (𝓘(ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ (D p.1).symm p.2) := by
    simpa only [hDi, Function.comp_def] using hD.comp (contMDiff_fst.neg.prodMk contMDiff_snd)
  have hinv : ContMDiff I (𝓘(ℝ, K).prod 𝓘(ℝ)) ∞ inverse := by
    apply ContMDiff.prodMk _ hbase
    apply (contMDiff_regularFiber_iff f c hf (fun x _ ↦ hreg x) _).mpr
    exact hDinverse.comp (((hf.comp contMDiff_subtype_val).sub contMDiff_const).prodMk
      contMDiff_subtype_val)
  let Θ : Diffeomorph (𝓘(ℝ, K).prod 𝓘(ℝ)) I ({x : M // f x = c} × Q) U ∞ :=
    { toEquiv := ⟨forward, inverse, hleft, hright⟩
      contMDiff_toFun := hfor
      contMDiff_invFun := hinv }
  refine ⟨Θ, hover, ?_⟩
  intro x
  change D (c - c) x.1 = x.1
  rw [sub_self, hD0]
  rfl

end DifferentialGeometry.Topology.Ehresmann
