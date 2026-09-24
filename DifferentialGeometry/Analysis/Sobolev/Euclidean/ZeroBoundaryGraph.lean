import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import DifferentialGeometry.Analysis.InnerProductSpace.WeakCompactness
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => Lp ℝ 2 (volume.restrict Ω)
local notation "Y" => Lp E 2 (volume.restrict Ω)

private def smoothTestGraph (hΩ : IsOpen Ω) : Submodule ℝ (X × Y) where
  carrier := {w | ∃ (f : E → ℝ) (hf : DeGiorgi.IsSmoothTestOn Ω f),
    w = (DeGiorgi.smoothFunToLp hΩ hf, DeGiorgi.smoothGradToLp hΩ hf)}
  zero_mem' := by
    refine ⟨0, DeGiorgi.IsSmoothTestOn.zero, ?_⟩
    simp only [DeGiorgi.smoothFunToLp_zero, DeGiorgi.smoothGradToLp_zero, Prod.mk_zero_zero]
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨fun x => f x + g x, hf.add hg, ?_⟩
    exact Prod.ext (DeGiorgi.smoothFunToLp_add hΩ hf hg).symm
      (DeGiorgi.smoothGradToLp_add hΩ hf hg).symm
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    refine ⟨fun x => c * f x, hf.smul c, ?_⟩
    exact Prod.ext (DeGiorgi.smoothFunToLp_smul hΩ c hf).symm
      (DeGiorgi.smoothGradToLp_smul hΩ c hf).symm

private theorem eLpNorm_euclidean_le_sum {ι : Type*} [Fintype ι]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → EuclideanSpace ℝ ι) (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ ≤ ∑ i, eLpNorm (fun x => f x i) 2 μ := by
  classical
  have hn (v : EuclideanSpace ℝ ι) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
    have heq : (∑ i, EuclideanSpace.single i (v i)) = v := by ext; simp
    calc
      ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := by rw [heq]
      _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
      _ = ∑ i, ‖v i‖ := by simp only [PiLp.norm_single]
  calc
    eLpNorm f 2 μ ≤ eLpNorm (∑ i, fun x => ‖f x i‖) 2 μ :=
      eLpNorm_mono_real (fun x => by simpa only [Finset.sum_apply] using hn (f x))
    _ ≤ ∑ i, eLpNorm (fun x => ‖f x i‖) 2 μ :=
      eLpNorm_sum_le (fun i _ => (hf.eval_piLp i).aestronglyMeasurable.norm) (by norm_num)
    _ = _ := by simp only [eLpNorm_norm]

private theorem mem_smoothTestGraph_closure (hΩ : IsOpen Ω)
    {f : E → ℝ} (hf : DeGiorgi.MemW01p 2 f Ω) :
    (hf.1.1.toLp f, DeGiorgi.gradLpOfWitness (Classical.choose hf.2)) ∈
      (smoothTestGraph hΩ).topologicalClosure := by
  let hw := Classical.choose hf.2
  obtain ⟨φ, hφs, hφc, hφΩ, hφf, hφg⟩ := Classical.choose_spec hf.2
  let ht (n : ℕ) : DeGiorgi.IsSmoothTestOn Ω (φ n) := ⟨hφs n, hφc n, hφΩ n⟩
  have hF : Tendsto (fun n => DeGiorgi.smoothFunToLp hΩ (ht n)) atTop
      (𝓝 (hf.1.1.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n =>
      (DeGiorgi.smoothTestWitness hΩ (ht n)).memLp) (f_lim_ℒp := hf.1.1)).mpr hφf
  have hG : Tendsto (fun n => DeGiorgi.smoothGradToLp hΩ (ht n)) atTop
      (𝓝 (DeGiorgi.gradLpOfWitness hw)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n =>
      (DeGiorgi.smoothTestWitness hΩ (ht n)).weakGrad_memLp)
      (f_lim_ℒp := hw.weakGrad_memLp)).mpr
    have hsum : Tendsto (fun n => ∑ i : Fin d, eLpNorm
        (fun x => DeGiorgi.smoothGradField (φ n) x i - hw.weakGrad x i)
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero, DeGiorgi.smoothGradField, PiLp.toLp_apply, hw] using
        tendsto_finsetSum Finset.univ (fun i _ => hφg i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le)
    intro n
    exact eLpNorm_euclidean_le_sum _
      ((DeGiorgi.smoothTestWitness hΩ (ht n)).weakGrad_memLp.sub hw.weakGrad_memLp)
  exact (smoothTestGraph hΩ).isClosed_topologicalClosure.mem_of_tendsto
    (hF.prodMk_nhds hG) (Eventually.of_forall fun n =>
      (smoothTestGraph hΩ).le_topologicalClosure ⟨φ n, ht n, rfl⟩)

private theorem memW01p_of_mem_smoothTestGraph_closure (hΩ : IsOpen Ω)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) {G : Y}
    (hG : (hf.toLp f, G) ∈ (smoothTestGraph hΩ).topologicalClosure) :
    DeGiorgi.MemW01p 2 f Ω ∧
      ∀ i, DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) f Ω := by
  change (hf.toLp f, G) ∈ closure (smoothTestGraph hΩ : Set (X × Y)) at hG
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp hG
  choose φ hφ heq using hw
  have hF : Tendsto (fun n => DeGiorgi.smoothFunToLp hΩ (hφ n)) atTop
      (𝓝 (hf.toLp f)) := by
    exact Tendsto.congr' (Eventually.of_forall fun n => congrArg Prod.fst (heq n))
      ((continuous_fst.tendsto (hf.toLp f, G)).comp hlim)
  have hV : Tendsto (fun n => DeGiorgi.smoothGradToLp hΩ (hφ n)) atTop
      (𝓝 G) := by
    exact Tendsto.congr' (Eventually.of_forall fun n => congrArg Prod.snd (heq n))
      ((continuous_snd.tendsto (hf.toLp f, G)).comp hlim)
  have hfun : Tendsto (fun n => eLpNorm (fun x => φ n x - f x) 2
      (volume.restrict Ω)) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n =>
      (DeGiorgi.smoothTestWitness hΩ (hφ n)).memLp) (f_lim_ℒp := hf)).mp hF
  have hgrad : Tendsto (fun n => eLpNorm (fun x =>
      DeGiorgi.smoothGradField (φ n) x - G x) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n =>
      (DeGiorgi.smoothTestWitness hΩ (hφ n)).weakGrad_memLp)
      (f_lim_ℒp := Lp.memLp G)).mp
    simpa only [Lp.toLp_coeFn, DeGiorgi.smoothGradToLp, DeGiorgi.gradLpOfWitness] using hV
  have hcoord (i : Fin d) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (φ n) x (EuclideanSpace.single i 1) - G x i)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgrad
      (fun _ => zero_le)
    intro n
    apply eLpNorm_mono_ae
    exact Eventually.of_forall fun x => PiLp.norm_apply_le
      (DeGiorgi.smoothGradField (φ n) x - G x) i
  have hweak (i : Fin d) : DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) f Ω := by
    apply hasWeakPartialDeriv_of_tendsto_eLpNorm (by norm_num) i
      (fun n => (DeGiorgi.smoothTestWitness hΩ (hφ n)).memLp)
      (fun n => (DeGiorgi.smoothTestWitness hΩ (hφ n)).weakGrad_component_memLp i)
      hf ((Lp.memLp G).eval_piLp i)
      (fun n => (DeGiorgi.smoothTestWitness hΩ (hφ n)).isWeakGrad i) hfun
    exact hcoord i
  let hwf : DeGiorgi.MemW1pWitness 2 f Ω :=
    { memLp := hf
      weakGrad := G
      weakGrad_component_memLp := fun i => (Lp.memLp G).eval_piLp i
      isWeakGrad := hweak }
  exact ⟨⟨hwf.memW1p, hwf, φ, fun n => (hφ n).1,
    fun n => (hφ n).2.1, fun n => (hφ n).2.2, hfun, hcoord⟩, hweak⟩

omit [NeZero d] in
private theorem tendsto_weak_prod_of_tendsto_inner
    {A : Type*} {l : Filter A} {U : A → X} {V : A → Y} {u : X} {v : Y}
    (hU : Tendsto U l (𝓝 u))
    (hV : ∀ z, Tendsto (fun a => inner ℝ (V a) z) l (𝓝 (inner ℝ v z))) :
    Tendsto (fun a => toWeakSpace ℝ (X × Y) (U a, V a)) l
      (𝓝 (toWeakSpace ℝ (X × Y) (u, v))) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _
    (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℝ (X × Y)))).mpr
  intro F
  change Tendsto (fun a => F (U a, V a)) l (𝓝 (F (u, v)))
  let F₁ : X →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ X Y)
  let F₂ : Y →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inr ℝ X Y)
  have hF₂ (w : Y) : F₂ w = inner ℝ w ((_root_.InnerProductSpace.toDual ℝ Y).symm F₂) := by
    rw [real_inner_comm, _root_.InnerProductSpace.toDual_symm_apply]
  have h₂ : Tendsto (fun a => F₂ (V a)) l (𝓝 (F₂ v)) := by
    simpa only [hF₂] using hV ((_root_.InnerProductSpace.toDual ℝ Y).symm F₂)
  have hsplit (x : X) (y : Y) : F (x, y) = F₁ x + F₂ y := by
    change F (x, y) = F (x, 0) + F (0, y)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simpa only [hsplit, Function.comp_apply] using ((F₁.continuous.tendsto u).comp hU).add h₂

theorem exists_weakly_convergent_gradients_of_tendsto_L2
    (hΩ : IsOpen Ω) {f : ℕ → E → ℝ} {v : E → ℝ}
    (hf : ∀ n, DeGiorgi.MemW01p 2 (f n) Ω)
    (hv : MemLp v 2 (volume.restrict Ω)) {C : ℝ}
    (hbound : ∀ n, ‖DeGiorgi.gradLpOfWitness (Classical.choose (hf n).2)‖ ≤ C)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - v x) 2
      (volume.restrict Ω)) atTop (𝓝 0)) :
    DeGiorgi.MemW01p 2 v Ω ∧
    ∃ (σ : ℕ → ℕ) (G : Y), StrictMono σ ∧ ‖G‖ ≤ C ∧
      (∀ z, Tendsto (fun n => inner ℝ
        (DeGiorgi.gradLpOfWitness (Classical.choose (hf (σ n)).2)) z)
        atTop (𝓝 (inner ℝ G z))) ∧
      ∀ i, DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) v Ω := by
  let _ : IsSeparable (volume.restrict Ω) := inferInstance
  let _ : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let _ : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let _ : SecondCountableTopology Y := Lp.SecondCountableTopology
  let _ : TopologicalSpace.SeparableSpace Y :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  let U : ℕ → X := fun n => (hf n).1.1.toLp (f n)
  let V : ℕ → Y := fun n => DeGiorgi.gradLpOfWitness (Classical.choose (hf n).2)
  obtain ⟨σ, G, hσ, hG⟩ :=
    Analysis.InnerProductSpace.exists_weakly_convergent_subsequence_of_norm_bounded V hbound
  have hU : Tendsto U atTop (𝓝 (hv.toLp v)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n => (hf n).1.1)
      (f_lim_ℒp := hv)).mpr hlim
  have hclosed : IsClosed ((toWeakSpace ℝ (X × Y)) ''
      ((smoothTestGraph hΩ).topologicalClosure : Set (X × Y))) := by
    rw [← closure_eq_iff_isClosed]
    rw [← (smoothTestGraph hΩ).topologicalClosure.convex.toWeakSpace_closure ℝ,
      (smoothTestGraph hΩ).isClosed_topologicalClosure.closure_eq]
  have hmem := hclosed.mem_of_tendsto
    (tendsto_weak_prod_of_tendsto_inner (hU.comp hσ.tendsto_atTop) hG)
    (Eventually.of_forall fun n => ⟨(U (σ n), V (σ n)),
      mem_smoothTestGraph_closure hΩ (hf (σ n)), rfl⟩)
  obtain ⟨w, hw, heq⟩ := hmem
  have heqw : w = (hv.toLp v, G) := (toWeakSpace ℝ (X × Y)).injective heq
  subst w
  obtain ⟨hv0, hvG⟩ := memW01p_of_mem_smoothTestGraph_closure hΩ hv hw
  have hGC : ‖G‖ ≤ C := by
    have hvv : inner ℝ G G ≤ C * ‖G‖ := le_of_tendsto (hG G) (Eventually.of_forall fun n =>
      (real_inner_le_norm (V (σ n)) G).trans
        (mul_le_mul_of_nonneg_right (hbound (σ n)) (norm_nonneg G)))
    rw [real_inner_self_eq_norm_sq] at hvv
    have hC : 0 ≤ C := (norm_nonneg (V 0)).trans (hbound 0)
    nlinarith [norm_nonneg G]
  exact ⟨hv0, σ, G, hσ, hGC, hG, hvG⟩

theorem memW01p_sub_of_tendsto_L2
    {ι : Type*} [Fintype ι] (hΩ : IsOpen Ω)
    {u : ℕ → E → EuclideanSpace ℝ ι} {v b : E → EuclideanSpace ℝ ι}
    (hb : MemLp b 2 (volume.restrict Ω))
    (hv : MemLp v 2 (volume.restrict Ω))
    (hu : ∀ i n, DeGiorgi.MemW01p 2 (fun x => u n x i - b x i) Ω)
    (R : ι → ℝ≥0∞) (hR : ∀ i, R i ≠ ∞)
    (hbound : ∀ i n, ∑ j : Fin d,
      eLpNorm (fun x => (Classical.choose (hu i n).2).weakGrad x j)
        2 (volume.restrict Ω) ≤ R i)
    (hlim : Tendsto (fun n => eLpNorm (fun x => u n x - v x) 2
      (volume.restrict Ω)) atTop (𝓝 0)) :
    ∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω := by
  intro i
  have hvb : MemLp (fun x => v x i - b x i) 2 (volume.restrict Ω) :=
    (hv.eval_piLp i).sub (hb.eval_piLp i)
  have hnorm (n : ℕ) :
      ‖DeGiorgi.gradLpOfWitness (Classical.choose (hu i n).2)‖ ≤ (R i).toReal := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp]
    exact ENNReal.toReal_mono (hR i)
      ((eLpNorm_euclidean_le_sum _ (Classical.choose (hu i n).2).weakGrad_memLp).trans
        (hbound i n))
  have ht : Tendsto (fun n => eLpNorm
      (fun x => (u n x i - b x i) - (v x i - b x i)) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le)
    intro n
    apply eLpNorm_mono_ae
    filter_upwards with x
    have heq : (u n x i - b x i) - (v x i - b x i) = u n x i - v x i := by ring
    rw [heq]
    exact PiLp.norm_apply_le (u n x - v x) i
  exact (exists_weakly_convergent_gradients_of_tendsto_L2 hΩ (hu i) hvb hnorm ht).1

end DifferentialGeometry.Analysis.Sobolev.Euclidean
