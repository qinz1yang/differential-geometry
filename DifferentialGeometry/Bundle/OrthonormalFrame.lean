import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

noncomputable section
open Bundle Filter
open scoped Topology BigOperators InnerProductSpace

variable {B Z : Type*} [TopologicalSpace B] [TopologicalSpace Z]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : B → Type*} [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
variable {b : Z → B} {x₀ : Z} {v w : ∀ z, V (b z)}

omit [IsContinuousRiemannianBundle F V] in
private theorem continuousAt_section_iff_linearMapAt (hb : ContinuousAt b x₀) :
    ContinuousAt (fun z => (⟨b z, v z⟩ : TotalSpace F V)) x₀ ↔
      ContinuousAt (fun z => (trivializationAt F V (b x₀)).linearMapAt ℝ (b z) (v z)) x₀ := by
  rw [FiberBundle.continuousAt_totalSpace]
  simp only [and_iff_right hb]
  apply continuousAt_congr
  filter_upwards [hb.eventually ((trivializationAt F V (b x₀)).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V (b x₀)))] with z hz
  exact ((trivializationAt F V (b x₀)).coe_linearMapAt_of_mem (R := ℝ) hz ▸ rfl)

omit [NormedSpace ℝ F] [∀ x, InnerProductSpace ℝ (V x)]
  [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V] in
private theorem ContinuousAt.base_bundle
    (hv : ContinuousAt (fun z => (⟨b z, v z⟩ : TotalSpace F V)) x₀) : ContinuousAt b x₀ := by
  rw [FiberBundle.continuousAt_totalSpace] at hv
  exact hv.1

private theorem ContinuousAt.norm_bundle
    (hv : ContinuousAt (fun z => (⟨b z, v z⟩ : TotalSpace F V)) x₀) :
    ContinuousAt (fun z => ‖v z‖) x₀ := by
  have h := (hv.inner_bundle hv).sqrt
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using h

omit [IsContinuousRiemannianBundle F V] in
private theorem ContinuousAt.sub_bundle
    (hv : ContinuousAt (fun z => (⟨b z, v z⟩ : TotalSpace F V)) x₀)
    (hw : ContinuousAt (fun z => (⟨b z, w z⟩ : TotalSpace F V)) x₀) :
    ContinuousAt (fun z => (⟨b z, v z - w z⟩ : TotalSpace F V)) x₀ := by
  have hb := hv.base_bundle
  rw [continuousAt_section_iff_linearMapAt hb] at hv hw ⊢
  simpa only [map_sub, Pi.sub_apply] using hv.fun_sub hw

omit [IsContinuousRiemannianBundle F V] in
private theorem ContinuousAt.smul_bundle {c : Z → ℝ}
    (hc : ContinuousAt c x₀)
    (hv : ContinuousAt (fun z => (⟨b z, v z⟩ : TotalSpace F V)) x₀) :
    ContinuousAt (fun z => (⟨b z, c z • v z⟩ : TotalSpace F V)) x₀ := by
  have hb := hv.base_bundle
  rw [continuousAt_section_iff_linearMapAt hb] at hv ⊢
  simpa only [map_smul, Pi.smul_apply] using hc.fun_smul hv

omit [IsContinuousRiemannianBundle F V] in
private theorem ContinuousAt.sum_bundle
    {ι : Type*} {f : ι → ∀ z, V (b z)} (s : Finset ι)
    (hb : ContinuousAt b x₀)
    (hf : ∀ i ∈ s, ContinuousAt (fun z => (⟨b z, f i z⟩ : TotalSpace F V)) x₀) :
    ContinuousAt (fun z => (⟨b z, ∑ i ∈ s, f i z⟩ : TotalSpace F V)) x₀ := by
  rw [continuousAt_section_iff_linearMapAt hb]
  have h := tendsto_finsetSum s (fun i hi =>
    (continuousAt_section_iff_linearMapAt hb).mp (hf i hi))
  simpa only [ContinuousAt, map_sum] using h

theorem continuousAt_gramSchmidt_bundle
    {n : ℕ} {f : Fin n → ∀ z, V (b z)}
    (hf : ∀ i, ContinuousAt (fun z => (⟨b z, f i z⟩ : TotalSpace F V)) x₀)
    (hlin : LinearIndependent ℝ (fun i => f i x₀)) (i : Fin n) :
    ContinuousAt (fun z => (⟨b z, InnerProductSpace.gramSchmidt ℝ (fun j => f j z) i⟩ :
      TotalSpace F V)) x₀ := by
  classical
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    let g : Fin n → ∀ z, V (b z) := fun j z =>
      InnerProductSpace.gramSchmidt ℝ (fun l => f l z) j
    have hcoef (j : Fin n) (hj : j ∈ Finset.Iio i) :
        ContinuousAt (fun z =>
          ⟪g j z, f i z⟫_ℝ / ‖g j z‖ ^ 2) x₀ :=
      ((ih j (Finset.mem_Iio.mp hj)).inner_bundle (hf i)).div
        ((ih j (Finset.mem_Iio.mp hj)).norm_bundle.pow 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero j hlin)))
    have hsum := ContinuousAt.sum_bundle (Finset.Iio i) (hf i).base_bundle
      (fun j hj => (hcoef j hj).smul_bundle (ih j (Finset.mem_Iio.mp hj)))
    have hsub := (hf i).sub_bundle hsum
    convert hsub using 1
    funext z
    congr 1
    exact eq_sub_of_add_eq (InnerProductSpace.gramSchmidt_def'' ℝ (fun j => f j z) i).symm

theorem continuousAt_gramSchmidtNormed_bundle
    {n : ℕ} {f : Fin n → ∀ z, V (b z)}
    (hf : ∀ i, ContinuousAt (fun z => (⟨b z, f i z⟩ : TotalSpace F V)) x₀)
    (hlin : LinearIndependent ℝ (fun i => f i x₀)) (i : Fin n) :
    ContinuousAt (fun z => (⟨b z, InnerProductSpace.gramSchmidtNormed ℝ (fun j => f j z) i⟩ :
      TotalSpace F V)) x₀ := by
  have hg := continuousAt_gramSchmidt_bundle hf hlin i
  exact (hg.norm_bundle.inv₀ (norm_ne_zero_iff.mpr
    (InnerProductSpace.gramSchmidt_ne_zero i hlin))).smul_bundle hg


theorem exists_continuous_orthonormal_sections
    (x₀ : B) {n : ℕ} (v : Fin n → V x₀) (hv : Orthonormal ℝ v) :
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧
      ∃ e : Fin n → ∀ y, V y,
        (∀ i, ContinuousOn (fun y => (⟨y, e i y⟩ : TotalSpace F V)) U) ∧
        (∀ y ∈ U, Orthonormal ℝ (fun i => e i y)) ∧
        ∀ i, e i x₀ = v i := by
  classical
  let t := trivializationAt F V x₀
  have hx : x₀ ∈ t.baseSet := mem_baseSet_trivializationAt F V x₀
  let raw : Fin n → ∀ y, V y := fun i y =>
    t.symmL ℝ y (t.continuousLinearMapAt ℝ x₀ (v i))
  have hraw (i : Fin n) :
      ContinuousOn (fun y => (⟨y, raw i y⟩ : TotalSpace F V)) t.baseSet := by
    have h := t.continuousOn_symm.comp
      (continuousOn_id.prodMk (continuousOn_const (c := t.continuousLinearMapAt ℝ x₀ (v i))))
      (fun y hy => ⟨hy, Set.mem_univ _⟩)
    apply h.congr
    intro y hy
    dsimp only [raw]
    rw [t.symmL_apply hy]
    rfl
  have hlin (y : B) (hy : y ∈ t.baseSet) :
      LinearIndependent ℝ (fun i => raw i y) := by
    let ex := t.continuousLinearEquivAt ℝ x₀ hx
    let ey := t.continuousLinearEquivAt ℝ y hy
    let e := ex.trans ey.symm
    have h := hv.linearIndependent.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    have heq : (fun i => raw i y) = fun i => e (v i) := by
      funext i
      change t.symmL ℝ y (t.continuousLinearMapAt ℝ x₀ (v i)) = ey.symm (ex (v i))
      rw [← t.symm_continuousLinearEquivAt_eq hy, ← t.coe_continuousLinearEquivAt_eq' hx]
      rfl
    rw [heq]
    exact h
  let e : Fin n → ∀ y, V y := fun i y =>
    InnerProductSpace.gramSchmidtNormed ℝ (fun j => raw j y) i
  refine ⟨t.baseSet, t.open_baseSet, hx, e, ?_, ?_, ?_⟩
  · intro i y hy
    exact (continuousAt_gramSchmidtNormed_bundle
      (fun j => (hraw j).continuousAt (t.open_baseSet.mem_nhds hy)) (hlin y hy) i).continuousWithinAt
  · intro y hy
    exact InnerProductSpace.gramSchmidtNormed_orthonormal (hlin y hy)
  · intro i
    have hrawx : (fun j => raw j x₀) = v := by
      funext j
      exact t.symmL_continuousLinearMapAt hx (v j)
    change InnerProductSpace.gramSchmidtNormed ℝ (fun j => raw j x₀) i = v i
    rw [hrawx, InnerProductSpace.gramSchmidtNormed]
    have hgs : InnerProductSpace.gramSchmidt ℝ v = v :=
      InnerProductSpace.gramSchmidt_of_orthogonal ℝ (fun j k hjk => hv.inner_eq_zero hjk)
    simp only [hgs, hv.norm_eq_one, RCLike.ofReal_one, inv_one, one_smul]

end

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {m : ℕ∞ω} [IsContMDiffRiemannianBundle I m F V]
  {x₀ : M}

private theorem ContMDiffAt.norm_bundle {v : ∀ x, V x}
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, F)) m (T% v) x₀) (hne : v x₀ ≠ 0) :
    ContMDiffAt I 𝓘(ℝ, ℝ) m (fun x => ‖v x‖) x₀ := by
  have hi := hv.inner_bundle hv
  have h := (Real.contDiffAt_sqrt (real_inner_self_pos.mpr hne).ne').contMDiffAt.comp x₀ hi
  simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using h

theorem contMDiffAt_gramSchmidt_bundle
    {n : ℕ} {f : Fin n → ∀ x, V x}
    (hf : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, F)) m (T% (f i)) x₀)
    (hlin : LinearIndependent ℝ (fun i => f i x₀)) (i : Fin n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) m
      (fun x => (⟨x, InnerProductSpace.gramSchmidt ℝ (fun j => f j x) i⟩ : TotalSpace F V))
      x₀ := by
  classical
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    let g : Fin n → ∀ x, V x := fun j x =>
      InnerProductSpace.gramSchmidt ℝ (fun l => f l x) j
    have hcoef (j : Fin n) (hj : j ∈ Finset.Iio i) :
        ContMDiffAt I 𝓘(ℝ, ℝ) m
          (fun x => inner ℝ (g j x) (f i x) / ‖g j x‖ ^ 2) x₀ :=
      ((ih j (Finset.mem_Iio.mp hj)).inner_bundle (hf i)).div₀
        (((ih j (Finset.mem_Iio.mp hj)).norm_bundle
          (InnerProductSpace.gramSchmidt_ne_zero j hlin)).pow 2)
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero j hlin)))
    have hsum := ContMDiffAt.sum_section (s := Finset.Iio i)
      (fun j hj => (hcoef j hj).smul_section (ih j (Finset.mem_Iio.mp hj)))
    have hsub := (hf i).sub_section hsum
    convert hsub using 1
    funext x
    congr 1
    exact eq_sub_of_add_eq (InnerProductSpace.gramSchmidt_def'' ℝ (fun j => f j x) i).symm

theorem contMDiffAt_gramSchmidtNormed_bundle
    {n : ℕ} {f : Fin n → ∀ x, V x}
    (hf : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, F)) m (T% (f i)) x₀)
    (hlin : LinearIndependent ℝ (fun i => f i x₀)) (i : Fin n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) m
      (fun x => (⟨x, InnerProductSpace.gramSchmidtNormed ℝ (fun j => f j x) i⟩ :
        TotalSpace F V)) x₀ := by
  have hg := contMDiffAt_gramSchmidt_bundle hf hlin i
  exact ((hg.norm_bundle (InnerProductSpace.gramSchmidt_ne_zero i hlin)).inv₀
    (norm_ne_zero_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero i hlin))).smul_section hg

theorem exists_contMDiff_orthonormal_sections
    [ContMDiffVectorBundle m F V I]
    (x₀ : M) {n : ℕ} (v : Fin n → V x₀) (hv : Orthonormal ℝ v) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ e : Fin n → ∀ y, V y,
        (∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, F)) m (fun y => (⟨y, e i y⟩ : TotalSpace F V)) U) ∧
        (∀ y ∈ U, Orthonormal ℝ (fun i => e i y)) ∧
        ∀ i, e i x₀ = v i := by
  classical
  let t := trivializationAt F V x₀
  have hx : x₀ ∈ t.baseSet := mem_baseSet_trivializationAt F V x₀
  let raw : Fin n → ∀ y, V y := fun i y =>
    t.symmL ℝ y (t.continuousLinearMapAt ℝ x₀ (v i))
  have hraw (i : Fin n) :
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) m (fun y => (⟨y, raw i y⟩ : TotalSpace F V)) t.baseSet := by
    have h := (t.contMDiffOn_symm (IB := I) (n := m)).comp
      (contMDiffOn_id.prodMk (contMDiffOn_const (c := t.continuousLinearMapAt ℝ x₀ (v i))))
      (fun y hy => t.mem_target.mpr hy)
    apply h.congr
    intro y hy
    dsimp only [raw]
    rw [t.symmL_apply hy, t.mk_symm hy]
    rfl
  have hlin (y : M) (hy : y ∈ t.baseSet) :
      LinearIndependent ℝ (fun i => raw i y) := by
    let ex := t.continuousLinearEquivAt ℝ x₀ hx
    let ey := t.continuousLinearEquivAt ℝ y hy
    let e := ex.trans ey.symm
    have h := hv.linearIndependent.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    have heq : (fun i => raw i y) = fun i => e (v i) := by
      funext i
      change t.symmL ℝ y (t.continuousLinearMapAt ℝ x₀ (v i)) = ey.symm (ex (v i))
      rw [← t.symm_continuousLinearEquivAt_eq hy, ← t.coe_continuousLinearEquivAt_eq' hx]
      rfl
    rw [heq]
    exact h
  let e : Fin n → ∀ y, V y := fun i y =>
    InnerProductSpace.gramSchmidtNormed ℝ (fun j => raw j y) i
  refine ⟨t.baseSet, t.open_baseSet, hx, e, ?_, ?_, ?_⟩
  · intro i y hy
    exact (contMDiffAt_gramSchmidtNormed_bundle
      (fun j => (hraw j).contMDiffAt (t.open_baseSet.mem_nhds hy)) (hlin y hy) i).contMDiffWithinAt
  · intro y hy
    exact InnerProductSpace.gramSchmidtNormed_orthonormal (hlin y hy)
  · intro i
    have hrawx : (fun j => raw j x₀) = v := by
      funext j
      exact t.symmL_continuousLinearMapAt hx (v j)
    change InnerProductSpace.gramSchmidtNormed ℝ (fun j => raw j x₀) i = v i
    rw [hrawx, InnerProductSpace.gramSchmidtNormed]
    have hgs : InnerProductSpace.gramSchmidt ℝ v = v :=
      InnerProductSpace.gramSchmidt_of_orthogonal ℝ (fun j k hjk => hv.inner_eq_zero hjk)
    simp only [hgs, hv.norm_eq_one, RCLike.ofReal_one, inv_one, one_smul]

end
