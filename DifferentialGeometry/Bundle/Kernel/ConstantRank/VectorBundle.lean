import DifferentialGeometry.Bundle.Kernel.ConstantRank.LocalFrames
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {X : Type*} {d : ℕ}

abbrev matrixKernelFiber (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) : Type _ :=
  LinearMap.ker (A x).mulVecLin

def matrixKernelInclusion (A : X → Matrix (Fin d) (Fin d) ℝ) (r : ℕ) :
    TotalSpace (Fin (d - r) → ℝ) (matrixKernelFiber A) → X × (Fin d → ℝ) :=
  fun z => (z.proj, z.snd.1)

theorem matrixKernelInclusion_injective
    (A : X → Matrix (Fin d) (Fin d) ℝ) (r : ℕ) :
    Function.Injective (matrixKernelInclusion A r) := by
  rintro ⟨p, v⟩ ⟨q, w⟩ h
  have hp : p = q := congrArg Prod.fst h
  subst q
  have hv : v = w := Subtype.ext (congrArg Prod.snd h)
  subst w
  rfl

private theorem linear_apply_sum_single {k : ℕ} {Y : Type*}
    [AddCommGroup Y] [Module ℝ Y] (T : (Fin k → ℝ) →ₗ[ℝ] Y) (v : Fin k → ℝ) :
    T v = ∑ j, v j • T (Pi.single j 1) := by
  have hv : ∑ j, v j • Pi.single j (1 : ℝ) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    T v = T (∑ j, v j • Pi.single j (1 : ℝ)) := congrArg T hv.symm
    _ = ∑ j, v j • T (Pi.single j 1) := by
      rw [map_sum]
      simp only [map_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  (A : X → Matrix (Fin d) (Fin d) ℝ) (r : ℕ)

local notation "FK" => (Fin (d - r) → ℝ)

private structure KernelCoordinateData (p : X) where
  domain : Set X
  isOpen : IsOpen domain
  mem_domain : p ∈ domain
  G : X → FK →ₗ[ℝ] (Fin d → ℝ)
  Q : (Fin d → ℝ) →ₗ[ℝ] FK
  smooth : ∀ v, ContMDiffOn I 𝓘(ℝ, Fin d → ℝ) ∞ (fun x => G x v) domain
  left_inv : ∀ x ∈ domain, ∀ v, Q (G x v) = v
  range_eq : ∀ x ∈ domain, LinearMap.range (G x) = LinearMap.ker (A x).mulVecLin

private def kernelCoordinateData
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) (p : X) : KernelCoordinateData (I := I) A r p := by
  have h : Nonempty (KernelCoordinateData (I := I) A r p) := by
    obtain ⟨W, G, Q, hW, hp, _hWs, hG, hQ, hRange⟩ :=
      exists_smooth_constant_rank_kernel_coordinates A isOpen_univ p (mem_univ p)
        (fun i j => (hA i j).contMDiffOn) (fun x _ => hr x)
    exact ⟨⟨W, hW, hp, G, Q, hG, hQ, hRange⟩⟩
  exact Classical.choice h

namespace KernelCoordinateData

variable {A r} {p : X} (D : KernelCoordinateData (I := I) A r p)

private def equiv (q : X) (hq : q ∈ D.domain) : FK ≃ₗ[ℝ] matrixKernelFiber A q where
  toFun v := ⟨D.G q v, by rw [← D.range_eq q hq]; exact ⟨v, rfl⟩⟩
  invFun v := D.Q v.1
  left_inv v := D.left_inv q hq v
  right_inv v := by
    apply Subtype.ext
    have hv : v.1 ∈ LinearMap.range (D.G q) := (D.range_eq q hq).ge v.property
    obtain ⟨w, hw⟩ := hv
    change D.G q (D.Q v.1) = v.1
    rw [← hw, D.left_inv q hq]
  map_add' v w := Subtype.ext ((D.G q).map_add v w)
  map_smul' c v := Subtype.ext ((D.G q).map_smul c v)

private theorem equiv_apply (q : X) (hq : q ∈ D.domain) (v : FK) :
    ((D.equiv q hq v) : Fin d → ℝ) = D.G q v := rfl

private theorem equiv_symm_apply (q : X) (hq : q ∈ D.domain)
    (v : matrixKernelFiber A q) : (D.equiv q hq).symm v = D.Q v.1 := rfl

private def pretrivialization :
    Pretrivialization FK (TotalSpace.proj : TotalSpace FK (matrixKernelFiber A) → X) := by
  classical
  refine
    { toFun := fun z => (z.proj, if hq : z.proj ∈ D.domain then
        (D.equiv z.proj hq).symm z.snd else 0)
      invFun := fun z => ⟨z.1, if hq : z.1 ∈ D.domain then D.equiv z.1 hq z.2 else 0⟩
      source := {z | z.proj ∈ D.domain}
      target := D.domain ×ˢ (univ : Set FK)
      baseSet := D.domain
      open_baseSet := D.isOpen
      open_target := D.isOpen.prod isOpen_univ
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl
      map_source' := fun z hz => ⟨hz, mem_univ _⟩
      map_target' := fun z hz => hz.1
      left_inv' := ?_
      right_inv' := ?_ }
  · rintro ⟨q, v⟩ hq
    change q ∈ D.domain at hq
    simp only [dif_pos hq, LinearEquiv.apply_symm_apply]
  · rintro ⟨q, v⟩ ⟨hq, _⟩
    simp only [dif_pos hq, LinearEquiv.symm_apply_apply]

private theorem pretrivialization_apply (q : X) (hq : q ∈ D.domain)
    (v : matrixKernelFiber A q) :
    D.pretrivialization ⟨q, v⟩ = (q, (D.equiv q hq).symm v) := by
  classical
  change (q, if h : q ∈ D.domain then (D.equiv q h).symm v else 0) = _
  rw [dif_pos hq]

private theorem pretrivialization_symm (q : X) (hq : q ∈ D.domain) (v : FK) :
    D.pretrivialization.symm q v = D.equiv q hq v := by
  have h := D.pretrivialization.symm_apply_apply_mk hq (D.equiv q hq v)
  rw [D.pretrivialization_apply q hq, LinearEquiv.symm_apply_apply] at h
  exact h

private theorem pretrivialization_isLinear : D.pretrivialization.IsLinear ℝ := by
  constructor
  intro q hq
  convert! (D.equiv q hq).symm.toLinearMap.isLinear using 1
  funext v
  exact congrArg Prod.snd (D.pretrivialization_apply q hq v)

private def transition {p' : X} (D' : KernelCoordinateData (I := I) A r p')
    (x : X) : FK →L[ℝ] FK :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := FK) (Fin (d - r))).symm
    (fun j => D'.Q (D.G x (Pi.single j 1)))

private theorem transition_apply {p' : X} (D' : KernelCoordinateData (I := I) A r p')
    (x : X) (v : FK) : D.transition D' x v = D'.Q (D.G x v) := by
  change ((LinearEquiv.piRing ℝ FK (Fin (d - r)) ℝ).symm _) v = _
  rw [LinearEquiv.piRing_symm_apply]
  exact (linear_apply_sum_single (D'.Q.comp (D.G x)) v).symm

private theorem transition_contMDiffAt {p' : X}
    (D' : KernelCoordinateData (I := I) A r p') {x : X} (hx : x ∈ D.domain) :
    ContMDiffAt I 𝓘(ℝ, FK →L[ℝ] FK) ∞ (D.transition D') x := by
  have hcols : ContMDiffAt I 𝓘(ℝ, Fin (d - r) → FK) ∞
      (fun y j => D'.Q (D.G y (Pi.single j 1))) x := by
    apply contMDiffAt_pi_space.2
    intro j
    exact D'.Q.toContinuousLinearMap.contMDiff.contMDiffAt.comp x
      ((D.smooth (Pi.single j 1)).contMDiffAt (D.isOpen.mem_nhds hx))
  exact (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := FK)
    (Fin (d - r))).symm.toContinuousLinearMap.contMDiff.contMDiffAt.comp x hcols

private theorem transition_eq_coordChange {p' : X}
    (D' : KernelCoordinateData (I := I) A r p')
    (q : X) (hq : q ∈ D.domain) (hq' : q ∈ D'.domain) (v : FK) :
    D.transition D' q v = (D'.pretrivialization ⟨q, D.pretrivialization.symm q v⟩).2 := by
  rw [D.pretrivialization_symm q hq, D'.pretrivialization_apply q hq',
    D'.equiv_symm_apply q hq', D.equiv_apply q hq, D.transition_apply]

private theorem totalSpaceMk_isInducing :
    _root_.Topology.IsInducing
      (D.pretrivialization ∘ (TotalSpace.mk p : matrixKernelFiber A p →
        TotalSpace FK (matrixKernelFiber A))) := by
  have h := (D.equiv p D.mem_domain).symm.toContinuousLinearEquiv.toHomeomorph.isInducing
  have hp := (_root_.Topology.isInducing_const_prod (x := p)).mpr h
  convert! hp using 1
  funext v
  exact D.pretrivialization_apply p D.mem_domain v

end KernelCoordinateData

def constantRankKernelPrebundle
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    VectorPrebundle ℝ FK (matrixKernelFiber A) := by
  let D := kernelCoordinateData A r hA hr
  refine
    { pretrivializationAtlas := Set.range (fun p : X => (D p).pretrivialization)
      pretrivializationAt := fun p => (D p).pretrivialization
      mem_base_pretrivializationAt := fun p => (D p).mem_domain
      pretrivialization_mem_atlas := fun p => ⟨p, rfl⟩
      pretrivialization_linear' := ?_
      exists_coordChange := ?_
      totalSpaceMk_isInducing := fun p => (D p).totalSpaceMk_isInducing }
  · rintro _ ⟨p, rfl⟩
    exact (D p).pretrivialization_isLinear
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
    refine ⟨(D p).transition (D p'), ?_, ?_⟩
    · intro q hq
      exact ((D p).transition_contMDiffAt (D p') hq.1).continuousAt.continuousWithinAt
    · intro q hq v
      exact (D p).transition_eq_coordChange (D p') q hq.1 hq.2 v

theorem constantRankKernel_isContMDiff
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    let a := constantRankKernelPrebundle A r hA hr
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiffVectorBundle ∞ FK (matrixKernelFiber A) I := by
  let a := constantRankKernelPrebundle A r hA hr
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  have ha : a.IsContMDiff I ∞ := by
    constructor
    rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
    let D := kernelCoordinateData A r hA hr
    refine ⟨(D p).transition (D p'), ?_, ?_⟩
    · intro q hq
      exact ((D p).transition_contMDiffAt (D p') hq.1).contMDiffWithinAt
    · intro q hq v
      exact (D p).transition_eq_coordChange (D p') q hq.1 hq.2 v
  let _ := ha
  exact a.contMDiffVectorBundle I

variable [IsManifold I ∞ X]

omit [IsManifold I ∞ X] in theorem matrixKernelInclusion_contMDiff
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    let a := constantRankKernelPrebundle A r hA hr
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiff (I.prod 𝓘(ℝ, FK)) (I.prod 𝓘(ℝ, Fin d → ℝ)) ∞
      (matrixKernelInclusion A r) := by
  classical
  let a := constantRankKernelPrebundle A r hA hr
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := constantRankKernel_isContMDiff A r hA hr
  let IK := I.prod 𝓘(ℝ, FK)
  have hb : ContMDiff IK I ∞ (TotalSpace.proj : TotalSpace FK (matrixKernelFiber A) → X) :=
    Bundle.contMDiff_proj (matrixKernelFiber A)
  change ContMDiff IK (I.prod 𝓘(ℝ, Fin d → ℝ)) ∞ (matrixKernelInclusion A r)
  intro z
  let D := kernelCoordinateData A r hA hr z.proj
  let e := trivializationAt FK (matrixKernelFiber A) z.proj
  have hc : ContMDiffAt IK 𝓘(ℝ, FK) ∞ (fun y => (e y).2) z :=
    (Bundle.contMDiffAt_totalSpace.mp (contMDiffAt_id (I := IK))).2
  have hcol (j : Fin (d - r)) : ContMDiffAt IK 𝓘(ℝ, Fin d → ℝ) ∞
      (fun y : TotalSpace FK (matrixKernelFiber A) => D.G y.proj (Pi.single j 1)) z :=
    ((D.smooth (Pi.single j 1)).contMDiffAt (D.isOpen.mem_nhds D.mem_domain)).comp z (hb z)
  have hsum : ContMDiffAt IK 𝓘(ℝ, Fin d → ℝ) ∞
      (fun y : TotalSpace FK (matrixKernelFiber A) =>
        ∑ j, (e y).2 j • D.G y.proj (Pi.single j 1)) z := by
    exact ContMDiffAt.sum fun j _ => (contMDiffAt_pi_space.mp hc j).smul (hcol j)
  change ContMDiffAt IK (I.prod 𝓘(ℝ, Fin d → ℝ)) ∞
    (fun y : TotalSpace FK (matrixKernelFiber A) => (y.proj, y.snd.1)) z
  refine (hb z).prodMk (hsum.congr_of_eventuallyEq ?_)
  have hD : ∀ᶠ y in 𝓝 z, y.proj ∈ D.domain :=
    (hb z).continuousAt (D.isOpen.mem_nhds D.mem_domain)
  filter_upwards [hD] with y hy
  have he : (e y).2 = (D.equiv y.proj hy).symm y.snd :=
    congrArg Prod.snd (D.pretrivialization_apply y.proj hy y.snd)
  have hv : D.G y.proj (e y).2 = y.snd.1 := by
    rw [he, ← D.equiv_apply y.proj hy]
    exact congrArg Subtype.val ((D.equiv y.proj hy).apply_symm_apply y.snd)
  rw [← hv]
  exact linear_apply_sum_single (D.G y.proj) (e y).2

omit [IsManifold I ∞ X] in theorem matrixKernelInclusion_isEmbedding
    (hA : ∀ i j : Fin d, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A x i j))
    (hr : ∀ x, (A x).rank = r) :
    let a := constantRankKernelPrebundle A r hA hr
    let _ := a.totalSpaceTopology
    _root_.Topology.IsEmbedding (matrixKernelInclusion A r) := by
  classical
  let a := constantRankKernelPrebundle A r hA hr
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := constantRankKernel_isContMDiff A r hA hr
  let inc := matrixKernelInclusion A r
  have hi : Continuous inc := (matrixKernelInclusion_contMDiff A r hA hr).continuous
  have hlift (f : Set.range inc → TotalSpace FK (matrixKernelFiber A))
      (x : Set.range inc) (hf : ContinuousAt (inc ∘ f) x) : ContinuousAt f x := by
    have hb : ContinuousAt (fun y => (f y).proj) x := continuous_fst.continuousAt.comp hf
    have hv : ContinuousAt (fun y => (f y).snd.1) x := continuous_snd.continuousAt.comp hf
    let D := kernelCoordinateData A r hA hr (f x).proj
    have hcoords : ContinuousAt (fun y => D.Q (f y).snd.1) x :=
      D.Q.toContinuousLinearMap.continuous.continuousAt.comp hv
    apply (FiberBundle.continuousAt_totalSpace FK f).mpr
    refine ⟨hb, hcoords.congr_of_eventuallyEq ?_⟩
    have hD : ∀ᶠ y in 𝓝 x, (f y).proj ∈ D.domain :=
      hb (D.isOpen.mem_nhds D.mem_domain)
    filter_upwards [hD] with y hy
    change (D.pretrivialization (f y)).2 = _
    rw [D.pretrivialization_apply (f y).proj hy, D.equiv_symm_apply (f y).proj hy]
  let e := Equiv.ofInjective inc (matrixKernelInclusion_injective A r)
  have he : Continuous e := hi.subtype_mk _
  have he' : Continuous e.symm := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply hlift e.symm x
    change ContinuousAt (inc ∘ (Equiv.ofInjective inc
      (matrixKernelInclusion_injective A r)).symm) x
    rw [Equiv.self_comp_ofInjective_symm]
    exact continuous_subtype_val.continuousAt
  let h : TotalSpace FK (matrixKernelFiber A) ≃ₜ Set.range inc :=
    { e with continuous_toFun := he, continuous_invFun := he' }
  exact _root_.Topology.IsEmbedding.subtypeVal.comp h.isEmbedding

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
