import DifferentialGeometry.Topology.Attachment.Defs
import DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace DifferentialGeometry.Topology.Handle

open scoped Manifold Topology

noncomputable section

universe u v w

@[reducible]
noncomputable def chartedSpaceOfHomeomorph {H : Type u} [TopologicalSpace H]
    {M : Type v} [TopologicalSpace M] {M' : Type w} [TopologicalSpace M']
    (h : M' ≃ₜ M) [ChartedSpace H M] : ChartedSpace H M' where
  atlas := {e : OpenPartialHomeomorph M' H | ∃ e₀ : OpenPartialHomeomorph M H,
    e₀ ∈ ChartedSpace.atlas (H := H) (M := M) ∧ e = h.toOpenPartialHomeomorph ≫ₕ e₀}
  chartAt := fun x : M' => h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := M) (h x))
  mem_chart_source := by
    intro x
    have hx : h x ∈ (chartAt (H := H) (M := M) (h x)).source :=
      mem_chart_source (H := H) (M := M) (h x)
    dsimp
    constructor
    · trivial
    · exact hx
  chart_mem_atlas := by
    intro x
    exact ⟨(chartAt (H := H) (M := M) (h x)), chart_mem_atlas (H := H) (M := M) (h x), rfl⟩

theorem isManifoldOfHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} {M' : Type*} [TopologicalSpace M'] (h : M' ≃ₜ M)
    [IsManifold I n M] :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (chartedSpaceOfHomeomorph h) := by
  classical
  letI : ChartedSpace H M' := chartedSpaceOfHomeomorph h
  have hmid : h.toOpenPartialHomeomorph.symm ≫ₕ h.toOpenPartialHomeomorph =
      (OpenPartialHomeomorph.refl M : OpenPartialHomeomorph M M) := by
    apply OpenPartialHomeomorph.ext
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · ext x
      simp
  have hgr : HasGroupoid M' (contDiffGroupoid n I) := by
    refine hasGroupoid_of_pregroupoid (contDiffPregroupoid n I) ?_
    intro e e' he he'
    rcases he with ⟨e₁, he₁, rfl⟩
    rcases he' with ⟨e₂, he₂, rfl⟩
    have htrans : (h.toOpenPartialHomeomorph ≫ₕ e₁).symm ≫ₕ (h.toOpenPartialHomeomorph ≫ₕ e₂) =
        e₁.symm ≫ₕ e₂ := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      rw [OpenPartialHomeomorph.trans_assoc]
      rw [← OpenPartialHomeomorph.trans_assoc (e'' := e₂)]
      rw [hmid]
      simp
    rw [htrans]
    have hmem : e₁.symm ≫ₕ e₂ ∈ contDiffGroupoid n I :=
      (inferInstance : HasGroupoid M (contDiffGroupoid n I)).compatible he₁ he₂
    have hm : e₁.symm ≫ₕ e₂ ∈ Pregroupoid.groupoid (contDiffPregroupoid n I) := by
      simpa [contDiffGroupoid] using hmem
    exact (mem_groupoid_of_pregroupoid.mp hm).1
  change IsManifold I n M'
  exact { toHasGroupoid := hgr }

theorem contMDiff_homeomorph_of_chartedSpaceOfHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {X' : Type*} [TopologicalSpace X']
    (h : X' ≃ₜ X) (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n X] :
    @ContMDiff 𝕜 _ E _ _ H _ I X' _ (chartedSpaceOfHomeomorph h) E _ _ H _ I X _ _ n h := by
  classical
  letI : ChartedSpace H X' := chartedSpaceOfHomeomorph h
  letI : IsManifold I n X' := isManifoldOfHomeomorph I h
  intro x
  have hchart : chartAt (H := H) (M := X') x =
      h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := X) (h x)) := rfl
  let c : OpenPartialHomeomorph X' H := chartAt (H := H) (M := X') x
  let c0 : OpenPartialHomeomorph X H := chartAt (H := H) (M := X) (h x)
  have hsource : c.source = h.toOpenPartialHomeomorph ⁻¹' c0.source := by
    change (chartAt (H := H) (M := X') x).source =
      h.toOpenPartialHomeomorph ⁻¹' c0.source
    rw [hchart]
    simp [c0]
  have hcomp : ContMDiffOn I I n (fun y : X' => c0.symm (c y)) c.source := by
    have hf : ContMDiffOn I I n c c.source :=
      contMDiffOn_chart (I := I) (H := H) (M := X') (n := n) (x := x)
    have hg : ContMDiffOn I I n c0.symm c0.target :=
      contMDiffOn_chart_symm (I := I) (H := H) (M := X) (n := n) (x := h x)
    refine hg.comp hf ?_
    intro y hy
    have hy' : h y ∈ c0.source := by
      rw [hsource] at hy
      exact hy
    have hyc : c y = c0 (h y) := by
      change (chartAt (H := H) (M := X') x) y = c0 (h y)
      rw [hchart]
      rfl
    simpa [hyc] using c0.mapsTo hy'
  have heq : ∀ y ∈ c.source, h y = c0.symm (c y) := by
    intro y hy
    have hy' : h y ∈ c0.source := by
      rw [hsource] at hy
      exact hy
    have hyc : c y = c0 (h y) := by
      change (chartAt (H := H) (M := X') x) y = c0 (h y)
      rw [hchart]
      rfl
    calc
      h y = c0.symm (c0 (h y)) := (c0.left_inv hy').symm
      _ = c0.symm (c y) := by rw [hyc]
  have hmd : ContMDiffOn I I n h c.source := hcomp.congr (by intro y hy; exact heq y hy)
  exact hmd.contMDiffAt (c.open_source.mem_nhds (mem_chart_source (H := H) (M := X') x))

theorem contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph {𝕜 : Type*}
    [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {X' : Type*} [TopologicalSpace X']
    (h : X' ≃ₜ X) (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n X] :
    @ContMDiff 𝕜 _ E _ _ H _ I X _ _ E _ _ H _ I X' _ (chartedSpaceOfHomeomorph h) n h.symm := by
  classical
  letI : ChartedSpace H X' := chartedSpaceOfHomeomorph h
  letI : IsManifold I n X' := isManifoldOfHomeomorph I h
  intro y
  have hchart : chartAt (H := H) (M := X') (h.symm y) =
      h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := X) y) := by
    change h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := X) (h (h.symm y))) =
      h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := X) y)
    exact congrArg (fun z : X => h.toOpenPartialHomeomorph ≫ₕ (chartAt (H := H) (M := X) z))
      (h.right_inv y)
  let c : OpenPartialHomeomorph X' H := chartAt (H := H) (M := X') (h.symm y)
  let c0 : OpenPartialHomeomorph X H := chartAt (H := H) (M := X) y
  have htarget : c.target = c0.target := by
    change (chartAt (H := H) (M := X') (h.symm y)).target = c0.target
    rw [hchart, OpenPartialHomeomorph.trans_target]
    simp [c0]
  have hcomp : ContMDiffOn I I n (fun z : X => c.symm (c0 z)) c0.source := by
    have hf : ContMDiffOn I I n c0 c0.source :=
      contMDiffOn_chart (I := I) (H := H) (M := X) (n := n) (x := y)
    have hg : ContMDiffOn I I n c.symm c.target :=
      contMDiffOn_chart_symm (I := I) (H := H) (M := X') (n := n) (x := h.symm y)
    refine hg.comp hf ?_
    intro z hz
    rw [htarget]
    exact c0.mapsTo hz
  have heq : ∀ z ∈ c0.source, h.symm z = c.symm (c0 z) := by
    intro z hz
    have hmem : h.symm z ∈ c.source := by
      change h.symm z ∈ (chartAt (H := H) (M := X') (h.symm y)).source
      rw [hchart, OpenPartialHomeomorph.trans_source]
      constructor
      · trivial
      · change h (h.symm z) ∈ (chartAt (H := H) (M := X) y).source
        simpa [h.right_inv z] using hz
    have hc : c (h.symm z) = c0 z := by
      change (chartAt (H := H) (M := X') (h.symm y)) (h.symm z) = c0 z
      rw [hchart]
      change (chartAt (H := H) (M := X) y) (h (h.symm z)) = c0 z
      simp [c0]
    calc
      h.symm z = c.symm (c (h.symm z)) := (c.left_inv hmem).symm
      _ = c.symm (c0 z) := by rw [hc]
  have hmd : ContMDiffOn I I n h.symm c0.source := hcomp.congr (by intro z hz; exact heq z hz)
  exact hmd.contMDiffAt (c0.open_source.mem_nhds (mem_chart_source (H := H) (M := X) y))

theorem contMDiff_of_contMDiff_comp_homeo {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {X' : Type*} [TopologicalSpace X']
    {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    (h : X' ≃ₜ X) (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) [IsManifold I n X]
    (f : M → X') (hf : ContMDiff I' I n (fun m : M => h (f m))) :
    @ContMDiff 𝕜 _ E' _ _ H' _ I' M _ _ E _ _ H _ I X' _ (chartedSpaceOfHomeomorph h) n f := by
  classical
  letI : ChartedSpace H X' := chartedSpaceOfHomeomorph h
  letI : IsManifold I n X' := isManifoldOfHomeomorph I h
  have hsymm : ContMDiff I I n (h.symm) :=
    contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph (𝕜 := 𝕜) h I n
  have hfun : f = fun m : M => h.symm (h (f m)) := by
    funext m
    exact (h.left_inv (f m)).symm
  rw [hfun]
  exact hsymm.comp hf

noncomputable def closedCellPermute {n : ℕ} (e : Fin n ≃ Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).reindex e |>.repr

theorem closedCellPermute_apply {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : closedCellPermute e x j = x (e.symm j) := by
  change ((EuclideanSpace.basisFun (Fin n) ℝ).reindex e).repr x j = x (e.symm j)
  rw [OrthonormalBasis.repr_apply_apply]
  rw [OrthonormalBasis.reindex_apply]
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x (e.symm j)

theorem closedCellPermute_norm {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖closedCellPermute e x‖ = ‖x‖ := by
  exact (closedCellPermute e).norm_map x

theorem closedCellPermute_zero {n : ℕ} (e : Fin n ≃ Fin n) :
    closedCellPermute e 0 = 0 := by
  ext j
  simp

theorem closedCellPermute_inv {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    closedCellPermute e.symm (closedCellPermute e x) = x := by
  ext j
  rw [closedCellPermute_apply, closedCellPermute_apply]
  simp

theorem closedCellPermute_inv' {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    closedCellPermute e (closedCellPermute e.symm x) = x := by
  simpa [Equiv.symm_symm] using closedCellPermute_inv e.symm x

theorem closedCellPermute_coord_ne_zero {n : ℕ} (e : Fin (n + 1) ≃ Fin (n + 1))
    {s : ℝ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : 0 < s * (closedCellPermute e x) (0)) :
    (closedCellPermute e x) (0) ≠ 0 := by
  intro h0
  rw [h0] at hx
  have : s * 0 = (0 : ℝ) := by ring
  rw [this] at hx
  norm_num at hx

theorem closedCellCoord_norm_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x (0)‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le x (0)

theorem closedCellPermute_symm_eq {n : ℕ} (e : Fin n ≃ Fin n) :
    (closedCellPermute e).symm = closedCellPermute e.symm := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (closedCellPermute e).injective
  calc
    (closedCellPermute e) ((closedCellPermute e).symm x) = x :=
      (closedCellPermute e).apply_symm_apply x
    _ = (closedCellPermute e) (closedCellPermute e.symm x) :=
      by simpa using (closedCellPermute_inv e.symm x).symm

theorem closedCellPermute_symm_apply {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : (closedCellPermute e).symm x j = x (e j) := by
  rw [closedCellPermute_symm_eq e]
  rw [closedCellPermute_apply]
  simp [Equiv.symm_symm]

theorem closedCellPermute_swap_zero {n : ℕ} [NeZero n] (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    closedCellPermute (Equiv.swap i ⟨0, NeZero.pos n⟩) x ⟨0, NeZero.pos n⟩ = x i := by
  rw [closedCellPermute_apply]
  change x ((Equiv.swap i ⟨0, NeZero.pos n⟩).symm ⟨0, NeZero.pos n⟩) = x i
  rw [Equiv.symm_swap]
  simp

noncomputable def closedCellTail (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n => x (Fin.succ j)

theorem closedCellTail_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    closedCellTail n x j = x (Fin.succ j) := rfl

noncomputable def closedCellModelTail (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n => y (Fin.succ j)

theorem closedCellModelTail_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    closedCellModelTail n y j = y (Fin.succ j) := rfl

theorem closedCellTail_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖closedCellTail n x‖ ^ 2 = ∑ j : Fin n, (x (Fin.succ j)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [closedCellTail]

noncomputable def closedCellCons (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) => Fin.cases t (fun j' : Fin n => v j') j)

theorem closedCellCons_apply_zero (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    closedCellCons n t v (0) = t := by
  simp [closedCellCons]

theorem closedCellCons_apply_succ (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : closedCellCons n t v (Fin.succ j) = v j := by
  simp [closedCellCons]

theorem closedCellCons_norm_sq (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖closedCellCons n t v‖ ^ 2 = t ^ 2 + ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [closedCellCons, Fin.cases_zero, Fin.cases_succ]
  rw [EuclideanSpace.real_norm_sq_eq]

theorem closedCellCons_tail (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    closedCellTail n (closedCellCons n t v) = v := by
  ext j
  rw [closedCellTail_apply, closedCellCons_apply_succ]

theorem closedCellCons_eq_cons (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    closedCellCons n t v = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp v)) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [closedCellCons]
  | succ j' => simp [closedCellCons]

def closedCellSign (σ : Bool) : ℝ := if σ then 1 else -1

theorem closedCellSign_ne_zero (σ : Bool) : closedCellSign σ ≠ 0 := by
  cases σ <;> norm_num [closedCellSign]

theorem closedCellSign_sq (σ : Bool) : closedCellSign σ ^ 2 = 1 := by
  cases σ <;> norm_num [closedCellSign, pow_two]

theorem closedCellSign_mul_self (σ : Bool) : closedCellSign σ * closedCellSign σ = 1 := by
  cases σ <;> norm_num [closedCellSign]

noncomputable def closedCellShiftSucc (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) =>
    if _ : j = (0) then x (0) + c else x j)

theorem closedCellShiftSucc_apply_zero (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n c x (0) = x (0) + c := by
  simp [closedCellShiftSucc]

theorem closedCellShiftSucc_apply_succ (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin n) : closedCellShiftSucc n c x (Fin.succ j) = x (Fin.succ j) := by
  simp [closedCellShiftSucc, Fin.succ_ne_zero]

theorem closedCellShiftSucc_apply_of_ne {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    {j : Fin (n + 1)} (hj : j ≠ (0)) :
    closedCellShiftSucc n c x j = x j := by
  dsimp [closedCellShiftSucc]
  change (if _ : j = (0) then x (0) + c else x j) = x j
  exact dif_neg hj

theorem closedCellShiftSucc_eq_add {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n c x = x + c • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ
      (0)) := by
  ext j
  by_cases hj : j = (0)
  · subst j
    rw [closedCellShiftSucc_apply_zero]
    simp [EuclideanSpace.basisFun_apply]
  · have hj' : j ≠ (0) := hj
    rw [closedCellShiftSucc_apply_of_ne c x hj']
    change x j = x j + c * ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0)) j)
    rw [EuclideanSpace.basisFun_apply, PiLp.single_apply]
    rw [if_neg hj']
    ring

theorem closedCellShiftSucc_neg (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n (-c) (closedCellShiftSucc n c x) = x := by
  ext j
  by_cases hj : j = (0)
  · subst j
    rw [closedCellShiftSucc_apply_zero, closedCellShiftSucc_apply_zero]
    ring
  · have hnot : j ≠ (0) := hj
    rw [closedCellShiftSucc_apply_of_ne (-c) (closedCellShiftSucc n c x) hnot]
    exact closedCellShiftSucc_apply_of_ne c x hnot

theorem closedCellShiftSucc_neg' (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n c (closedCellShiftSucc n (-c) x) = x := by
  ext j
  by_cases hj : j = (0)
  · subst j
    rw [closedCellShiftSucc_apply_zero, closedCellShiftSucc_apply_zero]
    ring
  · have hnot : j ≠ (0) := hj
    rw [closedCellShiftSucc_apply_of_ne c (closedCellShiftSucc n (-c) x) hnot]
    exact closedCellShiftSucc_apply_of_ne (-c) x hnot

noncomputable def closedCellProject {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ClosedCell n :=
  if h : ‖x‖ ≤ 1 then ⟨x, h⟩ else ⟨(1 / ‖x‖) • x, by
    have hxpos : 0 < ‖x‖ := lt_of_not_ge (fun hle0 : ‖x‖ ≤ 0 => h (le_trans hle0 (by norm_num)))
    have hnorm : ‖(1 / ‖x‖) • x‖ = 1 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hxpos))]
      rw [div_eq_mul_inv]
      rw [one_mul]
      exact inv_mul_cancel₀ (ne_of_gt hxpos)
    rw [hnorm]⟩

theorem closedCellProject_of_mem {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    closedCellProject x = ⟨x, hx⟩ := by
  simp [closedCellProject, hx]

noncomputable def closedCellInteriorChartValue (n : ℕ) (x : ClosedCell (n + 1)) :
    EuclideanHalfSpace (n + 1) :=
  ⟨closedCellShiftSucc n 1 x.1, by
    rw [closedCellShiftSucc_apply_zero]
    have hle : ‖x.1 (0)‖ ≤ 1 :=
      le_trans (PiLp.norm_apply_le x.1 (0)) (by
        change ‖x.1‖ ≤ 1
        exact x.2)
    have hlt : -1 ≤ x.1 (0) := (abs_le.mp (by simpa using hle)).1
    linarith⟩

theorem closedCellInteriorChartValue_coe (n : ℕ) (x : ClosedCell (n + 1)) :
    (closedCellInteriorChartValue n x).1 =
      closedCellShiftSucc n 1 x.1 := rfl

theorem closedCellSplit_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = (x (0)) ^ 2 + ‖closedCellTail n x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have htail : ‖closedCellTail n x‖ ^ 2 = ∑ j : Fin n, (x (Fin.succ j)) ^ 2 := by
    simpa [closedCellTail] using (EuclideanSpace.real_norm_sq_eq (closedCellTail n x))
  rw [htail]

theorem closedCellSign_mul_abs {σ : Bool} {a : ℝ} (h : 0 < closedCellSign σ * a) :
    closedCellSign σ * |a| = a := by
  cases σ with
  | true =>
      have ha : 0 < a := by simpa [closedCellSign] using h
      have hsign : closedCellSign true = (1 : ℝ) := rfl
      rw [hsign, abs_of_pos ha, one_mul]
  | false =>
      have hneg : 0 < -a := by simpa [closedCellSign] using h
      have ha : a < 0 := by linarith
      have hsign : closedCellSign false = (-1 : ℝ) := rfl
      rw [hsign, abs_of_neg ha]
      ring

noncomputable def closedCellInteriorChart (n : ℕ) :
    OpenPartialHomeomorph (ClosedCell (n + 1)) (EuclideanHalfSpace (n + 1)) where
  source := {x : ClosedCell (n + 1) | ‖x.1‖ < 1}
  target := {y : EuclideanHalfSpace (n + 1) | ‖closedCellShiftSucc n (-1) y.1‖ < 1}
  toFun := closedCellInteriorChartValue n
  invFun := fun y => closedCellProject (closedCellShiftSucc n (-1) y.1)
  map_source' := by
    intro x hx
    change ‖closedCellShiftSucc n (-1) (closedCellInteriorChartValue n x).1‖ < 1
    rw [closedCellInteriorChartValue_coe]
    rw [closedCellShiftSucc_neg n 1 x.1]
    exact hx
  map_target' := by
    intro y hy
    change ‖(closedCellProject (closedCellShiftSucc n (-1) y.1)).1‖ < 1
    rw [closedCellProject_of_mem (le_of_lt hy)]
    exact hy
  left_inv' := by
    intro x hx
    apply Subtype.ext
    change (closedCellProject (closedCellShiftSucc n (-1) (closedCellInteriorChartValue n x).1)).1 = x.1
    rw [closedCellInteriorChartValue_coe]
    rw [closedCellShiftSucc_neg n 1 x.1]
    rw [closedCellProject_of_mem (le_of_lt hx)]
  right_inv' := by
    intro y hy
    apply Subtype.ext
    change (closedCellInteriorChartValue n (closedCellProject (closedCellShiftSucc n (-1) y.1))).1 = y.1
    rw [closedCellInteriorChartValue_coe]
    rw [closedCellProject_of_mem (le_of_lt hy)]
    rw [closedCellShiftSucc_neg' n 1 y.1]
  open_source := by
    have hcont : Continuous (fun x : ClosedCell (n + 1) => ‖x.1‖) :=
      continuous_norm.comp continuous_subtype_val
    exact (isOpen_Iio : IsOpen (Set.Iio (1 : ℝ))).preimage hcont
  open_target := by
    have hcont : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        ‖closedCellShiftSucc n (-1) y.1‖) := by
      have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellShiftSucc n (-1) y) := by
        have hc : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0))) :=
          continuous_id.add continuous_const
        simpa [closedCellShiftSucc_eq_add] using hc
      exact continuous_norm.comp (hlin.comp continuous_subtype_val)
    exact (isOpen_Iio : IsOpen (Set.Iio (1 : ℝ))).preimage hcont
  continuousOn_toFun := by
    have hcont : Continuous (fun x : ClosedCell (n + 1) =>
        closedCellShiftSucc n 1 x.1) := by
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          x + (1 : ℝ) • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0))) :=
        continuous_id.add continuous_const
      have hlin' : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellShiftSucc n 1 x) := by
        simpa [closedCellShiftSucc_eq_add] using hc
      exact hlin'.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun x => by
      change 0 ≤ (closedCellShiftSucc n 1 x.1)
        (0)
      rw [closedCellShiftSucc_apply_zero]
      have hle : ‖x.1 (0)‖ ≤ 1 :=
        le_trans (PiLp.norm_apply_le x.1
          (0)) (by
            change ‖x.1‖ ≤ 1
            exact x.2)
      have hlt : -1 ≤ x.1 (0) :=
        (abs_le.mp (by simpa using hle)).1
      linarith)).continuousOn
  continuousOn_invFun := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        closedCellShiftSucc n (-1) y) := by
      have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0))) :=
        continuous_id.add continuous_const
      simpa [closedCellShiftSucc_eq_add] using hlin
    have hlin' : Continuous (fun y : {y : EuclideanHalfSpace (n + 1) |
        ‖closedCellShiftSucc n (-1) y.1‖ < 1} =>
        closedCellShiftSucc n (-1) (Subtype.val (Subtype.val y))) :=
      hlin.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.congr (Continuous.subtype_mk hlin' (fun y => by
      exact le_of_lt y.2)) (fun y => by
      change ⟨closedCellShiftSucc n (-1) (Subtype.val (Subtype.val y)), le_of_lt y.2⟩ =
        closedCellProject (closedCellShiftSucc n (-1) (Subtype.val (Subtype.val y)))
      exact (closedCellProject_of_mem (le_of_lt y.2)).symm)

theorem closedCellCons_split (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellCons n (x (0)) (closedCellTail n x) = x := by
  ext j
  refine Fin.cases ?zero ?succ j
  · simp [closedCellCons]
  · intro j'
    rw [closedCellCons_apply_succ]
    rfl


noncomputable def closedCellBoundaryChartValue (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (x : ClosedCell (n + 1)) : EuclideanHalfSpace (n + 1) :=
  ⟨closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1)), by
    rw [closedCellCons_apply_zero]
    have hsq : ‖x.1‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg x.1, x.2]
    linarith⟩

theorem closedCellBoundaryChartValue_coe (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (x : ClosedCell (n + 1)) :
    (closedCellBoundaryChartValue n e x).1 =
      closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1)) := rfl

noncomputable def closedCellBoundaryInvValue (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (s : ℝ) (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  closedCellPermute e.symm (closedCellCons n
    (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) (closedCellTail n y))

theorem closedCellBoundaryInvValue_norm_sq {n : ℕ} (e : Fin (n + 1) ≃ Fin (n + 1))
    {s : ℝ} (hs : s ^ 2 = 1) (y : EuclideanSpace ℝ (Fin (n + 1)))
    (hpos : 0 < 1 - y (0) - ‖closedCellTail n y‖ ^ 2) :
    ‖closedCellBoundaryInvValue n e s y‖ ^ 2 = 1 - y (0) := by
  dsimp [closedCellBoundaryInvValue]
  rw [closedCellPermute_norm]
  rw [closedCellCons_norm_sq]
  have hsqrt : (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) ^ 2 =
      1 - y (0) - ‖closedCellTail n y‖ ^ 2 := by
    rw [mul_pow, hs, one_mul]
    rw [Real.sq_sqrt (le_of_lt hpos)]
  change (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) ^ 2 +
      ‖closedCellTail n y‖ ^ 2 = 1 - y (0)
  rw [hsqrt]
  ring

theorem closedCellBoundaryInvValue_norm_le_one {n : ℕ} (e : Fin (n + 1) ≃ Fin (n + 1))
    {s : ℝ} (hs : s ^ 2 = 1) (y : EuclideanSpace ℝ (Fin (n + 1)))
    (hpos : 0 < 1 - y (0) - ‖closedCellTail n y‖ ^ 2)
    (ht0 : 0 ≤ y (0)) :
    ‖closedCellBoundaryInvValue n e s y‖ ≤ 1 := by
  have hsq := closedCellBoundaryInvValue_norm_sq e hs y hpos
  have hle : ‖closedCellBoundaryInvValue n e s y‖ ^ 2 ≤ 1 ^ 2 := by
    rw [hsq]
    nlinarith
  exact (abs_le.mp (by simpa using sq_le_sq.mp hle)).2

noncomputable def closedCellBoundaryChart (n : ℕ) (i : Fin (n + 1)) (σ : Bool) :
    OpenPartialHomeomorph (ClosedCell (n + 1)) (EuclideanHalfSpace (n + 1)) := by
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap i (0)
  let s : ℝ := closedCellSign σ
  have hs : s ^ 2 = 1 := by
    dsimp [s]
    exact closedCellSign_sq σ
  have hss : s * s = 1 := by
    dsimp [s]
    exact closedCellSign_mul_self σ
  refine
    { source := {x : ClosedCell (n + 1) |
        0 < s * (closedCellPermute e x.1) (0)}
      target := {y : EuclideanHalfSpace (n + 1) |
        y.1 (0) < 1 ∧
          0 < 1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2}
      toFun := closedCellBoundaryChartValue n e
      invFun := fun y => closedCellProject (closedCellBoundaryInvValue n e s y.1)
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := ?_
      open_target := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro x hx
    change 0 < s * (closedCellPermute e x.1) (0) at hx
    change (closedCellBoundaryChartValue n e x).1 (0) < 1 ∧
      0 < 1 - (closedCellBoundaryChartValue n e x).1 (0) -
        ‖closedCellTail n (closedCellBoundaryChartValue n e x).1‖ ^ 2
    rw [closedCellBoundaryChartValue_coe]
    rw [closedCellCons_apply_zero, closedCellCons_tail]
    constructor
    · have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
        closedCellPermute_coord_ne_zero e hx
      have hxpos : 0 < ‖x.1‖ := by
        have hle : ‖(closedCellPermute e x.1) (0)‖ ≤ ‖x.1‖ := by
          calc
            ‖(closedCellPermute e x.1) (0)‖ ≤ ‖closedCellPermute e x.1‖ :=
              closedCellCoord_norm_le_norm (closedCellPermute e x.1)
            _ = ‖x.1‖ := closedCellPermute_norm e x.1
        have habs : 0 < |(closedCellPermute e x.1) (0)| := abs_pos.mpr hx0
        have hpos : 0 < ‖(closedCellPermute e x.1) (0)‖ := by
          simpa using habs
        exact lt_of_lt_of_le hpos hle
      have hsq : 0 < ‖x.1‖ ^ 2 := by positivity
      linarith
    · have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
        closedCellPermute_coord_ne_zero e hx
      have hsplit := closedCellSplit_norm_sq n (closedCellPermute e x.1)
      rw [closedCellPermute_norm] at hsplit
      have hmain : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
          ((closedCellPermute e x.1) (0)) ^ 2 := by
        have hring : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
            ‖x.1‖ ^ 2 - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by ring
        rw [hring]
        rw [hsplit]
        ring
      rw [hmain]
      exact sq_pos_of_ne_zero hx0
  · intro y hy
    change 0 < s * (closedCellPermute e (closedCellProject
        (closedCellBoundaryInvValue n e s y.1)).1) (0)
    have hzle : ‖closedCellBoundaryInvValue n e s y.1‖ ≤ 1 :=
      closedCellBoundaryInvValue_norm_le_one e hs y.1 hy.2 y.2
    rw [closedCellProject_of_mem hzle]
    change 0 < s * (closedCellPermute e (closedCellBoundaryInvValue n e s y.1))
      (0)
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellPermute_inv']
    rw [closedCellCons_apply_zero]
    change 0 < s * (s * Real.sqrt (1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2))
    rw [← mul_assoc, hss, one_mul]
    exact Real.sqrt_pos.2 hy.2
  · intro x hx
    change 0 < s * (closedCellPermute e x.1) (0) at hx
    apply Subtype.ext
    change (closedCellProject (closedCellBoundaryInvValue n e s
        (closedCellBoundaryChartValue n e x).1)).1 = x.1
    have hzle : ‖closedCellBoundaryInvValue n e s (closedCellBoundaryChartValue n e x).1‖ ≤ 1 := by
      rw [closedCellBoundaryChartValue_coe]
      dsimp [closedCellBoundaryInvValue]
      rw [closedCellPermute_norm]
      rw [closedCellCons_apply_zero, closedCellCons_tail]
      have hsq : ‖closedCellCons n (s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
          ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2))
          (closedCellTail n (closedCellPermute e x.1))‖ ^ 2 ≤ 1 := by
        rw [closedCellCons_norm_sq]
        have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
          closedCellPermute_coord_ne_zero e hx
        have hsplit := closedCellSplit_norm_sq n (closedCellPermute e x.1)
        rw [closedCellPermute_norm] at hsplit
        have hmain : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
            ((closedCellPermute e x.1) (0)) ^ 2 := by
          have hring : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
              ‖x.1‖ ^ 2 - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by ring
          rw [hring]
          rw [hsplit]
          ring
        have hsqrt : (s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
            ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2)) ^ 2 =
            1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by
          rw [mul_pow, hs, one_mul]
          rw [Real.sq_sqrt (le_of_lt (by rw [hmain]; exact sq_pos_of_ne_zero hx0))]
        change (s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
            ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2)) ^ 2 +
            ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 ≤ 1
        rw [hsqrt]
        nlinarith [norm_nonneg x.1, x.2]
      have hzn : 0 ≤ ‖closedCellBoundaryInvValue n e s (closedCellBoundaryChartValue n e x).1‖ := norm_nonneg _
      nlinarith
    rw [closedCellProject_of_mem hzle]
    change (closedCellBoundaryInvValue n e s (closedCellBoundaryChartValue n e x).1) = x.1
    rw [closedCellBoundaryChartValue_coe]
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellCons_apply_zero, closedCellCons_tail]
    have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
      closedCellPermute_coord_ne_zero e hx
    have hsplit := closedCellSplit_norm_sq n (closedCellPermute e x.1)
    rw [closedCellPermute_norm] at hsplit
    have hmain : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
        ((closedCellPermute e x.1) (0)) ^ 2 := by
      have hring : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
          ‖x.1‖ ^ 2 - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by ring
      rw [hring]
      rw [hsplit]
      ring
    have hsqrt : s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
        ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2) =
        (closedCellPermute e x.1) (0) := by
      rw [hmain]
      rw [Real.sqrt_sq_eq_abs]
      exact closedCellSign_mul_abs hx
    rw [hsqrt]
    change (closedCellPermute e.symm (closedCellCons n ((closedCellPermute e x.1) (0))
        (closedCellTail n (closedCellPermute e x.1)))) = x.1
    rw [closedCellCons_split n (closedCellPermute e x.1)]
    exact closedCellPermute_inv e x.1
  · intro y hy
    apply Subtype.ext
    change (closedCellBoundaryChartValue n e (closedCellProject
        (closedCellBoundaryInvValue n e s y.1))).1 = y.1
    rw [closedCellBoundaryChartValue_coe]
    have hzle : ‖closedCellBoundaryInvValue n e s y.1‖ ≤ 1 :=
      closedCellBoundaryInvValue_norm_le_one e hs y.1 hy.2 y.2
    rw [closedCellProject_of_mem hzle]
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellPermute_inv']
    rw [closedCellCons_tail]
    have hnorm : ‖closedCellPermute e.symm (closedCellCons n
        (s * Real.sqrt (1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2))
          (closedCellTail n y.1))‖ ^ 2 = 1 - y.1 (0) :=
      closedCellBoundaryInvValue_norm_sq e hs y.1 hy.2
    have hmain : 1 - ‖closedCellPermute e.symm (closedCellCons n
        (s * Real.sqrt (1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2))
          (closedCellTail n y.1))‖ ^ 2 = y.1 (0) := by
      rw [hnorm]
      ring
    rw [hmain]
    exact closedCellCons_split n y.1
  · have hcont : Continuous (fun x : ClosedCell (n + 1) =>
        s * (closedCellPermute e x.1) (0)) := by
      have hlin : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellPermute e x) := (closedCellPermute e).continuous
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          (closedCellPermute e x) (0)) := by
        have hlin' : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
            WithLp.ofLp (closedCellPermute e x)) :=
          (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).comp hlin
        exact (continuous_apply (0 : Fin (n + 1))).comp hlin'
      exact continuous_const.mul (hc.comp continuous_subtype_val)
    exact (isOpen_Ioi (a := (0 : ℝ))).preimage hcont
  · have hcont1 : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        y.1 (0)) :=
      (continuous_apply (0 : Fin (n + 1))).comp
        ((PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).comp continuous_subtype_val)
    have htail : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        closedCellTail n y.1) := by
      unfold closedCellTail
      fun_prop
    have hcont2 : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2) :=
      (continuous_const.sub hcont1).sub ((continuous_norm.comp htail).pow 2)
    exact ((isOpen_Iio (a := (1 : ℝ))).preimage hcont1).inter
      ((isOpen_Ioi (a := (0 : ℝ))).preimage hcont2)
  · have hcont : Continuous (fun x : ClosedCell (n + 1) =>
        closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1))) := by
      have hlin : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellPermute e x) := (closedCellPermute e).continuous
      have htail : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellTail n x) := by
        unfold closedCellTail
        fun_prop
      have hcons : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellCons n (1 - ‖x‖ ^ 2) (closedCellTail n x)) := by
        have hfin : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
            (Fin.cons (1 - ‖x‖ ^ 2) (WithLp.ofLp (closedCellTail n x)) : Fin (n + 1) → ℝ)) := by
          refine Continuous.finCons (A := fun _ : Fin (n + 1) => ℝ) ?_ ?_
          · fun_prop
          · have htail' : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
                WithLp.ofLp (closedCellTail n x)) :=
              (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ)).comp htail
            exact htail'
        simpa [closedCellCons_eq_cons] using
          (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 1) => ℝ)).comp hfin
      exact Continuous.congr (hcons.comp (hlin.comp continuous_subtype_val)) (fun x => by
        change closedCellCons n (1 - ‖closedCellPermute e x.1‖ ^ 2)
            (closedCellTail n (closedCellPermute e x.1)) =
          closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1))
        congr 1
        rw [closedCellPermute_norm])
    exact (Continuous.subtype_mk hcont (fun x => by
      change 0 ≤ (closedCellCons n (1 - ‖x.1‖ ^ 2)
          (closedCellTail n (closedCellPermute e x.1))) (0)
      rw [closedCellCons_apply_zero]
      have hsq : ‖x.1‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg x.1, x.2]
      linarith)).continuousOn
  · refine continuousOn_iff_continuous_restrict.mpr ?_
    have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        closedCellBoundaryInvValue n e s y) := by
      dsimp [closedCellBoundaryInvValue]
      have hperm : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellPermute e.symm y) := (closedCellPermute e.symm).continuous
      have hcons : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellCons n (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2))
            (closedCellTail n y)) := by
        have htail : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            closedCellTail n y) := by
          unfold closedCellTail
          fun_prop
        have hsqrt : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) := by
          have harg : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
              1 - y (0) - ‖closedCellTail n y‖ ^ 2) :=
            let hc0 : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y (0)) :=
              (continuous_apply (0 : Fin (n + 1))).comp
                (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin (n + 1) => ℝ))
            (continuous_const.sub hc0).sub ((continuous_norm.comp htail).pow 2)
          exact Real.continuous_sqrt.comp harg
        have hfin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            (Fin.cons (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2))
              (WithLp.ofLp (closedCellTail n y)) : Fin (n + 1) → ℝ)) := by
          refine Continuous.finCons ?_ ?_
          · exact (continuous_const.mul hsqrt)
          · have htail' : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
                WithLp.ofLp (closedCellTail n y)) :=
              (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ)).comp htail
            exact htail'
        simpa [closedCellCons_eq_cons] using
          (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 1) => ℝ)).comp hfin
      exact hperm.comp hcons
    have hlin' : Continuous (fun y : {y : EuclideanHalfSpace (n + 1) |
        y.1 (0) < 1 ∧
          0 < 1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2} =>
        closedCellBoundaryInvValue n e s (Subtype.val (Subtype.val y))) :=
      hlin.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.congr (Continuous.subtype_mk hlin' (fun y => by
      exact closedCellBoundaryInvValue_norm_le_one e hs
        (Subtype.val (Subtype.val y)) y.2.2 (Subtype.val y).2)) (fun y => by
      change ⟨closedCellBoundaryInvValue n e s (Subtype.val (Subtype.val y)),
          closedCellBoundaryInvValue_norm_le_one e hs
            (Subtype.val (Subtype.val y)) y.2.2 (Subtype.val y).2⟩ =
        closedCellProject (closedCellBoundaryInvValue n e s (Subtype.val (Subtype.val y)))
      exact (closedCellProject_of_mem (closedCellBoundaryInvValue_norm_le_one e hs
        (Subtype.val (Subtype.val y)) y.2.2 (Subtype.val y).2)).symm)



theorem closedCellSign_mul_pos {a : ℝ} (ha : a ≠ 0) :
    0 < (if 0 < a then (1 : ℝ) else -1) * a := by
  by_cases hapos : 0 < a
  · simp [hapos]
  · have hneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
    simp [hapos, hneg]

theorem closedCell_exists_coord_ne_zero {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1)))
    (hx : 1 ≤ ‖x‖) : ∃ i : Fin (m + 1), x i ≠ 0 := by
  by_contra h
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  rw [hx0, norm_zero] at hx
  norm_num at hx

theorem closedCellPermute_swap_apply {m : ℕ} (i : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))) x) (0 : Fin (m + 1)) = x i := by
  rw [closedCellPermute_apply]
  change x.1 ((Equiv.swap i (0 : Fin (m + 1))).symm (0 : Fin (m + 1))) = x.1 i
  simp [Equiv.symm_swap, Equiv.swap_apply_right]

theorem closedCellSign_decide {a : ℝ} :
    closedCellSign (0 < a) = if 0 < a then (1 : ℝ) else -1 := by
  by_cases h : 0 < a
  · simp [h, closedCellSign]
  · simp [h, closedCellSign]

theorem mem_closedCellInteriorChart_source (n : ℕ) (x : ClosedCell (n + 1)) (hx : ‖x.1‖ < 1) :
    x ∈ (closedCellInteriorChart n).source := hx

theorem mem_closedCellBoundaryChart_source {m : ℕ} (x : ClosedCell (m + 1)) {i : Fin (m + 1)}
    (hi : x.1 i ≠ 0) :
    x ∈ (closedCellBoundaryChart m i (0 < x.1 i)).source := by
  change 0 < closedCellSign (0 < x.1 i) * (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
    x.1) (0 : Fin (m + 1))
  rw [closedCellPermute_swap_apply]
  rw [closedCellSign_decide]
  exact closedCellSign_mul_pos hi

noncomputable def closedCellChartAt {m : ℕ} (x : ClosedCell (m + 1)) :
    OpenPartialHomeomorph (ClosedCell (m + 1)) (EuclideanHalfSpace (m + 1)) :=
  if hx : ‖x.1‖ < 1 then closedCellInteriorChart m
  else
    let i : Fin (m + 1) := Classical.choose (closedCell_exists_coord_ne_zero x.1 (by
      have hle : ‖x.1‖ ≤ 1 := x.2
      have hnot : ¬ ‖x.1‖ < 1 := hx
      linarith))
    closedCellBoundaryChart m i (0 < x.1 i)

@[reducible]
noncomputable def closedCellChartedSpaceSucc (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) where
  atlas := Set.range closedCellChartAt
  chartAt := closedCellChartAt
  mem_chart_source := by
    intro x
    by_cases hx : ‖x.1‖ < 1
    · rw [closedCellChartAt, dif_pos hx]
      exact hx
    · rw [closedCellChartAt, dif_neg hx]
      have hne : x.1 (Classical.choose (closedCell_exists_coord_ne_zero x.1 (by
          have hle : ‖x.1‖ ≤ 1 := x.2
          have hnot : ¬ ‖x.1‖ < 1 := hx
          linarith))) ≠ 0 :=
        (Classical.choose_spec (closedCell_exists_coord_ne_zero x.1 (by
          have hle : ‖x.1‖ ≤ 1 := x.2
          have hnot : ¬ ‖x.1‖ < 1 := hx
          linarith)))
      exact mem_closedCellBoundaryChart_source x hne
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem closedCellCons_contDiff {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      closedCellCons m p.1 p.2) := by
  rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin m) => closedCellCons m p.1 p.2) =
      WithLp.toLp 2 ∘ (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        Fin.cons p.1 (WithLp.ofLp p.2)) from by
    funext p
    exact closedCellCons_eq_cons m p.1 p.2]
  have hfin : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (m + 1) → ℝ)) := by
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Fin.cons p.1 (WithLp.ofLp p.2)) =
        fun p j => (Fin.cases p.1 (fun j' : Fin m => (WithLp.ofLp p.2 : Fin m → ℝ) j') j : ℝ) from by
      funext p
      ext j
      by_cases hj : j = (0 : Fin (m + 1))
      · subst j
        rfl
      · have hsucc : ∃ j' : Fin m, Fin.succ j' = j := Fin.exists_succ_eq.mpr hj
        rcases hsucc with ⟨j', rfl⟩
        rfl]
    exact contDiff_pi' (fun j => by
      by_cases hj : j = (0 : Fin (m + 1))
      · subst j
        change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => p.1)
        exact contDiff_fst
      · have hsucc : ∃ j' : Fin m, Fin.succ j' = j := Fin.exists_succ_eq.mpr hj
        rcases hsucc with ⟨j', rfl⟩
        change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (WithLp.ofLp p.2) j')
        fun_prop)
  let htoLp : (Fin (m + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)).symm.toLinearMap
      cont := PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (m + 1) => ℝ) }
  have hfun : ⇑htoLp = (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) := by
    dsimp [htoLp]
    change ⇑(WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)).symm = WithLp.toLp 2
    exact WithLp.coe_symm_linearEquiv 2 ℝ (Fin (m + 1) → ℝ)
  simpa [hfun] using htoLp.contDiff.comp hfin

theorem closedCellShiftSucc_contDiff {m : ℕ} (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => closedCellShiftSucc m c x) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      x + c • (EuclideanSpace.basisFun (Fin (m + 1)) ℝ (0 : Fin (m + 1)))) :=
    contDiff_id.add contDiff_const
  simpa [closedCellShiftSucc_eq_add] using hlin

theorem closedCellPermute_contDiff {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (closedCellPermute e) := by
  exact (closedCellPermute e).toContinuousLinearEquiv.contDiff

theorem closedCellTail_contDiff {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => closedCellTail m x) := by
  unfold closedCellTail
  fun_prop

theorem closedCellCons_contDiffOn_left {m : ℕ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m x)) Set.univ := by
  have hcons : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m x)) := by
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        (1 - ‖x‖ ^ 2, closedCellTail m x)) := by
      have hnorm : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => 1 - ‖x‖ ^ 2) := by
        exact (contDiff_const.sub (contDiff_norm_sq ℝ))
      exact hnorm.prodMk (closedCellTail_contDiff (m := m))
    have hcons' : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        closedCellCons m p.1 p.2) := closedCellCons_contDiff
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
          closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m x)) := by
      simpa using hcons'.comp hpair
    exact hcomp
  exact hcons.contDiffOn

noncomputable def closedCellInteriorBoundaryTransition {m : ℕ} (i : Fin (m + 1))
    (y : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  closedCellCons m (1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2)
    (closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
      (closedCellShiftSucc m (-1) y)))

theorem closedCellInteriorBoundaryTransition_contDiff {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (closedCellInteriorBoundaryTransition i) := by
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellShiftSucc m (-1) y) := closedCellShiftSucc_contDiff (-1)
  have hperm : ContDiff ℝ (⊤ : ℕ∞) (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))) :=
    closedCellPermute_contDiff (Equiv.swap i (0 : Fin (m + 1)))
  have hnorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2) := by
    exact (contDiff_const.sub ((contDiff_norm_sq ℝ).comp hshift))
  have htail : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
        (closedCellShiftSucc m (-1) y))) := by
    exact (closedCellTail_contDiff (m := m)).comp (hperm.comp hshift)
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2,
        closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
          (closedCellShiftSucc m (-1) y)))) :=
    hnorm.prodMk htail
  simpa [closedCellInteriorBoundaryTransition] using (closedCellCons_contDiff (m := m)).comp hpair

noncomputable def closedCellBoundaryInteriorTransition {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    (y : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  closedCellShiftSucc m 1 (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
    (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
      (closedCellTail m y)))

theorem closedCellBoundaryInteriorTransition_contDiffOn {m : ℕ} (i : Fin (m + 1)) (σ : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (closedCellBoundaryInteriorTransition i σ)
      {y : EuclideanSpace ℝ (Fin (m + 1)) | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} := by
  let s : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2}
  have htail : ContDiff ℝ (⊤ : ℕ∞) (closedCellTail m) := closedCellTail_contDiff (m := m)
  have hargAll : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        1 - y (0 : Fin (m + 1))) := by
      exact (contDiff_const.sub (by fun_prop))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        ‖closedCellTail m y‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp htail
    exact h1.sub h2
  have harg : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2) s :=
    hargAll.contDiffOn.mono (Set.subset_univ s)
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2)) s :=
    ContDiffOn.sqrt (hf := harg) (s := s) (fun y hy => ne_of_gt hy)
  have hfirst : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2),
        closedCellTail m y)) s :=
    ((contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun _ : EuclideanSpace ℝ (Fin (m + 1)) => closedCellSign σ) s).mul hsqrt).prodMk
      htail.contDiffOn
  have hcons : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
        (closedCellTail m y)) s :=
    (closedCellCons_contDiff (m := m)).contDiffOn.comp hfirst (by intro y hy; exact Set.mem_univ _)
  have hperm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
          (closedCellTail m y))) s :=
    (closedCellPermute_contDiff (Equiv.swap i (0 : Fin (m + 1))).symm).contDiffOn.comp hcons
      (by intro y hy; exact Set.mem_univ _)
  have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellShiftSucc m 1 (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
          (closedCellTail m y)))) s :=
    (closedCellShiftSucc_contDiff 1).contDiffOn.comp hperm (by intro y hy; exact Set.mem_univ _)
  simpa [closedCellBoundaryInteriorTransition, s] using hshift

noncomputable def closedCellBoundaryBoundaryTransition {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    (i' : Fin (m + 1))
    (y : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin (m + 1)) :=
  closedCellCons m (y (0 : Fin (m + 1)))
    (closedCellTail m (closedCellPermute (Equiv.swap i' (0 : Fin (m + 1)))
      (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
          (closedCellTail m y)))))

theorem closedCellBoundaryBoundaryTransition_contDiffOn {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    (i' : Fin (m + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (closedCellBoundaryBoundaryTransition i σ i')
      {y : EuclideanSpace ℝ (Fin (m + 1)) | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} := by
  let s : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2}
  have htail : ContDiff ℝ (⊤ : ℕ∞) (closedCellTail m) := closedCellTail_contDiff (m := m)
  have hc0 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y (0 : Fin (m + 1))) := by
    fun_prop
  have hargAll : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        1 - y (0 : Fin (m + 1))) := by
      exact (contDiff_const.sub (by fun_prop))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        ‖closedCellTail m y‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp htail
    exact h1.sub h2
  have harg : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2) s :=
    hargAll.contDiffOn.mono (Set.subset_univ s)
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2)) s :=
    ContDiffOn.sqrt (hf := harg) (s := s) (fun y hy => ne_of_gt hy)
  have hfirst : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2),
        closedCellTail m y)) s :=
    ((contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun _ : EuclideanSpace ℝ (Fin (m + 1)) => closedCellSign σ) s).mul hsqrt).prodMk
      htail.contDiffOn
  have hcons : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
        (closedCellTail m y)) s :=
    (closedCellCons_contDiff (m := m)).contDiffOn.comp hfirst (by intro y hy; exact Set.mem_univ _)
  have hperm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
          (closedCellTail m y))) s :=
    (closedCellPermute_contDiff (Equiv.swap i (0 : Fin (m + 1))).symm).contDiffOn.comp hcons
      (by intro y hy; exact Set.mem_univ _)
  have hperm' : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellPermute (Equiv.swap i' (0 : Fin (m + 1)))
        (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
          (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
            (closedCellTail m y)))) s :=
    (closedCellPermute_contDiff (Equiv.swap i' (0 : Fin (m + 1)))).contDiffOn.comp hperm
      (by intro y hy; exact Set.mem_univ _)
  have htail' : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellTail m (closedCellPermute (Equiv.swap i' (0 : Fin (m + 1)))
        (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
          (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
            (closedCellTail m y))))) s :=
    htail.contDiffOn.comp hperm' (by intro y hy; exact Set.mem_univ _)
  have hfinal : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (y (0 : Fin (m + 1)), closedCellTail m (closedCellPermute (Equiv.swap i' (0 : Fin (m + 1)))
        (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
          (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
            (closedCellTail m y)))))) s :=
    hc0.contDiffOn.prodMk htail'
  have hout : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (y (0 : Fin (m + 1)))
        (closedCellTail m (closedCellPermute (Equiv.swap i' (0 : Fin (m + 1)))
          (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
            (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
              (closedCellTail m y)))))) s :=
    (closedCellCons_contDiff (m := m)).contDiffOn.comp hfinal (by intro y hy; exact Set.mem_univ _)
  simpa [closedCellBoundaryBoundaryTransition, s] using hout

theorem closedCellInteriorBoundary_transition_reduce {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : y ∈ ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹'
        ((closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)).source ∩
      Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))) :
    (modelWithCornersEuclideanHalfSpace (m + 1)) (((closedCellInteriorChart m).symm ≫ₕ
        (closedCellBoundaryChart m i σ)) ((modelWithCornersEuclideanHalfSpace (m + 1)).symm y)) =
      closedCellInteriorBoundaryTransition i y := by
  classical
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
    (closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)
  have hy1 : I.symm y ∈ t.source := hy.1
  have hy2 : y ∈ Set.range I := hy.2
  have hy2' : 0 ≤ y (0 : Fin (m + 1)) := by
    rw [range_modelWithCornersEuclideanHalfSpace (m + 1)] at hy2
    exact hy2
  have hy2t : y ∈ I.target := by
    change y ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x (0 : Fin (m + 1))}
    exact hy2'
  let z : EuclideanHalfSpace (m + 1) := ⟨y, hy2'⟩
  have hclamp : I.symm y = z := by
    apply Subtype.ext
    have hz : I (I.symm y) = y := I.right_inv' hy2t
    exact hz
  have hy1z : z ∈ t.source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ (closedCellInteriorChart m).target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hz2 : (closedCellInteriorChart m).symm z ∈ (closedCellBoundaryChart m i σ).source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.2
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change I ((closedCellBoundaryChart m i σ) ((closedCellInteriorChart m).symm z)) =
    closedCellInteriorBoundaryTransition i y
  have hsymm : (closedCellInteriorChart m).symm z =
      (⟨closedCellShiftSucc m (-1) z.1, le_of_lt hz1⟩ : ClosedCell (m + 1)) := by
    change closedCellProject (closedCellShiftSucc m (-1) z.1) =
      (⟨closedCellShiftSucc m (-1) z.1, le_of_lt hz1⟩ : ClosedCell (m + 1))
    exact closedCellProject_of_mem (le_of_lt hz1)
  rw [hsymm]
  change I ((closedCellBoundaryChart m i σ)
    (⟨closedCellShiftSucc m (-1) z.1, le_of_lt hz1⟩ : ClosedCell (m + 1))) =
      closedCellInteriorBoundaryTransition i y
  change (closedCellBoundaryChartValue m (Equiv.swap i (0 : Fin (m + 1)))
    (⟨closedCellShiftSucc m (-1) z.1, le_of_lt hz1⟩ : ClosedCell (m + 1))).1 =
      closedCellInteriorBoundaryTransition i y
  rw [closedCellBoundaryChartValue_coe]
  change closedCellCons m (1 - ‖closedCellShiftSucc m (-1) z.1‖ ^ 2)
      (closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
        (closedCellShiftSucc m (-1) z.1))) = closedCellInteriorBoundaryTransition i y
  change closedCellCons m (1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2)
      (closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
        (closedCellShiftSucc m (-1) y))) = closedCellInteriorBoundaryTransition i y
  rfl

theorem closedCellBoundaryInterior_transition_reduce {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : y ∈ ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹'
        ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)).source ∩
      Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))) :
    (modelWithCornersEuclideanHalfSpace (m + 1)) (((closedCellBoundaryChart m i σ).symm ≫ₕ
        (closedCellInteriorChart m)) ((modelWithCornersEuclideanHalfSpace (m + 1)).symm y)) =
      closedCellBoundaryInteriorTransition i σ y := by
  classical
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
    (closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)
  have hy1 : I.symm y ∈ t.source := hy.1
  have hy2 : y ∈ Set.range I := hy.2
  have hy2' : 0 ≤ y (0 : Fin (m + 1)) := by
    rw [range_modelWithCornersEuclideanHalfSpace (m + 1)] at hy2
    exact hy2
  have hy2t : y ∈ I.target := by
    change y ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x (0 : Fin (m + 1))}
    exact hy2'
  let z : EuclideanHalfSpace (m + 1) := ⟨y, hy2'⟩
  have hclamp : I.symm y = z := by
    apply Subtype.ext
    have hz : I (I.symm y) = y := I.right_inv' hy2t
    exact hz
  have hy1z : z ∈ t.source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ (closedCellBoundaryChart m i σ).target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hz2 : (closedCellBoundaryChart m i σ).symm z ∈ (closedCellInteriorChart m).source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.2
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change I ((closedCellInteriorChart m) ((closedCellBoundaryChart m i σ).symm z)) =
    closedCellBoundaryInteriorTransition i σ y
  have hsymm : (closedCellBoundaryChart m i σ).symm z =
      (⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
          (closedCellTail m z.1)),
          closedCellBoundaryInvValue_norm_le_one (Equiv.swap i (0 : Fin (m + 1)))
            (closedCellSign_sq σ) z.1 hz1.2 z.2⟩ : ClosedCell (m + 1)) := by
    change closedCellProject (closedCellBoundaryInvValue m (Equiv.swap i (0 : Fin (m + 1)))
      (closedCellSign σ) z.1) = ⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
          (closedCellTail m z.1)),
          closedCellBoundaryInvValue_norm_le_one (Equiv.swap i (0 : Fin (m + 1)))
            (closedCellSign_sq σ) z.1 hz1.2 z.2⟩
    exact closedCellProject_of_mem (closedCellBoundaryInvValue_norm_le_one
      (Equiv.swap i (0 : Fin (m + 1))) (closedCellSign_sq σ) z.1 hz1.2 z.2)
  rw [hsymm]
  change I ((closedCellInteriorChart m) (⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
        (closedCellTail m z.1)), _⟩ : ClosedCell (m + 1))) = closedCellBoundaryInteriorTransition i σ y
  change (closedCellInteriorChartValue m (⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
        (closedCellTail m z.1)), _⟩ : ClosedCell (m + 1))).1 = closedCellBoundaryInteriorTransition i σ y
  rw [closedCellInteriorChartValue_coe]
  change closedCellShiftSucc m 1 (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
        (closedCellTail m z.1))) = closedCellBoundaryInteriorTransition i σ y
  change closedCellShiftSucc m 1 (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
        (closedCellTail m y))) = closedCellBoundaryInteriorTransition i σ y
  rfl

theorem closedCellBoundaryBoundary_transition_reduce {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    (i' : Fin (m + 1)) (σ' : Bool)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : y ∈ ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹'
        ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellBoundaryChart m i' σ')).source ∩
      Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))) :
    (modelWithCornersEuclideanHalfSpace (m + 1)) (((closedCellBoundaryChart m i σ).symm ≫ₕ
        (closedCellBoundaryChart m i' σ')) ((modelWithCornersEuclideanHalfSpace (m + 1)).symm y)) =
      closedCellBoundaryBoundaryTransition i σ i' y := by
  classical
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
    (closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellBoundaryChart m i' σ')
  have hy1 : I.symm y ∈ t.source := hy.1
  have hy2 : y ∈ Set.range I := hy.2
  have hy2' : 0 ≤ y (0 : Fin (m + 1)) := by
    rw [range_modelWithCornersEuclideanHalfSpace (m + 1)] at hy2
    exact hy2
  have hy2t : y ∈ I.target := by
    change y ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x (0 : Fin (m + 1))}
    exact hy2'
  let z : EuclideanHalfSpace (m + 1) := ⟨y, hy2'⟩
  have hclamp : I.symm y = z := by
    apply Subtype.ext
    have hz : I (I.symm y) = y := I.right_inv' hy2t
    exact hz
  have hy1z : z ∈ t.source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ (closedCellBoundaryChart m i σ).target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hz2 : (closedCellBoundaryChart m i σ).symm z ∈ (closedCellBoundaryChart m i' σ').source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.2
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change I ((closedCellBoundaryChart m i' σ') ((closedCellBoundaryChart m i σ).symm z)) =
    closedCellBoundaryBoundaryTransition i σ i' y
  have hsymm : (closedCellBoundaryChart m i σ).symm z =
      (⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
          (closedCellTail m z.1)),
          closedCellBoundaryInvValue_norm_le_one (Equiv.swap i (0 : Fin (m + 1)))
            (closedCellSign_sq σ) z.1 hz1.2 z.2⟩ : ClosedCell (m + 1)) := by
    change closedCellProject (closedCellBoundaryInvValue m (Equiv.swap i (0 : Fin (m + 1)))
      (closedCellSign σ) z.1) = ⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
        (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
          (closedCellTail m z.1)),
          closedCellBoundaryInvValue_norm_le_one (Equiv.swap i (0 : Fin (m + 1)))
            (closedCellSign_sq σ) z.1 hz1.2 z.2⟩
    exact closedCellProject_of_mem (closedCellBoundaryInvValue_norm_le_one
      (Equiv.swap i (0 : Fin (m + 1))) (closedCellSign_sq σ) z.1 hz1.2 z.2)
  rw [hsymm]
  change I ((closedCellBoundaryChart m i' σ') (⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
        (closedCellTail m z.1)), _⟩ : ClosedCell (m + 1))) = closedCellBoundaryBoundaryTransition i σ i' y
  change (closedCellBoundaryChartValue m (Equiv.swap i' (0 : Fin (m + 1)))
    (⟨closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
        (closedCellTail m z.1)), _⟩ : ClosedCell (m + 1))).1 = closedCellBoundaryBoundaryTransition i σ i' y
  rw [closedCellBoundaryChartValue_coe]
  have hnorm : ‖closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
      (closedCellCons m (closedCellSign σ * Real.sqrt (1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2))
        (closedCellTail m z.1))‖ ^ 2 = 1 - z.1 (0 : Fin (m + 1)) := by
    simpa [closedCellBoundaryInvValue] using (closedCellBoundaryInvValue_norm_sq
      (Equiv.swap i (0 : Fin (m + 1))) (closedCellSign_sq σ) z.1 hz1.2)
  rw [hnorm]
  rw [show 1 - (1 - z.1 (0 : Fin (m + 1))) = z.1 (0 : Fin (m + 1)) by ring]
  change closedCellCons m (y (0 : Fin (m + 1)))
      (closedCellTail m (closedCellPermute (Equiv.swap i' (0 : Fin (m + 1)))
        (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))).symm
          (closedCellCons m (closedCellSign σ * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
            (closedCellTail m y))))) = closedCellBoundaryBoundaryTransition i σ i' y
  rfl

theorem closedCellInteriorInterior_transition_reduce {m : ℕ}
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : y ∈ ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹'
        ((closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)).source ∩
      Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))) :
    (modelWithCornersEuclideanHalfSpace (m + 1)) (((closedCellInteriorChart m).symm ≫ₕ
        (closedCellInteriorChart m)) ((modelWithCornersEuclideanHalfSpace (m + 1)).symm y)) = y := by
  classical
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
    (closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)
  have hy1 : I.symm y ∈ t.source := hy.1
  have hy2 : y ∈ Set.range I := hy.2
  have hy2' : 0 ≤ y (0 : Fin (m + 1)) := by
    rw [range_modelWithCornersEuclideanHalfSpace (m + 1)] at hy2
    exact hy2
  have hy2t : y ∈ I.target := by
    change y ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x (0 : Fin (m + 1))}
    exact hy2'
  let z : EuclideanHalfSpace (m + 1) := ⟨y, hy2'⟩
  have hclamp : I.symm y = z := by
    apply Subtype.ext
    have hz : I (I.symm y) = y := I.right_inv' hy2t
    exact hz
  have hy1z : z ∈ t.source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ (closedCellInteriorChart m).target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hz2 : (closedCellInteriorChart m).symm z ∈ (closedCellInteriorChart m).source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.2
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change I ((closedCellInteriorChart m) ((closedCellInteriorChart m).symm z)) = y
  change ((closedCellInteriorChart m) ((closedCellInteriorChart m).symm z)).1 = y
  exact congrArg Subtype.val ((closedCellInteriorChart m).right_inv hz1)

theorem closedCellBoundaryChart_trans_source_mem_sqrt_domain {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    {e : OpenPartialHomeomorph (ClosedCell (m + 1)) (EuclideanHalfSpace (m + 1))}
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : y ∈ ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹'
        ((closedCellBoundaryChart m i σ).symm ≫ₕ e).source ∩
      Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))) :
    0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2 := by
  classical
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  have hy2 : y ∈ Set.range I := hy.2
  have hy2' : 0 ≤ y (0 : Fin (m + 1)) := by
    rw [range_modelWithCornersEuclideanHalfSpace (m + 1)] at hy2
    exact hy2
  have hy2t : y ∈ I.target := by
    change y ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x (0 : Fin (m + 1))}
    exact hy2'
  let z : EuclideanHalfSpace (m + 1) := ⟨y, hy2'⟩
  have hclamp : I.symm y = z := by
    apply Subtype.ext
    have hz : I (I.symm y) = y := I.right_inv' hy2t
    exact hz
  have hz1 : z ∈ (closedCellBoundaryChart m i σ).target := by
    have hsrc : I.symm y ∈ (closedCellBoundaryChart m i σ).symm.source := by
      have htrans : I.symm y ∈ (closedCellBoundaryChart m i σ).symm.source ∩
          (closedCellBoundaryChart m i σ).symm ⁻¹' e.source := by
        simpa [OpenPartialHomeomorph.trans_source] using hy.1
      exact htrans.1
    rw [← hclamp]
    exact hsrc
  have hz1' : 0 < 1 - z.1 (0 : Fin (m + 1)) - ‖closedCellTail m z.1‖ ^ 2 := hz1.2
  simpa [z] using hz1'

theorem closedCellInteriorInterior_transition_mem_groupoid {m : ℕ} :
    ((closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)) ∈
      contDiffGroupoid (⊤ : ℕ∞) (modelWithCornersEuclideanHalfSpace (m + 1)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)
    exact (contDiff_id.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y)
      (I.symm ⁻¹' t.source ∩ Set.range I)).congr (by
        intro y hy
        exact closedCellInteriorInterior_transition_reduce hy)
  · rw [show ((closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)).symm =
        (closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        simp]
    rw [show ((closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)).target =
        ((closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)).source from by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellInteriorChart m).symm ≫ₕ (closedCellInteriorChart m)
    exact (contDiff_id.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y)
      (I.symm ⁻¹' t.source ∩ Set.range I)).congr (by
        intro y hy
        exact closedCellInteriorInterior_transition_reduce hy)

theorem closedCellInteriorBoundary_transition_mem_groupoid {m : ℕ} (i : Fin (m + 1)) (σ : Bool) :
    ((closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)) ∈
      contDiffGroupoid (⊤ : ℕ∞) (modelWithCornersEuclideanHalfSpace (m + 1)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)
    exact ((closedCellInteriorBoundaryTransition_contDiff i).contDiffOn.mono (Set.subset_univ _)).congr
      (by intro y hy; exact closedCellInteriorBoundary_transition_reduce i σ hy)
  · rw [show ((closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)).symm =
        (closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)).target =
        ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)).source from by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)
    exact ((closedCellBoundaryInteriorTransition_contDiffOn i σ).mono (by
      intro y hy
      exact closedCellBoundaryChart_trans_source_mem_sqrt_domain i σ hy)).congr (by
        intro y hy
        exact closedCellBoundaryInterior_transition_reduce i σ hy)

theorem closedCellBoundaryInterior_transition_mem_groupoid {m : ℕ} (i : Fin (m + 1)) (σ : Bool) :
    ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)) ∈
      contDiffGroupoid (⊤ : ℕ∞) (modelWithCornersEuclideanHalfSpace (m + 1)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)
    exact ((closedCellBoundaryInteriorTransition_contDiffOn i σ).mono (by
      intro y hy
      exact closedCellBoundaryChart_trans_source_mem_sqrt_domain i σ hy)).congr (by
        intro y hy
        exact closedCellBoundaryInterior_transition_reduce i σ hy)
  · rw [show ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)).symm =
        (closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellInteriorChart m)).target =
        ((closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)).source from by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellInteriorChart m).symm ≫ₕ (closedCellBoundaryChart m i σ)
    exact ((closedCellInteriorBoundaryTransition_contDiff i).contDiffOn.mono (Set.subset_univ _)).congr
      (by intro y hy; exact closedCellInteriorBoundary_transition_reduce i σ hy)

theorem closedCellBoundaryBoundary_transition_mem_groupoid {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    (i' : Fin (m + 1)) (σ' : Bool) :
    ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellBoundaryChart m i' σ')) ∈
      contDiffGroupoid (⊤ : ℕ∞) (modelWithCornersEuclideanHalfSpace (m + 1)) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellBoundaryChart m i' σ')
    exact ((closedCellBoundaryBoundaryTransition_contDiffOn i σ i').mono (by
      intro y hy
      exact closedCellBoundaryChart_trans_source_mem_sqrt_domain i σ hy)).congr (by
        intro y hy
        exact closedCellBoundaryBoundary_transition_reduce i σ i' σ' hy)
  · rw [show ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellBoundaryChart m i' σ')).symm =
        (closedCellBoundaryChart m i' σ').symm ≫ₕ (closedCellBoundaryChart m i σ) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((closedCellBoundaryChart m i σ).symm ≫ₕ (closedCellBoundaryChart m i' σ')).target =
        ((closedCellBoundaryChart m i' σ').symm ≫ₕ (closedCellBoundaryChart m i σ)).source from by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
      modelWithCornersEuclideanHalfSpace (m + 1)
    let t : OpenPartialHomeomorph (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (m + 1)) :=
      (closedCellBoundaryChart m i' σ').symm ≫ₕ (closedCellBoundaryChart m i σ)
    exact ((closedCellBoundaryBoundaryTransition_contDiffOn i' σ' i).mono (by
      intro y hy
      exact closedCellBoundaryChart_trans_source_mem_sqrt_domain i' σ' hy)).congr (by
        intro y hy
        exact closedCellBoundaryBoundary_transition_reduce i' σ' i σ hy)

theorem closedCellChart_transition_mem_groupoid {m : ℕ} (x₁ x₂ : ClosedCell (m + 1)) :
    (closedCellChartAt x₁).symm ≫ₕ (closedCellChartAt x₂) ∈
      contDiffGroupoid (⊤ : ℕ∞) (modelWithCornersEuclideanHalfSpace (m + 1)) := by
  by_cases hx₁ : ‖x₁.1‖ < 1
  · by_cases hx₂ : ‖x₂.1‖ < 1
    · unfold closedCellChartAt
      rw [dif_pos hx₁, dif_pos hx₂]
      exact closedCellInteriorInterior_transition_mem_groupoid
    · unfold closedCellChartAt
      rw [dif_pos hx₁, dif_neg hx₂]
      exact closedCellInteriorBoundary_transition_mem_groupoid
        (Classical.choose (closedCell_exists_coord_ne_zero x₂.1 (by
          have hle : ‖x₂.1‖ ≤ 1 := x₂.2
          have hnot : ¬ ‖x₂.1‖ < 1 := hx₂
          linarith))) (0 < x₂.1 (Classical.choose (closedCell_exists_coord_ne_zero x₂.1 (by
          have hle : ‖x₂.1‖ ≤ 1 := x₂.2
          have hnot : ¬ ‖x₂.1‖ < 1 := hx₂
          linarith))))
  · by_cases hx₂ : ‖x₂.1‖ < 1
    · unfold closedCellChartAt
      rw [dif_neg hx₁, dif_pos hx₂]
      exact closedCellBoundaryInterior_transition_mem_groupoid
        (Classical.choose (closedCell_exists_coord_ne_zero x₁.1 (by
          have hle : ‖x₁.1‖ ≤ 1 := x₁.2
          have hnot : ¬ ‖x₁.1‖ < 1 := hx₁
          linarith))) (0 < x₁.1 (Classical.choose (closedCell_exists_coord_ne_zero x₁.1 (by
          have hle : ‖x₁.1‖ ≤ 1 := x₁.2
          have hnot : ¬ ‖x₁.1‖ < 1 := hx₁
          linarith))))
    · unfold closedCellChartAt
      rw [dif_neg hx₁, dif_neg hx₂]
      exact closedCellBoundaryBoundary_transition_mem_groupoid
        (Classical.choose (closedCell_exists_coord_ne_zero x₁.1 (by
          have hle : ‖x₁.1‖ ≤ 1 := x₁.2
          have hnot : ¬ ‖x₁.1‖ < 1 := hx₁
          linarith))) (0 < x₁.1 (Classical.choose (closedCell_exists_coord_ne_zero x₁.1 (by
          have hle : ‖x₁.1‖ ≤ 1 := x₁.2
          have hnot : ¬ ‖x₁.1‖ < 1 := hx₁
          linarith))))
        (Classical.choose (closedCell_exists_coord_ne_zero x₂.1 (by
          have hle : ‖x₂.1‖ ≤ 1 := x₂.2
          have hnot : ¬ ‖x₂.1‖ < 1 := hx₂
          linarith))) (0 < x₂.1 (Classical.choose (closedCell_exists_coord_ne_zero x₂.1 (by
          have hle : ‖x₂.1‖ ≤ 1 := x₂.2
          have hnot : ¬ ‖x₂.1‖ < 1 := hx₂
          linarith))))

theorem closedCellHasGroupoid (m : ℕ) :
    @HasGroupoid (EuclideanHalfSpace (m + 1)) _ (ClosedCell (m + 1)) _
      (closedCellChartedSpaceSucc m) (contDiffGroupoid (⊤ : ℕ∞)
        (modelWithCornersEuclideanHalfSpace (m + 1))) := by
  letI := closedCellChartedSpaceSucc m
  refine ⟨?_⟩
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  exact closedCellChart_transition_mem_groupoid x₁ x₂

theorem closedCellIsManifold (m : ℕ) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (m + 1))) _ _ (EuclideanHalfSpace (m + 1)) _
      (modelWithCornersEuclideanHalfSpace (m + 1)) (⊤ : ℕ∞) (ClosedCell (m + 1)) _
      (closedCellChartedSpaceSucc m) := by
  letI := closedCellChartedSpaceSucc m
  exact { toHasGroupoid := closedCellHasGroupoid m }

theorem closedCellBoundaryInvValue_contDiffOn {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (s : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        (closedCellBoundaryInvValue m e s y : EuclideanSpace ℝ (Fin (m + 1))))
      {y : EuclideanSpace ℝ (Fin (m + 1)) |
        0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} := by
  have htail : ContDiff ℝ (⊤ : ℕ∞) (closedCellTail m) := closedCellTail_contDiff (m := m)
  have hargAll : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        1 - y (0 : Fin (m + 1))) := by
      exact (contDiff_const.sub (by fun_prop))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        ‖closedCellTail m y‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp htail
    exact h1.sub h2
  have harg : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2)
      {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} :=
    hargAll.contDiffOn.mono (Set.subset_univ _)
  have hsqrt : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
      {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} := by
    intro y hy
    have hc : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2)
        {z | 0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} y := harg y hy
    exact (ContDiffWithinAt.sqrt hc (ne_of_gt hy))
  have hfirst : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (s * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2),
        closedCellTail m y)) {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} := by
    have hsmul : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        s * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
        {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} := by
      intro y hy
      simpa [mul_comm] using (hsqrt y hy).mul (contDiffWithinAt_const (c := s))
    exact hsmul.prodMk (htail.contDiffOn.mono (Set.subset_univ _))
  have hcons : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (s * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
        (closedCellTail m y)) {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} :=
    (closedCellCons_contDiff (m := m)).contDiffOn.comp hfirst (by intro y hy; exact Set.mem_univ _)
  have hperm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellPermute e.symm (closedCellCons m (s * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
        (closedCellTail m y))) {y | 0 < 1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2} :=
    (closedCellPermute_contDiff e.symm).contDiffOn.comp hcons (by intro y hy; exact Set.mem_univ _)
  have hdef : (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (closedCellBoundaryInvValue m e s y : EuclideanSpace ℝ (Fin (m + 1)))) =
      fun y => closedCellPermute e.symm
        (closedCellCons m (s * Real.sqrt (1 - y (0 : Fin (m + 1)) - ‖closedCellTail m y‖ ^ 2))
          (closedCellTail m y)) := by
    funext y
    rfl
  rw [hdef]
  exact hperm

theorem closedCellInteriorChart_symm_val {m : ℕ} (y : EuclideanHalfSpace (m + 1))
    (hy : y ∈ (closedCellInteriorChart m).target) :
    ((closedCellInteriorChart m).symm y : EuclideanSpace ℝ (Fin (m + 1))) =
      closedCellShiftSucc m (-1) y.1 := by
  dsimp [closedCellInteriorChart]
  rw [closedCellProject_of_mem (le_of_lt hy)]

theorem closedCellBoundaryChart_symm_val {m : ℕ} (i : Fin (m + 1)) (σ : Bool)
    (y : EuclideanHalfSpace (m + 1)) (hy : y ∈ (closedCellBoundaryChart m i σ).target) :
    ((closedCellBoundaryChart m i σ).symm y : EuclideanSpace ℝ (Fin (m + 1))) =
      closedCellBoundaryInvValue m (Equiv.swap i (0 : Fin (m + 1))) (closedCellSign σ) y.1 := by
  dsimp [closedCellBoundaryChart]
  rw [closedCellProject_of_mem (closedCellBoundaryInvValue_norm_le_one (Equiv.swap i (0 : Fin (m + 1)))
    (by
      dsimp [closedCellSign]
      exact closedCellSign_sq σ) y.1 hy.2 y.2)]

theorem modelWithCornersEuclideanHalfSpace_symm_range {m : ℕ}
    (z : EuclideanSpace ℝ (Fin (m + 1)))
    (hz : z ∈ Set.range (modelWithCornersEuclideanHalfSpace (m + 1))) :
    (modelWithCornersEuclideanHalfSpace (m + 1)).symm z =
      (⟨z, by
        rcases hz with ⟨w, hw⟩
        rw [← hw]
        exact w.2⟩ : EuclideanHalfSpace (m + 1)) := by
  apply Subtype.ext
  rcases hz with ⟨w, hw⟩
  have hz' : z = (modelWithCornersEuclideanHalfSpace (m + 1)) w := hw.symm
  subst hz'
  exact congrArg (fun t : EuclideanHalfSpace (m + 1) => t.1)
    ((modelWithCornersEuclideanHalfSpace (m + 1)).left_inv w)

theorem closedCellInteriorChart_symm_smooth {m : ℕ} :
    ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (⊤ : ℕ∞)
      (fun y : EuclideanHalfSpace (m + 1) =>
        ((closedCellInteriorChart m).symm y : EuclideanSpace ℝ (Fin (m + 1))))
      (closedCellInteriorChart m).target := by
  classical
  intro y hy
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellShiftSucc m (-1) z) := closedCellShiftSucc_contDiff (-1)
  have hcont : Continuous I.symm := (modelWithCornersEuclideanHalfSpace (m + 1)).continuous_invFun
  have hmemT : I.symm (I y) ∈ (closedCellInteriorChart m).target := by
    simpa [I, (modelWithCornersEuclideanHalfSpace (m + 1)).left_inv y] using hy
  have hopen : IsOpen (I.symm ⁻¹' (closedCellInteriorChart m).target) :=
    Continuous.isOpen_preimage hcont (closedCellInteriorChart m).target (closedCellInteriorChart m).open_target
  have hmem : (I y) ∈ I.symm ⁻¹' (closedCellInteriorChart m).target := hmemT
  let S : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    (I.symm ⁻¹' (closedCellInteriorChart m).target) ∩ Set.range I
  have hS : S ∈ nhdsWithin (I y) (Set.range I) := by
    have hTopen : I.symm ⁻¹' (closedCellInteriorChart m).target ∈ nhds (I y) := hopen.mem_nhds hmem
    have hTuniv : I.symm ⁻¹' (closedCellInteriorChart m).target ∈ nhdsWithin (I y) Set.univ := by
      simpa [nhdsWithin_univ] using hTopen
    have hT' : I.symm ⁻¹' (closedCellInteriorChart m).target ∈ nhdsWithin (I y) (Set.range I) :=
      nhdsWithin_mono (I y) (Set.subset_univ (Set.range I)) hTuniv
    exact Filter.inter_mem hT' self_mem_nhdsWithin
  have hagree : (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
      ((closedCellInteriorChart m).symm (I.symm z) : EuclideanSpace ℝ (Fin (m + 1)))) =ᶠ[nhdsWithin (I y) (Set.range I)]
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) => closedCellShiftSucc m (-1) z) := by
    refine Filter.eventuallyEq_of_mem hS ?_
    intro z hz
    have hzmem : z ∈ (I.symm ⁻¹' (closedCellInteriorChart m).target) ∩ Set.range I := hz
    have hzt : I.symm z ∈ (closedCellInteriorChart m).target := hzmem.1
    have hzrange : z ∈ Set.range I := hzmem.2
    have hI := modelWithCornersEuclideanHalfSpace_symm_range z hzrange
    have hcoord : (I.symm z).1 = z := by
      rw [hI]
    have hsymm := closedCellInteriorChart_symm_val (m := m) (I.symm z) hzt
    simpa [hcoord] using hsymm
  have hpoint : ((closedCellInteriorChart m).symm (I.symm (I y)) : EuclideanSpace ℝ (Fin (m + 1))) =
      closedCellShiftSucc m (-1) (I y) := by
    have hcoord : (I.symm (I y)).1 = I y := by
      change (I.symm (I y)).1 = y.1
      rw [(modelWithCornersEuclideanHalfSpace (m + 1)).left_inv y]
    have hsymm := closedCellInteriorChart_symm_val (m := m) (I.symm (I y)) hmemT
    rw [hcoord] at hsymm
    exact hsymm
  have hrep : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((closedCellInteriorChart m).symm (I.symm z) : EuclideanSpace ℝ (Fin (m + 1))))
      (Set.range I) (I y) := by
    have hlin' : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin (m + 1)) => closedCellShiftSucc m (-1) z)
        (Set.range I) (I y) := hlin.contDiffWithinAt
    exact ContDiffWithinAt.congr_of_eventuallyEq hlin' hagree hpoint
  rw [contMDiffWithinAt_iff]
  constructor
  · have h1 : ContinuousAt (closedCellInteriorChart m).symm y :=
      (closedCellInteriorChart m).continuousAt_symm hy
    exact (continuous_subtype_val.continuousAt.comp h1).continuousWithinAt
  · have hext : (extChartAt (modelWithCornersEuclideanHalfSpace (m + 1)) y) =
        (modelWithCornersEuclideanHalfSpace (m + 1)).toPartialEquiv := by
      dsimp [extChartAt, OpenPartialHomeomorph.extend]
      simp
    have hdom : (I.symm ⁻¹' (closedCellInteriorChart m).target ∩ Set.range I) ⊆ Set.range I := by
      intro z hz
      exact hz.2
    rw [show (extChartAt (modelWithCornersEuclideanHalfSpace (m + 1)) y).symm =
        (modelWithCornersEuclideanHalfSpace (m + 1)).symm from congrArg PartialEquiv.symm hext]
    dsimp [I] at hrep hdom ⊢
    change ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((closedCellInteriorChart m).symm ((modelWithCornersEuclideanHalfSpace (m + 1)).symm z) :
          EuclideanSpace ℝ (Fin (m + 1))))
      ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹' (closedCellInteriorChart m).target ∩
        Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))
      ((modelWithCornersEuclideanHalfSpace (m + 1)) y)
    simpa using (hrep.mono hdom)

theorem closedCellBoundaryChart_symm_smooth {m : ℕ} (i : Fin (m + 1)) (σ : Bool) :
    ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (⊤ : ℕ∞)
      (fun y : EuclideanHalfSpace (m + 1) =>
        ((closedCellBoundaryChart m i σ).symm y : EuclideanSpace ℝ (Fin (m + 1))))
      (closedCellBoundaryChart m i σ).target := by
  classical
  intro y hy
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m + 1))) (EuclideanHalfSpace (m + 1)) :=
    modelWithCornersEuclideanHalfSpace (m + 1)
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (0 : Fin (m + 1))
  let s : ℝ := closedCellSign σ
  have hargAll : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        1 - z (0 : Fin (m + 1))) := by
      exact (contDiff_const.sub (by fun_prop))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        ‖closedCellTail m z‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (closedCellTail_contDiff (m := m))
    exact h1.sub h2
  have hDopen : IsOpen {z : EuclideanSpace ℝ (Fin (m + 1)) |
      0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} := by
    exact IsOpen.preimage hargAll.continuous isOpen_Ioi
  have hiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        (closedCellBoundaryInvValue m e s z : EuclideanSpace ℝ (Fin (m + 1))))
      {z : EuclideanSpace ℝ (Fin (m + 1)) |
        0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} := by
    simpa [e, s] using (closedCellBoundaryInvValue_contDiffOn (m := m) e s)
  have hcont : Continuous I.symm := (modelWithCornersEuclideanHalfSpace (m + 1)).continuous_invFun
  have hmemT : I.symm (I y) ∈ (closedCellBoundaryChart m i σ).target := by
    simpa [I, (modelWithCornersEuclideanHalfSpace (m + 1)).left_inv y] using hy
  have hmem : (I y) ∈ I.symm ⁻¹' (closedCellBoundaryChart m i σ).target := hmemT
  have hz0inD : (I y) ∈ {z : EuclideanSpace ℝ (Fin (m + 1)) |
      0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} := by
    simpa [I] using hy.2
  have hf : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        (closedCellBoundaryInvValue m e s z : EuclideanSpace ℝ (Fin (m + 1))))
      (Set.range I) (I y) := by
    have hbase : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
          (closedCellBoundaryInvValue m e s z : EuclideanSpace ℝ (Fin (m + 1))))
        {z : EuclideanSpace ℝ (Fin (m + 1)) |
          0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} (I y) :=
      hiv (I y) hz0inD
    have hDnhds : {z : EuclideanSpace ℝ (Fin (m + 1)) |
        0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} ∈ nhds (I y) :=
      hDopen.mem_nhds hz0inD
    have hDuniv : {z : EuclideanSpace ℝ (Fin (m + 1)) |
        0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} ∈
        nhdsWithin (I y) Set.univ := by
      simpa [nhdsWithin_univ] using hDnhds
    have hDrange : {z : EuclideanSpace ℝ (Fin (m + 1)) |
        0 < 1 - z (0 : Fin (m + 1)) - ‖closedCellTail m z‖ ^ 2} ∈
        nhdsWithin (I y) (Set.range I) :=
      nhdsWithin_mono (I y) (Set.subset_univ (Set.range I)) hDuniv
    exact hbase.mono_of_mem_nhdsWithin hDrange
  have hopen : IsOpen (I.symm ⁻¹' (closedCellBoundaryChart m i σ).target) :=
    Continuous.isOpen_preimage hcont (closedCellBoundaryChart m i σ).target
      (closedCellBoundaryChart m i σ).open_target
  let S : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    (I.symm ⁻¹' (closedCellBoundaryChart m i σ).target) ∩ Set.range I
  have hS : S ∈ nhdsWithin (I y) (Set.range I) := by
    have hTopen : I.symm ⁻¹' (closedCellBoundaryChart m i σ).target ∈ nhds (I y) :=
      hopen.mem_nhds hmem
    have hTuniv : I.symm ⁻¹' (closedCellBoundaryChart m i σ).target ∈
        nhdsWithin (I y) Set.univ := by
      simpa [nhdsWithin_univ] using hTopen
    have hT' : I.symm ⁻¹' (closedCellBoundaryChart m i σ).target ∈
        nhdsWithin (I y) (Set.range I) :=
      nhdsWithin_mono (I y) (Set.subset_univ (Set.range I)) hTuniv
    exact Filter.inter_mem hT' self_mem_nhdsWithin
  have hagree : (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
      ((closedCellBoundaryChart m i σ).symm (I.symm z) : EuclideanSpace ℝ (Fin (m + 1)))) =ᶠ[nhdsWithin (I y) (Set.range I)]
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        (closedCellBoundaryInvValue m e s z : EuclideanSpace ℝ (Fin (m + 1)))) := by
    refine Filter.eventuallyEq_of_mem hS ?_
    intro z hz
    have hzt : I.symm z ∈ (closedCellBoundaryChart m i σ).target := hz.1
    have hzrange : z ∈ Set.range I := hz.2
    have hI := modelWithCornersEuclideanHalfSpace_symm_range z hzrange
    have hcoord : (I.symm z).1 = z := by
      rw [hI]
    have hsymm := closedCellBoundaryChart_symm_val (m := m) i σ (I.symm z) hzt
    simpa [e, s, hcoord] using hsymm
  have hpoint : ((closedCellBoundaryChart m i σ).symm (I.symm (I y)) :
        EuclideanSpace ℝ (Fin (m + 1))) = closedCellBoundaryInvValue m e s (I y) := by
    have hcoord : (I.symm (I y)).1 = I y := by
      change (I.symm (I y)).1 = y.1
      rw [(modelWithCornersEuclideanHalfSpace (m + 1)).left_inv y]
    have hsymm := closedCellBoundaryChart_symm_val (m := m) i σ (I.symm (I y)) hmemT
    rw [hcoord] at hsymm
    simpa [e, s] using hsymm
  have hrep : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((closedCellBoundaryChart m i σ).symm (I.symm z) : EuclideanSpace ℝ (Fin (m + 1))))
      (Set.range I) (I y) := by
    exact ContDiffWithinAt.congr_of_eventuallyEq hf hagree hpoint
  rw [contMDiffWithinAt_iff]
  constructor
  · have h1 : ContinuousAt (closedCellBoundaryChart m i σ).symm y :=
      (closedCellBoundaryChart m i σ).continuousAt_symm hy
    exact (continuous_subtype_val.continuousAt.comp h1).continuousWithinAt
  · have hext : (extChartAt (modelWithCornersEuclideanHalfSpace (m + 1)) y) =
        (modelWithCornersEuclideanHalfSpace (m + 1)).toPartialEquiv := by
      dsimp [extChartAt, OpenPartialHomeomorph.extend]
      simp
    have hdom : (I.symm ⁻¹' (closedCellBoundaryChart m i σ).target ∩ Set.range I) ⊆
        Set.range I := by
      intro z hz
      exact hz.2
    rw [show (extChartAt (modelWithCornersEuclideanHalfSpace (m + 1)) y).symm =
        (modelWithCornersEuclideanHalfSpace (m + 1)).symm from congrArg PartialEquiv.symm hext]
    dsimp [I] at hrep hdom ⊢
    change ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((closedCellBoundaryChart m i σ).symm ((modelWithCornersEuclideanHalfSpace (m + 1)).symm z) :
          EuclideanSpace ℝ (Fin (m + 1))))
      ((modelWithCornersEuclideanHalfSpace (m + 1)).symm ⁻¹' (closedCellBoundaryChart m i σ).target ∩
        Set.range (modelWithCornersEuclideanHalfSpace (m + 1)))
      ((modelWithCornersEuclideanHalfSpace (m + 1)) y)
    simpa using (hrep.mono hdom)

theorem closedCellInclusion_contMDiff (m : ℕ) :
    @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin (m + 1))) _ _
      (EuclideanHalfSpace (m + 1)) _ (modelWithCornersEuclideanHalfSpace (m + 1))
      (ClosedCell (m + 1)) _ (closedCellChartedSpaceSucc m)
      (EuclideanSpace ℝ (Fin (m + 1))) _ _ (EuclideanSpace ℝ (Fin (m + 1))) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (EuclideanSpace ℝ (Fin (m + 1))) _ _
      (⊤ : ℕ∞) (fun v : ClosedCell (m + 1) => (v : EuclideanSpace ℝ (Fin (m + 1)))) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpaceSucc m
  letI : IsManifold (modelWithCornersEuclideanHalfSpace (m + 1)) (⊤ : ℕ∞)
      (ClosedCell (m + 1)) :=
    closedCellIsManifold m
  intro x
  by_cases hx : ‖x.1‖ < 1
  · have hchart : chartAt (H := EuclideanHalfSpace (m + 1)) (M := ClosedCell (m + 1)) x =
        closedCellInteriorChart m := by
      change closedCellChartAt x = closedCellInteriorChart m
      rw [closedCellChartAt, dif_pos hx]
    have hc : ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
        (modelWithCornersEuclideanHalfSpace (m + 1)) (⊤ : ℕ∞)
        (closedCellInteriorChart m) (closedCellInteriorChart m).source := by
      have h := contMDiffOn_chart (I := modelWithCornersEuclideanHalfSpace (m + 1))
        (H := EuclideanHalfSpace (m + 1)) (M := ClosedCell (m + 1)) (n := (⊤ : ℕ∞)) (x := x)
      simpa [hchart] using h
    have hst : (closedCellInteriorChart m).source ⊆
        (closedCellInteriorChart m) ⁻¹' (closedCellInteriorChart m).target := by
      intro y hy
      exact (closedCellInteriorChart m).mapsTo hy
    have hcomp : ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (⊤ : ℕ∞)
        (fun v : ClosedCell (m + 1) =>
          ((closedCellInteriorChart m).symm ((closedCellInteriorChart m) v) :
            EuclideanSpace ℝ (Fin (m + 1))))
        (closedCellInteriorChart m).source :=
      (closedCellInteriorChart_symm_smooth (m := m)).comp hc hst
    have hcong : ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (⊤ : ℕ∞)
        (fun v : ClosedCell (m + 1) => (v : EuclideanSpace ℝ (Fin (m + 1))))
        (closedCellInteriorChart m).source := by
      refine hcomp.congr ?_
      intro y hy
      change (y : EuclideanSpace ℝ (Fin (m + 1))) =
        ((closedCellInteriorChart m).symm ((closedCellInteriorChart m) y) :
          EuclideanSpace ℝ (Fin (m + 1)))
      rw [(closedCellInteriorChart m).left_inv hy]
    exact hcong.contMDiffAt ((closedCellInteriorChart m).open_source.mem_nhds hx)
  · let i : Fin (m + 1) := Classical.choose (closedCell_exists_coord_ne_zero x.1 (by
      have hle : ‖x.1‖ ≤ 1 := x.2
      have hnot : ¬ ‖x.1‖ < 1 := hx
      linarith))
    let σ : Bool := 0 < x.1 i
    have hchart : chartAt (H := EuclideanHalfSpace (m + 1)) (M := ClosedCell (m + 1)) x =
        closedCellBoundaryChart m i σ := by
      change closedCellChartAt x = closedCellBoundaryChart m i σ
      rw [closedCellChartAt, dif_neg hx]
    have hxsrc : x ∈ (closedCellBoundaryChart m i σ).source := by
      simpa [hchart] using (mem_chart_source (H := EuclideanHalfSpace (m + 1))
        (M := ClosedCell (m + 1)) x)
    have hc : ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
        (modelWithCornersEuclideanHalfSpace (m + 1)) (⊤ : ℕ∞)
        (closedCellBoundaryChart m i σ) (closedCellBoundaryChart m i σ).source := by
      have h := contMDiffOn_chart (I := modelWithCornersEuclideanHalfSpace (m + 1))
        (H := EuclideanHalfSpace (m + 1)) (M := ClosedCell (m + 1)) (n := (⊤ : ℕ∞)) (x := x)
      simpa [hchart] using h
    have hst : (closedCellBoundaryChart m i σ).source ⊆
        (closedCellBoundaryChart m i σ) ⁻¹' (closedCellBoundaryChart m i σ).target := by
      intro y hy
      exact (closedCellBoundaryChart m i σ).mapsTo hy
    have hcomp : ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (⊤ : ℕ∞)
        (fun v : ClosedCell (m + 1) =>
          ((closedCellBoundaryChart m i σ).symm ((closedCellBoundaryChart m i σ) v) :
            EuclideanSpace ℝ (Fin (m + 1))))
        (closedCellBoundaryChart m i σ).source :=
      (closedCellBoundaryChart_symm_smooth (m := m) i σ).comp hc hst
    have hcong : ContMDiffOn (modelWithCornersEuclideanHalfSpace (m + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (⊤ : ℕ∞)
        (fun v : ClosedCell (m + 1) => (v : EuclideanSpace ℝ (Fin (m + 1))))
        (closedCellBoundaryChart m i σ).source := by
      refine hcomp.congr ?_
      intro y hy
      change (y : EuclideanSpace ℝ (Fin (m + 1))) =
        ((closedCellBoundaryChart m i σ).symm ((closedCellBoundaryChart m i σ) y) :
          EuclideanSpace ℝ (Fin (m + 1)))
      rw [(closedCellBoundaryChart m i σ).left_inv hy]
    exact hcong.contMDiffAt ((closedCellBoundaryChart m i σ).open_source.mem_nhds hxsrc)

theorem hasGroupoid_prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H' M'] {n : WithTop ℕ∞}
    [HasGroupoid M (contDiffGroupoid n I)] [HasGroupoid M' (contDiffGroupoid n I')] :
    HasGroupoid (M × M') (contDiffGroupoid n (I.prod I')) := by
  refine ⟨?_⟩
  intro e e' he he'
  rcases he with ⟨e₁, he₁, e₂, he₂, rfl⟩
  rcases he' with ⟨e₁', he₁', e₂', he₂', rfl⟩
  change ((e₁.prod e₂).symm ≫ₕ (e₁'.prod e₂')) ∈ contDiffGroupoid n (I.prod I')
  rw [OpenPartialHomeomorph.prod_symm]
  rw [OpenPartialHomeomorph.prod_trans]
  change ((e₁.symm ≫ₕ e₁').prod (e₂.symm ≫ₕ e₂') :
      OpenPartialHomeomorph (ModelProd H H') (ModelProd H H')) ∈
    contDiffGroupoid n (I.prod I')
  rw [contDiffGroupoid]
  apply mem_groupoid_of_pregroupoid.mpr
  let t₁ : OpenPartialHomeomorph H H := e₁.symm ≫ₕ e₁'
  let t₂ : OpenPartialHomeomorph H' H' := e₂.symm ≫ₕ e₂'
  have ht₁ : (e₁.symm ≫ₕ e₁') ∈ contDiffGroupoid n I := HasGroupoid.compatible he₁ he₁'
  have ht₂ : (e₂.symm ≫ₕ e₂') ∈ contDiffGroupoid n I' := HasGroupoid.compatible he₂ he₂'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at ht₁ ht₂
  have hr : Set.range (I.prod I') = Set.range I ×ˢ Set.range I' := by
    change Set.range (Prod.map (I : H → E) (I' : H' → E')) = Set.range I ×ˢ Set.range I'
    exact Set.range_prodMap
  constructor
  · let s₁ : Set E := (I.symm ⁻¹' t₁.source ∩ Set.range I)
    let s₂ : Set E' := (I'.symm ⁻¹' t₂.source ∩ Set.range I')
    let s : Set (E × E') := {p | p.1 ∈ s₁ ∧ p.2 ∈ s₂}
    have hf₁ : ContDiffOn 𝕜 n (I ∘ (t₁ : H → H) ∘ I.symm) s₁ := ht₁.1
    have hf₂ : ContDiffOn 𝕜 n (I' ∘ (t₂ : H' → H') ∘ I'.symm) s₂ := ht₂.1
    have hprod : ContDiffOn 𝕜 n
        (fun p : E × E' => ((I ∘ (t₁ : H → H) ∘ I.symm) p.1,
          (I' ∘ (t₂ : H' → H') ∘ I'.symm) p.2)) s :=
      (ContDiffOn.prodMap hf₁ hf₂).mono (by
        intro p hp
        exact hp)
    have hD : (I.prod I').symm ⁻¹' (t₁.prod t₂).source ∩ Set.range (I.prod I') = s := by
      ext p
      constructor
      · intro hp
        have hpsrc : (I.prod I').symm p ∈ (t₁.prod t₂).source := hp.1
        have hprange : p ∈ Set.range (I.prod I') := hp.2
        change p.1 ∈ s₁ ∧ p.2 ∈ s₂
        constructor
        · constructor
          · change I.symm p.1 ∈ t₁.source
            have hsymm : (I.prod I').symm p = (I.symm p.1, I'.symm p.2) := rfl
            have hsrc : (I.symm p.1, I'.symm p.2) ∈ (t₁.prod t₂).source := by
              rwa [hsymm] at hpsrc
            have hpsrc' : (I.symm p.1, I'.symm p.2) ∈ t₁.source ×ˢ t₂.source := by
              simpa [PartialEquiv.prod_source] using hsrc
            exact hpsrc'.1
          · rw [hr] at hprange
            exact hprange.1
        · constructor
          · change I'.symm p.2 ∈ t₂.source
            have hsymm : (I.prod I').symm p = (I.symm p.1, I'.symm p.2) := rfl
            have hsrc : (I.symm p.1, I'.symm p.2) ∈ (t₁.prod t₂).source := by
              rwa [hsymm] at hpsrc
            have hpsrc' : (I.symm p.1, I'.symm p.2) ∈ t₁.source ×ˢ t₂.source := by
              simpa [PartialEquiv.prod_source] using hsrc
            exact hpsrc'.2
          · rw [hr] at hprange
            exact hprange.2
      · intro hp
        constructor
        · change (I.prod I').symm p ∈ (t₁.prod t₂).source
          have hsymm : (I.prod I').symm p = (I.symm p.1, I'.symm p.2) := rfl
          rw [hsymm]
          simpa [PartialEquiv.prod_source] using ⟨hp.1.1, hp.2.1⟩
        · rw [hr]
          exact ⟨hp.1.2, hp.2.2⟩
    have hfun : (I.prod I') ∘ (t₁.prod t₂) ∘ (I.prod I').symm =
        fun p : E × E' => ((I ∘ (t₁ : H → H) ∘ I.symm) p.1,
          (I' ∘ (t₂ : H' → H') ∘ I'.symm) p.2) := by
      funext p
      rfl
    change ContDiffOn 𝕜 n ((I.prod I') ∘ (t₁.prod t₂) ∘ (I.prod I').symm)
      ((I.prod I').symm ⁻¹' (t₁.prod t₂).source ∩ Set.range (I.prod I'))
    rw [hD, hfun]
    exact hprod
  · change (contDiffPregroupoid n (I.prod I')).property
      (((e₁.symm ≫ₕ e₁').prod (e₂.symm ≫ₕ e₂')).symm)
      (((e₁.symm ≫ₕ e₁').prod (e₂.symm ≫ₕ e₂')).target)
    rw [OpenPartialHomeomorph.prod_symm]
    have htarget : (t₁.prod t₂).target = (t₁.symm.prod t₂.symm).source := by
      rw [show (t₁.prod t₂).target = (t₁.toPartialEquiv.prod t₂.toPartialEquiv).target from rfl]
      rw [PartialEquiv.prod_target]
      rw [show (t₁.symm.prod t₂.symm).source = (t₁.symm.toPartialEquiv.prod t₂.symm.toPartialEquiv).source from rfl]
      rw [PartialEquiv.prod_source]
      rfl
    rw [htarget]
    change (contDiffPregroupoid n (I.prod I')).property
      (t₁.symm.prod t₂.symm) (t₁.symm.prod t₂.symm).source
    let s₁ : Set E := (I.symm ⁻¹' t₁.symm.source ∩ Set.range I)
    let s₂ : Set E' := (I'.symm ⁻¹' t₂.symm.source ∩ Set.range I')
    let s : Set (E × E') := {p | p.1 ∈ s₁ ∧ p.2 ∈ s₂}
    have hf₁ : ContDiffOn 𝕜 n (I ∘ (t₁.symm : H → H) ∘ I.symm) s₁ := ht₁.2
    have hf₂ : ContDiffOn 𝕜 n (I' ∘ (t₂.symm : H' → H') ∘ I'.symm) s₂ := ht₂.2
    have hprod : ContDiffOn 𝕜 n
        (fun p : E × E' => ((I ∘ (t₁.symm : H → H) ∘ I.symm) p.1,
          (I' ∘ (t₂.symm : H' → H') ∘ I'.symm) p.2)) s :=
      (ContDiffOn.prodMap hf₁ hf₂).mono (by
        intro p hp
        exact hp)
    have hD : (I.prod I').symm ⁻¹' (t₁.symm.prod t₂.symm).source ∩ Set.range (I.prod I') = s := by
      ext p
      constructor
      · intro hp
        have hpsrc : (I.prod I').symm p ∈ (t₁.symm.prod t₂.symm).source := hp.1
        have hprange : p ∈ Set.range (I.prod I') := hp.2
        change p.1 ∈ s₁ ∧ p.2 ∈ s₂
        constructor
        · constructor
          · change I.symm p.1 ∈ t₁.symm.source
            have hsymm : (I.prod I').symm p = (I.symm p.1, I'.symm p.2) := rfl
            have hsrc : (I.symm p.1, I'.symm p.2) ∈ (t₁.symm.prod t₂.symm).source := by
              rwa [hsymm] at hpsrc
            have hpsrc' : (I.symm p.1, I'.symm p.2) ∈ t₁.symm.source ×ˢ t₂.symm.source := by
              simpa [PartialEquiv.prod_source] using hsrc
            exact hpsrc'.1
          · rw [hr] at hprange
            exact hprange.1
        · constructor
          · change I'.symm p.2 ∈ t₂.symm.source
            have hsymm : (I.prod I').symm p = (I.symm p.1, I'.symm p.2) := rfl
            have hsrc : (I.symm p.1, I'.symm p.2) ∈ (t₁.symm.prod t₂.symm).source := by
              rwa [hsymm] at hpsrc
            have hpsrc' : (I.symm p.1, I'.symm p.2) ∈ t₁.symm.source ×ˢ t₂.symm.source := by
              simpa [PartialEquiv.prod_source] using hsrc
            exact hpsrc'.2
          · rw [hr] at hprange
            exact hprange.2
      · intro hp
        constructor
        · change (I.prod I').symm p ∈ (t₁.symm.prod t₂.symm).source
          have hsymm : (I.prod I').symm p = (I.symm p.1, I'.symm p.2) := rfl
          rw [hsymm]
          simpa [PartialEquiv.prod_source] using ⟨hp.1.1, hp.2.1⟩
        · rw [hr]
          exact ⟨hp.1.2, hp.2.2⟩
    have hfun : (I.prod I') ∘ (t₁.symm.prod t₂.symm) ∘ (I.prod I').symm =
        fun p : E × E' => ((I ∘ (t₁.symm : H → H) ∘ I.symm) p.1,
          (I' ∘ (t₂.symm : H' → H') ∘ I'.symm) p.2) := by
      funext p
      rfl
    change ContDiffOn 𝕜 n ((I.prod I') ∘ (t₁.symm.prod t₂.symm) ∘ (I.prod I').symm)
      ((I.prod I').symm ⁻¹' (t₁.symm.prod t₂.symm).source ∩ Set.range (I.prod I'))
    rw [hD, hfun]
    exact hprod

@[reducible]
noncomputable def standardHandleChartedSpaceSucc (m n : ℕ) :
    ChartedSpace (ModelProd (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (n + 1)))
      (ClosedCell (m + 1) × ClosedCell (n + 1)) := by
  letI : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpaceSucc m
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) (ClosedCell (n + 1)) :=
    closedCellChartedSpaceSucc n
  exact prodChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1))
    (EuclideanHalfSpace (n + 1)) (ClosedCell (n + 1))

theorem standardHandleHasGroupoid (m n : ℕ) :
    @HasGroupoid (ModelProd (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (n + 1))) _
      (ClosedCell (m + 1) × ClosedCell (n + 1)) _ (standardHandleChartedSpaceSucc m n)
      (contDiffGroupoid (⊤ : ℕ∞)
        ((modelWithCornersEuclideanHalfSpace (m + 1)).prod
          (modelWithCornersEuclideanHalfSpace (n + 1)))) := by
  letI : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpaceSucc m
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) (ClosedCell (n + 1)) :=
    closedCellChartedSpaceSucc n
  letI : HasGroupoid (ClosedCell (m + 1)) (contDiffGroupoid (⊤ : ℕ∞)
      (modelWithCornersEuclideanHalfSpace (m + 1))) := closedCellHasGroupoid m
  letI : HasGroupoid (ClosedCell (n + 1)) (contDiffGroupoid (⊤ : ℕ∞)
      (modelWithCornersEuclideanHalfSpace (n + 1))) := closedCellHasGroupoid n
  exact hasGroupoid_prod

theorem standardHandleIsManifold (m n : ℕ) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (n + 1))) _ _
      (ModelProd (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (n + 1))) _
      ((modelWithCornersEuclideanHalfSpace (m + 1)).prod
        (modelWithCornersEuclideanHalfSpace (n + 1))) (⊤ : ℕ∞)
      (ClosedCell (m + 1) × ClosedCell (n + 1)) _ (standardHandleChartedSpaceSucc m n) := by
  letI := standardHandleChartedSpaceSucc m n
  exact { toHasGroupoid := standardHandleHasGroupoid m n }

noncomputable def cellBoundarySphereHomeomorph (k : ℕ) :
    CellBoundary k ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 where
  toFun := fun x => ⟨x.1, by
    change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1
    rw [dist_eq_norm, sub_zero]
    exact x.2⟩
  invFun := fun x => ⟨x.1, by
    have hx := x.2
    change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1 at hx
    rw [dist_eq_norm, sub_zero] at hx
    exact hx⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_subtype_val (fun x => by
      change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1
      rw [dist_eq_norm, sub_zero]
      exact x.2)
  continuous_invFun := by
    exact Continuous.subtype_mk continuous_subtype_val (fun x => by
      have hx := x.2
      change dist (x.1 : EuclideanSpace ℝ (Fin k)) 0 = 1 at hx
      rw [dist_eq_norm, sub_zero] at hx
      exact hx)

instance (k : ℕ) : Neg (CellBoundary k) :=
  ⟨fun x => ⟨-x.1, by simp [x.2]⟩⟩

instance (k : ℕ) [NeZero k] :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1) := by
  exact ⟨by
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := by simp
    rw [hfin]
    have hk : 0 < k := NeZero.pos k
    omega⟩

instance (k : ℕ) [NeZero k] : Fact (k = (k - 1) + 1) := by
  exact ⟨by
    have hk : 0 < k := NeZero.pos k
    omega⟩

noncomputable def cellBoundaryChart (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    (v : CellBoundary k) :
    OpenPartialHomeomorph (CellBoundary k) (EuclideanSpace ℝ (Fin (k - 1))) :=
  (cellBoundarySphereHomeomorph k).toOpenPartialHomeomorph ≫ₕ
    stereographic' (k - 1) (cellBoundarySphereHomeomorph k v)

@[reducible]
noncomputable def cellBoundaryChartedSpace (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) where
  atlas := Set.range (fun v : CellBoundary k => cellBoundaryChart k v)
  chartAt := fun v : CellBoundary k => cellBoundaryChart k (-v)
  mem_chart_source := by
    intro v
    have hne : v ≠ -v := by
      intro h
      have h0 : (v : EuclideanSpace ℝ (Fin k)) = 0 := by
        have h2 : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin k)) = 0 := by
          have h' : (v : EuclideanSpace ℝ (Fin k)) = -(v : EuclideanSpace ℝ (Fin k)) :=
            congrArg (fun z : CellBoundary k => (z : EuclideanSpace ℝ (Fin k))) h
          have hplus : (v : EuclideanSpace ℝ (Fin k)) + (v : EuclideanSpace ℝ (Fin k)) = 0 := by
            nth_rewrite 1 [h']
            simp
          simpa [two_smul] using hplus
        exact smul_eq_zero.mp h2 |>.resolve_left (by norm_num)
      have hnorm : ‖(v : EuclideanSpace ℝ (Fin k))‖ = 1 := v.2
      rw [h0] at hnorm
      norm_num at hnorm
    change v ∈ (cellBoundaryChart k (-v)).source
    dsimp [cellBoundaryChart]
    constructor
    · trivial
    · change (cellBoundarySphereHomeomorph k v) ∈
        (stereographic' (k - 1) (cellBoundarySphereHomeomorph k (-v))).source
      rw [stereographic'_source]
      change (cellBoundarySphereHomeomorph k v) ≠ (cellBoundarySphereHomeomorph k (-v))
      exact fun hh => hne (by
        have hh' := congrArg (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 => z.1) hh
        exact Subtype.ext hh')
  chart_mem_atlas := fun v => ⟨-v, rfl⟩

theorem cellBoundaryHasGroupoid (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    @HasGroupoid (EuclideanSpace ℝ (Fin (k - 1))) _ (CellBoundary k) _
      (cellBoundaryChartedSpace k)
      (contDiffGroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1))) := by
  classical
  letI := cellBoundaryChartedSpace k
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1))) ?_
  intro e e' he he'
  rcases he with ⟨v₁, rfl⟩
  rcases he' with ⟨v₂, rfl⟩
  let h : CellBoundary k ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    cellBoundarySphereHomeomorph k
  let s₁ : OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (EuclideanSpace ℝ (Fin (k - 1))) := stereographic' (k - 1) (h v₁)
  let s₂ : OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (EuclideanSpace ℝ (Fin (k - 1))) := stereographic' (k - 1) (h v₂)
  have hmid : h.toOpenPartialHomeomorph.symm ≫ₕ h.toOpenPartialHomeomorph =
      (OpenPartialHomeomorph.refl (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
        OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)) := by
    apply OpenPartialHomeomorph.ext
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · intro x
      change h.toPartialEquiv.toFun (h.toOpenPartialHomeomorph.symm x) = x
      exact h.right_inv x
    · ext x
      simp
  have ht : (cellBoundaryChart k v₁).symm ≫ₕ (cellBoundaryChart k v₂) = s₁.symm ≫ₕ s₂ := by
    dsimp [cellBoundaryChart]
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    change (s₁.symm ≫ₕ h.toOpenPartialHomeomorph.symm) ≫ₕ
        (h.toOpenPartialHomeomorph ≫ₕ s₂) = s₁.symm ≫ₕ s₂
    rw [OpenPartialHomeomorph.trans_assoc]
    rw [← OpenPartialHomeomorph.trans_assoc (e'' := s₂)]
    rw [hmid]
    simp
  rw [ht]
  have hmemOmega : s₁.symm ≫ₕ s₂ ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k - 1)) :=
    (inferInstance : HasGroupoid (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (k - 1)))).compatible ⟨h v₁, rfl⟩ ⟨h v₂, rfl⟩
  have hmemInfty : s₁.symm ≫ₕ s₂ ∈ contDiffGroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1)) :=
    contDiffGroupoid_le (by exact le_top : (⊤ : ℕ∞) ≤ (⊤ : WithTop ℕ∞)) hmemOmega
  have hm : s₁.symm ≫ₕ s₂ ∈ Pregroupoid.groupoid
      (contDiffPregroupoid (↑(⊤ : ℕ∞) : WithTop ℕ∞) (𝓡 (k - 1))) := by
    simpa [contDiffGroupoid] using hmemInfty
  exact (mem_groupoid_of_pregroupoid.mp hm).1

theorem cellBoundaryIsManifold (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (k - 1))) _ _ (EuclideanSpace ℝ (Fin (k - 1))) _
      (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) _ (cellBoundaryChartedSpace k) := by
  letI := cellBoundaryChartedSpace k
  exact { toHasGroupoid := cellBoundaryHasGroupoid k }

theorem cellBoundaryInclusion_contMDiff (k : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)] :
    @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin (k - 1))) _ _ (EuclideanSpace ℝ (Fin (k - 1))) _
      (𝓡 (k - 1)) (CellBoundary k) _ (cellBoundaryChartedSpace k)
      (EuclideanSpace ℝ (Fin k)) _ _ (EuclideanSpace ℝ (Fin k)) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (EuclideanSpace ℝ (Fin k)) _ _
      (⊤ : ℕ∞)
      (fun u : CellBoundary k => (u : EuclideanSpace ℝ (Fin k))) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1)))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    EuclideanSpace.instChartedSpaceSphere (n := k - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : WithTop ℕ∞)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    EuclideanSpace.instIsManifoldSphere (n := k - 1)
  intro u
  let h : CellBoundary k ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    cellBoundarySphereHomeomorph k
  have hchart : chartAt (H := EuclideanSpace ℝ (Fin (k - 1))) (M := CellBoundary k) u =
      cellBoundaryChart k (-u) := rfl
  have hc : ContMDiffOn (𝓡 (k - 1)) (𝓡 (k - 1)) (⊤ : ℕ∞)
      (cellBoundaryChart k (-u)) (cellBoundaryChart k (-u)).source := by
    have h := contMDiffOn_chart (I := 𝓡 (k - 1))
      (H := EuclideanSpace ℝ (Fin (k - 1))) (M := CellBoundary k) (n := (⊤ : ℕ∞)) (x := u)
    simpa [hchart] using h
  let s₀ : OpenPartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
      (EuclideanSpace ℝ (Fin (k - 1))) := stereographic' (k - 1) (h (-u))
  have hs : chartAt (H := EuclideanSpace ℝ (Fin (k - 1)))
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) (h u) = s₀ := by
    dsimp [s₀]
    change stereographic' (k - 1) (-(h u)) = stereographic' (k - 1) (h (-u))
    congr 1
  have hchartDef : cellBoundaryChart k (-u) = h.toOpenPartialHomeomorph ≫ₕ s₀ := by
    rfl
  have hsymm0 : ContMDiffOn (𝓡 (k - 1)) (𝓡 (k - 1)) (⊤ : ℕ∞)
      s₀.symm s₀.target := by
    have hω := contMDiffOn_chart_symm (I := 𝓡 (k - 1))
      (H := EuclideanSpace ℝ (Fin (k - 1)))
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) (n := (⊤ : WithTop ℕ∞)) (x := h u)
    simpa [hs] using hω.of_le (by exact le_top : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hcoe : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 → EuclideanSpace ℝ (Fin k)) Set.univ :=
    contMDiffOn_univ.mpr (contMDiff_coe_sphere (m := (⊤ : ℕ∞)) (n := k - 1))
  have hsymm : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (k - 1)) =>
        ((s₀.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
          EuclideanSpace ℝ (Fin k)))
      s₀.target := by
    refine hcoe.comp hsymm0 ?_
    intro y hy
    trivial
  have htarget : (cellBoundaryChart k (-u)).target = s₀.target := by
    rw [hchartDef]
    simp
  have hval : ∀ y ∈ s₀.target,
      ((cellBoundaryChart k (-u)).symm y : EuclideanSpace ℝ (Fin k)) =
        ((s₀.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
          EuclideanSpace ℝ (Fin k)) := by
    intro y hy
    rw [hchartDef]
    change (((s₀.symm.trans h.toOpenPartialHomeomorph.symm) y : CellBoundary k) :
        EuclideanSpace ℝ (Fin k)) =
      ((s₀.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :
        EuclideanSpace ℝ (Fin k))
    rw [OpenPartialHomeomorph.coe_trans]
    rfl
  have hg : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (k - 1)) =>
        ((cellBoundaryChart k (-u)).symm y : EuclideanSpace ℝ (Fin k)))
      (cellBoundaryChart k (-u)).target := by
    rw [htarget]
    exact hsymm.congr hval
  have hst : (cellBoundaryChart k (-u)).source ⊆
      (cellBoundaryChart k (-u)) ⁻¹' (cellBoundaryChart k (-u)).target := by
    intro y hy
    exact (cellBoundaryChart k (-u)).mapsTo hy
  have hcomp : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun x : CellBoundary k =>
        ((cellBoundaryChart k (-u)).symm ((cellBoundaryChart k (-u)) x) :
          EuclideanSpace ℝ (Fin k)))
      (cellBoundaryChart k (-u)).source :=
    hg.comp hc hst
  have hcong : ContMDiffOn (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun u : CellBoundary k => (u : EuclideanSpace ℝ (Fin k)))
      (cellBoundaryChart k (-u)).source := by
    refine hcomp.congr ?_
    intro y hy
    change (y : EuclideanSpace ℝ (Fin k)) =
      ((cellBoundaryChart k (-u)).symm ((cellBoundaryChart k (-u)) y) :
        EuclideanSpace ℝ (Fin k))
    rw [(cellBoundaryChart k (-u)).left_inv hy]
  exact hcong.contMDiffAt ((cellBoundaryChart k (-u)).open_source.mem_nhds (by
    simpa [hchart] using (mem_chart_source (H := EuclideanSpace ℝ (Fin (k - 1)))
      (M := CellBoundary k) u)))

noncomputable def closedCellReindex (l : ℕ) [Fact (l = (l - 1) + 1)] :
    EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((l - 1) + 1)) :=
  (EuclideanSpace.basisFun (Fin l) ℝ).reindex
    (Equiv.cast (congrArg Fin (Fact.out : l = (l - 1) + 1))) |>.repr

noncomputable def closedCellReindexHomeo (l : ℕ) [Fact (l = (l - 1) + 1)] :
    ClosedCell l ≃ₜ ClosedCell ((l - 1) + 1) := by
  let e : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((l - 1) + 1)) :=
    closedCellReindex l
  refine { toFun := fun x => ⟨e x.1, by
             exact (le_of_eq (e.norm_map x.1)).trans x.2⟩,
           invFun := fun x => ⟨e.symm x.1, by
             exact (le_of_eq (e.symm.norm_map x.1)).trans x.2⟩,
           left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x.1,
           right_inv := by intro x; apply Subtype.ext; exact e.apply_symm_apply x.1,
           continuous_toFun := by
             exact Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) (fun x => by
               exact (le_of_eq (e.norm_map x.1)).trans x.2),
           continuous_invFun := by
             exact Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) (fun x => by
               exact (le_of_eq (e.symm.norm_map x.1)).trans x.2) }

@[reducible]
noncomputable def closedCellChartedSpace (l : ℕ)
    [Fact (l = (l - 1) + 1)] :
    ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) := by
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell ((l - 1) + 1)) :=
    closedCellChartedSpaceSucc (l - 1)
  exact chartedSpaceOfHomeomorph (closedCellReindexHomeo l)

@[reducible]
noncomputable def standardHandleChartedSpace (k l : ℕ)
    [Fact (k = (k - 1) + 1)] [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle k l) := by
  letI : ChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k) :=
    closedCellChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  exact prodChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k)
    (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l)

noncomputable def closedCellZeroHomeo : ClosedCell 0 ≃ₜ EuclideanSpace ℝ (Fin 0) where
  toFun := fun _ => 0
  invFun := fun _ => ⟨0, by simp⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact Subsingleton.elim _ _
  right_inv := by
    intro y
    exact Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

@[reducible]
noncomputable def closedCellZeroChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
  chartedSpaceOfHomeomorph closedCellZeroHomeo

theorem closedCellZeroInclusion_contMDiff :
    @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin 0)) _ _
      (EuclideanSpace ℝ (Fin 0)) _ (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (ClosedCell 0) _ (closedCellZeroChartedSpace)
      (EuclideanSpace ℝ (Fin 0)) _ _ (EuclideanSpace ℝ (Fin 0)) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (EuclideanSpace ℝ (Fin 0)) _ _
      (⊤ : ℕ∞)
      (fun x : ClosedCell 0 => (x : EuclideanSpace ℝ (Fin 0))) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  letI : IsManifold (𝓡 0) (⊤ : ℕ∞) (ClosedCell 0) :=
    isManifoldOfHomeomorph (𝓡 0) closedCellZeroHomeo
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro x y
    apply (contDiffOn_const (𝕜 := ℝ) (n := (⊤ : ℕ∞))
      (c := (0 : EuclideanSpace ℝ (Fin 0)))).congr
    intro z hz
    exact Subsingleton.elim _ _

@[reducible]
noncomputable def standardHandleZeroChartedSpace (l : ℕ) [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle 0 l) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  exact prodChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0)
    (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l)

@[reducible]
noncomputable def standardHandleTopChartedSpace (k : ℕ) [Fact (k = (k - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanSpace ℝ (Fin 0)))
      (StandardHandle k 0) := by
  letI : ChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k) :=
    closedCellChartedSpace k
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  exact prodChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k)
    (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0)

noncomputable def finSubSelfIso (n : ℕ) :
    EuclideanSpace ℝ (Fin (n - n)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 0) :=
  (EuclideanSpace.basisFun (Fin (n - n)) ℝ).reindex
    (Equiv.cast (congrArg Fin (Nat.sub_self n))) |>.repr

noncomputable def closedCellSubSelfHomeo (n : ℕ) : ClosedCell (n - n) ≃ₜ ClosedCell 0 := by
  let e : EuclideanSpace ℝ (Fin (n - n)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 0) := finSubSelfIso n
  refine { toFun := fun x => ⟨e x.1, by
             exact (le_of_eq (e.norm_map x.1)).trans x.2⟩,
           invFun := fun x => ⟨e.symm x.1, by
             exact (le_of_eq (e.symm.norm_map x.1)).trans x.2⟩,
           left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x.1,
           right_inv := by intro x; apply Subtype.ext; exact e.apply_symm_apply x.1,
           continuous_toFun := by
             exact Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) (fun x => by
               exact (le_of_eq (e.norm_map x.1)).trans x.2),
           continuous_invFun := by
             exact Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) (fun x => by
               exact (le_of_eq (e.symm.norm_map x.1)).trans x.2) }

@[reducible]
noncomputable def closedCellSubSelfChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell (n - n)) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) := closedCellZeroChartedSpace
  exact chartedSpaceOfHomeomorph (closedCellSubSelfHomeo n)

@[reducible]
noncomputable def standardHandleTopSubChartedSpace (n : ℕ) [Fact (n = (n - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanHalfSpace ((n - 1) + 1)) (EuclideanSpace ℝ (Fin 0)))
      (StandardHandle n (n - n)) := by
  letI : ChartedSpace (EuclideanHalfSpace ((n - 1) + 1)) (ClosedCell n) :=
    closedCellChartedSpace n
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell (n - n)) :=
    closedCellSubSelfChartedSpace n
  exact prodChartedSpace (EuclideanHalfSpace ((n - 1) + 1)) (ClosedCell n)
    (EuclideanSpace ℝ (Fin 0)) (ClosedCell (n - n))

theorem closedCellSubSelfInclusion_contMDiff (n : ℕ) :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin 0)) _ _ (EuclideanSpace ℝ (Fin 0)) _ (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (ClosedCell (n - n)) _ (closedCellSubSelfChartedSpace n)
      (EuclideanSpace ℝ (Fin (n - n))) _ _ (EuclideanSpace ℝ (Fin (n - n))) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - n)))) (EuclideanSpace ℝ (Fin (n - n))) _ _
      (⊤ : ℕ∞)
      (fun v : ClosedCell (n - n) => (v : EuclideanSpace ℝ (Fin (n - n)))) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) := closedCellZeroChartedSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell (n - n)) :=
    chartedSpaceOfHomeomorph (closedCellSubSelfHomeo n)
  letI : IsManifold (𝓡 0) (⊤ : ℕ∞) (ClosedCell 0) := isManifoldOfHomeomorph (𝓡 0) closedCellZeroHomeo
  let h : ClosedCell (n - n) ≃ₜ ClosedCell 0 := closedCellSubSelfHomeo n
  let e : EuclideanSpace ℝ (Fin 0) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n - n)) := (finSubSelfIso n).symm
  have hh : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (⊤ : ℕ∞)
      (fun x : ClosedCell (n - n) => (h x : ClosedCell 0)) := by
    exact contMDiff_homeomorph_of_chartedSpaceOfHomeomorph (H := EuclideanSpace ℝ (Fin 0))
      (h := h) (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (⊤ : ℕ∞)
  have hz : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (⊤ : ℕ∞)
      (fun x : ClosedCell 0 => (x : EuclideanSpace ℝ (Fin 0))) :=
    closedCellZeroInclusion_contMDiff
  have he : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - n)))) (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 0) => e x) := by
    exact contMDiff_iff_contDiff.mpr (e.contDiff)
  have hcomp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - n)))) (⊤ : ℕ∞)
      (fun x : ClosedCell (n - n) => e ((h x : ClosedCell 0) : EuclideanSpace ℝ (Fin 0))) :=
    he.comp (hz.comp hh)
  refine ContMDiff.congr (f := fun x : ClosedCell (n - n) =>
      e ((h x : ClosedCell 0) : EuclideanSpace ℝ (Fin 0))) hcomp ?_
  intro x
  dsimp [h, e, closedCellSubSelfHomeo, finSubSelfIso]
  simp

theorem closedCellInclusion_contMDiff_of (l : ℕ) [Fact (l = (l - 1) + 1)] :
    @ContMDiff ℝ _ (EuclideanSpace ℝ (Fin ((l - 1) + 1))) _ _
      (EuclideanHalfSpace ((l - 1) + 1)) _ (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
      (ClosedCell l) _ (closedCellChartedSpace l)
      (EuclideanSpace ℝ (Fin l)) _ _ (EuclideanSpace ℝ (Fin l)) _
      (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (EuclideanSpace ℝ (Fin l)) _ _
      (⊤ : ℕ∞)
      (fun v : ClosedCell l => (v : EuclideanSpace ℝ (Fin l))) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell ((l - 1) + 1)) :=
    closedCellChartedSpaceSucc (l - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((l - 1) + 1)) := closedCellIsManifold (l - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell l) :=
    isManifoldOfHomeomorph (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
      (closedCellReindexHomeo l)
  intro x
  let r : ClosedCell l ≃ₜ ClosedCell ((l - 1) + 1) := closedCellReindexHomeo l
  let e : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((l - 1) + 1)) :=
    closedCellReindex l
  have hnorm : ‖(r x).1‖ = ‖x.1‖ := by
    change ‖(e x.1 : EuclideanSpace ℝ (Fin ((l - 1) + 1)))‖ = ‖x.1‖
    rw [e.norm_map]
  have hchartBase : chartAt (H := EuclideanHalfSpace ((l - 1) + 1)) (M := ClosedCell l) x =
      r.toOpenPartialHomeomorph ≫ₕ (chartAt (H := EuclideanHalfSpace ((l - 1) + 1))
        (M := ClosedCell ((l - 1) + 1)) (r x)) := rfl
  by_cases hx : ‖x.1‖ < 1
  · have hc' : chartAt (H := EuclideanHalfSpace ((l - 1) + 1))
        (M := ClosedCell ((l - 1) + 1)) (r x) = closedCellInteriorChart (l - 1) := by
      change closedCellChartAt (r x) = closedCellInteriorChart (l - 1)
      rw [closedCellChartAt, dif_pos (by
        rwa [hnorm])]
    have hchart : chartAt (H := EuclideanHalfSpace ((l - 1) + 1)) (M := ClosedCell l) x =
        r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1) := by
      rw [hchartBase, hc']
    have hc : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
        (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).source := by
      have h := contMDiffOn_chart (I := modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (H := EuclideanHalfSpace ((l - 1) + 1)) (M := ClosedCell l) (n := (⊤ : ℕ∞)) (x := x)
      simpa [hchart] using h
    have hg0 : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin ((l - 1) + 1)))) (⊤ : ℕ∞)
        (fun y : EuclideanHalfSpace ((l - 1) + 1) =>
          ((closedCellInteriorChart (l - 1)).symm y :
            EuclideanSpace ℝ (Fin ((l - 1) + 1))))
        (closedCellInteriorChart (l - 1)).target :=
      closedCellInteriorChart_symm_smooth (m := l - 1)
    have hele : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin ((l - 1) + 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (e.symm : EuclideanSpace ℝ (Fin ((l - 1) + 1)) → EuclideanSpace ℝ (Fin l)) Set.univ :=
      contMDiffOn_univ.mpr (contMDiff_iff_contDiff.mpr e.symm.contDiff)
    have hg1 : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun y : EuclideanHalfSpace ((l - 1) + 1) =>
          e.symm (((closedCellInteriorChart (l - 1)).symm y :
            EuclideanSpace ℝ (Fin ((l - 1) + 1)))))
        (closedCellInteriorChart (l - 1)).target := by
      refine hele.comp hg0 ?_
      intro y hy
      trivial
    have hval : ∀ y ∈ (closedCellInteriorChart (l - 1)).target,
        (((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).symm y : ClosedCell l) :
            EuclideanSpace ℝ (Fin l)) =
          e.symm (((closedCellInteriorChart (l - 1)).symm y :
            EuclideanSpace ℝ (Fin ((l - 1) + 1)))) := by
      intro y hy
      change ((((closedCellInteriorChart (l - 1)).symm.trans r.toOpenPartialHomeomorph.symm) y :
          ClosedCell l) : EuclideanSpace ℝ (Fin l)) =
        e.symm (((closedCellInteriorChart (l - 1)).symm y :
          EuclideanSpace ℝ (Fin ((l - 1) + 1))))
      rw [OpenPartialHomeomorph.coe_trans]
      rfl
    have htarget : (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).target =
        (closedCellInteriorChart (l - 1)).target := by
      simp
    have hg : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun y : EuclideanHalfSpace ((l - 1) + 1) =>
          (((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).symm y : ClosedCell l) :
            EuclideanSpace ℝ (Fin l)))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).target := by
      rw [htarget]
      exact hg1.congr hval
    have hst : (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).source ⊆
        (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)) ⁻¹'
          (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).target := by
      intro y hy
      exact (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).mapsTo hy
    have hcomp : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun v : ClosedCell l =>
          (((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).symm
            ((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)) v) : ClosedCell l) :
            EuclideanSpace ℝ (Fin l)))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).source :=
      hg.comp hc hst
    have hcong : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun v : ClosedCell l => (v : EuclideanSpace ℝ (Fin l)))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).source := by
      refine hcomp.congr ?_
      intro y hy
      change (y : EuclideanSpace ℝ (Fin l)) =
        (((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).symm
          ((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)) y) : ClosedCell l) :
          EuclideanSpace ℝ (Fin l))
      rw [(r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).left_inv hy]
    exact hcong.contMDiffAt ((r.toOpenPartialHomeomorph ≫ₕ closedCellInteriorChart (l - 1)).open_source.mem_nhds (by
      simpa [hchart] using (mem_chart_source (H := EuclideanHalfSpace ((l - 1) + 1))
        (M := ClosedCell l) x)))
  · let i : Fin ((l - 1) + 1) := Classical.choose (closedCell_exists_coord_ne_zero (r x).1 (by
      have hle : ‖(r x).1‖ ≤ 1 := (r x).2
      have hnot : ¬ ‖(r x).1‖ < 1 := by
        intro h
        exact hx (by
          rwa [← hnorm])
      linarith))
    let σ : Bool := 0 < (r x).1 i
    have hc' : chartAt (H := EuclideanHalfSpace ((l - 1) + 1))
        (M := ClosedCell ((l - 1) + 1)) (r x) = closedCellBoundaryChart (l - 1) i σ := by
      change closedCellChartAt (r x) = closedCellBoundaryChart (l - 1) i σ
      rw [closedCellChartAt, dif_neg (by
        rwa [hnorm])]
    have hchart : chartAt (H := EuclideanHalfSpace ((l - 1) + 1)) (M := ClosedCell l) x =
        r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ := by
      rw [hchartBase, hc']
    have hxsrc : x ∈ (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).source := by
      simpa [hchart] using (mem_chart_source (H := EuclideanHalfSpace ((l - 1) + 1))
        (M := ClosedCell l) x)
    have hc : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
        (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ)
        (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).source := by
      have h := contMDiffOn_chart (I := modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (H := EuclideanHalfSpace ((l - 1) + 1)) (M := ClosedCell l) (n := (⊤ : ℕ∞)) (x := x)
      simpa [hchart] using h
    have hg0 : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin ((l - 1) + 1)))) (⊤ : ℕ∞)
        (fun y : EuclideanHalfSpace ((l - 1) + 1) =>
          ((closedCellBoundaryChart (l - 1) i σ).symm y :
            EuclideanSpace ℝ (Fin ((l - 1) + 1))))
        (closedCellBoundaryChart (l - 1) i σ).target :=
      closedCellBoundaryChart_symm_smooth (m := l - 1) i σ
    have hele : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin ((l - 1) + 1))))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (e.symm : EuclideanSpace ℝ (Fin ((l - 1) + 1)) → EuclideanSpace ℝ (Fin l)) Set.univ :=
      contMDiffOn_univ.mpr (contMDiff_iff_contDiff.mpr e.symm.contDiff)
    have hg1 : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun y : EuclideanHalfSpace ((l - 1) + 1) =>
          e.symm (((closedCellBoundaryChart (l - 1) i σ).symm y :
            EuclideanSpace ℝ (Fin ((l - 1) + 1)))))
        (closedCellBoundaryChart (l - 1) i σ).target := by
      refine hele.comp hg0 ?_
      intro y hy
      trivial
    have hval : ∀ y ∈ (closedCellBoundaryChart (l - 1) i σ).target,
        (((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).symm y : ClosedCell l) :
            EuclideanSpace ℝ (Fin l)) =
          e.symm (((closedCellBoundaryChart (l - 1) i σ).symm y :
            EuclideanSpace ℝ (Fin ((l - 1) + 1)))) := by
      intro y hy
      change ((((closedCellBoundaryChart (l - 1) i σ).symm.trans
          r.toOpenPartialHomeomorph.symm) y : ClosedCell l) : EuclideanSpace ℝ (Fin l)) =
        e.symm (((closedCellBoundaryChart (l - 1) i σ).symm y :
          EuclideanSpace ℝ (Fin ((l - 1) + 1))))
      rw [OpenPartialHomeomorph.coe_trans]
      rfl
    have htarget : (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).target =
        (closedCellBoundaryChart (l - 1) i σ).target := by
      simp
    have hg : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun y : EuclideanHalfSpace ((l - 1) + 1) =>
          (((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).symm y : ClosedCell l) :
            EuclideanSpace ℝ (Fin l)))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).target := by
      rw [htarget]
      exact hg1.congr hval
    have hst : (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).source ⊆
        (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ) ⁻¹'
          (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).target := by
      intro y hy
      exact (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).mapsTo hy
    have hcomp : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun v : ClosedCell l =>
          (((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).symm
            ((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ) v) : ClosedCell l) :
            EuclideanSpace ℝ (Fin l)))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).source :=
      hg.comp hc hst
    have hcong : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin l))) (⊤ : ℕ∞)
        (fun v : ClosedCell l => (v : EuclideanSpace ℝ (Fin l)))
        (r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).source := by
      refine hcomp.congr ?_
      intro y hy
      change (y : EuclideanSpace ℝ (Fin l)) =
        (((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).symm
          ((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ) y) : ClosedCell l) :
          EuclideanSpace ℝ (Fin l))
      rw [(r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).left_inv hy]
    exact hcong.contMDiffAt ((r.toOpenPartialHomeomorph ≫ₕ closedCellBoundaryChart (l - 1) i σ).open_source.mem_nhds hxsrc)

@[reducible]
noncomputable def attachingRegionChartedSpace (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1)))
      (AttachingRegion k l) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  infer_instance

instance attachingRegionChartedSpaceInst (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1)))
      (AttachingRegion k l) :=
  attachingRegionChartedSpace k l

theorem attachingRegionIsManifold (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    @IsManifold ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((l - 1) + 1))) _
      _ (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))) (⊤ : ℕ∞)
      (AttachingRegion k l) _ (attachingRegionChartedSpace k l) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell ((l - 1) + 1)) :=
    closedCellChartedSpaceSucc (l - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((l - 1) + 1)) := closedCellIsManifold (l - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell l) := isManifoldOfHomeomorph
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (closedCellReindexHomeo l)
  change @IsManifold ℝ _
    (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((l - 1) + 1))) _
    _ (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1))) _
    ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))) (⊤ : ℕ∞)
    (CellBoundary k × ClosedCell l) _ (attachingRegionChartedSpace k l)
  exact IsManifold.prod (I := 𝓡 (k - 1))
    (I' := modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (n := (⊤ : ℕ∞))
    (CellBoundary k) (ClosedCell l)

instance attachingRegionIsManifoldInst (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    IsManifold ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))) (⊤ : ℕ∞)
      (AttachingRegion k l) :=
  attachingRegionIsManifold k l

end

end DifferentialGeometry.Topology.Handle
