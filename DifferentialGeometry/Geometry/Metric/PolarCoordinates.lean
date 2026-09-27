import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Bundle Metric Set TopologicalSpace DifferentialGeometry.Geometry
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def euclideanPolarMap (q : sphere (0 : E) 1 × ℝ) : E := q.2 • (q.1 : E)

theorem euclideanPolarMap_smooth :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (euclideanPolarMap (E := E)) :=
  contMDiff_snd.smul ((contMDiff_coe_sphere (n := n)).comp contMDiff_fst)

theorem euclideanPolarMap_mfderiv (q : sphere (0 : E) 1 × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) q) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) euclideanPolarMap q v =
      v.2 • (q.1 : E) + q.2 • dIncl (n := n) q.1 v.1 := by
  let f : sphere (0 : E) 1 × ℝ → ℝ := Prod.snd
  let g : sphere (0 : E) 1 × ℝ → E := fun z => (z.1 : E)
  have hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) f q :=
    mdifferentiableAt_snd
  have hg : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) g q :=
    ((contMDiff_coe_sphere (n := n)).comp contMDiff_fst).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hs := congrArg (fun D => D v) (mvfderiv_fun_smul hf hg)
  have hgc := mfderiv_comp (I := ((𝓡 n).prod 𝓘(ℝ, ℝ))) (I' := 𝓡 n)
    (I'' := 𝓘(ℝ, E)) q
    ((contMDiff_coe_sphere (n := n)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)) mdifferentiableAt_fst
  have hgd : mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) g q v = dIncl (n := n) q.1 v.1 := by
    change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) g q v = _
    have hh := congrArg (fun D => D v) hgc
    rw [mfderiv_fst] at hh
    with_unfolding_all exact hh
  have hfd : mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) f q v = v.2 := by
    change (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd q v : ℝ) = _
    rw [mfderiv_snd]
    rfl
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hgd, hfd, f, g, add_comm] at hs
  with_unfolding_all exact hs

@[simp] theorem euclideanPolarMap_norm (q : sphere (0 : E) 1 × ℝ) :
    ‖euclideanPolarMap q‖ = |q.2| := by
  simp only [euclideanPolarMap, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]

theorem euclideanPolarMap_norm_of_pos {q : sphere (0 : E) 1 × ℝ} (hq : 0 < q.2) :
    ‖euclideanPolarMap q‖ = q.2 := by
  rw [euclideanPolarMap_norm, abs_of_pos hq]

theorem euclideanPolarMap_ne_zero {q : sphere (0 : E) 1 × ℝ} (hq : 0 < q.2) :
    euclideanPolarMap q ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [euclideanPolarMap_norm_of_pos hq]
  exact hq.ne'

private def polarTargetOpen : Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩

private def polarBack (x : polarTargetOpen (E := E)) : sphere (0 : E) 1 × ℝ :=
  let q := homeomorphUnitSphereProd E x
  (q.1, q.2.1)

private theorem polarBack_fst_val (x : polarTargetOpen (E := E)) :
    ((polarBack x).1 : E) = ‖(x : E)‖⁻¹ • (x : E) := by
  exact homeomorphUnitSphereProd_apply_fst_coe E x

private theorem polarBack_snd (x : polarTargetOpen (E := E)) :
    (polarBack x).2 = ‖(x : E)‖ := by
  exact homeomorphUnitSphereProd_apply_snd_coe E x

private theorem polarBack_smooth :
    ContMDiff 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (polarBack (E := E)) := by
  have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : polarTargetOpen (E := E) => ‖(x : E)‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := polarTargetOpen (E := E))).mpr
    exact (contDiffAt_norm ℝ (Set.mem_compl_singleton_iff.mp x.2)).contMDiffAt
  have hnorm (x : polarTargetOpen (E := E)) : ‖(x : E)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Set.mem_compl_singleton_iff.mp x.2)
  have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : polarTargetOpen (E := E) => ‖(x : E)‖⁻¹) := hn.inv₀ hnorm
  have hamb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun x : polarTargetOpen (E := E) => ((polarBack x).1 : E)) := by
    simp_rw [polarBack_fst_val]
    exact hi.smul (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := polarTargetOpen (E := E)))
  have hdir : ContMDiff 𝓘(ℝ, E) (𝓡 n) ∞
      (fun x : polarTargetOpen (E := E) => (polarBack x).1) :=
    ContMDiff.codRestrict_sphere hamb (fun x => (polarBack x).1.2)
  have hrad : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : polarTargetOpen (E := E) => (polarBack x).2) := by
    simpa only [polarBack_snd] using hn
  exact hdir.prodMk hrad

private theorem polarBack_left {q : sphere (0 : E) 1 × ℝ} (hq : 0 < q.2) :
    polarBack ⟨euclideanPolarMap q, euclideanPolarMap_ne_zero hq⟩ = q := by
  have h := (homeomorphUnitSphereProd E).apply_symm_apply (q.1, ⟨q.2, hq⟩)
  exact congrArg (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => (z.1, (z.2 : ℝ))) h

private theorem polarBack_right (x : polarTargetOpen (E := E)) :
    euclideanPolarMap (polarBack x) = (x : E) := by
  exact congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply x)

private noncomputable def polarDefault [Nontrivial E] : sphere (0 : E) 1 × ℝ :=
  (Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ
    (E := E) (r := (1 : ℝ)) zero_le_one), 0)

private noncomputable def polarInverse [Nontrivial E] (x : E) : sphere (0 : E) 1 × ℝ := by
  classical
  exact if hx : x ≠ 0 then polarBack ⟨x, hx⟩ else polarDefault

private theorem polarInverse_of_ne_zero [Nontrivial E] {x : E} (hx : x ≠ 0) :
    polarInverse x = polarBack ⟨x, hx⟩ := dif_pos hx

def euclideanPolarDiffeomorph [Nontrivial E] :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (sphere (0 : E) 1 × ℝ) E ∞ where
  toFun := euclideanPolarMap
  invFun := polarInverse
  source := {q | 0 < q.2}
  target := {0}ᶜ
  map_source' := fun q hq => euclideanPolarMap_ne_zero hq
  map_target' := fun x hx => by
    rw [polarInverse_of_ne_zero hx]
    change 0 < (polarBack ⟨x, hx⟩).2
    rw [polarBack_snd]
    exact norm_pos_iff.mpr hx
  left_inv' := fun q hq => by
    rw [polarInverse_of_ne_zero (euclideanPolarMap_ne_zero hq)]
    exact polarBack_left hq
  right_inv' := fun x hx => by
    rw [polarInverse_of_ne_zero hx]
    exact polarBack_right ⟨x, hx⟩
  open_source := isOpen_Ioi.preimage continuous_snd
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := (euclideanPolarMap_smooth (n := n)).contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    have hsub : ContMDiffAt 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun y : polarTargetOpen (E := E) => polarInverse (y : E)) ⟨x, hx⟩ := by
      have heq : (fun y : polarTargetOpen (E := E) => polarInverse (y : E)) =
          polarBack := by
        funext y
        exact polarInverse_of_ne_zero (Set.mem_compl_singleton_iff.mp y.2)
      rw [heq]
      exact (polarBack_smooth (n := n)).contMDiffAt
    exact (contMDiffAt_subtype_iff (U := polarTargetOpen (E := E))).mp hsub
      |>.contMDiffWithinAt

@[simp] theorem euclideanPolarDiffeomorph_apply [Nontrivial E]
    (q : sphere (0 : E) 1 × ℝ) :
    euclideanPolarDiffeomorph (n := n) q = euclideanPolarMap q := rfl

@[simp] theorem euclideanPolarDiffeomorph_source [Nontrivial E] :
    (euclideanPolarDiffeomorph (E := E) (n := n)).source = {q | 0 < q.2} := rfl

@[simp] theorem euclideanPolarDiffeomorph_target [Nontrivial E] :
    (euclideanPolarDiffeomorph (E := E) (n := n)).target = {0}ᶜ := rfl

theorem euclideanPolarDiffeomorph_symm_fst_val [Nontrivial E] {x : E} (hx : x ≠ 0) :
    (((euclideanPolarDiffeomorph (n := n)).symm x).1 : E) = ‖x‖⁻¹ • x := by
  change ((polarInverse x).1 : E) = _
  rw [polarInverse_of_ne_zero hx, polarBack_fst_val]

theorem euclideanPolarDiffeomorph_symm_snd [Nontrivial E] {x : E} (hx : x ≠ 0) :
    ((euclideanPolarDiffeomorph (n := n)).symm x).2 = ‖x‖ := by
  change (polarInverse x).2 = _
  rw [polarInverse_of_ne_zero hx, polarBack_snd]

theorem euclideanPolarMap_injOn :
    InjOn (euclideanPolarMap (E := E)) {q | 0 < q.2} := by
  intro q hq q' hq' h
  have hh : (⟨euclideanPolarMap q, euclideanPolarMap_ne_zero hq⟩ :
      polarTargetOpen (E := E)) = ⟨euclideanPolarMap q', euclideanPolarMap_ne_zero hq'⟩ :=
    Subtype.ext h
  simpa only [polarBack_left hq, polarBack_left hq'] using congrArg polarBack hh

theorem euclideanPolarMap_bijOn :
    BijOn (euclideanPolarMap (E := E)) {q | 0 < q.2} {0}ᶜ := by
  refine ⟨fun q hq => euclideanPolarMap_ne_zero hq, euclideanPolarMap_injOn, ?_⟩
  intro x hx
  refine ⟨polarBack ⟨x, hx⟩, ?_, polarBack_right ⟨x, hx⟩⟩
  change 0 < (polarBack ⟨x, hx⟩).2
  rw [polarBack_snd]
  exact norm_pos_iff.mpr hx

end DifferentialGeometry.Geometry.Riemannian
