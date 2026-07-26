import DifferentialGeometry.Geometry.Coordinates.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Metric.Sphere.PolarBij

/-!
# Smooth polar coordinates on the round sphere

This file packages the ambient polar formulas as a genuine smooth partial
diffeomorphism.  The direction variable is the unit sphere in the orthogonal
complement of the pole, so the source is an honest open subset of a manifold,
not a non-open subset of `ℝ × E`.
-/

noncomputable section

open Metric Module Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 2)]

/-- The sphere of unit directions orthogonal to a pole. -/
abbrev PolarDir (p : sphere (0 : E) 1) :=
  sphere (0 : (ℝ ∙ (p : E))ᗮ) 1

/-- The open polar cylinder. -/
def polarSource (p : sphere (0 : E) 1) :
    Set (ℝ × PolarDir p) :=
  {q | q.1 ∈ Ioo 0 Real.pi}

/-- The unit sphere with the pole and its antipode removed. -/
def polarTarget (p : sphere (0 : E) 1) :
    Set (sphere (0 : E) 1) :=
  {x | x ≠ p ∧ x ≠ -p}

/-- The orthogonal direction space has the expected codimension-one
dimension. -/
theorem polarDir_finrank (p : sphere (0 : E) 1) :
    finrank ℝ (ℝ ∙ (p : E))ᗮ = n + 1 := by
  have hp0 : (p : E) ≠ 0 :=
    ne_zero_of_mem_unit_sphere p
  exact Submodule.finrank_orthogonal_span_singleton hp0

private noncomputable instance polarDirFact
    (p : sphere (0 : E) 1) :
    Fact (finrank ℝ (ℝ ∙ (p : E))ᗮ = n + 1) :=
  ⟨polarDir_finrank (n := n) p⟩

private noncomputable instance polarDirCharted
    (p : sphere (0 : E) 1) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (PolarDir p) := by
  letI : Fact (finrank ℝ (ℝ ∙ (p : E))ᗮ = n + 1) :=
    polarDirFact (n := n) p
  exact EuclideanSpace.instChartedSpaceSphere

private noncomputable instance polarDirMfld
    (p : sphere (0 : E) 1) :
    IsManifold (𝓡 n) ∞ (PolarDir p) := by
  letI : Fact (finrank ℝ (ℝ ∙ (p : E))ᗮ = n + 1) :=
    polarDirFact (n := n) p
  exact EuclideanSpace.instIsManifoldSphere.of_le le_top

private noncomputable instance unitSphereMfld :
    IsManifold (𝓡 (n + 1)) ∞ (sphere (0 : E) 1) :=
  EuclideanSpace.instIsManifoldSphere.of_le le_top

private theorem polarSource_open (p : sphere (0 : E) 1) :
    IsOpen (polarSource p) := by
  exact isOpen_Ioo.preimage continuous_fst

omit [InnerProductSpace ℝ E] in
private theorem polarTarget_open (p : sphere (0 : E) 1) :
    IsOpen (polarTarget p) := by
  change IsOpen ({p}ᶜ ∩ ({-p}ᶜ : Set (sphere (0 : E) 1)))
  exact isOpen_compl_singleton.inter isOpen_compl_singleton

private def polarSourceO (p : sphere (0 : E) 1) :
    Opens (ℝ × PolarDir p) :=
  ⟨polarSource p, polarSource_open p⟩

private def polarTargetO (p : sphere (0 : E) 1) :
    Opens (sphere (0 : E) 1) :=
  ⟨polarTarget p, polarTarget_open p⟩

private theorem polar_dir_inner
    (p : sphere (0 : E) 1) (w : PolarDir p) :
    ⟪(p : E), ((w : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.1.2

private theorem polar_dir_norm
    (p : sphere (0 : E) 1) (w : PolarDir p) :
    ‖((w : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := by
  simpa only [Submodule.coe_norm] using
    (mem_sphere_zero_iff_norm.mp w.2)

private theorem polar_norm
    (p : sphere (0 : E) 1) (q : ℝ × PolarDir p) :
    ‖spherePolar (p : E)
        (q.1, ((q.2 : (ℝ ∙ (p : E))ᗮ) : E))‖ = 1 := by
  have hp : ‖(p : E)‖ = 1 :=
    norm_eq_of_mem_sphere p
  have hw : ‖((q.2 : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 :=
    polar_dir_norm p q.2
  have hpw :
      ⟪(p : E), ((q.2 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ = 0 :=
    polar_dir_inner p q.2
  have horth :
      ⟪Real.cos q.1 • (p : E),
        Real.sin q.1 • ((q.2 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right, hpw, mul_zero]
  have hsq :
      ‖spherePolar (p : E)
          (q.1, ((q.2 : (ℝ ∙ (p : E))ᗮ) : E))‖ ^ 2 = 1 := by
    change
      ‖Real.cos q.1 • (p : E) +
        Real.sin q.1 • ((q.2 : (ℝ ∙ (p : E))ᗮ) : E)‖ ^ 2 = 1
    rw [norm_add_sq_real]
    simp only [horth, mul_zero, add_zero, norm_smul, Real.norm_eq_abs,
      hp, hw, mul_one, sq_abs]
    exact Real.cos_sq_add_sin_sq q.1
  nlinarith [norm_nonneg
    (spherePolar (p : E)
      (q.1, ((q.2 : (ℝ ∙ (p : E))ᗮ) : E)))]

private noncomputable def polarMap
    (p : sphere (0 : E) 1) :
    ℝ × PolarDir p → sphere (0 : E) 1 :=
  fun q =>
    ⟨spherePolar (p : E)
        (q.1, ((q.2 : (ℝ ∙ (p : E))ᗮ) : E)), by
      rw [mem_sphere_zero_iff_norm]
      exact polar_norm p q⟩

private theorem polarMap_smooth
    (p : sphere (0 : E) 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞
      (polarMap p) := by
  let K : Submodule ℝ E := (ℝ ∙ (p : E))ᗮ
  have hdir :
      ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞
        (fun w : PolarDir p => ((w : K) : E)) := by
    exact
      K.subtypeL.contDiff.contMDiff.comp
        (contMDiff_coe_sphere (E := K) (n := n))
  have hamb :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × PolarDir p =>
          spherePolar (p : E) (q.1, ((q.2 : K) : E))) := by
    exact
      ((Real.contDiff_cos.contMDiff.comp contMDiff_fst).smul
        contMDiff_const).add
      ((Real.contDiff_sin.contMDiff.comp contMDiff_fst).smul
        (hdir.comp contMDiff_snd))
  exact ContMDiff.codRestrict_sphere hamb
    (fun q => mem_sphere_zero_iff_norm.mpr (polar_norm p q))

private theorem polarMap_target
    (p : sphere (0 : E) 1) {q : ℝ × PolarDir p}
    (hq : q ∈ polarSource p) :
    polarMap p q ∈ polarTarget p := by
  have hp : ‖(p : E)‖ = 1 :=
    norm_eq_of_mem_sphere p
  have hq' :
      (q.1, ((q.2 : (ℝ ∙ (p : E))ᗮ) : E)) ∈
        Ioo 0 Real.pi ×ˢ
          {w : E | ⟪(p : E), w⟫_ℝ = 0 ∧ ‖w‖ = 1} := by
    exact ⟨hq, polar_dir_inner p q.2, polar_dir_norm p q.2⟩
  have hmap := (polar_bijOn hp).mapsTo hq'
  constructor
  · intro h
    exact hmap.2.1 (congrArg Subtype.val h)
  · intro h
    exact hmap.2.2 (by
      simpa using congrArg Subtype.val h)

private theorem polarBack_data
    (p : sphere (0 : E) 1) (x : polarTargetO p) :
    let r := Real.arccos ⟪(p : E), (x : E)⟫_ℝ
    let w := (Real.sin r)⁻¹ •
      ((x : E) - ⟪(p : E), (x : E)⟫_ℝ • (p : E))
    r ∈ Ioo 0 Real.pi ∧
      w ∈ (ℝ ∙ (p : E))ᗮ ∧ ‖w‖ = 1 ∧
        spherePolar (p : E) (r, w) = (x : E) := by
  have hp : ‖(p : E)‖ = 1 :=
    norm_eq_of_mem_sphere p
  have hx : ‖(x : E)‖ = 1 :=
    norm_eq_of_mem_sphere x.1
  have hxp : (x : E) ≠ (p : E) := by
    intro h
    exact x.2.1 (Subtype.ext h)
  have hxnp : (x : E) ≠ -(p : E) := by
    intro h
    apply x.2.2
    apply Subtype.ext
    simpa using h
  have hdec := polar_decomp hp hx hxp hxnp
  dsimp only at hdec ⊢
  exact ⟨hdec.1,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hdec.2.1,
    hdec.2.2.1, hdec.2.2.2⟩

private noncomputable def polarBack
    (p : sphere (0 : E) 1) :
    polarTargetO p → polarSourceO p :=
  fun x =>
    let r := Real.arccos ⟪(p : E), (x : E)⟫_ℝ
    let w := (Real.sin r)⁻¹ •
      ((x : E) - ⟪(p : E), (x : E)⟫_ℝ • (p : E))
    ⟨(r, ⟨⟨w, (polarBack_data p x).2.1⟩, by
        apply mem_sphere_zero_iff_norm.mpr
        simpa only [Submodule.coe_norm] using
          (polarBack_data p x).2.2.1⟩),
      (polarBack_data p x).1⟩

@[simp] private theorem polarBack_fst
    (p : sphere (0 : E) 1) (x : polarTargetO p) :
    (polarBack p x : ℝ × PolarDir p).1 =
      Real.arccos ⟪(p : E), (x : E)⟫_ℝ :=
  rfl

@[simp] private theorem polarBack_dir
    (p : sphere (0 : E) 1) (x : polarTargetO p) :
    ((((polarBack p x : ℝ × PolarDir p).2 :
        (ℝ ∙ (p : E))ᗮ)) : E) =
      (spherePolarInv (p : E) (x : E)).2 :=
  rfl

private theorem polarBack_smooth
    (p : sphere (0 : E) 1) :
    ContMDiff (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (polarBack p) := by
  let K : Submodule ℝ E := (ℝ ∙ (p : E))ᗮ
  let V : Opens (sphere (0 : E) 1) := polarTargetO p
  have hopen :
      IsOpen {y : E | |⟪(p : E), y⟫_ℝ| < 1} := by
    exact isOpen_lt
      ((continuous_const.inner continuous_id).abs) continuous_const
  have hraw :
      ContMDiff (𝓡 (n + 1))
        𝓘(ℝ, ℝ × E) ∞
        (fun x : V => spherePolarInv (p : E) (x : E)) := by
    intro x
    have hp : ‖(p : E)‖ = 1 :=
      norm_eq_of_mem_sphere p
    have hx : ‖(x : E)‖ = 1 :=
      norm_eq_of_mem_sphere x.1
    have hxp : (x : E) ≠ (p : E) := by
      intro h
      exact x.2.1 (Subtype.ext h)
    have hxnp : (x : E) ≠ -(p : E) := by
      intro h
      apply x.2.2
      apply Subtype.ext
      simpa using h
    have ht_le :
        ⟪(p : E), (x : E)⟫_ℝ ≤ 1 :=
      real_inner_le_one_of_norm_eq_one hp hx
    have ht_ne : ⟪(p : E), (x : E)⟫_ℝ ≠ 1 := by
      intro ht
      apply hxp
      exact ((inner_eq_one_iff_of_norm_eq_one hp hx).mp ht).symm
    have hneg_le :
        -1 ≤ ⟪(p : E), (x : E)⟫_ℝ :=
      neg_one_le_real_inner_of_norm_eq_one hp hx
    have hneg_ne :
        (-1 : ℝ) ≠ ⟪(p : E), (x : E)⟫_ℝ := by
      intro ht
      apply hxnp
      have hinner :
          ⟪(x : E), (p : E)⟫_ℝ = -1 := by
        rw [real_inner_comm]
        exact ht.symm
      exact (inner_eq_neg_one_iff_of_norm_eq_one hx hp).mp hinner
    have habs :
        |⟪(p : E), (x : E)⟫_ℝ| < 1 := by
      exact abs_lt.mpr
        ⟨lt_of_le_of_ne hneg_le hneg_ne,
          lt_of_le_of_ne ht_le ht_ne⟩
    have hamb :
        ContDiffAt ℝ ∞ (spherePolarInv (p : E)) (x : E) :=
      (polarInv_smooth (p : E) (x : E) habs).contDiffAt
        (hopen.mem_nhds habs)
    have hcoe :
        ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, E) ∞
          (fun y : V => (y : E)) x :=
      ((contMDiff_coe_sphere (E := E) (n := n + 1)).comp
        (contMDiff_subtype_val (I := 𝓡 (n + 1)) (U := V))).contMDiffAt
    exact hamb.contMDiffAt.comp x hcoe
  have hfst :
      ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
        (fun x : V => (spherePolarInv (p : E) (x : E)).1) :=
    (ContinuousLinearMap.fst ℝ ℝ E).contDiff.contMDiff.comp hraw
  have hperp :
      letI : TopologicalSpace K :=
        (inferInstance : NormedAddCommGroup K).toMetricSpace.toUniformSpace.toTopologicalSpace
      letI : ChartedSpace K K := chartedSpaceSelf K
      ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, K) ∞
        (fun x : V => K.orthogonalProjection
          (spherePolarInv (p : E) (x : E)).2) := by
    letI : TopologicalSpace K :=
      (inferInstance : NormedAddCommGroup K).toMetricSpace.toUniformSpace.toTopologicalSpace
    letI : ChartedSpace K K := chartedSpaceSelf K
    let L : (ℝ × E) →L[ℝ] (ℝ ∙ (p : E))ᗮ :=
      (ℝ ∙ (p : E))ᗮ.orthogonalProjection.comp
        (ContinuousLinearMap.snd ℝ ℝ E)
    exact L.contDiff.contMDiff.comp hraw
  have hperp_eq (x : V) :
      K.orthogonalProjection
          (spherePolarInv (p : E) (x : E)).2 =
        ((polarBack p x : ℝ × PolarDir p).2 : K) := by
    have hraw :
        (spherePolarInv (p : E) (x : E)).2 =
          (((polarBack p x : ℝ × PolarDir p).2 : K) : E) :=
      (polarBack_dir p x).symm
    rw [hraw, K.orthogonalProjection_mem_subspace_eq_self]
  have hdir :
      ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞
        (fun x : V => (polarBack p x : ℝ × PolarDir p).2) := by
    exact ContMDiff.codRestrict_sphere
      (by simpa only [hperp_eq] using hperp)
      (fun x => (polarBack p x : ℝ × PolarDir p).2.2)
  have hpair :
      ContMDiff (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun x : V => (polarBack p x : ℝ × PolarDir p)) := by
    exact hfst.prodMk hdir
  intro x
  exact codRestr_contMDiffAt
    (I := 𝓡 (n + 1)) (J := 𝓘(ℝ, ℝ).prod (𝓡 n))
    (V := polarSourceO p)
    (f := fun y : V => (polarBack p y : ℝ × PolarDir p))
    (fun y => (polarBack p y).2) hpair.contMDiffAt

private noncomputable def polarOpenDiffeo
    (p : sphere (0 : E) 1) :
    Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1))
      (polarSourceO p) (polarTargetO p) ∞ where
  toFun q := ⟨polarMap p q, polarMap_target p q.2⟩
  invFun := polarBack p
  left_inv q := by
    have hq : (q.1 : ℝ × PolarDir p) ∈ polarSource p :=
      q.2
    have hleft :
        spherePolarInv (p : E)
            (spherePolar (p : E)
              (q.1.1, ((q.1.2 : (ℝ ∙ (p : E))ᗮ) : E))) =
          (q.1.1, ((q.1.2 : (ℝ ∙ (p : E))ᗮ) : E)) :=
      polar_left_inv (norm_eq_of_mem_sphere p)
        ⟨hq, polar_dir_inner p q.1.2, polar_dir_norm p q.1.2⟩
    apply Subtype.ext
    apply Prod.ext
    · change
        (spherePolarInv (p : E)
          (spherePolar (p : E)
            (q.1.1, ((q.1.2 : (ℝ ∙ (p : E))ᗮ) : E)))).1 =
          q.1.1
      exact congrArg Prod.fst hleft
    · apply Subtype.ext
      apply Subtype.ext
      change
        (spherePolarInv (p : E)
          (spherePolar (p : E)
            (q.1.1, ((q.1.2 : (ℝ ∙ (p : E))ᗮ) : E)))).2 =
          ((q.1.2 : (ℝ ∙ (p : E))ᗮ) : E)
      exact congrArg Prod.snd hleft
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change
      spherePolar (p : E)
          ((polarBack p x : ℝ × PolarDir p).1,
            (((polarBack p x : ℝ × PolarDir p).2 :
              (ℝ ∙ (p : E))ᗮ) : E)) =
        (x : E)
    exact (polarBack_data p x).2.2.2
  contMDiff_toFun := by
    intro q
    exact codRestr_contMDiffAt
      (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) (J := 𝓡 (n + 1))
      (V := polarTargetO p)
      (f := fun y : polarSourceO p => polarMap p y)
      (fun y => polarMap_target (p := p) y.2)
      ((polarMap_smooth (n := n) p).comp
        (contMDiff_subtype_val
          (I := 𝓘(ℝ, ℝ).prod (𝓡 n))
          (U := polarSourceO p))).contMDiffAt
  contMDiff_invFun := polarBack_smooth (n := n) p

private noncomputable def polarDefault
    (p : sphere (0 : E) 1) :
    ℝ × PolarDir p := by
  let K : Submodule ℝ E := (ℝ ∙ (p : E))ᗮ
  letI : Nontrivial K :=
    Module.nontrivial_of_finrank_pos (by
      rw [polarDir_finrank (n := n) p]
      omega)
  exact
    (0, Classical.choice
      (NormedSpace.sphere_nonempty_rclike ℝ
        (E := K) (r := (1 : ℝ)) zero_le_one))

private noncomputable def polarInv
    (p : sphere (0 : E) 1) :
    sphere (0 : E) 1 → ℝ × PolarDir p := by
  classical
  exact fun x =>
    if hx : x ∈ polarTarget p then
      (polarOpenDiffeo (n := n) p).symm ⟨x, hx⟩
    else
      polarDefault (n := n) p

private theorem polarInv_mem
    (p : sphere (0 : E) 1) {x : sphere (0 : E) 1}
    (hx : x ∈ polarTarget p) :
    polarInv (n := n) p x =
      (polarOpenDiffeo (n := n) p).symm ⟨x, hx⟩ := by
  simp only [polarInv, dif_pos hx]

/-- Smooth polar coordinates as a partial diffeomorphism from the open polar
cylinder to the unit sphere with its two poles removed. -/
noncomputable def spherePolarPD
    (p : sphere (0 : E) 1) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1))
      (ℝ × PolarDir p) (sphere (0 : E) 1) ∞ where
  toFun := polarMap p
  invFun := polarInv (n := n) p
  source := polarSource p
  target := polarTarget p
  map_source' := fun q hq => polarMap_target p hq
  map_target' := fun x hx => by
    rw [polarInv_mem (n := n) p hx]
    exact ((polarOpenDiffeo (n := n) p).symm ⟨x, hx⟩).2
  left_inv' := fun q hq => by
    rw [polarInv_mem (n := n) p (polarMap_target p hq)]
    exact congrArg Subtype.val
      ((polarOpenDiffeo (n := n) p).left_inv ⟨q, hq⟩)
  right_inv' := fun x hx => by
    rw [polarInv_mem (n := n) p hx]
    exact congrArg Subtype.val
      ((polarOpenDiffeo (n := n) p).right_inv ⟨x, hx⟩)
  open_source := polarSource_open p
  open_target := polarTarget_open p
  contMDiffOn_toFun := (polarMap_smooth (n := n) p).contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    let V : Opens (sphere (0 : E) 1) := polarTargetO p
    have hsub :
        ContMDiffAt (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
          (fun y : V =>
            polarInv (n := n) p (y : sphere (0 : E) 1)) ⟨x, hx⟩ := by
      have hbase :
          ContMDiff (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
            (fun y : V =>
              ((polarOpenDiffeo (n := n) p).symm y :
                polarSourceO p).1) :=
        (contMDiff_subtype_val
          (I := 𝓘(ℝ, ℝ).prod (𝓡 n))
          (U := polarSourceO p)).comp
            (polarOpenDiffeo (n := n) p).symm.contMDiff
      have heq :
          (fun y : V =>
            polarInv (n := n) p (y : sphere (0 : E) 1)) =
          (fun y : V =>
            ((polarOpenDiffeo (n := n) p).symm y :
              polarSourceO p).1) := by
        funext y
        exact polarInv_mem (n := n) p y.2
      rw [heq]
      exact hbase.contMDiffAt
    exact
      (contMDiffAt_subtype_iff
        (I := 𝓡 (n + 1))
        (I' := 𝓘(ℝ, ℝ).prod (𝓡 n))
        (U := V)).mp hsub |>.contMDiffWithinAt

@[simp] theorem spherePolarPD_apply
    (p : sphere (0 : E) 1) (q : ℝ × PolarDir p) :
    spherePolarPD (n := n) p q = polarMap p q :=
  rfl

@[simp] theorem spherePolarPD_source
    (p : sphere (0 : E) 1) :
    (spherePolarPD (n := n) p).source = polarSource p :=
  rfl

@[simp] theorem spherePolarPD_target
    (p : sphere (0 : E) 1) :
    (spherePolarPD (n := n) p).target = polarTarget p :=
  rfl

end Geometry
end DifferentialGeometry
