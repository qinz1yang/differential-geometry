import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass

noncomputable section

open Set Bundle Manifold
open scoped Topology unitInterval Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

def sphereCubeVector (x : I^(Fin 2)) : ThreeSpace := by
  classical
  let u : ℝ := (2 * (x 0 : ℝ) - 1) / ((x 0 : ℝ) * (1 - (x 0 : ℝ)))
  let v : ℝ := (2 * (x 1 : ℝ) - 1) / ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
  exact if x ∈ Cube.boundary (Fin 2) then EuclideanSpace.single 2 1 else
    WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
      (u^2+v^2-1) / (1+u^2+v^2)]

theorem sphereCubeVector_norm (x : I^(Fin 2)) : ‖sphereCubeVector x‖ = 1 := by
  classical
  by_cases hb : x ∈ Cube.boundary (Fin 2)
  · simp [sphereCubeVector, hb, PiLp.norm_single]
  let u : ℝ := (2 * (x 0 : ℝ) - 1) / ((x 0 : ℝ) * (1 - (x 0 : ℝ)))
  let v : ℝ := (2 * (x 1 : ℝ) - 1) / ((x 1 : ℝ) * (1 - (x 1 : ℝ)))
  have hd : 1 + u^2 + v^2 ≠ 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
  have hsq : ‖sphereCubeVector x‖^2 = 1 := by
    simp only [sphereCubeVector, if_neg hb]
    change ‖(WithLp.toLp 2 ![2*u / (1+u^2+v^2), -2*v / (1+u^2+v^2),
      (u^2+v^2-1) / (1+u^2+v^2)] : ThreeSpace)‖^2 = 1
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    field_simp [hd]
    ring
  nlinarith [norm_nonneg (sphereCubeVector x)]

theorem sphereCubeVector_continuous : Continuous sphereCubeVector := by
  sorry


def sphereCubeParameter : C(I^(Fin 2), Sphere 2) :=
  ⟨fun x => ⟨sphereCubeVector x, by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereCubeVector_norm x⟩,
    sphereCubeVector_continuous.subtype_mk (fun x => by
      simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using sphereCubeVector_norm x)⟩

variable {X : Type u} [TopologicalSpace X] {x : X}

theorem exists_unique_sphereFactor (c : GenLoop (Fin 2) X x) :
    ∃! f : C(Sphere 2, X), f.comp sphereCubeParameter = c.val := by
  sorry

def sphereFactor (c : GenLoop (Fin 2) X x) : C(Sphere 2, X) :=
  Classical.choose (exists_unique_sphereFactor c)

theorem sphereFactor_eq (c : GenLoop (Fin 2) X x) :
    (sphereFactor c).comp sphereCubeParameter = c.val :=
  (Classical.choose_spec (exists_unique_sphereFactor c)).1

theorem sphereFactor_homotopic {c d : GenLoop (Fin 2) X x}
    (h : c.val.HomotopicRel d.val (Cube.boundary (Fin 2))) :
    ContinuousMap.Homotopic (sphereFactor c) (sphereFactor d) := by
  sorry


def forgetBasedSphere (x : X) : HomotopyGroup (Fin 2) X x → FreeHomotopyClass (Sphere 2) X :=
  Quotient.lift (fun c => FreeHomotopyClass.mk (sphereFactor c))
    (fun _ _ h => (FreeHomotopyClass.mk_eq_mk_iff _ _).2 (sphereFactor_homotopic h))

def contractibleLoopInclusion : C(ContractibleContinuousLoop X, ContinuousFreeLoop X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem forgetBasedSphere_one (x : X) : forgetBasedSphere x 1 =
    FreeHomotopyClass.mk (ContinuousMap.const (Sphere 2) x) := by
  rw [HomotopyGroup.one_def]
  change FreeHomotopyClass.mk (sphereFactor (GenLoop.const : GenLoop (Fin 2) X x)) = _
  apply congrArg FreeHomotopyClass.mk
  exact ((Classical.choose_spec (exists_unique_sphereFactor
    (GenLoop.const : GenLoop (Fin 2) X x))).2 (ContinuousMap.const (Sphere 2) x) rfl).symm

theorem sphereFamily_homotopic_const_of_pi2_subsingleton
    (h : ∀ q : X, Subsingleton (HomotopyGroup (Fin 2) X q))
    (f : C(Sphere 2, X)) :
    ∃ q : X, ContinuousMap.Homotopic f (ContinuousMap.const (Sphere 2) q) := by
  classical
  have hz : (0 : I^(Fin 2)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  let q : X := f (sphereCubeParameter 0)
  let c : GenLoop (Fin 2) X q := ⟨f.comp sphereCubeParameter, by
    intro y hy
    change f (sphereCubeParameter y) = f (sphereCubeParameter 0)
    apply congrArg f
    apply Subtype.ext
    change sphereCubeVector y = sphereCubeVector 0
    simp [sphereCubeVector, hy, hz]⟩
  have hf : sphereFactor c = f :=
    ((Classical.choose_spec (exists_unique_sphereFactor c)).2 f rfl).symm
  have hc : (⟦c⟧ : HomotopyGroup (Fin 2) X q) =
      (1 : HomotopyGroup (Fin 2) X q) := (h q).elim _ _
  refine ⟨q, (FreeHomotopyClass.mk_eq_mk_iff _ _).mp ?_⟩
  have he : forgetBasedSphere q (⟦c⟧ : HomotopyGroup (Fin 2) X q) =
      forgetBasedSphere q (1 : HomotopyGroup (Fin 2) X q) :=
    congrArg (forgetBasedSphere q) hc
  rw [forgetBasedSphere_one] at he
  change FreeHomotopyClass.mk (sphereFactor c) = _ at he
  rwa [hf] at he

private def zeroPt : Icc (0 : ℝ) (0 + 1) := ⟨0, by constructor <;> norm_num⟩

private def onePt : Icc (0 : ℝ) (0 + 1) := ⟨0 + 1, by constructor <;> norm_num⟩

private def circleQuotLift {Y : Type v} [TopologicalSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) :
    Y × Quot (AddCircle.EndpointIdent (1 : ℝ) 0) → X :=
  fun q => Quot.lift (r := AddCircle.EndpointIdent (1 : ℝ) 0) (fun t => φ (q.1, t))
    (fun a b hab => by cases hab; exact hφ q.1) q.2

private theorem continuous_circleQuotLift {Y : Type v} [TopologicalSpace Y]
    [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) :
    Continuous (circleQuotLift φ hφ) := by
  refine (isQuotientMap_quot_mk (r := AddCircle.EndpointIdent (1 : ℝ) 0)
    (X := Icc (0 : ℝ) (0 + 1))).continuous_lift_prod_right ?_
  have h : (fun p : Y × Icc (0 : ℝ) (0 + 1) =>
      circleQuotLift φ hφ (p.1, Quot.mk _ p.2)) = φ := by
    funext p
    simp [circleQuotLift]
  rw [h]
  exact φ.continuous

private def circleLift {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) :
    C(Y × Circle, X) where
  toFun q := circleQuotLift φ hφ (q.1, AddCircle.homeoIccQuot (1 : ℝ) 0 q.2)
  continuous_toFun :=
    (continuous_circleQuotLift φ hφ).comp
      (continuous_fst.prodMk
        ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp continuous_snd))

private theorem homeoIccQuot_coe {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (0 + 1)) :
    AddCircle.homeoIccQuot (1 : ℝ) 0 (t : Circle) =
      Quot.mk (AddCircle.EndpointIdent (1 : ℝ) 0) ⟨t, Ico_subset_Icc_self ht⟩ := by
  have h := congr_fun (AddCircle.equivIccQuot_comp_mk_eq_toIcoMod (1 : ℝ) 0) t
  simp only [Function.comp_apply] at h
  have hmod : toIcoMod (by norm_num : (0 : ℝ) < 1) 0 t = t :=
    (toIcoMod_eq_iff (by norm_num : (0 : ℝ) < 1)).2 ⟨ht, 0, by simp⟩
  simp only [hmod] at h
  exact h

private theorem circleLift_apply {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt)) (q : Y × Circle) :
    circleLift φ hφ q =
      circleQuotLift φ hφ (q.1, AddCircle.homeoIccQuot (1 : ℝ) 0 q.2) := rfl

private theorem circleLift_coe {Y : Type v} [TopologicalSpace Y] [LocallyCompactSpace Y]
    (φ : C(Y × Icc (0 : ℝ) (0 + 1), X))
    (hφ : ∀ y : Y, φ (y, zeroPt) = φ (y, onePt))
    (y : Y) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (0 + 1)) :
    circleLift φ hφ (y, (t : Circle)) = φ (y, ⟨t, Ico_subset_Icc_self ht⟩) := by
  rw [circleLift_apply, homeoIccQuot_coe ht]
  simp only [circleQuotLift]

private theorem subinterval_mem_I {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    t ∈ Icc (0 : ℝ) 1 :=
  ⟨ht.1, ht.2.le⟩

private theorem subinterval_coe_mem_I (t : Icc (0 : ℝ) (0 + 1)) : (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
  ⟨t.2.1, by simpa using t.2.2⟩

private theorem onePt_val : (onePt : ℝ) = 1 := zero_add 1

private theorem zeroPt_I : (⟨(zeroPt : ℝ), subinterval_coe_mem_I zeroPt⟩ : I) = 0 := rfl

private theorem onePt_I : (⟨(onePt : ℝ), subinterval_coe_mem_I onePt⟩ : I) = 1 :=
  Subtype.ext onePt_val

private def cubeParamHom : C((I^(Fin 2)) × Icc (0 : ℝ) (0 + 1), I^(Fin 3)) where
  toFun q := ![q.1 0, q.1 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply (0 : Fin 2)).comp continuous_fst
    · exact (continuous_apply (1 : Fin 2)).comp continuous_fst
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _

private theorem cubeParamHom_apply (q : (I^(Fin 2)) × Icc (0 : ℝ) (0 + 1)) :
    cubeParamHom q = ![q.1 0, q.1 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩] := rfl

private theorem cubeParamHom_zero (p : I^(Fin 2)) :
    cubeParamHom (p, zeroPt) = ![p 0, p 1, (0 : I)] := by
  rw [cubeParamHom_apply]
  rfl

private theorem cubeParamHom_one (p : I^(Fin 2)) :
    cubeParamHom (p, onePt) = ![p 0, p 1, (1 : I)] := by
  rw [cubeParamHom_apply]
  rw [onePt_I]

private def cubeLoopParam (c : GenLoop (Fin 3) X x) :
    C((I^(Fin 2)) × Icc (0 : ℝ) (0 + 1), X) :=
  c.val.comp cubeParamHom

private theorem cubeLoopParam_zero (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    cubeLoopParam c (p, zeroPt) = x := by
  rw [cubeLoopParam, ContinuousMap.comp_apply, cubeParamHom_zero p]
  exact c.property _ ⟨2, Or.inl rfl⟩

private theorem cubeLoopParam_one (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    cubeLoopParam c (p, onePt) = x := by
  rw [cubeLoopParam, ContinuousMap.comp_apply, cubeParamHom_one p]
  exact c.property _ ⟨2, Or.inr rfl⟩

private def cubeLoopFamily (c : GenLoop (Fin 3) X x) : C((I^(Fin 2)) × Circle, X) :=
  circleLift (X := X) (Y := I^(Fin 2)) (cubeLoopParam c)
    (fun p => (cubeLoopParam_zero c p).trans (cubeLoopParam_one c p).symm)

private theorem cubeLoopFamily_coe (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    cubeLoopFamily c (p, (t : Circle)) = c ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [cubeLoopFamily, circleLift_coe _ _ _ (by simpa using ht)]
  rw [cubeLoopParam, ContinuousMap.comp_apply, cubeParamHom_apply]
  rfl

private theorem cubeLoopFamily_zero (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    cubeLoopFamily c (p, ((0 : ℝ) : Circle)) = x := by
  rw [cubeLoopFamily_coe c p (t := 0) (by constructor <;> norm_num)]
  exact c.property _ ⟨2, Or.inl rfl⟩

private theorem cubeLoopFamily_base (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) :
    ((cubeLoopFamily c).curry p) 0 = x := by
  rw [ContinuousMap.curry_apply, ← AddCircle.coe_zero (1 : ℝ)]
  exact cubeLoopFamily_zero c p

private def cubeAdjunctVal (c : GenLoop (Fin 3) X x) : C(I^(Fin 2), BasedContinuousLoop x) where
  toFun p := ⟨(cubeLoopFamily c).curry p, cubeLoopFamily_base c p⟩
  continuous_toFun :=
    ((cubeLoopFamily c).curry).continuous.subtype_mk (cubeLoopFamily_base c)

private theorem cubeAdjunctVal_coe (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (cubeAdjunctVal c p : C(Circle, X)) (t : Circle) =
      c ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [cubeAdjunctVal]
  exact cubeLoopFamily_coe c p ht

private theorem mem_boundary_three_of_mem_boundary_two (p : I^(Fin 2))
    (hp : p ∈ Cube.boundary (Fin 2)) (t : I) :
    ![p 0, p 1, t] ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hp
  fin_cases i
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

private theorem cubeAdjunctVal_boundary (c : GenLoop (Fin 3) X x) {p : I^(Fin 2)}
    (hp : p ∈ Cube.boundary (Fin 2)) :
    cubeAdjunctVal c p = basedConstantLoop x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  rw [cubeAdjunctVal_coe c p ht]
  exact c.property _
    (mem_boundary_three_of_mem_boundary_two p hp ⟨t, subinterval_mem_I ht⟩)

private def cubeAdjunctGenLoop (c : GenLoop (Fin 3) X x) :
    GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  ⟨cubeAdjunctVal c, by intro p hp; exact cubeAdjunctVal_boundary c hp⟩

private theorem cubeAdjunctGenLoop_coe (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    (cubeAdjunctGenLoop c p : C(Circle, X)) (t : Circle) =
      c ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] :=
  cubeAdjunctVal_coe c p ht

private theorem cubeAdjunctGenLoop_apply (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) (t : I) :
    (cubeAdjunctGenLoop c p : C(Circle, X)) ((t : ℝ) : Circle) = c ![p 0, p 1, t] := by
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · rw [cubeAdjunctGenLoop_coe c p ⟨t.2.1, ht⟩]
  · have hz : ((t : ℝ) : Circle) = 0 := by rw [ht, AddCircle.coe_period (1 : ℝ)]
    have h1 : (cubeAdjunctGenLoop c p : C(Circle, X)) ((t : ℝ) : Circle) = x := by
      rw [hz]
      exact (cubeAdjunctGenLoop c p).2
    have h2 : c ![p 0, p 1, t] = x := c.property _ ⟨2, Or.inr (Subtype.ext ht)⟩
    rw [h1, h2]

private theorem cubeAdjunctGenLoop_unique (c : GenLoop (Fin 3) X x)
    (A : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (hA : ∀ p : I^(Fin 2), ∀ t : I,
      (A p : C(Circle, X)) ((t : ℝ) : Circle) = c ![p 0, p 1, t]) :
    A = cubeAdjunctGenLoop c := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (hA p ⟨t, subinterval_mem_I ht⟩).trans (cubeAdjunctGenLoop_coe c p ht).symm

theorem exists_unique_cubeAdjunct (c : GenLoop (Fin 3) X x) :
    ∃! A : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x),
      ∀ p : I^(Fin 2), ∀ t : I,
        (A p).1 ((t : ℝ) : Circle) = c ![p 0, p 1, t] :=
  ⟨cubeAdjunctGenLoop c, cubeAdjunctGenLoop_apply c, fun A hA =>
    cubeAdjunctGenLoop_unique c A hA⟩

def cubeAdjunct (c : GenLoop (Fin 3) X x) :
    GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  Classical.choose (exists_unique_cubeAdjunct c)

theorem cubeAdjunct_apply (c : GenLoop (Fin 3) X x) (p : I^(Fin 2)) (t : I) :
    (cubeAdjunct c p).1 ((t : ℝ) : Circle) = c ![p 0, p 1, t] :=
  (Classical.choose_spec (exists_unique_cubeAdjunct c)).1 p t

private def cubeHomotopyParamHom :
    C((I × I^(Fin 2)) × Icc (0 : ℝ) (0 + 1), I × I^(Fin 3)) where
  toFun q := (q.1.1, ![q.1.2 0, q.1.2 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩])
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_fst
    · apply continuous_pi
      intro i
      fin_cases i
      · exact (continuous_apply (0 : Fin 2)).comp continuous_fst.snd
      · exact (continuous_apply (1 : Fin 2)).comp continuous_fst.snd
      · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _

private theorem cubeHomotopyParamHom_apply (q : (I × I^(Fin 2)) × Icc (0 : ℝ) (0 + 1)) :
    cubeHomotopyParamHom q =
      (q.1.1, ![q.1.2 0, q.1.2 1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩]) := rfl

private theorem cubeHomotopyParamHom_zero (q : I × I^(Fin 2)) :
    cubeHomotopyParamHom (q, zeroPt) = (q.1, ![q.2 0, q.2 1, (0 : I)]) := by
  rw [cubeHomotopyParamHom_apply]
  rfl

private theorem cubeHomotopyParamHom_one (q : I × I^(Fin 2)) :
    cubeHomotopyParamHom (q, onePt) = (q.1, ![q.2 0, q.2 1, (1 : I)]) := by
  rw [cubeHomotopyParamHom_apply, onePt_I]

private theorem cubeHomotopyParamHom_endpoints {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) :
    H.toContinuousMap (cubeHomotopyParamHom (q, zeroPt)) =
      H.toContinuousMap (cubeHomotopyParamHom (q, onePt)) := by
  rw [cubeHomotopyParamHom_zero q, cubeHomotopyParamHom_one q]
  exact ((H.eq_fst q.1 ⟨2, Or.inl rfl⟩).trans (c.property _ ⟨2, Or.inl rfl⟩)).trans
    (((c.property _ ⟨2, Or.inr rfl⟩).symm).trans (H.eq_fst q.1 ⟨2, Or.inr rfl⟩).symm)

private def cubeHomotopyLoopFamily {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3))) :
    C(I × I^(Fin 2), C(Circle, X)) :=
  (circleLift (X := X) (Y := I × I^(Fin 2))
    (H.toContinuousMap.comp cubeHomotopyParamHom)
    (fun q => cubeHomotopyParamHom_endpoints H q)).curry

private theorem cubeHomotopyLoopFamily_coe {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    cubeHomotopyLoopFamily H q (t : Circle) =
      H (q.1, ![q.2 0, q.2 1, ⟨t, subinterval_mem_I ht⟩]) := by
  rw [cubeHomotopyLoopFamily, ContinuousMap.curry_apply,
    circleLift_coe _ _ _ (by simpa using ht)]
  rw [ContinuousMap.comp_apply, cubeHomotopyParamHom_apply]
  rfl

private theorem cubeHomotopyLoopFamily_base {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) :
    cubeHomotopyLoopFamily H q 0 = x := by
  rw [cubeHomotopyLoopFamily, ContinuousMap.curry_apply, ← AddCircle.coe_zero (1 : ℝ),
    circleLift_coe _ _ _ (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1))]
  rw [ContinuousMap.comp_apply, cubeHomotopyParamHom_apply]
  exact (H.eq_fst q.1 ⟨2, Or.inl rfl⟩).trans (c.property _ ⟨2, Or.inl rfl⟩)

private def cubeAdjunctHomotopy {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3))) :
    C(I × I^(Fin 2), BasedContinuousLoop x) where
  toFun q := ⟨cubeHomotopyLoopFamily H q, cubeHomotopyLoopFamily_base H q⟩
  continuous_toFun :=
    (cubeHomotopyLoopFamily H).continuous.subtype_mk (cubeHomotopyLoopFamily_base H)

private theorem cubeAdjunctHomotopy_coe {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (q : I × I^(Fin 2)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (cubeAdjunctHomotopy H q : C(Circle, X)) (t : Circle) =
      H (q.1, ![q.2 0, q.2 1, ⟨t, subinterval_mem_I ht⟩]) :=
  cubeHomotopyLoopFamily_coe H q ht

private theorem cubeAdjunctHomotopy_zero {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (p : I^(Fin 2)) :
    cubeAdjunctHomotopy H (0, p) = (cubeAdjunct c).val p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (cubeAdjunctHomotopy_coe H (0, p) ht).trans
    ((H.apply_zero _).trans (cubeAdjunct_apply c p ⟨t, subinterval_mem_I ht⟩).symm)

private theorem cubeAdjunctHomotopy_one {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (p : I^(Fin 2)) :
    cubeAdjunctHomotopy H (1, p) = (cubeAdjunct d).val p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (cubeAdjunctHomotopy_coe H (1, p) ht).trans
    ((H.apply_one _).trans (cubeAdjunct_apply d p ⟨t, subinterval_mem_I ht⟩).symm)

private theorem cubeAdjunctHomotopy_eq_const {c d : GenLoop (Fin 3) X x}
    (H : ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)))
    (s : I) {p : I^(Fin 2)} (hp : p ∈ Cube.boundary (Fin 2)) :
    cubeAdjunctHomotopy H (s, p) = basedConstantLoop x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  exact (cubeAdjunctHomotopy_coe H (s, p) ht).trans
    ((H.eq_fst s (mem_boundary_three_of_mem_boundary_two p hp ⟨t, subinterval_mem_I ht⟩)).trans
      (c.property _ (mem_boundary_three_of_mem_boundary_two p hp ⟨t, subinterval_mem_I ht⟩)))

theorem cubeAdjunct_homotopic {c d : GenLoop (Fin 3) X x}
    (h : c.val.HomotopicRel d.val (Cube.boundary (Fin 3))) :
    (cubeAdjunct c).val.HomotopicRel (cubeAdjunct d).val (Cube.boundary (Fin 2)) := by
  obtain ⟨H⟩ := h
  exact ⟨{ toContinuousMap := cubeAdjunctHomotopy H
           map_zero_left := fun p => cubeAdjunctHomotopy_zero H p
           map_one_left := fun p => cubeAdjunctHomotopy_one H p
           prop' := fun s p hp =>
             (cubeAdjunctHomotopy_eq_const H s hp).trans
               ((cubeAdjunct c).property p hp).symm }⟩


def basedLoopAdjunction (x : X) : HomotopyGroup (Fin 3) X x →
    HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  Quotient.map cubeAdjunct (fun _ _ h => cubeAdjunct_homotopic h)

private theorem cubeAdjunct_const (x : X) :
    cubeAdjunct (GenLoop.const : GenLoop (Fin 3) X x) = GenLoop.const :=
  ((Classical.choose_spec
      (exists_unique_cubeAdjunct (GenLoop.const : GenLoop (Fin 3) X x))).2
    GenLoop.const (fun _ _ => rfl)).symm

private theorem basedLoopAdjunction_mk (x : X) (c : GenLoop (Fin 3) X x) :
    basedLoopAdjunction x (Quotient.mk _ c) = Quotient.mk _ (cubeAdjunct c) :=
  Quotient.map_mk cubeAdjunct (fun _ _ h => cubeAdjunct_homotopic h) c

private theorem update_fin_two (p : I^(Fin 2)) (u : I) :
    Function.update p 0 u = ![u, p 1] := by
  funext i
  fin_cases i <;> simp

private theorem update_fin_three (p : I^(Fin 2)) (u t : I) :
    Function.update ![p 0, p 1, t] (0 : Fin 3) u = ![u, p 1, t] := by
  funext i
  fin_cases i <;> simp

private theorem vecThree_zero (p : I^(Fin 2)) (t : I) :
    (![p 0, p 1, t] : I^(Fin 3)) 0 = p 0 := rfl

private theorem cubeAdjunct_transAt_left (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hP : (p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 2) (cubeAdjunct d) (cubeAdjunct c) p).1
        ((t : ℝ) : Circle) =
      d ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ)), p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, if_pos hP,
    cubeAdjunct_apply d (Function.update p 0 (Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ))))
      ⟨t, subinterval_mem_I ht⟩, update_fin_two]
  rfl

private theorem cubeAdjunct_transAt_right (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (hP : ¬(p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 2) (cubeAdjunct d) (cubeAdjunct c) p).1
        ((t : ℝ) : Circle) =
      c ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ) - 1), p 1,
        ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, if_neg hP,
    cubeAdjunct_apply c
      (Function.update p 0 (Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ) - 1)))
      ⟨t, subinterval_mem_I ht⟩, update_fin_two]
  rfl

private theorem cubeTransAt_left (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hP : (p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 3) d c) ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] =
      d ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ)), p 1, ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, vecThree_zero p ⟨t, subinterval_mem_I ht⟩, if_pos hP,
    update_fin_three]

private theorem cubeTransAt_right (c d : GenLoop (Fin 3) X x) (p : I^(Fin 2)) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hP : ¬(p 0 : ℝ) ≤ 1 / 2) :
    (GenLoop.transAt (0 : Fin 3) d c) ![p 0, p 1, ⟨t, subinterval_mem_I ht⟩] =
      c ![Set.projIcc 0 1 zero_le_one (2 * (p 0 : ℝ) - 1), p 1,
        ⟨t, subinterval_mem_I ht⟩] := by
  rw [GenLoop.transAt, GenLoop.coe_copy, vecThree_zero p ⟨t, subinterval_mem_I ht⟩, if_neg hP,
    update_fin_three]

private theorem cubeAdjunct_transAt (c d : GenLoop (Fin 3) X x) :
    cubeAdjunct (GenLoop.transAt (0 : Fin 3) d c) =
      GenLoop.transAt (0 : Fin 2) (cubeAdjunct d) (cubeAdjunct c) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  refine (cubeAdjunct_apply (GenLoop.transAt (0 : Fin 3) d c) p
    ⟨t, subinterval_mem_I ht⟩).trans ?_
  by_cases hP : (p 0 : ℝ) ≤ 1 / 2
  · exact (cubeTransAt_left c d p ht hP).trans (cubeAdjunct_transAt_left c d p ht hP).symm
  · exact (cubeTransAt_right c d p ht hP).trans (cubeAdjunct_transAt_right c d p ht hP).symm

private def twoCubeCurried (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x)) :
    C(I^(Fin 2), C(Circle, X)) where
  toFun p := (a p : C(Circle, X))
  continuous_toFun := continuous_subtype_val.comp a.val.continuous

private theorem twoCubeCurried_apply
    (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x)) (p : I^(Fin 2)) :
    twoCubeCurried a p = (a p : C(Circle, X)) := rfl

private theorem uncurriedTwoCubeCurried_apply
    (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (p : I^(Fin 2)) (w : Circle) :
    ContinuousMap.uncurry (twoCubeCurried a) (p, w) = (a p : C(Circle, X)) w := by
  rw [ContinuousMap.uncurry_apply]
  rfl

private theorem circleCoe_zero_of_eq_zero {t : I} (h : t = 0) :
    ((t : ℝ) : Circle) = 0 := by
  rw [h]
  rfl

private theorem circleCoe_zero_of_eq_one {t : I} (h : t = 1) :
    ((t : ℝ) : Circle) = 0 := by
  have h' : (t : ℝ) = 1 := by simpa using congrArg (fun s : I => (s : ℝ)) h
  rw [h']
  exact AddCircle.coe_period (1 : ℝ)

private theorem vecThree_eta (z : I^(Fin 3)) :
    ![(![z 0, z 1] : I^(Fin 2)) 0, (![z 0, z 1] : I^(Fin 2)) 1, z 2] = z := by
  funext i
  fin_cases i <;> rfl

private theorem vecTwo_eta_sub (p : I^(Fin 2)) (t : I) :
    ![(![p 0, p 1, t] : I^(Fin 3)) 0, (![p 0, p 1, t] : I^(Fin 3)) 1] = p := by
  funext i
  fin_cases i <;> rfl

private def threeCubeParamHom : C(I^(Fin 3), (I^(Fin 2)) × Circle) where
  toFun z := (![z 0, z 1], ((z 2 : ℝ) : Circle))
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_apply 0
      · exact continuous_apply 1
    · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
        (continuous_subtype_val.comp (continuous_apply 2))

private theorem threeCubeParamHom_apply (z : I^(Fin 3)) :
    threeCubeParamHom z = (![z 0, z 1], ((z 2 : ℝ) : Circle)) := rfl

private theorem twoCube_boundary_of_zero {z : I^(Fin 3)} (h : z 0 = 0 ∨ z 0 = 1) :
    (![z 0, z 1] : I^(Fin 2)) ∈ Cube.boundary (Fin 2) :=
  ⟨0, by simpa using h⟩

private theorem twoCube_boundary_of_one {z : I^(Fin 3)} (h : z 1 = 0 ∨ z 1 = 1) :
    (![z 0, z 1] : I^(Fin 2)) ∈ Cube.boundary (Fin 2) :=
  ⟨1, by simpa using h⟩

private def twoCubeAdjunctFun (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) : C(I^(Fin 3), X) :=
  (ContinuousMap.uncurry (twoCubeCurried a)).comp threeCubeParamHom

private theorem twoCubeAdjunctFun_apply (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) (z : I^(Fin 3)) :
    twoCubeAdjunctFun a z = (a ![z 0, z 1] : C(Circle, X)) ((z 2 : ℝ) : Circle) := by
  rw [twoCubeAdjunctFun, ContinuousMap.comp_apply, threeCubeParamHom_apply,
    uncurriedTwoCubeCurried_apply]

private def twoCubeAdjunct (a : GenLoop (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x)) :
    GenLoop (Fin 3) X x :=
  ⟨twoCubeAdjunctFun a, by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    fin_cases i
    · exact (congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X))
          ((z 2 : ℝ) : Circle))
        (a.property ![z 0, z 1] (twoCube_boundary_of_zero hi))).trans rfl
    · exact (congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X))
          ((z 2 : ℝ) : Circle))
        (a.property ![z 0, z 1] (twoCube_boundary_of_one hi))).trans rfl
    · have hz2 : ((z 2 : ℝ) : Circle) = 0 := by
        rcases hi with h | h
        · exact circleCoe_zero_of_eq_zero h
        · exact circleCoe_zero_of_eq_one h
      exact (congrArg (fun w : Circle => (a ![z 0, z 1] : C(Circle, X)) w) hz2).trans
        (a ![z 0, z 1]).2⟩

private theorem twoCubeAdjunct_apply (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) (z : I^(Fin 3)) :
    twoCubeAdjunct a z = (a ![z 0, z 1] : C(Circle, X)) ((z 2 : ℝ) : Circle) := by
  exact twoCubeAdjunctFun_apply a z

private theorem twoCubeAdjunct_adjunct (a : GenLoop (Fin 2) (BasedContinuousLoop x)
    (basedConstantLoop x)) :
    cubeAdjunct (twoCubeAdjunct a) = a :=
  ((Classical.choose_spec (exists_unique_cubeAdjunct (twoCubeAdjunct a))).2 a (fun p t => by
    rw [twoCubeAdjunct_apply]
    exact congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((t : ℝ) : Circle))
      (congrArg a (vecTwo_eta_sub p t)).symm)).symm

private def twoCubeHomotopyParamHom : C(I × I^(Fin 3), (I × I^(Fin 2)) × Circle) where
  toFun q := ((q.1, ![q.2 0, q.2 1]), ((q.2 2 : ℝ) : Circle))
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.prodMk
      · exact continuous_fst
      · apply continuous_pi
        intro i
        fin_cases i <;> fun_prop
    · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
        (continuous_subtype_val.comp ((continuous_apply 2).comp continuous_snd))

private theorem twoCubeHomotopyParamHom_apply (q : I × I^(Fin 3)) :
    twoCubeHomotopyParamHom q = ((q.1, ![q.2 0, q.2 1]), ((q.2 2 : ℝ) : Circle)) := rfl

private def twoCubeHomotopyCurried {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2))) :
    C(I × I^(Fin 2), C(Circle, X)) where
  toFun q := (A q : C(Circle, X))
  continuous_toFun := continuous_subtype_val.comp A.toContinuousMap.continuous

private theorem uncurriedTwoCubeHomotopyCurried_apply {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (q : I × I^(Fin 2)) (w : Circle) :
    ContinuousMap.uncurry (twoCubeHomotopyCurried A) (q, w) = (A q : C(Circle, X)) w := by
  rw [ContinuousMap.uncurry_apply]
  rfl

private def twoCubeHomotopyUncurried {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2))) : C(I × I^(Fin 3), X) :=
  (ContinuousMap.uncurry (twoCubeHomotopyCurried A)).comp twoCubeHomotopyParamHom

private theorem twoCubeHomotopyUncurried_apply {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (s : I) (z : I^(Fin 3)) :
    twoCubeHomotopyUncurried A (s, z) =
      (A (s, ![z 0, z 1]) : C(Circle, X)) ((z 2 : ℝ) : Circle) := by
  rw [twoCubeHomotopyUncurried, ContinuousMap.comp_apply, twoCubeHomotopyParamHom_apply,
    uncurriedTwoCubeHomotopyCurried_apply]

private theorem twoCubeHomotopy_const_of_boundary {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (s : I) {z : I^(Fin 3)} (hb : ![z 0, z 1] ∈ Cube.boundary (Fin 2)) :
    (A (s, ![z 0, z 1]) : C(Circle, X)) ((z 2 : ℝ) : Circle) = x :=
  (congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
    (A.prop s ![z 0, z 1] hb)).trans
  ((congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
    ((cubeAdjunct c).property ![z 0, z 1] hb)).trans rfl)

private theorem twoCubeHomotopy_const_of_circle_eq {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2)))
    (s : I) {z : I^(Fin 3)} (h : ((z 2 : ℝ) : Circle) = 0) :
    (A (s, ![z 0, z 1]) : C(Circle, X)) ((z 2 : ℝ) : Circle) = x :=
  (congrArg (fun w : Circle => (A (s, ![z 0, z 1]) : C(Circle, X)) w) h).trans
    (A (s, ![z 0, z 1])).2

private def cubeHomotopyOfAdjunctHomotopy {c d : GenLoop (Fin 3) X x}
    (A : ContinuousMap.HomotopyRel (cubeAdjunct c).val (cubeAdjunct d).val
      (Cube.boundary (Fin 2))) :
    ContinuousMap.HomotopyRel c.val d.val (Cube.boundary (Fin 3)) where
  toContinuousMap := twoCubeHomotopyUncurried A
  map_zero_left := fun z =>
    (twoCubeHomotopyUncurried_apply A 0 z).trans
      ((congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
        (A.apply_zero ![z 0, z 1])).trans
      ((cubeAdjunct_apply c ![z 0, z 1] (z 2)).trans (congrArg c (vecThree_eta z))))
  map_one_left := fun z =>
    (twoCubeHomotopyUncurried_apply A 1 z).trans
      ((congrArg (fun γ : BasedContinuousLoop x => (γ : C(Circle, X)) ((z 2 : ℝ) : Circle))
        (A.apply_one ![z 0, z 1])).trans
      ((cubeAdjunct_apply d ![z 0, z 1] (z 2)).trans (congrArg d (vecThree_eta z))))
  prop' := fun s z hz => by
    have h := twoCubeHomotopyUncurried_apply A s z
    obtain ⟨i, hi⟩ := hz
    fin_cases i
    · exact h.trans ((twoCubeHomotopy_const_of_boundary A s (twoCube_boundary_of_zero hi)).trans
        (c.property z ⟨0, hi⟩).symm)
    · exact h.trans ((twoCubeHomotopy_const_of_boundary A s (twoCube_boundary_of_one hi)).trans
        (c.property z ⟨1, hi⟩).symm)
    · have hz2 : ((z 2 : ℝ) : Circle) = 0 := by
        rcases hi with hh | hh
        · exact circleCoe_zero_of_eq_zero hh
        · exact circleCoe_zero_of_eq_one hh
      exact h.trans ((twoCubeHomotopy_const_of_circle_eq A s hz2).trans
        (c.property z ⟨2, hi⟩).symm)

theorem basedLoopAdjunction_bijective (x : X) : Function.Bijective (basedLoopAdjunction x) := by
  constructor
  · rintro a b hab
    induction a using Quotient.inductionOn with
    | h c =>
      induction b using Quotient.inductionOn with
      | h d =>
        rw [basedLoopAdjunction_mk, basedLoopAdjunction_mk] at hab
        obtain ⟨A⟩ := Quotient.exact hab
        exact Quotient.sound ⟨cubeHomotopyOfAdjunctHomotopy A⟩
  · intro b
    induction b using Quotient.inductionOn with
    | h a =>
      exact ⟨Quotient.mk _ (twoCubeAdjunct a), by
        rw [basedLoopAdjunction_mk]
        exact congrArg (Quotient.mk _) (twoCubeAdjunct_adjunct a)⟩

theorem basedLoopAdjunction_one (x : X) : basedLoopAdjunction x 1 = 1 := by
  rw [HomotopyGroup.one_def, basedLoopAdjunction_mk, cubeAdjunct_const x]
  exact HomotopyGroup.one_def.symm

theorem basedLoopAdjunction_mul (a b : HomotopyGroup (Fin 3) X x) :
    basedLoopAdjunction x (a * b) = basedLoopAdjunction x a * basedLoopAdjunction x b := by
  induction a using Quotient.inductionOn with
  | h c =>
    induction b using Quotient.inductionOn with
    | h d =>
      have hm : ((· * ·) : HomotopyGroup (Fin 3) X x → HomotopyGroup (Fin 3) X x →
          HomotopyGroup (Fin 3) X x) ⟦c⟧ ⟦d⟧ =
          (⟦GenLoop.transAt (0 : Fin 3) d c⟧ : HomotopyGroup (Fin 3) X x) :=
        HomotopyGroup.mul_spec (i := (0 : Fin 3)) (p := c) (q := d)
      have h3 : basedLoopAdjunction x
            (((· * ·) : HomotopyGroup (Fin 3) X x → HomotopyGroup (Fin 3) X x →
              HomotopyGroup (Fin 3) X x) ⟦c⟧ ⟦d⟧) =
          (((· * ·) : HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) →
              HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) →
              HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
            (basedLoopAdjunction x ⟦c⟧) (basedLoopAdjunction x ⟦d⟧)) := by
        rw [hm, basedLoopAdjunction_mk, basedLoopAdjunction_mk, basedLoopAdjunction_mk]
        exact (congrArg (Quotient.mk _) (cubeAdjunct_transAt c d)).trans
          (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := cubeAdjunct c)
            (q := cubeAdjunct d)).symm
      exact h3

def basedLoopAdjunctionEquiv (x : X) : HomotopyGroup (Fin 3) X x ≃*
    HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x) :=
  MulEquiv.ofBijective
    ({ toFun := basedLoopAdjunction x
       map_one' := basedLoopAdjunction_one x
       map_mul' := basedLoopAdjunction_mul } : HomotopyGroup (Fin 3) X x →*
      HomotopyGroup (Fin 2) (BasedContinuousLoop x) (basedConstantLoop x))
    (basedLoopAdjunction_bijective x)


def freeLoopAdjunction (x : X) : HomotopyGroup (Fin 3) X x →
    HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  basedHomotopyMap (basedLoopInclusion x) (basedConstantLoop x) ∘ basedLoopAdjunction x

def freeLoopAdjunctionHom (x : X) : HomotopyGroup (Fin 3) X x →*
    HomotopyGroup (Fin 2) (ContinuousFreeLoop X) (constantLoops x) :=
  (basedHomotopyHom (basedLoopInclusion x) (basedConstantLoop x)).comp
    (basedLoopAdjunctionEquiv x).toMonoidHom

@[simp] theorem freeLoopAdjunctionHom_apply (x : X) (a : HomotopyGroup (Fin 3) X x) :
    freeLoopAdjunctionHom x a = freeLoopAdjunction x a := rfl

theorem freeLoopAdjunction_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (a : HomotopyGroup (Fin 3) X x) :
    basedHomotopyMap (loopPostcompose f) (constantLoops x) (freeLoopAdjunction x a) =
      freeLoopAdjunction (f x) (basedHomotopyMap f x a) := by
  sorry

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hConnected : ConnectedSpace M] [hSimplyConnected : SimplyConnectedSpace M]

include hT2 hCompact hConnected hSimplyConnected

theorem rfs_free_loop_class (o : TangentOrientationSection M) (q : M) :
    PathConnectedSpace (ContinuousFreeLoop M) ∧ SimplyConnectedSpace (ContinuousFreeLoop M) ∧
    Function.Bijective (freeLoopAdjunction q) ∧
    Function.Bijective (forgetBasedSphere (constantLoops q)) := by
  sorry

def freeLoopAdjunctionEquiv (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 3) M q ≃*
      HomotopyGroup (Fin 2) (ContinuousFreeLoop M) (constantLoops q) :=
  MulEquiv.ofBijective (freeLoopAdjunctionHom q) (rfs_free_loop_class o q).2.2.1

def positiveBasedLoopClass (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 2) (ContinuousFreeLoop M) (constantLoops q) :=
  freeLoopAdjunction q (positiveHomotopyClass o q)

def positiveFreeLoopClass (o : TangentOrientationSection M) : FreeSphereClass M :=
  let q : M := Classical.choice inferInstance
  forgetBasedSphere (constantLoops q) (positiveBasedLoopClass o q)

theorem positiveFreeLoopClass_eq (o : TangentOrientationSection M) (q : M) :
    positiveFreeLoopClass o = forgetBasedSphere (constantLoops q) (positiveBasedLoopClass o q) := by
  sorry

theorem positiveFreeLoopClass_nontrivial (o : TangentOrientationSection M) (q : M) :
    positiveFreeLoopClass o ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2) (constantLoops q)) := by
  intro h
  rw [positiveFreeLoopClass_eq o q, ← forgetBasedSphere_one (constantLoops q)] at h
  have hb := (rfs_free_loop_class o q).2.2.2.injective h
  have ha : positiveHomotopyClass o q = 1 := by
    apply (rfs_free_loop_class o q).2.2.1.injective
    exact hb.trans (freeLoopAdjunctionHom q).map_one.symm
  have h10 : (1 : ℤ) = 0 := (positiveHomotopyClass_infiniteOrder o q)
    (by simpa only [zpow_one, zpow_zero] using ha)
  norm_num at h10

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] hT2 hCompact hConnected in
theorem every_continuousLoop_contractible (γ : ContinuousFreeLoop M) : IsContractibleLoop γ := by
  let pγ : Path (γ 0) (γ 0) :=
    { toFun := fun u : I => γ ((u : ℝ) : Circle)
      continuous_toFun :=
        γ.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)
      source' := rfl
      target' := congrArg γ (AddCircle.coe_period (1 : ℝ)) }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic pγ (Path.refl (γ 0))
  let φ : C(I × Icc (0 : ℝ) (0 + 1), M) :=
    ⟨fun q => F.toContinuousMap (q.1, ⟨(q.2 : ℝ), subinterval_coe_mem_I q.2⟩), by
      apply Continuous.comp F.toContinuousMap.continuous
      apply Continuous.prodMk continuous_fst
      exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _⟩
  have hφ : ∀ s : I, φ (s, zeroPt) = φ (s, onePt) := fun s =>
    ((congrArg (fun u : I => F.toContinuousMap (s, u)) zeroPt_I).trans
      ((F.eq_fst s (by simp)).trans pγ.source')).trans
    (((congrArg (fun u : I => F.toContinuousMap (s, u)) onePt_I).trans
      ((F.eq_fst s (by simp)).trans pγ.target')).symm)
  refine ⟨γ 0, ⟨circleLift (X := M) (Y := I) φ hφ, ?_, ?_⟩⟩
  · intro z
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    exact (circleLift_coe φ hφ 0 (by simpa using ht)).trans ((F.apply_zero _).trans rfl)
  · intro z
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    exact (circleLift_coe φ hφ 1 (by simpa using ht)).trans ((F.apply_one _).trans rfl)

def toContractibleLoops : C(ContinuousFreeLoop M, ContractibleContinuousLoop M) :=
  ⟨fun γ => ⟨γ, every_continuousLoop_contractible γ⟩, continuous_id.subtype_mk _⟩

def positiveFreeContractibleClass (o : TangentOrientationSection M) : FreeContractibleSphereClass M :=
  FreeHomotopyClass.map toContractibleLoops (positiveFreeLoopClass o)

theorem positiveFreeContractibleClass_inclusion (o : TangentOrientationSection M) :
    FreeHomotopyClass.map contractibleLoopInclusion (positiveFreeContractibleClass o) =
      positiveFreeLoopClass o := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  exact FreeHomotopyClass.map_id _

theorem positiveFreeContractibleClass_nontrivial (o : TangentOrientationSection M) (q : M) :
    positiveFreeContractibleClass o ≠ FreeHomotopyClass.mk
      (ContinuousMap.const (Sphere 2) (⟨constantLoops q, isContractibleLoop_constant q⟩ :
        ContractibleContinuousLoop M)) := by
  intro h
  apply positiveFreeLoopClass_nontrivial o q
  have hh := congrArg (FreeHomotopyClass.map contractibleLoopInclusion) h
  rw [positiveFreeContractibleClass_inclusion, FreeHomotopyClass.map_mk] at hh
  exact hh

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]

theorem positiveFreeLoopClass_natural (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1) :
    FreeHomotopyClass.map (loopPostcompose f) (positiveFreeLoopClass oM) =
      positiveFreeLoopClass oN := by
  sorry

theorem positiveFreeContractibleClass_natural (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (hf : orientedDegree oM oN f = 1) :
    FreeHomotopyClass.map (contractibleLoopPostcompose f) (positiveFreeContractibleClass oM) =
      positiveFreeContractibleClass oN := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  have hcomp : (contractibleLoopPostcompose f).comp (toContractibleLoops (M := M)) =
      (toContractibleLoops (M := N)).comp (loopPostcompose f) := rfl
  rw [hcomp, FreeHomotopyClass.map_comp, positiveFreeLoopClass_natural oM oN f hf]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
