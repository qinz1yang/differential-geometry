import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03Differentiability
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

noncomputable local instance tensorialityModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensorialityModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensorialityModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensorialityModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensorialityTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensorialityTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance tensorialityTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance tensorialityTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tensorialityTangentTrilinearNormedAddCommGroup x).toAddCommGroup

local instance tensorialityTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensorialityTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensorialityTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

local instance tensorialityTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tensorialityTangentTrilinearModule x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

local instance tensorialityTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensorialityTangentTrilinearNormedAddCommGroup x
  infer_instance

noncomputable local instance tensorialityTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tensorialityTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [FiniteDimensional ℝ E] in
lemma tensor03Scalar_tensorialAt_X
    (_covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) (Y Z W : Π x : M, TangentSpace I x)
    (_hY : MDiffAt (T% Y) x) (_hZ : MDiffAt (T% Z) x) (_hW : MDiffAt (T% W) x) :
    TensorialAt I E (tensor03Scalar cov T x · Y Z W) x where
  smul {f X} _hf _hX := by
    classical
    unfold tensor03Scalar
    have hfX : (f • X) x = f x • X x := rfl
    rw [hfX]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x).map_smul]
    rw [(cov.toFun Y x).map_smul, (cov.toFun Z x).map_smul, (cov.toFun W x).map_smul]
    rw [(T x).map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul]
    rw [smul_sub, smul_sub, smul_sub]
  add {X X'} _hX _hX' := by
    classical
    unfold tensor03Scalar
    have hXX' : (X + X') x = X x + X' x := rfl
    rw [hXX']
    rw [map_add, (cov.toFun Y x).map_add, (cov.toFun Z x).map_add, (cov.toFun W x).map_add]
    rw [(T x).map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel

omit [FiniteDimensional ℝ E] in
lemma tensor03Scalar_tensorialAt_Y
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor03 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Z W : Π x : M, TangentSpace I x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x) :
    TensorialAt I E (tensor03Scalar cov T x X · Z W) x where
  smul {g Y} hg hY := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b ((g • Y) b) (Z b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      change T b ((g • Y) b) (Z b) (W b) = g b * h b
      have : (g • Y) b = g b • Y b := rfl
      rw [this, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b ((g • Y) b) (Z b) (W b)) x (X x)
        - T x (cov.toFun (g • Y) x (X x)) (Z x) (W x)
        - T x ((g • Y) x) (cov.toFun Z x (X x)) (W x)
        - T x ((g • Y) x) (Z x) (cov.toFun W x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hY hg (Set.mem_univ x)]
    have h_gY_x : (g • Y) x = g x • Y x := rfl
    rw [h_gY_x]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  add {Y Y'} hY hY' := by
    classical
    change extDerivFun (I := I) (fun b => T b ((Y + Y') b) (Z b) (W b)) x (X x)
        - T x (cov.toFun (Y + Y') x (X x)) (Z x) (W x)
        - T x ((Y + Y') x) (cov.toFun Z x (X x)) (W x)
        - T x ((Y + Y') x) (Z x) (cov.toFun W x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y' b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y' x (X x)) (Z x) (W x)
        - T x (Y' x) (cov.toFun Z x (X x)) (W x)
        - T x (Y' x) (Z x) (cov.toFun W x (X x)))
    have hadd_fun : (fun b : M => T b ((Y + Y') b) (Z b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T b (Y' b) (Z b) (W b)) := by
      funext b
      change T b ((Y + Y') b) (Z b) (W b) = T b (Y b) (Z b) (W b) + T b (Y' b) (Z b) (W b)
      have : (Y + Y') b = Y b + Y' b := rfl
      rw [this, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y' b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY' hZ hW
    have hext_add : extDerivFun (I := I) (fun b => T b ((Y + Y') b) (Z b) (W b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T b (Y' b) (Z b) (W b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add]
    rw [covOn.add hY hY' (Set.mem_univ x)]
    have h_YY' : (Y + Y') x = Y x + Y' x := rfl
    rw [h_YY']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

omit [FiniteDimensional ℝ E] in
lemma tensor03Scalar_tensorialAt_Z
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor03 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Y W : Π x : M, TangentSpace I x) (hY : MDiffAt (T% Y) x) (hW : MDiffAt (T% W) x) :
    TensorialAt I E (tensor03Scalar cov T x X Y · W) x where
  smul {g Z} hg hZ := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b (Y b) ((g • Z) b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      change T b (Y b) ((g • Z) b) (W b) = g b * h b
      have : (g • Z) b = g b • Z b := rfl
      rw [this, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b (Y b) ((g • Z) b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) ((g • Z) x) (W x)
        - T x (Y x) (cov.toFun (g • Z) x (X x)) (W x)
        - T x (Y x) ((g • Z) x) (cov.toFun W x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hZ hg (Set.mem_univ x)]
    have h_gZ_x : (g • Z) x = g x • Z x := rfl
    rw [h_gZ_x]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  add {Z Z'} hZ hZ' := by
    classical
    change extDerivFun (I := I) (fun b => T b (Y b) ((Z + Z') b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) ((Z + Z') x) (W x)
        - T x (Y x) (cov.toFun (Z + Z') x (X x)) (W x)
        - T x (Y x) ((Z + Z') x) (cov.toFun W x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y b) (Z' b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z' x) (W x)
        - T x (Y x) (cov.toFun Z' x (X x)) (W x)
        - T x (Y x) (Z' x) (cov.toFun W x (X x)))
    have hadd_fun : (fun b : M => T b (Y b) ((Z + Z') b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T b (Y b) (Z' b) (W b)) := by
      funext b
      change T b (Y b) ((Z + Z') b) (W b) = T b (Y b) (Z b) (W b) + T b (Y b) (Z' b) (W b)
      have : (Z + Z') b = Z b + Z' b := rfl
      rw [this, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z' b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ' hW
    have hext_add : extDerivFun (I := I) (fun b => T b (Y b) ((Z + Z') b) (W b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T b (Y b) (Z' b) (W b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add]
    rw [covOn.add hZ hZ' (Set.mem_univ x)]
    have h_ZZ' : (Z + Z') x = Z x + Z' x := rfl
    rw [h_ZZ']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

omit [FiniteDimensional ℝ E] in
lemma tensor03Scalar_tensorialAt_W
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor03 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Y Z : Π x : M, TangentSpace I x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (tensor03Scalar cov T x X Y Z) x where
  smul {g W} hg hW := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b (Y b) (Z b) ((g • W) b)) = (fun b : M => g b * h b) := by
      funext b
      change T b (Y b) (Z b) ((g • W) b) = g b * h b
      have : (g • W) b = g b • W b := rfl
      rw [this, ContinuousLinearMap.map_smul, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b (Y b) (Z b) ((g • W) b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) ((g • W) x)
        - T x (Y x) (cov.toFun Z x (X x)) ((g • W) x)
        - T x (Y x) (Z x) (cov.toFun (g • W) x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hW hg (Set.mem_univ x)]
    have h_gW_x : (g • W) x = g x • W x := rfl
    rw [h_gW_x]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  add {W W'} hW hW' := by
    classical
    change extDerivFun (I := I) (fun b => T b (Y b) (Z b) ((W + W') b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) ((W + W') x)
        - T x (Y x) (cov.toFun Z x (X x)) ((W + W') x)
        - T x (Y x) (Z x) (cov.toFun (W + W') x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W' b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W' x)
        - T x (Y x) (cov.toFun Z x (X x)) (W' x)
        - T x (Y x) (Z x) (cov.toFun W' x (X x)))
    have hadd_fun : (fun b : M => T b (Y b) (Z b) ((W + W') b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T b (Y b) (Z b) (W' b)) := by
      funext b
      change T b (Y b) (Z b) ((W + W') b) = T b (Y b) (Z b) (W b) + T b (Y b) (Z b) (W' b)
      have : (W + W') b = W b + W' b := rfl
      rw [this, ContinuousLinearMap.map_add]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W' b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW'
    have hext_add : extDerivFun (I := I) (fun b => T b (Y b) (Z b) ((W + W') b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W' b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add]
    rw [covOn.add hW hW' (Set.mem_univ x)]
    have h_WW' : (W + W') x = W x + W' x := rfl
    rw [h_WW']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

private noncomputable def tensor03TrilinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (v : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  mkHom₃ (fun Y Z W => tensor03Scalar (cov.toFun) T x (FiberBundle.extend E v) Y Z W) x
    (fun Z W hZ hW =>
      tensor03Scalar_tensorialAt_Y cov.isCovariantDerivativeOnUniv hT
        (FiberBundle.extend E v) (mdifferentiableAt_extend ..) Z W hZ hW)
    (fun Y W hY hW =>
      tensor03Scalar_tensorialAt_Z cov.isCovariantDerivativeOnUniv hT
        (FiberBundle.extend E v) (mdifferentiableAt_extend ..) Y W hY hW)
    (fun Y Z hY hZ =>
      tensor03Scalar_tensorialAt_W cov.isCovariantDerivativeOnUniv hT
        (FiberBundle.extend E v) (mdifferentiableAt_extend ..) Y Z hY hZ)

private lemma tensor03TrilinAt_apply_extend
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (v : TangentSpace I x)
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x) :
    tensor03TrilinAt cov hT v (Y x) (Z x) (W x) =
      tensor03Scalar (cov.toFun) T x (FiberBundle.extend E v) Y Z W := by
  classical
  unfold tensor03TrilinAt
  exact mkHom₃_apply _ _ _ hY hZ hW

private noncomputable def tensor03XSlot
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) :
    TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun v := tensor03TrilinAt cov hT v
  map_add' v v' := by
    classical
    ext y z w
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hYx : Y x = y := FiberBundle.extend_apply_self E y
    have hZx : Z x = z := FiberBundle.extend_apply_self E z
    have hWx : W x = w := FiberBundle.extend_apply_self E w
    rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    rw [tensor03TrilinAt_apply_extend cov hT (v + v') hY hZ hW,
        tensor03TrilinAt_apply_extend cov hT v hY hZ hW,
        tensor03TrilinAt_apply_extend cov hT v' hY hZ hW]
    have h1 : (FiberBundle.extend E (v + v') : Π x : M, TangentSpace I x) x = v + v' :=
      FiberBundle.extend_apply_self E (v + v')
    have h2 : (FiberBundle.extend E v : Π x : M, TangentSpace I x) x = v :=
      FiberBundle.extend_apply_self E v
    have h3 : (FiberBundle.extend E v' : Π x : M, TangentSpace I x) x = v' :=
      FiberBundle.extend_apply_self E v'
    unfold tensor03Scalar
    rw [h1, h2, h3]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x).map_add]
    rw [(cov.toFun Y x).map_add, (cov.toFun Z x).map_add, (cov.toFun W x).map_add]
    rw [(T x).map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel
  map_smul' c v := by
    classical
    ext y z w
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hYx : Y x = y := FiberBundle.extend_apply_self E y
    have hZx : Z x = z := FiberBundle.extend_apply_self E z
    have hWx : W x = w := FiberBundle.extend_apply_self E w
    rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    rw [tensor03TrilinAt_apply_extend cov hT (c • v) hY hZ hW,
        tensor03TrilinAt_apply_extend cov hT v hY hZ hW]
    have h1 : (FiberBundle.extend E (c • v) : Π x : M, TangentSpace I x) x = c • v :=
      FiberBundle.extend_apply_self E (c • v)
    have h2 : (FiberBundle.extend E v : Π x : M, TangentSpace I x) x = v :=
      FiberBundle.extend_apply_self E v
    unfold tensor03Scalar
    rw [h1, h2]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x).map_smul]
    rw [(cov.toFun Y x).map_smul, (cov.toFun Z x).map_smul, (cov.toFun W x).map_smul]
    rw [(T x).map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul]
    ring

def tensor03CovAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) :
    TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  classical
  by_cases hT : MDiffAtTensor03 T x
  · exact LinearMap.toContinuousLinearMap (tensor03XSlot cov hT)
  · exact 0

lemma tensor03CovAt_apply_of_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (v : TangentSpace I x) :
    tensor03CovAt cov T x v = tensor03TrilinAt cov hT v := by
  classical
  unfold tensor03CovAt
  rw [dif_pos hT]
  rfl

lemma tensor03CovAt_apply_of_diff_extend
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) {X Y Z W : Π x : M, TangentSpace I x}
    (_hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hW : MDiffAt (T% W) x) :
    tensor03CovAt cov T x (X x) (Y x) (Z x) (W x) =
      tensor03Scalar (cov.toFun) T x X Y Z W := by
  classical
  rw [tensor03CovAt_apply_of_diff cov hT (X x)]
  rw [tensor03TrilinAt_apply_extend cov hT (X x) hY hZ hW]
  unfold tensor03Scalar
  have hext : (FiberBundle.extend E (X x) : Π x : M, TangentSpace I x) x = X x :=
    FiberBundle.extend_apply_self E (X x)
  rw [hext]

@[simp] lemma tensor03CovAt_of_not_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : ¬ MDiffAtTensor03 T x) :
    tensor03CovAt cov T x = 0 := by
  classical
  unfold tensor03CovAt
  rw [dif_neg hT]

def tensor03CovFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  fun T x => tensor03CovAt cov T x

@[simp] lemma tensor03CovFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) :
    tensor03CovFun cov T x = tensor03CovAt cov T x := rfl

end Connection
end Geometry
end DifferentialGeometry

end

