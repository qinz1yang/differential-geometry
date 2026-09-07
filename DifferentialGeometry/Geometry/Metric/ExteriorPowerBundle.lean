import DifferentialGeometry.Geometry.Metric.ExteriorPowerSmooth
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.FiniteDimensional

noncomputable section

open scoped Bundle Manifold ContDiff

namespace Bundle.Pretrivialization

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def exteriorPower (k : ℕ) (e : Trivialization F (π F V)) [e.IsLinear ℝ] :
    Pretrivialization (⋀[ℝ]^k F) (π (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))) where
  toFun p := ⟨p.1, exteriorPower.map k (e.continuousLinearMapAt ℝ p.1).toLinearMap p.2⟩
  invFun p := ⟨p.1, exteriorPower.map k (e.symmL ℝ p.1).toLinearMap p.2⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' := by
    rintro ⟨x, u⟩ hx
    rw [TotalSpace.mk_inj]
    change exteriorPower.map k (e.symmL ℝ x).toLinearMap
      (exteriorPower.map k (e.continuousLinearMapAt ℝ x).toLinearMap u) = u
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have h : (e.symmL ℝ x).toLinearMap.comp (e.continuousLinearMapAt ℝ x).toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact e.symmₗ_linearMapAt hx v
    rw [h, exteriorPower.map_id]
    rfl
  right_inv' := by
    rintro ⟨x, u⟩ ⟨hx, _⟩
    rw [Prod.mk_right_inj]
    change exteriorPower.map k (e.continuousLinearMapAt ℝ x).toLinearMap
      (exteriorPower.map k (e.symmL ℝ x).toLinearMap u) = u
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have h : (e.continuousLinearMapAt ℝ x).toLinearMap.comp (e.symmL ℝ x).toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact e.linearMapAt_symmₗ hx v
    rw [h, exteriorPower.map_id]
    rfl
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance exteriorPower.isLinear (k : ℕ) (e : Trivialization F (π F V)) [e.IsLinear ℝ] :
    (exteriorPower k e).IsLinear ℝ where
  linear x _ := (exteriorPower.map k (e.continuousLinearMapAt ℝ x).toLinearMap).isLinear

def exteriorPowerCoordChange (k : ℕ) (e e' : Trivialization F (π F V))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] (x : B) : (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F :=
  exteriorPower.mapContinuousLinearMap k (e.coordChangeL ℝ e' x).toContinuousLinearMap

omit [VectorBundle ℝ F V] in
theorem exteriorPower_symm_apply (k : ℕ) (e : Trivialization F (π F V)) [e.IsLinear ℝ]
    {x : B} (hx : x ∈ e.baseSet) (u : ⋀[ℝ]^k F) :
    (exteriorPower k e).symm x u = exteriorPower.map k (e.symmL ℝ x).toLinearMap u := by
  rw [Pretrivialization.symm_apply]
  · rfl
  exact hx

omit [VectorBundle ℝ F V] in
theorem exteriorPowerCoordChange_apply (k : ℕ) (e e' : Trivialization F (π F V))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] (x : B) (hx : x ∈ e.baseSet ∩ e'.baseSet)
    (u : ⋀[ℝ]^k F) : exteriorPowerCoordChange k e e' x u =
      (exteriorPower k e' ⟨x, (exteriorPower k e).symm x u⟩).2 := by
  rw [exteriorPower_symm_apply k e hx.1]
  change exteriorPower.map k (e.coordChangeL ℝ e' x).toLinearEquiv.toLinearMap u =
    exteriorPower.map k (e'.continuousLinearMapAt ℝ x).toLinearMap
      (exteriorPower.map k (e.symmL ℝ x).toLinearMap u)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  congr 2
  apply LinearMap.ext
  intro v
  change e.coordChangeL ℝ e' x v = e'.continuousLinearMapAt ℝ x (e.symmL ℝ x v)
  rw [Trivialization.coordChangeL_apply e e' hx, Trivialization.symmL_apply e hx.1]
  exact (e'.continuousLinearMapAt_apply_of_mem (R := ℝ) hx.2 _).symm

theorem continuousOn_exteriorPowerCoordChange (k : ℕ)
    (e e' : Trivialization F (π F V))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (exteriorPowerCoordChange k e e') (e.baseSet ∩ e'.baseSet) :=
  (exteriorPower.contDiff_mapContinuousLinearMap k 0).continuous.comp_continuousOn
    (continuousOn_coordChange ℝ e e')

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B] {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]

theorem contMDiffOn_exteriorPowerCoordChange (k : ℕ)
    (e e' : Trivialization F (π F V))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) n
      (exteriorPowerCoordChange k e e') (e.baseSet ∩ e'.baseSet) :=
  (exteriorPower.contDiff_mapContinuousLinearMap k n).contMDiff.comp_contMDiffOn
    (contMDiffOn_coordChangeL (IB := IB) e e')

end Bundle.Pretrivialization

namespace Bundle.ExteriorPower

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def vectorPrebundle (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    VectorPrebundle ℝ (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  exact
    { pretrivializationAtlas :=
        {e' | ∃ (e : Trivialization F (π F V)) (_ : MemTrivializationAtlas e),
          e' = Pretrivialization.exteriorPower k e}
      pretrivialization_linear' := by
        rintro _ ⟨e, he, rfl⟩
        infer_instance
      pretrivializationAt x := Pretrivialization.exteriorPower k (trivializationAt F V x)
      mem_base_pretrivializationAt x := mem_baseSet_trivializationAt F V x
      pretrivialization_mem_atlas x := ⟨trivializationAt F V x, inferInstance, rfl⟩
      exists_coordChange := by
        rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
        exact ⟨Pretrivialization.exteriorPowerCoordChange k e e',
          Pretrivialization.continuousOn_exteriorPowerCoordChange k e e',
          Pretrivialization.exteriorPowerCoordChange_apply k e e'⟩
      totalSpaceMk_isInducing x := by
        let e := trivializationAt F V x
        let L := e.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt F V x)
        let A := (LinearEquiv.ofBijective (exteriorPower.map k L.toLinearEquiv.toLinearMap)
          ⟨exteriorPower.map_injective_field L.injective,
            exteriorPower.map_surjective L.surjective⟩).toContinuousLinearEquiv
        change Topology.IsInducing (fun u : ⋀[ℝ]^k (V x) =>
          (x, exteriorPower.map k (e.continuousLinearMapAt ℝ x).toLinearMap u))
        rw [Topology.isInducing_const_prod]
        convert A.toHomeomorph.isInducing using 1
        change ⇑(exteriorPower.map k (e.continuousLinearMapAt ℝ x).toLinearMap) =
          ⇑(exteriorPower.map k L.toLinearEquiv.toLinearMap)
        have hL : (e.continuousLinearMapAt ℝ x).toLinearMap = L.toLinearEquiv.toLinearMap := by
          apply LinearMap.ext
          intro v
          exact congrFun
            (Trivialization.coe_continuousLinearEquivAt_eq e
              (mem_baseSet_trivializationAt F V x)).symm v
        rw [hL] }

@[instance_reducible]
def totalSpaceTopology (k : ℕ) :
    TopologicalSpace (TotalSpace (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  exact (vectorPrebundle F V k).totalSpaceTopology

@[instance_reducible]
def fiberBundle (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    FiberBundle (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  exact (vectorPrebundle F V k).toFiberBundle

theorem vector_bundle (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    VectorBundle ℝ (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  exact (vectorPrebundle F V k).toVectorBundle

def trivialization (k : ℕ) (e : Trivialization F (π F V)) [he : MemTrivializationAtlas e] :
    letI := totalSpaceTopology F V k
    Trivialization (⋀[ℝ]^k F) (π (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  exact (vectorPrebundle F V k).trivializationOfMemPretrivializationAtlas ⟨e, he, rfl⟩

theorem trivialization_apply (k : ℕ) (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] (x : B) (u : ⋀[ℝ]^k (V x)) :
    trivialization F V k e ⟨x, u⟩ =
      (x, exteriorPower.map k (e.continuousLinearMapAt ℝ x).toLinearMap u) := rfl

@[simp]
theorem baseSet_trivialization (k : ℕ) (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] :
    letI := totalSpaceTopology F V k
    (trivialization F V k e).baseSet = e.baseSet := rfl

theorem trivialization_symm_apply (k : ℕ) (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) (u : ⋀[ℝ]^k F) :
    letI := totalSpaceTopology F V k
    (trivialization F V k e).symm x u =
      exteriorPower.map k (e.symmL ℝ x).toLinearMap u := by
  exact Pretrivialization.exteriorPower_symm_apply k e hx u

theorem trivializationAt_eq (k : ℕ) (x : B) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    trivializationAt (⋀[ℝ]^k F) (fun y => ⋀[ℝ]^k (V y)) x =
      trivialization F V k (trivializationAt F V x) := rfl

theorem trivialization_memTrivializationAtlas (k : ℕ) (e : Trivialization F (π F V))
    [he : MemTrivializationAtlas e] :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    MemTrivializationAtlas (trivialization F V k e) := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := totalSpaceTopology F V k
  let := fiberBundle F V k
  exact ⟨_, ⟨e, he, rfl⟩, rfl⟩

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B] {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]

theorem vectorPrebundle_isContMDiff (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    (vectorPrebundle F V k).IsContMDiff IB n := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  exact
    { exists_contMDiffCoordChange := by
        rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
        exact ⟨Pretrivialization.exteriorPowerCoordChange k e e',
          Pretrivialization.contMDiffOn_exteriorPowerCoordChange k e e',
          Pretrivialization.exteriorPowerCoordChange_apply k e e'⟩ }

theorem contMDiffVectorBundle (k : ℕ) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := totalSpaceTopology F V k
    letI := fiberBundle F V k
    letI := vector_bundle F V k
    ContMDiffVectorBundle n (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) IB := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : (vectorPrebundle F V k).IsContMDiff IB n := vectorPrebundle_isContMDiff F V k
  exact (vectorPrebundle F V k).contMDiffVectorBundle IB

end Bundle.ExteriorPower
