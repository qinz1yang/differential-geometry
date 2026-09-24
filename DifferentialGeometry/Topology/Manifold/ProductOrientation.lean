import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

def tangentProdEquiv (p : M × N) :
    TangentSpace (I.prod J) p ≃ₗ[ℝ] TangentSpace I p.1 × TangentSpace J p.2 := by
  change (E × F) ≃ₗ[ℝ] (E × F)
  exact LinearEquiv.refl ℝ (E × F)

def productTangentBasis {m n : ℕ} {x : M} {y : N}
    (b : Basis (Fin m) ℝ (TangentSpace I x))
    (c : Basis (Fin n) ℝ (TangentSpace J y)) :
    Basis (Fin (m + n)) ℝ (TangentSpace (I.prod J) (x, y)) :=
  ((b.prod c).reindex finSumFinEquiv).map (tangentProdEquiv I J (x, y)).symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

private theorem compLinearMap_domDomCongr {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {ι ι' : Type*} (e : V ≃ₗ[ℝ] W) (eι : ι ≃ ι')
    (v : V [⋀^ι]→ₗ[ℝ] ℝ) :
    (v.domDomCongr eι).compLinearMap (e.symm : W →ₗ[ℝ] V) =
      (v.compLinearMap (e.symm : W →ₗ[ℝ] V)).domDomCongr eι := by
  ext g
  simp [AlternatingMap.compLinearMap_apply, Function.comp_def]

private theorem orientation_map_reindex {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {ι ι' : Type*} (e : V ≃ₗ[ℝ] W) (eι : ι ≃ ι')
    (x : Orientation ℝ V ι) :
    Orientation.map ι' e (Orientation.reindex ℝ V eι x) =
      Orientation.reindex ℝ W eι (Orientation.map ι e x) := by
  induction x using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply, Orientation.reindex_apply]
    refine (ray_eq_iff _ _).mpr ?_
    rw [compLinearMap_domDomCongr]

private noncomputable def basisEquiv {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b₀ b : Basis ι ℝ V) : V ≃ₗ[ℝ] V :=
  b₀.equiv b (Equiv.refl ι)

private theorem map_basisEquiv {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b₀ b : Basis ι ℝ V) : b₀.map (basisEquiv b₀ b) = b := by
  ext i
  rw [Basis.map_apply, basisEquiv, Basis.equiv_apply, Equiv.refl_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem prod_map_prodCongr {m n : ℕ} (b : Basis (Fin m) ℝ E) (c : Basis (Fin n) ℝ F)
    (A : E ≃ₗ[ℝ] E) (B : F ≃ₗ[ℝ] F) :
    (b.prod c).map (A.prodCongr B) = (b.map A).prod (c.map B) := by
  ext i <;> rcases i with i | i <;>
    simp [Basis.map_apply, LinearEquiv.prodCongr_apply]

private theorem prodBasis_orientation_eq {m n : ℕ} (b b₀ : Basis (Fin m) ℝ E)
    (c c₀ : Basis (Fin n) ℝ F) (hb : b.orientation = b₀.orientation)
    (hc : c.orientation = c₀.orientation) :
    (b.prod c).orientation = (b₀.prod c₀).orientation := by
  have hA : 0 < LinearMap.det (basisEquiv b₀ b : E →ₗ[ℝ] E) := by
    rw [← (Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos b₀ (basisEquiv b₀ b)),
      map_basisEquiv]
    exact hb
  have hB : 0 < LinearMap.det (basisEquiv c₀ c : F →ₗ[ℝ] F) := by
    rw [← (Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos c₀ (basisEquiv c₀ c)),
      map_basisEquiv]
    exact hc
  have hdet : 0 < LinearMap.det
      (((basisEquiv b₀ b).prodCongr (basisEquiv c₀ c)) : (E × F) →ₗ[ℝ] (E × F)) := by
    rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
    exact mul_pos hA hB
  have h := (Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos (b₀.prod c₀)
    ((basisEquiv b₀ b).prodCongr (basisEquiv c₀ c))).mpr hdet
  rwa [prod_map_prodCongr, map_basisEquiv, map_basisEquiv] at h

private noncomputable def someBasisOf {m : ℕ} (h : Nonempty (Fin m))
    (o : Orientation ℝ E (Fin m)) (hm : m = Module.finrank ℝ E) : Basis (Fin m) ℝ E := by
  letI := h
  exact o.someBasis (by simpa using hm)

private theorem someBasisOf_orientation {m : ℕ} (h : Nonempty (Fin m))
    (o : Orientation ℝ E (Fin m)) (hm : m = Module.finrank ℝ E) :
    (someBasisOf h o hm).orientation = o :=
  letI := h
  Orientation.someBasis_orientation o (by simpa using hm)

private noncomputable def prodOrientationAt {m n : ℕ} (hM : Nonempty (Fin m))
    (hN : Nonempty (Fin n)) (oM : Orientation ℝ E (Fin m)) (oN : Orientation ℝ F (Fin n))
    (hm : m = Module.finrank ℝ E) (hn : n = Module.finrank ℝ F) :
    Orientation ℝ (E × F) (Fin (m + n)) :=
  Orientation.reindex ℝ (E × F) finSumFinEquiv
    ((someBasisOf hM oM hm).prod (someBasisOf hN oN hn)).orientation

private theorem prodOrientationAt_eq {m n : ℕ} (hM : Nonempty (Fin m)) (hN : Nonempty (Fin n))
    (b : Basis (Fin m) ℝ E) (c : Basis (Fin n) ℝ F) (oM : Orientation ℝ E (Fin m))
    (oN : Orientation ℝ F (Fin n)) (hm : m = Module.finrank ℝ E)
    (hn : n = Module.finrank ℝ F) (hb : b.orientation = oM) (hc : c.orientation = oN) :
    prodOrientationAt hM hN oM oN hm hn =
      Orientation.reindex ℝ (E × F) finSumFinEquiv ((b.prod c).orientation) := by
  rw [prodOrientationAt]
  exact congrArg (Orientation.reindex ℝ (E × F) finSumFinEquiv)
    (prodBasis_orientation_eq
      (b := someBasisOf hM oM hm) (c := someBasisOf hN oN hn) (b₀ := b) (c₀ := c)
      ((someBasisOf_orientation hM oM hm).trans hb.symm)
      ((someBasisOf_orientation hN oN hn).trans hc.symm))

private theorem prodOrientationAt_map {m n : ℕ} (hM : Nonempty (Fin m)) (hN : Nonempty (Fin n))
    (oM : Orientation ℝ E (Fin m)) (oN : Orientation ℝ F (Fin n))
    (hm : m = Module.finrank ℝ E) (hn : n = Module.finrank ℝ F) (A : E ≃ₗ[ℝ] E)
    (B : F ≃ₗ[ℝ] F) :
    Orientation.map (Fin (m + n)) (A.prodCongr B) (prodOrientationAt hM hN oM oN hm hn) =
      prodOrientationAt hM hN (Orientation.map (Fin m) A oM) (Orientation.map (Fin n) B oN)
        hm hn := by
  have hL : prodOrientationAt hM hN oM oN hm hn =
      Orientation.reindex ℝ (E × F) finSumFinEquiv
        ((someBasisOf hM oM hm).prod (someBasisOf hN oN hn)).orientation :=
    prodOrientationAt_eq hM hN _ _ oM oN hm hn
      (someBasisOf_orientation hM oM hm)
      (someBasisOf_orientation hN oN hn)
  have hR : prodOrientationAt hM hN (Orientation.map (Fin m) A oM)
        (Orientation.map (Fin n) B oN) hm hn =
      Orientation.reindex ℝ (E × F) finSumFinEquiv
        (((someBasisOf hM oM hm).map A).prod ((someBasisOf hN oN hn).map B)).orientation :=
    prodOrientationAt_eq hM hN _ _ _ _ hm hn
      (by rw [Basis.orientation_map, someBasisOf_orientation])
      (by rw [Basis.orientation_map, someBasisOf_orientation])
  rw [hL, hR, orientation_map_reindex, ← Basis.orientation_map, prod_map_prodCongr]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem tangentCoordChange_prod (p z : M × N)
    (hz : z ∈ (chartAt (ModelProd H H') p).source) :
    tangentCoordChange (I.prod J) z p z =
      (tangentCoordChange I z.1 p.1 z.1).prodMap
        (tangentCoordChange J z.2 p.2 z.2) := by
  have hz' : z.1 ∈ (chartAt H p.1).source ∧ z.2 ∈ (chartAt H' p.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod] using hz
  have hz₁ : z.1 ∈ (extChartAt I z.1).source ∩ (extChartAt I p.1).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz'.1⟩
  have hz₂ : z.2 ∈ (extChartAt J z.2).source ∩ (extChartAt J p.2).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz'.2⟩
  have hzp : z ∈ (extChartAt (I.prod J) z).source ∩ (extChartAt (I.prod J) p).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz⟩
  refine ((I.prod J).uniqueDiffWithinAt_image (x := (chartAt (ModelProd H H') z) z)).eq
    (hasFDerivWithinAt_tangentCoordChange (I := I.prod J) hzp) ?_
  have h₁ := hasFDerivWithinAt_tangentCoordChange (I := I) hz₁
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := J) hz₂
  have hs₁ : Prod.fst '' (Set.range (I.prod J)) = Set.range I := by
    rw [ModelWithCorners.range_prod]
    exact Set.fst_image_prod (Set.range I) ⟨J ((chartAt H' p.2) p.2), Set.mem_range_self _⟩
  have hs₂ : Prod.snd '' (Set.range (I.prod J)) = Set.range J := by
    rw [ModelWithCorners.range_prod]
    exact Set.snd_image_prod ⟨I ((chartAt H p.1) p.1), Set.mem_range_self _⟩ (Set.range J)
  rw [← hs₁] at h₁
  rw [← hs₂] at h₂
  have h := HasFDerivWithinAt.prodMap (p := (extChartAt I z.1 z.1, extChartAt J z.2 z.2)) h₁ h₂
  have hfun : ((extChartAt (I.prod J) p) ∘ (extChartAt (I.prod J) z).symm) =
      Prod.map ((extChartAt I p.1) ∘ (extChartAt I z.1).symm)
        ((extChartAt J p.2) ∘ (extChartAt J z.2).symm) := by
    funext q
    simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]
    rfl
  have hpt : extChartAt (I.prod J) z z = (extChartAt I z.1 z.1, extChartAt J z.2 z.2) := by
    simp only [extChartAt_prod, PartialEquiv.prod_coe]
  rw [← hfun, ← hpt] at h
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
set_option backward.isDefEq.respectTransparency false in
private theorem tangentChartEquiv_prod (p z : M × N)
    (hz : z ∈ (trivializationAt (E × F) (TangentSpace (I.prod J)) p).baseSet)
    (h₁ : z.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet)
    (h₂ : z.2 ∈ (trivializationAt F (TangentSpace J) p.2).baseSet) :
    tangentChartEquiv (I.prod J) (M × N) p z hz =
      (tangentChartEquiv I M p.1 z.1 h₁).prodCongr (tangentChartEquiv J N p.2 z.2 h₂) := by
  have hzc : z ∈ (chartAt (ModelProd H H') p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hz
  have h₁c : z.1 ∈ (chartAt H p.1).source := h₁
  have h₂c : z.2 ∈ (chartAt H' p.2).source := h₂
  refine LinearEquiv.ext fun v => ?_
  change (Bundle.Trivialization.linearEquivAt ℝ
      (trivializationAt (E × F) (TangentSpace (I.prod J)) p) z hz) v =
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) p.1) z.1 h₁ v.1,
      Bundle.Trivialization.linearEquivAt ℝ (trivializationAt F (TangentSpace J) p.2) z.2 h₂ v.2)
  simp only [Bundle.Trivialization.linearEquivAt_apply]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hz,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₁,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₂]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hzc,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h₁c,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h₂c]
  exact congrArg (fun L => L v) (tangentCoordChange_prod I J p z hzc)

theorem exists_unique_product_orientation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    ∃! o : ManifoldOrientation (I.prod J) (M × N) (m + n),
      ∀ x y, ∀ b : Basis (Fin m) ℝ (TangentSpace I x),
        ∀ c : Basis (Fin n) ℝ (TangentSpace J y),
          b.orientation = oM.orientation x → c.orientation = oN.orientation y →
            (productTangentBasis I J b c).orientation = o.orientation (x, y) := by
  let orientation : (p : M × N) → Orientation ℝ (TangentSpace (I.prod J) p) (Fin (m + n)) :=
    fun p => prodOrientationAt ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩ (oM.orientation p.1) (oN.orientation p.2)
      oM.dimension_eq.symm oN.dimension_eq.symm
  have hchar : ∀ (x : M) (y : N) (b : Basis (Fin m) ℝ (TangentSpace I x))
      (c : Basis (Fin n) ℝ (TangentSpace J y)), b.orientation = oM.orientation x →
      c.orientation = oN.orientation y →
        (productTangentBasis I J b c).orientation = orientation (x, y) := by
    intro x y b c hb hc
    rw [productTangentBasis, Basis.orientation_map, tangentProdEquiv, Basis.orientation_reindex]
    exact (prodOrientationAt_eq (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩ b c (oM.orientation x)
      (oN.orientation y) oM.dimension_eq.symm oN.dimension_eq.symm hb hc).symm
  refine ⟨⟨?_, orientation, ?_⟩, hchar, ?_⟩
  · simp [Module.finrank_prod, oM.dimension_eq, oN.dimension_eq]
  · intro p x hx
    have hx' : x ∈ (chartAt (ModelProd H H') p).source := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hx
    have hx'' : x.1 ∈ (chartAt H p.1).source ∧ x.2 ∈ (chartAt H' p.2).source := by
      simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod] using hx'
    have hx₁ : x.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := hx''.1
    have hx₂ : x.2 ∈ (trivializationAt F (TangentSpace J) p.2).baseSet := hx''.2
    obtain ⟨U₁, hU₁open, hx₁U₁, hU₁, hlc₁⟩ := oM.locally_constant p.1 x.1 hx₁
    obtain ⟨U₂, hU₂open, hx₂U₂, hU₂, hlc₂⟩ := oN.locally_constant p.2 x.2 hx₂
    have hU : U₁ ×ˢ U₂ ⊆ (trivializationAt (E × F) (TangentSpace (I.prod J)) p).baseSet := by
      intro y hy
      have hy' : y.1 ∈ (chartAt H p.1).source ∧ y.2 ∈ (chartAt H' p.2).source :=
        ⟨hU₁ hy.1, hU₂ hy.2⟩
      have hy'' : y ∈ (chartAt (ModelProd H H') p).source := by
        simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod] using hy'
      simpa only [TangentBundle.trivializationAt_baseSet] using hy''
    refine ⟨U₁ ×ˢ U₂, hU₁open.prod hU₂open, ⟨hx₁U₁, hx₂U₂⟩, hU, ?_⟩
    intro y hy
    have hmap_y := tangentChartEquiv_prod I J p y (hU hy) (hU₁ hy.1) (hU₂ hy.2)
    have hmap_x := tangentChartEquiv_prod I J p x hx hx₁ hx₂
    have h₁ := hlc₁ y.1 hy.1
    have h₂ := hlc₂ y.2 hy.2
    rw [hmap_y, hmap_x]
    have hpy : orientation y = prodOrientationAt (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩
        (oM.orientation y.1) (oN.orientation y.2) oM.dimension_eq.symm oN.dimension_eq.symm := rfl
    have hpx : orientation x = prodOrientationAt (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩
        (oM.orientation x.1) (oN.orientation x.2) oM.dimension_eq.symm oN.dimension_eq.symm := rfl
    calc (Orientation.map (Fin (m + n))
          ((tangentChartEquiv I M p.1 y.1 (hU₁ hy.1)).prodCongr
            (tangentChartEquiv J N p.2 y.2 (hU₂ hy.2)))) (orientation y)
        = prodOrientationAt (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩
            (Orientation.map (Fin m) (tangentChartEquiv I M p.1 y.1 (hU₁ hy.1))
              (oM.orientation y.1))
            (Orientation.map (Fin n) (tangentChartEquiv J N p.2 y.2 (hU₂ hy.2))
              (oN.orientation y.2)) oM.dimension_eq.symm oN.dimension_eq.symm := by
          rw [hpy]
          exact prodOrientationAt_map (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩ _
            _ oM.dimension_eq.symm oN.dimension_eq.symm _
            _
      _ = prodOrientationAt (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩
            (Orientation.map (Fin m) (tangentChartEquiv I M p.1 x.1 hx₁) (oM.orientation x.1))
            (Orientation.map (Fin n) (tangentChartEquiv J N p.2 x.2 hx₂)
              (oN.orientation x.2)) oM.dimension_eq.symm oN.dimension_eq.symm := by
          rw [h₁, h₂]
      _ = (Orientation.map (Fin (m + n))
            ((tangentChartEquiv I M p.1 x.1 hx₁).prodCongr
              (tangentChartEquiv J N p.2 x.2 hx₂))) (orientation x) := by
          rw [hpx]
          exact (prodOrientationAt_map (E := E) (F := F) ⟨⟨0, hm⟩⟩ ⟨⟨0, hn⟩⟩ _
            _ oM.dimension_eq.symm oN.dimension_eq.symm _
            _).symm
  · intro o' ho'
    refine ManifoldOrientation.ext fun p => ?_
    obtain ⟨x, y⟩ := p
    have hb := someBasisOf_orientation (E := E) ⟨⟨0, hm⟩⟩ (oM.orientation x) oM.dimension_eq.symm
    have hc := someBasisOf_orientation (E := F) ⟨⟨0, hn⟩⟩ (oN.orientation y) oN.dimension_eq.symm
    exact (ho' x y _ _ hb hc).symm.trans (hchar x y _ _ hb hc)

def productOrientation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    ManifoldOrientation (I.prod J) (M × N) (m + n) :=
  (exists_unique_product_orientation I J hm hn oM oN).exists.choose

theorem productOrientation_characterization {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n)
    (x : M) (y : N) (b : Basis (Fin m) ℝ (TangentSpace I x))
    (c : Basis (Fin n) ℝ (TangentSpace J y))
    (hb : b.orientation = oM.orientation x) (hc : c.orientation = oN.orientation y) :
    (productTangentBasis I J b c).orientation =
      (productOrientation I J hm hn oM oN).orientation (x, y) :=
  (exists_unique_product_orientation I J hm hn oM oN).exists.choose_spec x y b c hb hc

theorem productOrientation_unique {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n)
    (o : ManifoldOrientation (I.prod J) (M × N) (m + n))
    (ho : ∀ x y, ∀ b : Basis (Fin m) ℝ (TangentSpace I x),
      ∀ c : Basis (Fin n) ℝ (TangentSpace J y),
        b.orientation = oM.orientation x → c.orientation = oN.orientation y →
          (productTangentBasis I J b c).orientation = o.orientation (x, y)) :
    o = productOrientation I J hm hn oM oN :=
  (exists_unique_product_orientation I J hm hn oM oN).unique ho
    (productOrientation_characterization I J hm hn oM oN)

end DifferentialGeometry
