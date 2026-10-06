import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianRetractP

/-!
# CP1-A3 (G2): null-homotopy transfer from the exterior region to the deeper exterior region
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1
open GC.LongTime

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

theorem slide_mem_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b) {t : ℝ}
    (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) (i : Fin cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (E.truncation i).cuspMap q (x, halfSpaceOneLift (τ * b)) ∈
      (cores.domain i t : Set (cores.model i).Carrier) ∧
    cores.map i t (hc_of_deep_CPA3 E hb ht) ((E.truncation i).cuspMap q (x, halfSpaceOneLift (τ * b)))
      ∈ E.region t := by
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hcol : (E.truncation i).cuspMap q (x, halfSpaceOneLift (τ * b)) ∈
      ⋃ q', cuspCollar_CPA2 (E.truncation i) q' b := by
    refine mem_iUnion.mpr ⟨q, (x, halfSpaceOneLift (τ * b)), ⟨trivial, ?_⟩, rfl⟩
    change (halfSpaceOneLift (τ * b)).val 0 ≤ b
    rw [halfSpaceOneLift_val_CPA2 (by positivity)]
    nlinarith
  have hD := collar_subset_domain_CPA3 E hb ht i hcol
  refine ⟨hD, ?_⟩
  refine (mem_region_image_iff_CPA3 E (start_le_of_deep_CPA3 E hb ht) i hD).mpr ?_
  exact (not_mem_interior_image_iff_CPA3 (E.truncation i) _).mpr (mem_iUnion.mpr ⟨q, _, rfl⟩)

/-- **Null-homotopy transfer.** If the exterior-region loop `φ ∘ u` of the torus at the old cusp
torus is null-homotopic in the region of `E`, then the corresponding loop at the deeper torus is
null-homotopic in the region of the deepening. -/
theorem nullhomotopic_transfer_CPA3 (E : PersistentCuspExterior cores) {b : ℝ} (hb : 2 ≤ b)
    {t : ℝ} (ht : (deepExteriorOf_CPA2 E hb).start ≤ t) (i : Fin cores.count)
    (q : Fin (E.truncation i).count)
    (φ : C(Torus, ↥(E.region t)))
    (hφ : ∀ z, (φ z : (postStage F.observation t).Carrier) =
      cores.map i t (hc_of_deep_CPA3 E hb ht) ((E.truncation i).cuspMap q (z, halfZero)))
    (φ' : C(Torus, ↥((deepExteriorOf_CPA2 E hb).region t)))
    (hφ' : ∀ z, (φ' z : (postStage F.observation t).Carrier) =
      cores.map i t (hc_of_deep_CPA3 E hb ht)
        (((deepExteriorOf_CPA2 E hb).truncation i).cuspMap q (z, halfZero)))
    (u : freeLoop Torus) (hu : (φ.comp u).Nullhomotopic) : (φ'.comp u).Nullhomotopic := by
  have hc := hc_of_deep_CPA3 E hb ht
  have hmc : ContinuousOn (cores.map i t hc) (cores.domain i t : Set (cores.model i).Carrier) :=
    continuousOn_map_CPA3 i t hc
  -- the sliding map
  let S : unitInterval × Torus → (cores.model i).Carrier := fun y =>
    (E.truncation i).cuspMap q (y.2, halfSpaceOneLift ((y.1 : ℝ) * b))
  have hSc : Continuous S := by
    refine ((E.truncation i).cuspEmbedding q).contMDiff.continuous.comp
      (continuous_snd.prodMk (continuous_halfSpaceOneLift_CPA2.comp ?_))
    exact (continuous_subtype_val.comp continuous_fst).mul continuous_const
  have hSm : ∀ y, S y ∈ (cores.domain i t : Set (cores.model i).Carrier) ∧
      cores.map i t hc (S y) ∈ E.region t := fun y =>
    slide_mem_CPA3 E hb ht i q y.2 y.1.2.1 y.1.2.2
  have hHc : Continuous (fun y : unitInterval × Torus => cores.map i t hc (S y)) :=
    hmc.comp_continuous hSc (fun y => (hSm y).1)
  let H : ContinuousMap.Homotopy φ ((inclMap_CPA3 E hb ht).comp φ') :=
    { toContinuousMap := ⟨fun y => ⟨cores.map i t hc (S y), (hSm y).2⟩, hHc.subtype_mk _⟩
      map_zero_left := fun z => by
        refine Subtype.ext ?_
        rw [hφ z]
        change cores.map i t hc (S (0, z)) = _
        have : S (0, z) = (E.truncation i).cuspMap q (z, halfZero) := by
          change (E.truncation i).cuspMap q (z, halfSpaceOneLift (((0 : unitInterval) : ℝ) * b)) = _
          rw [show (((0 : unitInterval) : ℝ) * b) = 0 by simp]
          congr 2
          apply Subtype.ext; ext j; rw [Subsingleton.elim j 0]
          change max (0 : ℝ) 0 = 0
          exact max_self 0
        rw [this]
      map_one_left := fun z => by
        refine Subtype.ext ?_
        change cores.map i t hc (S (1, z)) = ((φ' z : (postStage F.observation t).Carrier))
        rw [hφ' z]
        have : S (1, z) = ((deepExteriorOf_CPA2 E hb).truncation i).cuspMap q (z, halfZero) := by
          change (E.truncation i).cuspMap q (z, halfSpaceOneLift (((1 : unitInterval) : ℝ) * b)) =
            (E.truncation i).cuspMap q (shift_CPA2 b (z, halfZero))
          congr 1
          refine Prod.ext rfl ?_
          change _ = halfSpaceOneLift (halfZero.val 0 + b)
          have : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl
          rw [this]; simp
        rw [this] }
  have hhom : (φ.comp u).Homotopic (((inclMap_CPA3 E hb ht).comp φ').comp u) :=
    ContinuousMap.Homotopic.comp ⟨H⟩ (ContinuousMap.Homotopic.refl u)
  have hn1 : (((inclMap_CPA3 E hb ht).comp φ').comp u).Nullhomotopic := by
    obtain ⟨y, hy⟩ := hu
    exact ⟨y, hhom.symm.trans hy⟩
  have := hn1.comp_right (retrMap_CPA3 E hb ht)
  have hid : (retrMap_CPA3 E hb ht).comp (((inclMap_CPA3 E hb ht).comp φ').comp u) = φ'.comp u := by
    rw [ContinuousMap.comp_assoc, ← ContinuousMap.comp_assoc (retrMap_CPA3 E hb ht),
      retrMap_comp_inclMap_CPA3, ContinuousMap.id_comp]
  rwa [hid] at this

end GC.LongTime.CuspP1
