/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import
  DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceRectangleBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTwistedReading

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private def horizontal (t : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  seamWitnessPlane '' (Icc (0 : ℝ) 1 ×ˢ {t})

private theorem reflection_mapsTo_horizontal (t : ℝ) :
    MapsTo twistedStripReflection (horizontal t) (horizontal (1 - t)) := by
  rintro z ⟨⟨s, r⟩, ⟨hs, hr⟩, rfl⟩
  have hr' : r = t := hr
  subst r
  rw [twistedStripReflection_apply]
  exact ⟨(1 - s, 1 - t), ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩, rfl⟩

private theorem exists_reflected_path
    {p q u v : frontier twistedStripCell.domain} (P : Path p q) (Q : Path u v) {t : ℝ}
    (hP : Set.range (fun r => (P r : EuclideanSpace ℝ (Fin 2))) = horizontal t)
    (hQ : Set.range (fun r => (Q r : EuclideanSpace ℝ (Fin 2))) = horizontal (1 - t))
    (hu : twistedStripReflection p = u) (hv : twistedStripReflection q = v) :
    ∃ R : Path u v,
      (∀ r, (R r : EuclideanSpace ℝ (Fin 2)) = twistedStripReflection (P r)) ∧
        Set.range R ⊆ Set.range Q := by
  have hmem (r : unitInterval) : twistedStripReflection (P r) ∈
      Set.range (fun s => (Q s : EuclideanSpace ℝ (Fin 2))) := by
    rw [hQ]
    apply reflection_mapsTo_horizontal t
    rw [← hP]
    exact ⟨r, rfl⟩
  have hfront (r : unitInterval) : twistedStripReflection (P r) ∈
      frontier twistedStripCell.domain := by
    obtain ⟨s, hs⟩ := hmem r
    exact hs ▸ (Q s).property
  let R : Path u v := {
    toFun r := ⟨twistedStripReflection (P r), hfront r⟩
    continuous_toFun :=
      (twistedStripReflection.continuous_of_finiteDimensional.comp
        (continuous_subtype_val.comp P.continuous)).subtype_mk _
    source' := Subtype.ext (by simpa only [Path.source] using hu)
    target' := Subtype.ext (by simpa only [Path.target] using hv) }
  refine ⟨R, fun _ => rfl, ?_⟩
  rintro z ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := hmem r
  exact ⟨s, Subtype.ext hs⟩

private theorem exists_twisted_boundary_paths :
    ∃ (p q u v : frontier twistedStripCell.domain)
      (σ : Path p q) (τ : Path q u) (υ : Path u v) (φ : Path v p)
      (e : loopCircle ≃ₜ frontier twistedStripCell.domain),
      (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (0, 0) ∧
      (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (0, 1) ∧
      (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (1, 1) ∧
      (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (1, 0) ∧
      Set.range (fun t => (σ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc (-1 / 4) 0 ×ˢ Icc (0 : ℝ) 1)) ∩
          frontier twistedStripCell.domain ∧
      Set.range (fun t => (τ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc 0 1 ×ˢ {(1 : ℝ)})) ∧
      Set.range (fun t => (υ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc 1 (5 / 4) ×ˢ Icc (0 : ℝ) 1)) ∩
          frontier twistedStripCell.domain ∧
      Set.range (fun t => (φ t : EuclideanSpace ℝ (Fin 2))) =
        (seamWitnessPlane '' (Icc 0 1 ×ˢ {(0 : ℝ)})) ∧
      (∀ θ, e θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
      Function.Injective σ ∧ Function.Injective τ ∧
      Function.Injective υ ∧ Function.Injective φ :=
  exists_boundaryParam_four_paths_of_rectangle
    (by norm_num : (-1 / 4 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 5 / 4)

theorem twistedStripCell_exists_reversing_boundaryWordWitnesses
    {B : Set halfTurnQuotient}
    (hD : NormalSingularCellData twistedStripCell (frontier twistedStripSide) B)
    {c : hD.singularSet.Branch}
    (hc : hD.singularSet.branchCarrier c =
      doublePointSet (⇑twistedStripCell) twistedStripCell.domain)
    {X : Type*} [TopologicalSpace X] {ρ : X → halfTurnQuotient}
    (hρ : IsEmbedding ρ) (f : frontier twistedStripCell.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier twistedStripCell.domain, ρ (f z) = twistedStripCell z) :
    ∃ (p q u v : frontier twistedStripCell.domain)
      (σ₀ : Path p q) (τ₀ : Path q u) (υ₀ : Path u v) (φ₀ : Path v p)
      (e : loopCircle ≃ₜ frontier twistedStripCell.domain)
      (a b : X) (σ υ : Path a b) (τ φ : Path b a)
      (Gd : SingularTwoCell halfTurnQuotient),
      (p : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (0, 0) ∧
      (q : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (0, 1) ∧
      (u : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (1, 1) ∧
      (v : EuclideanSpace ℝ (Fin 2)) = seamWitnessPlane (1, 0) ∧
      (∀ θ, e θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      Function.Injective σ₀ ∧ Function.Injective τ₀ ∧
      Function.Injective υ₀ ∧ Function.Injective φ₀ ∧
      (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
      (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) ∧
      hD.IsBoundarySurgeryCell c Gd ∧
      Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm))) ∧
      ∃ W : BoundaryWordWitness crossRegluedTwistedCell ρ
        (pathToCircle (σ.trans (φ.trans (υ.trans τ)))), W.param = e := by
  obtain ⟨D₁, D₂, D₃, hcut, hD₁, -, hD₃⟩ := twistedStripCell_exists_reversing_cut hD hc
  obtain ⟨p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, hp, hq, hu, hv,
    hrσ, hrτ, hrυ, hrφ, he, hσinj, hτinj, hυinj, hφinj⟩ :=
      exists_twisted_boundary_paths
  have huX : f u = f p := by
    apply hρ.injective
    rw [hfρ, hfρ, hu, hp]
    exact twistedStripCell_reversing_endpoints.1.symm
  have hvX : f v = f q := by
    apply hρ.injective
    rw [hfρ, hfρ, hv, hq]
    exact twistedStripCell_reversing_endpoints.2.1.symm
  let σ := σ₀.map hf
  let τ : Path (f q) (f p) := (τ₀.map hf).cast rfl huX.symm
  let υ : Path (f p) (f q) := (υ₀.map hf).cast huX.symm hvX.symm
  let φ : Path (f q) (f p) := (φ₀.map hf).cast hvX.symm rfl
  obtain ⟨τ₁, hτ₁, hrτ₁⟩ := exists_reflected_path τ₀ φ₀ hrτ
    (by simpa only [sub_self, horizontal] using hrφ)
    (by rw [hq, hv, twistedStripReflection_apply]; norm_num)
    (by rw [hu, hp, twistedStripReflection_apply]; norm_num)
  obtain ⟨φ₁, hφ₁, hrφ₁⟩ := exists_reflected_path φ₀ τ₀ hrφ
    (by simpa only [sub_zero, horizontal] using hrτ)
    (by rw [hv, hq, twistedStripReflection_apply]; norm_num)
    (by rw [hp, hu, twistedStripReflection_apply]; norm_num)
  let τX : Path (f q) (f p) := (τ₁.map hf).cast hvX.symm rfl
  let φX : Path (f q) (f p) := (φ₁.map hf).cast rfl huX.symm
  have hτhom : τX.Homotopic φ :=
    BoundaryWordWitness.push_source_homotopy f hf hφinj hrτ₁
      (fun _ => rfl) (fun _ => rfl)
  have hφhom : φX.Homotopic τ :=
    BoundaryWordWitness.push_source_homotopy f hf hτinj hrφ₁
      (fun _ => rfl) (fun _ => rfl)
  have hσeq (t : unitInterval) : (σ.map hρ.continuous) t =
      crossRegluedTwistedCell (σ₀ t) := by
    change ρ (f (σ₀ t)) = _
    rw [hfρ]
    apply (crossRegluedTwistedCell_eq_left _).symm
    exact (hrσ ▸ Set.mem_range_self t).1
  have hυeq (t : unitInterval) : (υ.map hρ.continuous) t =
      crossRegluedTwistedCell (υ₀ t) := by
    change ρ (f (υ₀ t)) = _
    rw [hfρ]
    apply (crossRegluedTwistedCell_eq_right _).symm
    exact (hrυ ▸ Set.mem_range_self t).1
  have hτeq (t : unitInterval) : (τX.map hρ.continuous) t =
      crossRegluedTwistedCell (τ₀ t) := by
    change ρ (f (τ₁ t)) = _
    rw [hfρ, hτ₁]
    apply (crossRegluedTwistedCell_eq_middle _).symm
    have hmem := mem_image_seamWitnessPlane.mp (hrτ ▸ Set.mem_range_self t)
    exact mem_image_seamWitnessPlane.mpr ⟨hmem.1, by rw [hmem.2]; norm_num⟩
  have hφeq (t : unitInterval) : (φX.map hρ.continuous) t =
      crossRegluedTwistedCell (φ₀ t) := by
    change ρ (f (φ₁ t)) = _
    rw [hfρ, hφ₁]
    apply (crossRegluedTwistedCell_eq_middle _).symm
    have hmem := mem_image_seamWitnessPlane.mp (hrφ ▸ Set.mem_range_self t)
    exact mem_image_seamWitnessPlane.mpr ⟨hmem.1, by rw [hmem.2]; norm_num⟩
  have hwhole : ∀ t,
      ((σ.trans (τX.trans (υ.trans φX))).map hρ.continuous) t =
        crossRegluedTwistedCell ((σ₀.trans (τ₀.trans (υ₀.trans φ₀))) t) := by
    have htail := trans_apply_eq_map
      (f := fun z : frontier twistedStripCell.domain => crossRegluedTwistedCell z)
      (α := υ₀) (β := φ₀) hυeq hφeq
    have hmiddle := trans_apply_eq_map
      (f := fun z : frontier twistedStripCell.domain => crossRegluedTwistedCell z)
      (α := τ₀) hτeq htail
    simpa only [Path.map_trans] using trans_apply_eq_map
      (f := fun z : frontier twistedStripCell.domain => crossRegluedTwistedCell z)
      (α := σ₀) hσeq hmiddle
  let W : BoundaryWordWitness crossRegluedTwistedCell ρ
      (pathToCircle (σ.trans (φ.trans (υ.trans τ)))) := {
    param := e
    loop := pathToCircle (σ.trans (τX.trans (υ.trans φX)))
    realizes := fun θ => by
      change ρ (pathToCircle (σ.trans (τX.trans (υ.trans φX))) θ) =
        crossRegluedTwistedCell (e θ : EuclideanSpace ℝ (Fin 2))
      rw [he θ]
      obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
      simp only [pathToCircle_coe]
      exact hwhole t
    homotopic := pathToCircle_homotopic
      ((Path.Homotopic.refl σ).hcomp (hτhom.hcomp ((Path.Homotopic.refl υ).hcomp hφhom))) }
  have hrυsymm : Set.range (fun t => (υ₀.symm t : EuclideanSpace ℝ (Fin 2))) =
      D₃.domain ∩ frontier twistedStripCell.domain := by
    change Set.range (Subtype.val ∘ ⇑υ₀.symm) = _
    rw [Set.range_comp, Path.symm_range, ← Set.range_comp, hD₃]
    exact hrυ
  obtain ⟨Gd, hGd, Wd⟩ := hD.exists_boundaryWordWitness_direct_of_cut hcut f hf hfρ
    σ₀ υ₀.symm hp hq
    (by rw [hv]; rw [twistedStripReflection_apply]; norm_num)
    (by rw [hu]; rw [twistedStripReflection_apply]; norm_num)
    hσinj (hυinj.comp unitInterval.symm_bijective.injective)
    (by rw [hD₁]; exact hrσ) hrυsymm
    (σ := σ) (υ := υ.symm) (fun _ => rfl) (fun _ => rfl)
  exact ⟨p, q, u, v, σ₀, τ₀, υ₀, φ₀, e, f p, f q, σ, υ, τ, φ, Gd,
    hp, hq, hu, hv, he, hσinj, hτinj, hυinj, hφinj,
    (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), hGd, Wd, W, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
