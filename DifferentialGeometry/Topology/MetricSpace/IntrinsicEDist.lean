import DifferentialGeometry.Topology.MetricSpace.PathVariation
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace Metric

noncomputable def intrinsicEDist {X : Type*} [PseudoEMetricSpace X] (x y : X) : ℝ≥0∞ :=
  ⨅ γ : Path x y, eVariationOn γ univ

theorem intrinsicEDist_le_path_variation {X : Type*} [PseudoEMetricSpace X]
    {x y : X} (γ : Path x y) : intrinsicEDist x y ≤ eVariationOn γ univ :=
  iInf_le _ γ

theorem intrinsicEDist_le_curve_variation {X : Type*} [PseudoEMetricSpace X]
    {x y : X} {c : unitInterval → X} (hc : Continuous c) (hc0 : c 0 = x) (hc1 : c 1 = y) :
    intrinsicEDist x y ≤ eVariationOn c univ :=
  intrinsicEDist_le_path_variation (⟨⟨c, hc⟩, hc0, hc1⟩ : Path x y)

theorem edist_le_intrinsicEDist {X : Type*} [PseudoEMetricSpace X] (x y : X) :
    edist x y ≤ intrinsicEDist x y := by
  apply le_iInf
  intro γ
  simpa only [Path.source, Path.target] using
    eVariationOn.edist_le γ (mem_univ (0 : unitInterval)) (mem_univ 1)

theorem intrinsicEDist_self {X : Type*} [PseudoEMetricSpace X] (x : X) :
    intrinsicEDist x x = 0 := by
  apply le_antisymm _ bot_le
  have hz : eVariationOn (Path.refl x) univ = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro s hs t ht
    exact edist_self x
  exact (intrinsicEDist_le_path_variation (Path.refl x)).trans_eq hz

theorem intrinsicEDist_comm {X : Type*} [PseudoEMetricSpace X] (x y : X) :
    intrinsicEDist x y = intrinsicEDist y x := by
  have hle (a b : X) : intrinsicEDist a b ≤ intrinsicEDist b a := by
    apply le_iInf
    intro γ
    exact (intrinsicEDist_le_path_variation γ.symm).trans_eq γ.eVariationOn_symm
  exact le_antisymm (hle x y) (hle y x)

theorem intrinsicEDist_triangle {X : Type*} [PseudoEMetricSpace X] (x y z : X) :
    intrinsicEDist x z ≤ intrinsicEDist x y + intrinsicEDist y z := by
  change intrinsicEDist x z ≤ (⨅ γ : Path x y, eVariationOn γ univ) +
    ⨅ η : Path y z, eVariationOn η univ
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro γ
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro η
  exact (intrinsicEDist_le_path_variation (γ.trans η)).trans_eq (γ.eVariationOn_trans η)

theorem intrinsicEDist_lt_top_iff {X : Type*} [PseudoEMetricSpace X] (x y : X) :
    intrinsicEDist x y < ⊤ ↔ ∃ γ : Path x y, eVariationOn γ univ < ⊤ :=
  iInf_lt_iff

theorem intrinsicEDist_eq_top_of_not_path {X : Type*} [PseudoEMetricSpace X]
    {x y : X} (h : ¬ Nonempty (Path x y)) : intrinsicEDist x y = ⊤ := by
  have : IsEmpty (Path x y) := not_nonempty_iff.mp h
  change (⨅ γ : Path x y, eVariationOn γ univ) = ⊤
  exact iInf_of_empty (fun γ : Path x y => eVariationOn γ univ)

theorem intrinsicEDist_eq_zero_iff {X : Type*} [EMetricSpace X] (x y : X) :
    intrinsicEDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    exact edist_eq_zero.mp (le_antisymm ((edist_le_intrinsicEDist x y).trans_eq h) bot_le)
  · rintro rfl
    exact intrinsicEDist_self x

theorem intrinsicEDist_eq_edist_of_arbitrarily_short_curves
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε)) (x y : X) :
    intrinsicEDist x y = edist x y := by
  apply le_antisymm _ (edist_le_intrinsicEDist x y)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfin
  obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves x y ε hε
  have ht := (intrinsicEDist_le_curve_variation hc hc0 hc1).trans hlen.le
  simpa only [ENNReal.ofReal_add dist_nonneg ε.coe_nonneg, ← edist_dist,
    ENNReal.ofReal_coe_nnreal] using ht

@[instance_reducible]
noncomputable def intrinsicEMetricSpace (X : Type*) [EMetricSpace X] : EMetricSpace X where
  toPseudoEMetricSpace := PseudoEMetricSpace.ofEDist intrinsicEDist
    intrinsicEDist_self intrinsicEDist_comm intrinsicEDist_triangle
  eq_of_edist_eq_zero := (intrinsicEDist_eq_zero_iff _ _).mp

@[instance_reducible]
noncomputable def intrinsicMetricSpace (X : Type*) [EMetricSpace X]
    (hfinite : ∀ x y : X, intrinsicEDist x y ≠ ⊤) : MetricSpace X :=
  letI := intrinsicEMetricSpace X
  EMetricSpace.toMetricSpace hfinite

theorem intrinsicMetricSpace_edist {X : Type*} [EMetricSpace X]
    (hfinite : ∀ x y : X, intrinsicEDist x y ≠ ⊤) (x y : X) :
    @edist X (intrinsicMetricSpace X hfinite).toEDist x y = intrinsicEDist x y := rfl

theorem intrinsicMetricSpace_dist {X : Type*} [EMetricSpace X]
    (hfinite : ∀ x y : X, intrinsicEDist x y ≠ ⊤) (x y : X) :
    @dist X (intrinsicMetricSpace X hfinite).toDist x y = (intrinsicEDist x y).toReal := rfl

end Metric
