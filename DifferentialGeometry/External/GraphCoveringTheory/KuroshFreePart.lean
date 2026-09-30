/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshTree

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

noncomputable def testQuotientPathLift {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H} (u : H) :
    ∀ {b : RawBassSerreOrbitVertex G H},
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b →
      Σ v : H, @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G)) _
        (u.1 • rawTreeRepresentative G H a)
        (v.1 • rawTreeRepresentative G H b)
  | _, Quiver.Path.nil => ⟨u, Quiver.Path.nil⟩
  | _, @Quiver.Path.cons _ _ _ b c p e => by
      let ih := testQuotientPathLift G H u p
      let v : H := ih.1
      cases e using Sum.rec with
      | inl f =>
          let d := quotientEdgeRawData G H f
          let s := quotientEdgeCoherentSourceAlign G H f
          let l := quotientEdgeLabel G H f
          have hsl : s.1 • rawBassSerreEdgeDataTarget G d =
              l.1⁻¹ • rawTreeRepresentative G H c := by
            apply smul_left_cancel l.1
            rw [quotientEdgeLabel_transport_coherent G H f]
            simp [smul_smul]
          have hsource : (v * s).1 • rawBassSerreEdgeDataSource G d =
              v.1 • rawTreeRepresentative G H b := by
            calc
              (v * s).1 • rawBassSerreEdgeDataSource G d =
                  v.1 • (s.1 • rawBassSerreEdgeDataSource G d) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul]
              _ = v.1 • rawTreeRepresentative G H b := by
                    rw [quotientEdgeCoherentSourceAlign_spec G H f]
          have htarget : (v * s).1 • rawBassSerreEdgeDataTarget G d =
              (v * l⁻¹).1 • rawTreeRepresentative G H c := by
            calc
              (v * s).1 • rawBassSerreEdgeDataTarget G d =
                  v.1 • (s.1 • rawBassSerreEdgeDataTarget G d) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul]
              _ = v.1 • (l.1⁻¹ • rawTreeRepresentative G H c) := by
                    rw [hsl]
              _ = (v * l⁻¹).1 • rawTreeRepresentative G H c := by
                    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
                    rw [smul_smul]
          let base : @Quiver.Hom (RawBassSerreVertex G)
              (rawBassSerreQuiver G) (rawBassSerreEdgeDataSource G d)
              (rawBassSerreEdgeDataTarget G d) :=
            RawBassSerreEdge.centralFactor d.1 d.2
          let e' : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G)) _
              (v.1 • rawTreeRepresentative G H b)
              ((v * l⁻¹).1 • rawTreeRepresentative G H c) :=
            Quiver.Hom.toPos (Quiver.Hom.cast hsource htarget
              (rawBassSerreEdgeAction G (v * s).1 base))
          exact ⟨v * l⁻¹, Quiver.Path.cons ih.2 e'⟩
      | inr f =>
          let d := quotientEdgeRawData G H f
          let s := quotientEdgeCoherentSourceAlign G H f
          let l := quotientEdgeLabel G H f
          have hsource : (v * l * s).1 •
                rawBassSerreEdgeDataTarget G d =
              v.1 • rawTreeRepresentative G H b := by
            calc
              (v * l * s).1 • rawBassSerreEdgeDataTarget G d =
                  v.1 • (l.1 • (s.1 • rawBassSerreEdgeDataTarget G d)) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul, smul_smul]
              _ = v.1 • rawTreeRepresentative G H b := by
                    rw [quotientEdgeLabel_transport_coherent G H f]
          have htarget : (v * l * s).1 •
                rawBassSerreEdgeDataSource G d =
              (v * l).1 • rawTreeRepresentative G H c := by
            calc
              (v * l * s).1 • rawBassSerreEdgeDataSource G d =
                  (v * l).1 • (s.1 • rawBassSerreEdgeDataSource G d) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul]
              _ = (v * l).1 • rawTreeRepresentative G H c := by
                    rw [quotientEdgeCoherentSourceAlign_spec G H f]
          let base : @Quiver.Hom (RawBassSerreVertex G)
              (rawBassSerreQuiver G) (rawBassSerreEdgeDataSource G d)
              (rawBassSerreEdgeDataTarget G d) :=
            RawBassSerreEdge.centralFactor d.1 d.2
          let e' : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G)) _
              (v.1 • rawTreeRepresentative G H b)
              ((v * l).1 • rawTreeRepresentative G H c) :=
            Quiver.Hom.toNeg
              (Quiver.Hom.cast htarget hsource
                (rawBassSerreEdgeAction G (v * l * s).1 base))
          exact ⟨v * l, Quiver.Path.cons ih.2 e'⟩

theorem test_rawOrbitAction_source_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (d : rawBassSerreEdgeData G) (h : H) :
    actionOrbitMk H (RawBassSerreVertex G)
        (rawBassSerreEdgeDataSource G (h.1 • d)) =
      actionOrbitMk H (RawBassSerreVertex G)
        (rawBassSerreEdgeDataSource G d) := by
  cases d with
  | mk g i =>
      change actionOrbitMk H (RawBassSerreVertex G)
          (RawBassSerreVertex.central (h.1 * g)) =
        actionOrbitMk H (RawBassSerreVertex G)
          (RawBassSerreVertex.central g)
      exact actionOrbitMk_smul H (RawBassSerreVertex G) h
        (RawBassSerreVertex.central g)

theorem test_rawOrbitAction_target_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (d : rawBassSerreEdgeData G) (h : H) :
    actionOrbitMk H (RawBassSerreVertex G)
        (rawBassSerreEdgeDataTarget G (h.1 • d)) =
      actionOrbitMk H (RawBassSerreVertex G)
        (rawBassSerreEdgeDataTarget G d) := by
  cases d with
  | mk g i =>
      change actionOrbitMk H (RawBassSerreVertex G)
          (RawBassSerreVertex.factor i
            (factorCosetMk G i (h.1 * g))) =
        actionOrbitMk H (RawBassSerreVertex G)
          (RawBassSerreVertex.factor i (factorCosetMk G i g))
      rw [show RawBassSerreVertex.factor i
            (factorCosetMk G i (h.1 * g)) =
          h.1 • RawBassSerreVertex.factor i (factorCosetMk G i g) by
        have hact := rawBassSerreEdgeData_target_action G h.1 (g, i)
        change RawBassSerreVertex.factor i
            (factorCosetMk G i (h.1 * g)) =
          h.1 • RawBassSerreVertex.factor i (factorCosetMk G i g) at hact
        exact hact]
      exact actionOrbitMk_smul H (RawBassSerreVertex G) h
        (RawBassSerreVertex.factor i (factorCosetMk G i g))

noncomputable def test_rawOrbitQuiverEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : RawBassSerreOrbitEdge G H) :
    rawBassSerreOrbitEdgeSource G H q ⟶
      rawBassSerreOrbitEdgeTarget G H q :=
  ⟨q, rfl, rfl⟩

theorem test_rawOrbitQuiverEdge_toPos_heq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {q r : RawBassSerreOrbitEdge G H} (h : q = r) :
    HEq (Quiver.Hom.toPos (test_rawOrbitQuiverEdge G H q))
      (Quiver.Hom.toPos (test_rawOrbitQuiverEdge G H r)) := by
  cases h
  rfl

theorem test_rawOrbitQuiverEdge_toNeg_heq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {q r : RawBassSerreOrbitEdge G H} (h : q = r) :
    HEq (Quiver.Hom.toNeg (test_rawOrbitQuiverEdge G H q))
      (Quiver.Hom.toNeg (test_rawOrbitQuiverEdge G H r)) := by
  cases h
  rfl

theorem test_rawOrbitQuiverEdge_action_pos_heq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (g : FreeProduct G) (i : ι) (h : H) :
    HEq
      (Quiver.Hom.toPos
        (rawBassSerreOrbitQuiverEdge G H (h.1 * g, i)))
      (Quiver.Hom.toPos
        (rawBassSerreOrbitQuiverEdge G H (g, i))) := by
  exact test_rawOrbitQuiverEdge_toPos_heq G H
    (actionOrbitMk_smul H (rawBassSerreEdgeData G) h (g, i))

theorem test_rawOrbitQuiverEdge_action_neg_heq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (g : FreeProduct G) (i : ι) (h : H) :
    HEq
      (Quiver.Hom.toNeg
        (rawBassSerreOrbitQuiverEdge G H (h.1 * g, i)))
      (Quiver.Hom.toNeg
        (rawBassSerreOrbitQuiverEdge G H (g, i))) := by
  exact test_rawOrbitQuiverEdge_toNeg_heq G H
    (actionOrbitMk_smul H (rawBassSerreEdgeData G) h (g, i))

theorem test_rawOrbitMap_action_pos {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (d : rawBassSerreEdgeData G) (h : H) :
    Quiver.Hom.cast
        (by
          change actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataSource G (h.1 • d)) =
            actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataSource G d)
          exact test_rawOrbitAction_source_eq G H d h)
        (by
          change actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataTarget G (h.1 • d)) =
            actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataTarget G d)
          exact test_rawOrbitAction_target_eq G H d h)
        ((rawBassSerreOrbitSymmPrefunctor G H).map
          (@Quiver.Hom.toPos (RawBassSerreVertex G) (rawBassSerreQuiver G)
            _ _ (rawBassSerreEdgeAction G h.1
              (RawBassSerreEdge.centralFactor d.1 d.2)))) =
      (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) _ _
        (rawBassSerreOrbitEdgeMap G H
          (RawBassSerreEdge.centralFactor d.1 d.2))) := by
  cases d with
  | mk g i =>
      dsimp [rawBassSerreOrbitSymmPrefunctor,
        rawBassSerreOrbitPrefunctorToSymm, rawBassSerreOrbitPrefunctor,
        rawBassSerreOrbitEdgeMap, rawBassSerreEdgeAction]
      rw [Quiver.Hom.cast_eq_iff_heq]
      change HEq
        (Quiver.Hom.toPos
          (rawBassSerreOrbitQuiverEdge G H (h.1 * g, i)))
        (Quiver.Hom.toPos
          (rawBassSerreOrbitQuiverEdge G H (g, i)))
      exact test_rawOrbitQuiverEdge_action_pos_heq G H g i h

theorem test_rawOrbitMap_action_neg {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (d : rawBassSerreEdgeData G) (h : H) :
    Quiver.Hom.cast
        (by
          change actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataTarget G (h.1 • d)) =
            actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataTarget G d)
          exact test_rawOrbitAction_target_eq G H d h)
        (by
          change actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataSource G (h.1 • d)) =
            actionOrbitMk H (RawBassSerreVertex G)
              (rawBassSerreEdgeDataSource G d)
          exact test_rawOrbitAction_source_eq G H d h)
        ((rawBassSerreOrbitSymmPrefunctor G H).map
          (@Quiver.Hom.toNeg (RawBassSerreVertex G) (rawBassSerreQuiver G)
            _ _ (rawBassSerreEdgeAction G h.1
              (RawBassSerreEdge.centralFactor d.1 d.2)))) =
      (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) _ _
        (rawBassSerreOrbitEdgeMap G H
          (RawBassSerreEdge.centralFactor d.1 d.2))) := by
  cases d with
  | mk g i =>
      dsimp [rawBassSerreOrbitSymmPrefunctor,
        rawBassSerreOrbitPrefunctorToSymm, rawBassSerreOrbitPrefunctor,
        rawBassSerreOrbitEdgeMap, rawBassSerreEdgeAction]
      rw [Quiver.Hom.cast_eq_iff_heq]
      change HEq
        (Quiver.Hom.toNeg
          (rawBassSerreOrbitQuiverEdge G H (h.1 * g, i)))
        (Quiver.Hom.toNeg
          (rawBassSerreOrbitQuiverEdge G H (g, i)))
      exact test_rawOrbitQuiverEdge_action_neg_heq G H g i h

theorem test_rawTreeRepresentative_smul_orbit {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) (h : H) :
    actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • rawTreeRepresentative G H a) = a := by
  calc
    actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • rawTreeRepresentative G H a) =
      actionOrbitMk H (RawBassSerreVertex G)
        (rawTreeRepresentative G H a) := by
      apply (actionOrbitMk_eq_iff H (RawBassSerreVertex G) _ _).2
      refine ⟨h⁻¹, ?_⟩
      change (h⁻¹).1 • (h.1 • rawTreeRepresentative G H a) =
        rawTreeRepresentative G H a
      calc
        (h⁻¹).1 • (h.1 • rawTreeRepresentative G H a) =
            ((h⁻¹).1 * h.1) • rawTreeRepresentative G H a :=
          smul_smul (h⁻¹).1 h.1
            (rawTreeRepresentative G H a)
        _ = rawTreeRepresentative G H a := by simp
    _ = a := rawTreeRepresentative_orbit G H a

theorem test_path_cast_nil {U : Type u} [Quiver.{v} U]
    {a b : U} (h₁ h₂ : a = b) :
    Quiver.Path.cast h₁ h₂ (Quiver.Path.nil : Quiver.Path a a) =
      (Quiver.Path.nil : Quiver.Path b b) := by
  have hh : h₂ = h₁ := Subsingleton.elim _ _
  cases hh
  exact Quiver.Path.cast_nil h₁

theorem test_rawOrbitSymm_map_pos_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {x y x' y' : RawBassSerreVertex G}
    (hx : x = x') (hy : y = y')
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) x y) :
    (rawBassSerreOrbitSymmPrefunctor G H).map
        (@Quiver.Hom.toPos (RawBassSerreVertex G)
          (rawBassSerreQuiver G) _ _
          (@Quiver.Hom.cast (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _ _ _ hx hy e)) =
      @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
        (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj hx)
        (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj hy)
        ((rawBassSerreOrbitSymmPrefunctor G H).map
          (@Quiver.Hom.toPos (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _ e)) := by
  cases hx
  cases hy
  rfl

theorem test_rawOrbitSymm_map_neg_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {x y x' y' : RawBassSerreVertex G}
    (hx : x = x') (hy : y = y')
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) x y) :
    (rawBassSerreOrbitSymmPrefunctor G H).map
        (@Quiver.Hom.toNeg (RawBassSerreVertex G)
          (rawBassSerreQuiver G) _ _
          (@Quiver.Hom.cast (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _ _ _ hx hy e)) =
      @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
        (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj hy)
        (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj hx)
        ((rawBassSerreOrbitSymmPrefunctor G H).map
          (@Quiver.Hom.toNeg (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _ e)) := by
  cases hx
  cases hy
  rfl

theorem test_rawOrbitEdge_cast_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (d : rawBassSerreEdgeData G)
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b)
    (ha : rawBassSerreOrbitEdgeSource G H
      (rawBassSerreOrbitEdgeMk G H d) = a)
    (hb : rawBassSerreOrbitEdgeTarget G H
      (rawBassSerreOrbitEdgeMk G H d) = b)
    (hd : rawBassSerreOrbitEdgeMk G H d = f.1) :
    @Quiver.Hom.cast (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H)
      (rawBassSerreOrbitEdgeSource G H (rawBassSerreOrbitEdgeMk G H d))
      (rawBassSerreOrbitEdgeTarget G H (rawBassSerreOrbitEdgeMk G H d)) a b ha hb
      (rawBassSerreOrbitQuiverEdge G H d) = f := by
  cases f using Subtype.rec with
  | mk q hq =>
    change rawBassSerreOrbitEdgeMk G H d = q at hd
    subst q
    cases ha
    cases hb
    apply Subtype.ext
    rfl

theorem test_rawOrbitSymm_toPos_cast_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (d : rawBassSerreEdgeData G)
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b)
    (ha : rawBassSerreOrbitEdgeSource G H
      (rawBassSerreOrbitEdgeMk G H d) = a)
    (hb : rawBassSerreOrbitEdgeTarget G H
      (rawBassSerreOrbitEdgeMk G H d) = b)
    (hd : rawBassSerreOrbitEdgeMk G H d = f.1) :
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitEdgeSource G H (rawBassSerreOrbitEdgeMk G H d))
      (rawBassSerreOrbitEdgeTarget G H (rawBassSerreOrbitEdgeMk G H d)) a b ha hb
      (Quiver.Hom.toPos (rawBassSerreOrbitQuiverEdge G H d)) =
        Quiver.Hom.toPos f := by
  have he := test_rawOrbitEdge_cast_eq G H d f ha hb hd
  cases ha
  cases hb
  cases he
  rfl

theorem test_rawOrbitSymm_toPos_map_cast_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (d : rawBassSerreEdgeData G)
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b)
    (ha : actionOrbitMk H (RawBassSerreVertex G)
      (rawBassSerreEdgeDataSource G d) = a)
    (hb : actionOrbitMk H (RawBassSerreVertex G)
      (rawBassSerreEdgeDataTarget G d) = b)
    (hd : rawBassSerreOrbitEdgeMk G H d = f.1) :
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ ha hb
      (Quiver.Hom.toPos
        (rawBassSerreOrbitEdgeMap G H
          (RawBassSerreEdge.centralFactor d.1 d.2))) =
        Quiver.Hom.toPos f := by
  cases d with
  | mk g i =>
      dsimp [rawBassSerreOrbitEdgeMap]
      have he := test_rawOrbitEdge_cast_eq G H (g, i) f ha hb hd
      cases ha
      cases hb
      cases he
      rfl

theorem test_rawOrbitSymm_toNeg_map_cast_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (d : rawBassSerreEdgeData G)
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b)
    (ha : actionOrbitMk H (RawBassSerreVertex G)
      (rawBassSerreEdgeDataSource G d) = a)
    (hb : actionOrbitMk H (RawBassSerreVertex G)
      (rawBassSerreEdgeDataTarget G d) = b)
    (hd : rawBassSerreOrbitEdgeMk G H d = f.1) :
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ hb ha
      (Quiver.Hom.toNeg
        (rawBassSerreOrbitEdgeMap G H
          (RawBassSerreEdge.centralFactor d.1 d.2))) =
        Quiver.Hom.toNeg f := by
  cases d with
  | mk g i =>
      dsimp [rawBassSerreOrbitEdgeMap]
      have he := test_rawOrbitEdge_cast_eq G H (g, i) f ha hb hd
      cases ha
      cases hb
      cases he
      rfl

theorem test_path_cons_cast {U : Type u} [Quiver.{v} U]
    {a a' b b' c c' : U}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (p : Quiver.Path a b) (p' : Quiver.Path a' b')
    (e : b ⟶ c) (e' : b' ⟶ c')
    (hp : Quiver.Path.cast ha hb p = p')
    (he : Quiver.Hom.cast hb hc e = e') :
    Quiver.Path.cast ha hc (p.cons e) = p'.cons e' := by
  cases ha
  cases hb
  cases hc
  cases hp
  cases he
  rfl

theorem test_hom_cast_cast_explicit {U : Type u} [q : Quiver.{v} U]
    {x y x' y' x'' y'' : U}
    (e : @Quiver.Hom U q x y)
    (hx : x = x') (hy : y = y')
    (hx' : x' = x'') (hy' : y' = y'') :
    @Quiver.Hom.cast U q x' y' x'' y'' hx' hy'
        (@Quiver.Hom.cast U q x y x' y' hx hy e) =
      @Quiver.Hom.cast U q x y x'' y'' (hx.trans hx') (hy.trans hy') e := by
  exact @Quiver.Hom.cast_cast U q x y x' y' x'' y'' e hx hy hx' hy'

theorem test_hom_cast_proof_irrel {U : Type u} [q : Quiver.{v} U]
    {x y x' y' : U} (e : @Quiver.Hom U q x y)
    (hx hx' : x = x') (hy hy' : y = y') :
    @Quiver.Hom.cast U q x y x' y' hx hy e =
      @Quiver.Hom.cast U q x y x' y' hx' hy' e := by
  have hxx : hx = hx' := Subsingleton.elim _ _
  have hyy : hy = hy' := Subsingleton.elim _ _
  cases hxx
  cases hyy
  rfl

theorem test_lift_pos_edge_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b) (v : H)
    (hs : (v * quotientEdgeCoherentSourceAlign G H f).1 •
          rawBassSerreEdgeDataSource G (quotientEdgeRawData G H f) =
        v.1 • rawTreeRepresentative G H a)
    (ht : (v * quotientEdgeCoherentSourceAlign G H f).1 •
          rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H f) =
        (v * (quotientEdgeLabel G H f)⁻¹).1 •
          rawTreeRepresentative G H b) :
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
      (test_rawTreeRepresentative_smul_orbit G H a v)
      (test_rawTreeRepresentative_smul_orbit G H b
        (v * (quotientEdgeLabel G H f)⁻¹))
      ((rawBassSerreOrbitSymmPrefunctor G H).map
        (@Quiver.Hom.toPos (RawBassSerreVertex G)
          (rawBassSerreQuiver G) _ _
          (@Quiver.Hom.cast (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _ _ _ hs ht
            (rawBassSerreEdgeAction G
              (v * quotientEdgeCoherentSourceAlign G H f).1
              (RawBassSerreEdge.centralFactor
                (quotientEdgeRawData G H f).1
                (quotientEdgeRawData G H f).2))))) =
      @Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) a b f := by
  let d := quotientEdgeRawData G H f
  let s := quotientEdgeCoherentSourceAlign G H f
  let l := quotientEdgeLabel G H f
  have hmap := test_rawOrbitSymm_map_pos_cast G H hs ht
    (rawBassSerreEdgeAction G (v * s).1
      (RawBassSerreEdge.centralFactor d.1 d.2))
  have hact := test_rawOrbitMap_action_pos G H d (v * s)
  have hactsrc :
      actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataSource G ((v * s).1 • d)) =
        actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataSource G d) := by
    exact actionOrbitMk_smul H (RawBassSerreVertex G) (v * s)
      (rawBassSerreEdgeDataSource G d)
  have hacttgt :
      actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataTarget G ((v * s).1 • d)) =
        actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataTarget G d) := by
    exact actionOrbitMk_smul H (RawBassSerreVertex G) (v * s)
      (rawBassSerreEdgeDataTarget G d)
  have hsrc :
      (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj hs).trans
          (test_rawTreeRepresentative_smul_orbit G H a v) =
        hactsrc.trans (quotientEdgeSource_orbit G H f) := by
    apply Subsingleton.elim
  have htgt :
      (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj ht).trans
          (test_rawTreeRepresentative_smul_orbit G H b
            (v * l⁻¹)) =
        hacttgt.trans (quotientEdgeTarget_orbit G H f) := by
    apply Subsingleton.elim
  rw [hmap]
  change
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _
      (@Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _ _) = _
  rw [@Quiver.Hom.cast_cast
    (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
    (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H))]
  rw [hsrc, htgt]
  change
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
      (hactsrc.trans (quotientEdgeSource_orbit G H f))
      (hacttgt.trans (quotientEdgeTarget_orbit G H f))
      ((rawBassSerreOrbitSymmPrefunctor G H).map
        (@Quiver.Hom.toPos (RawBassSerreVertex G)
          (rawBassSerreQuiver G) _ _
          (rawBassSerreEdgeAction G (v * s).1
            (RawBassSerreEdge.centralFactor d.1 d.2)))) = f.toPos
  calc
    _ = @Quiver.Hom.cast
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (quotientEdgeSource_orbit G H f)
          (quotientEdgeTarget_orbit G H f)
          (@Quiver.Hom.cast
            (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
            hactsrc hacttgt
            ((rawBassSerreOrbitSymmPrefunctor G H).map
              (@Quiver.Hom.toPos (RawBassSerreVertex G)
                (rawBassSerreQuiver G) _ _
                (rawBassSerreEdgeAction G (v * s).1
                  (RawBassSerreEdge.centralFactor d.1 d.2))))) := by
      convert (@Quiver.Hom.cast_cast
        (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _
        ((rawBassSerreOrbitSymmPrefunctor G H).map
          (@Quiver.Hom.toPos (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _
            (rawBassSerreEdgeAction G (v * s).1
              (RawBassSerreEdge.centralFactor d.1 d.2))))
        hactsrc hacttgt
        (quotientEdgeSource_orbit G H f)
        (quotientEdgeTarget_orbit G H f)).symm using 1 <;>
        (try rfl) <;>
        (try (congr 1 <;> apply Subsingleton.elim))
    _ = @Quiver.Hom.cast
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (quotientEdgeSource_orbit G H f)
          (quotientEdgeTarget_orbit G H f)
          (rawBassSerreOrbitEdgeMap G H
            (RawBassSerreEdge.centralFactor d.1 d.2)).toPos := by
      exact congrArg
        (fun z => @Quiver.Hom.cast
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (quotientEdgeSource_orbit G H f)
          (quotientEdgeTarget_orbit G H f) z) hact
    _ = f.toPos := test_rawOrbitSymm_toPos_map_cast_eq G H d f
      (quotientEdgeSource_orbit G H f)
      (quotientEdgeTarget_orbit G H f)
      (quotientEdgeRawData_mk G H f)

theorem test_lift_neg_edge_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b) (v : H)
    (hs : (v * quotientEdgeLabel G H f *
            quotientEdgeCoherentSourceAlign G H f).1 •
          rawBassSerreEdgeDataTarget G (quotientEdgeRawData G H f) =
        v.1 • rawTreeRepresentative G H b)
    (ht : (v * quotientEdgeLabel G H f *
            quotientEdgeCoherentSourceAlign G H f).1 •
          rawBassSerreEdgeDataSource G (quotientEdgeRawData G H f) =
        (v * quotientEdgeLabel G H f).1 •
          rawTreeRepresentative G H a) :
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
      (test_rawTreeRepresentative_smul_orbit G H b v)
      (test_rawTreeRepresentative_smul_orbit G H a
        (v * quotientEdgeLabel G H f))
      ((rawBassSerreOrbitSymmPrefunctor G H).map
        (@Quiver.Hom.toNeg (RawBassSerreVertex G)
          (rawBassSerreQuiver G) _ _
          (@Quiver.Hom.cast (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _ _ _ ht hs
            (rawBassSerreEdgeAction G
              (v * quotientEdgeLabel G H f *
                quotientEdgeCoherentSourceAlign G H f).1
              (RawBassSerreEdge.centralFactor
                (quotientEdgeRawData G H f).1
                (quotientEdgeRawData G H f).2))))) =
      @Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) a b f := by
  let d := quotientEdgeRawData G H f
  let s := quotientEdgeCoherentSourceAlign G H f
  let l := quotientEdgeLabel G H f
  have hmap := test_rawOrbitSymm_map_neg_cast G H ht hs
    (rawBassSerreEdgeAction G (v * l * s).1
      (RawBassSerreEdge.centralFactor d.1 d.2))
  have hact := test_rawOrbitMap_action_neg G H d (v * l * s)
  have hactsrc :
      actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataSource G ((v * l * s).1 • d)) =
        actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataSource G d) := by
    exact actionOrbitMk_smul H (RawBassSerreVertex G) (v * l * s)
      (rawBassSerreEdgeDataSource G d)
  have hacttgt :
      actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataTarget G ((v * l * s).1 • d)) =
        actionOrbitMk H (RawBassSerreVertex G)
          (rawBassSerreEdgeDataTarget G d) := by
    exact actionOrbitMk_smul H (RawBassSerreVertex G) (v * l * s)
      (rawBassSerreEdgeDataTarget G d)
  have hsrc :
      (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj hs).trans
          (test_rawTreeRepresentative_smul_orbit G H b v) =
        hacttgt.trans (quotientEdgeTarget_orbit G H f) := by
    apply Subsingleton.elim
  have htgt :
      (congrArg (rawBassSerreOrbitSymmPrefunctor G H).obj ht).trans
          (test_rawTreeRepresentative_smul_orbit G H a (v * l)) =
        hactsrc.trans (quotientEdgeSource_orbit G H f) := by
    apply Subsingleton.elim
  rw [hmap]
  change
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _
      (@Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _ _) = _
  rw [@Quiver.Hom.cast_cast
    (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
    (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H))]
  rw [hsrc, htgt]
  change
    @Quiver.Hom.cast (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
      (hacttgt.trans (quotientEdgeTarget_orbit G H f))
      (hactsrc.trans (quotientEdgeSource_orbit G H f))
      ((rawBassSerreOrbitSymmPrefunctor G H).map
        (@Quiver.Hom.toNeg (RawBassSerreVertex G)
          (rawBassSerreQuiver G) _ _
          (rawBassSerreEdgeAction G (v * l * s).1
            (RawBassSerreEdge.centralFactor d.1 d.2)))) =
      @Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) a b f
  calc
    _ = @Quiver.Hom.cast
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (quotientEdgeTarget_orbit G H f)
          (quotientEdgeSource_orbit G H f)
          (@Quiver.Hom.cast
            (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
            hacttgt hactsrc
            ((rawBassSerreOrbitSymmPrefunctor G H).map
              (@Quiver.Hom.toNeg (RawBassSerreVertex G)
                (rawBassSerreQuiver G) _ _
                (rawBassSerreEdgeAction G (v * l * s).1
                  (RawBassSerreEdge.centralFactor d.1 d.2))))) := by
      convert (@Quiver.Hom.cast_cast
        (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _
        ((rawBassSerreOrbitSymmPrefunctor G H).map
          (@Quiver.Hom.toNeg (RawBassSerreVertex G)
            (rawBassSerreQuiver G) _ _
            (rawBassSerreEdgeAction G (v * l * s).1
              (RawBassSerreEdge.centralFactor d.1 d.2))))
        hacttgt hactsrc
        (quotientEdgeTarget_orbit G H f)
        (quotientEdgeSource_orbit G H f)).symm using 1 <;>
        (try rfl) <;>
        (try (congr 1 <;> apply Subsingleton.elim))
    _ = @Quiver.Hom.cast
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (quotientEdgeTarget_orbit G H f)
          (quotientEdgeSource_orbit G H f)
          (Quiver.Hom.toNeg
            (rawBassSerreOrbitEdgeMap G H
              (RawBassSerreEdge.centralFactor d.1 d.2))) := by
      exact congrArg
        (fun z => @Quiver.Hom.cast
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (quotientEdgeTarget_orbit G H f)
          (quotientEdgeSource_orbit G H f) z) hact
    _ = @Quiver.Hom.toNeg (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
          (rawBassSerreOrbitQuiver.inst G H) a b f :=
      test_rawOrbitSymm_toNeg_map_cast_eq G H d f
        (quotientEdgeSource_orbit G H f)
        (quotientEdgeTarget_orbit G H f)
        (quotientEdgeRawData_mk G H f)

theorem testQuotientPathLift_map {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H} (u : H) :
    ∀ {b : RawBassSerreOrbitVertex G H}
      (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b),
      (@Quiver.Path.cast
        (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _
          (test_rawTreeRepresentative_smul_orbit G H a u)
          (test_rawTreeRepresentative_smul_orbit G H b
            (testQuotientPathLift G H u p).1)
          (@Prefunctor.mapPath
            (Quiver.Symmetrify (RawBassSerreVertex G))
            (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
              (rawBassSerreQuiver G))
            (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H))
            (rawBassSerreOrbitSymmPrefunctor G H)
            _ _ (testQuotientPathLift G H u p).2)) = p
  | _, Quiver.Path.nil => by
      dsimp [testQuotientPathLift]
      apply test_path_cast_nil
  | _, @Quiver.Path.cons _ _ _ b c p e => by
      let ih := testQuotientPathLift_map G H u p
      let L := testQuotientPathLift G H u p
      let v : H := L.1
      cases e using Sum.rec with
      | inl f =>
          dsimp [testQuotientPathLift]
          let d := quotientEdgeRawData G H f
          let s := quotientEdgeCoherentSourceAlign G H f
          let l := quotientEdgeLabel G H f
          have hsl : s.1 • rawBassSerreEdgeDataTarget G d =
              l.1⁻¹ • rawTreeRepresentative G H c := by
            apply smul_left_cancel l.1
            rw [quotientEdgeLabel_transport_coherent G H f]
            simp [smul_smul]
          have hsource : (v * s).1 •
                rawBassSerreEdgeDataSource G d =
              v.1 • rawTreeRepresentative G H b := by
            calc
              (v * s).1 • rawBassSerreEdgeDataSource G d =
                  v.1 • (s.1 • rawBassSerreEdgeDataSource G d) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul]
              _ = v.1 • rawTreeRepresentative G H b := by
                    rw [quotientEdgeCoherentSourceAlign_spec G H f]
          have htarget : (v * s).1 •
                rawBassSerreEdgeDataTarget G d =
              (v * l⁻¹).1 • rawTreeRepresentative G H c := by
            calc
              (v * s).1 • rawBassSerreEdgeDataTarget G d =
                  v.1 • (s.1 • rawBassSerreEdgeDataTarget G d) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul]
              _ = v.1 • (l.1⁻¹ • rawTreeRepresentative G H c) := by
                    rw [hsl]
              _ = (v * l⁻¹).1 • rawTreeRepresentative G H c := by
                    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
                    rw [smul_smul]
          refine @test_path_cons_cast
            (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _
            (test_rawTreeRepresentative_smul_orbit G H a u)
            (test_rawTreeRepresentative_smul_orbit G H b v)
            (test_rawTreeRepresentative_smul_orbit G H c (v * l⁻¹))
            ((rawBassSerreOrbitSymmPrefunctor G H).mapPath L.2)
            p _ (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) _ _ f) ?_ ?_
          · simpa [L, v] using ih
          · exact test_lift_pos_edge_map G H f v
              (by simpa [d, s] using hsource)
              (by simpa [d, s, l] using htarget)
      | inr f =>
          dsimp [testQuotientPathLift]
          let d := quotientEdgeRawData G H f
          let s := quotientEdgeCoherentSourceAlign G H f
          let l := quotientEdgeLabel G H f
          have hsource : (v * l * s).1 •
                rawBassSerreEdgeDataTarget G d =
              v.1 • rawTreeRepresentative G H b := by
            calc
              (v * l * s).1 • rawBassSerreEdgeDataTarget G d =
                  v.1 • (l.1 • (s.1 • rawBassSerreEdgeDataTarget G d)) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul, smul_smul]
              _ = v.1 • rawTreeRepresentative G H b := by
                    rw [quotientEdgeLabel_transport_coherent G H f]
          have htarget : (v * l * s).1 •
                rawBassSerreEdgeDataSource G d =
              (v * l).1 • rawTreeRepresentative G H c := by
            calc
              (v * l * s).1 • rawBassSerreEdgeDataSource G d =
                  (v * l).1 • (s.1 • rawBassSerreEdgeDataSource G d) := by
                    simp only [Subgroup.coe_mul]
                    rw [smul_smul]
              _ = (v * l).1 • rawTreeRepresentative G H c := by
                    rw [quotientEdgeCoherentSourceAlign_spec G H f]
          refine @test_path_cons_cast
            (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H)) _ _ _ _ _ _
            (test_rawTreeRepresentative_smul_orbit G H a u)
            (test_rawTreeRepresentative_smul_orbit G H b v)
            (test_rawTreeRepresentative_smul_orbit G H c (v * l))
            ((rawBassSerreOrbitSymmPrefunctor G H).mapPath L.2)
            p _ (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) _ _ f) ?_ ?_
          · simpa [L, v] using ih
          · convert (test_lift_neg_edge_map G H f v
              (by simpa [d, s, l] using hsource)
              (by simpa [d, s, l] using htarget)) using 1

theorem testQuotientPathLift_value {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H} (u : H) :
    ∀ {b : RawBassSerreOrbitVertex G H}
      (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b),
      quotientRawPathValue G H p =
        (testQuotientPathLift G H u p).1⁻¹ * u := by
  intro b p
  induction p generalizing u with
  | nil =>
      have hnil := quotientRawPathValue_nil G H
        (show RawBassSerreOrbitVertex G H from b)
      calc
        quotientRawPathValue G H
            (@Quiver.Path.nil (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) b) = 1 := hnil
        _ = (testQuotientPathLift G H u
            (@Quiver.Path.nil (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) b)).1⁻¹ * u := by
              simp [testQuotientPathLift]
  | @cons b c p e ih =>
      cases e using Sum.rec with
      | inl f =>
          change quotientRawPathValue G H
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) b c f)) =
            (testQuotientPathLift G H u
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) b c f))).1⁻¹ * u
          have hcons := @quotientRawPathValue_cons _ G _ H a b c
            (show @Quiver.Path (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a b from p)
            (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) b c f)
          rw [hcons, ih u]
          simp [quotientSymmEdgeLabel, testQuotientPathLift, mul_assoc]
      | inr f =>
          change quotientRawPathValue G H
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) c b f)) =
            (testQuotientPathLift G H u
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) c b f))).1⁻¹ * u
          have hcons := @quotientRawPathValue_cons _ G _ H a b c
            (show @Quiver.Path (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a b from p)
            (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) c b f)
          rw [hcons, ih u]
          simp [quotientSymmEdgeLabel, testQuotientPathLift, mul_assoc]

theorem test_homOfEq_comp_homOfEq {C : Type*} [Category C]
    {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    Quiver.homOfEq f hX hY ≫ Quiver.homOfEq g hY hZ =
      Quiver.homOfEq (f ≫ g) hX hZ := by
  subst hX hY hZ
  rfl

noncomputable def testRawOrbitFreeGroupoidFunctor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) :
    Quiver.FreeGroupoid (RawBassSerreVertex G) ⥤
      Quiver.FreeGroupoid (RawBassSerreOrbitVertex G H) :=
  Quiver.freeGroupoidFunctor (rawBassSerreOrbitPrefunctor G H)

noncomputable def testRawOrbitFreeGroupoidFunctor_obj {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) (x : RawBassSerreVertex G) :
    (testRawOrbitFreeGroupoidFunctor G H).obj
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x) =
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj
        ((rawBassSerreOrbitPrefunctor G H).obj x) := by
  change (Quiver.FreeGroupoid.lift
      (rawBassSerreOrbitPrefunctor G H ⋙q
        Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H))).obj
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x) = _
  exact Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec
      (rawBassSerreOrbitPrefunctor G H ⋙q
        Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H))) x

theorem testRawOrbitFreeGroupoidFunctor_map_of {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b) :
    Quiver.homOfEq
        ((testRawOrbitFreeGroupoidFunctor G H).map
          ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map e))
        (testRawOrbitFreeGroupoidFunctor_obj G H a)
        (testRawOrbitFreeGroupoidFunctor_obj G H b) =
      (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map
        ((rawBassSerreOrbitPrefunctor G H).map e) := by
  change Quiver.homOfEq
      ((Quiver.FreeGroupoid.lift
        (rawBassSerreOrbitPrefunctor G H ⋙q
          Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H))).map
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map e))
      (Prefunctor.congr_obj
        (Quiver.FreeGroupoid.lift_spec
          (rawBassSerreOrbitPrefunctor G H ⋙q
            Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H))) a)
      (Prefunctor.congr_obj
        (Quiver.FreeGroupoid.lift_spec
          (rawBassSerreOrbitPrefunctor G H ⋙q
            Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H))) b) =
    (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map
      ((rawBassSerreOrbitPrefunctor G H).map e)
  have hs := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec
      (rawBassSerreOrbitPrefunctor G H ⋙q
        Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H))) e
  exact hs

theorem testRawOrbitFreeGroupoidFunctor_map_path {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) a b) :
    Quiver.homOfEq
        ((testRawOrbitFreeGroupoidFunctor G H).map
          (@testFreePathHom (RawBassSerreVertex G)
            (rawBassSerreQuiver G) (show RawBassSerreVertex G from a)
            (show RawBassSerreVertex G from b) p))
        (testRawOrbitFreeGroupoidFunctor_obj G H
          (show RawBassSerreVertex G from a))
        (testRawOrbitFreeGroupoidFunctor_obj G H
          (show RawBassSerreVertex G from b)) =
      (@testFreePathHom (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) _ _
        ((rawBassSerreOrbitSymmPrefunctor G H).mapPath p)) := by
  induction p with
  | nil =>
      change Quiver.homOfEq (𝟙 _) _ _ = 𝟙 _
      have h := testRawOrbitFreeGroupoidFunctor_obj G H
        (show RawBassSerreVertex G from a)
      cases h
      rfl
  | @cons b c p e ih =>
      cases e using Sum.rec with
      | inl f =>
          simp only [testFreePathHom, Prefunctor.mapPath]
          rw [Functor.map_comp, ← test_homOfEq_comp_homOfEq,
            ih, testRawOrbitFreeGroupoidFunctor_map_of G H
              (a := show RawBassSerreVertex G from b)
              (b := show RawBassSerreVertex G from c) f]
          · rfl
          · exact testRawOrbitFreeGroupoidFunctor_obj G H
              (show RawBassSerreVertex G from b)
      | inr f =>
          simp only [testFreePathHom, Prefunctor.mapPath]
          have hmapinv := (testRawOrbitFreeGroupoidFunctor G H).map_inv
            ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map f)
          have hmapinv' :
              (testRawOrbitFreeGroupoidFunctor G H).map
                  (Groupoid.inv
                    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map f)) =
                Groupoid.inv
                  ((testRawOrbitFreeGroupoidFunctor G H).map
                    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map f)) := by
            simpa only [Groupoid.inv_eq_inv] using hmapinv
          rw [Functor.map_comp, hmapinv', ← test_homOfEq_comp_homOfEq, ih,
            show Quiver.homOfEq
                (Groupoid.inv
                  ((testRawOrbitFreeGroupoidFunctor G H).map
                    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map f)))
                (testRawOrbitFreeGroupoidFunctor_obj G H
                  (show RawBassSerreVertex G from b))
                (testRawOrbitFreeGroupoidFunctor_obj G H
                  (show RawBassSerreVertex G from c)) = _ from by
              have hinv := congrArg Groupoid.inv
                (testRawOrbitFreeGroupoidFunctor_map_of G H
                  (a := show RawBassSerreVertex G from c)
                  (b := show RawBassSerreVertex G from b) f)
              rw [testGroupoid_inv_homOfEq] at hinv]
          · rfl
          · exact testRawOrbitFreeGroupoidFunctor_obj G H
              (show RawBassSerreVertex G from b)

theorem testRawFreeGroupoid_end_subsingleton_at {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (x : Quiver.FreeGroupoid (RawBassSerreVertex G)) :
    Subsingleton (End x) := by
  letI : Quiver.RootedConnected
      (show Quiver.Symmetrify (RawBassSerreVertex G) from
        RawBassSerreVertex.central 1) :=
    rawBassSerre_rootedConnected G
  letI : IsConnected (Quiver.FreeGroupoid (RawBassSerreVertex G)) :=
    testFreeGroupoid_isConnected_of_rootedConnected
      (RawBassSerreVertex.central 1)
  obtain ⟨p⟩ :=
    CategoryTheory.nonempty_hom_of_preconnected_groupoid
      ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
        (RawBassSerreVertex.central 1)) x
  constructor
  intro f g
  have hroot : p ≫ f ≫ Groupoid.inv p =
      p ≫ g ≫ Groupoid.inv p := by
    exact @Subsingleton.elim _ (testRawFreeGroupoid_end_subsingleton G) _ _
  have hcancel := congrArg
    (fun z => Groupoid.inv p ≫ z ≫ p) hroot
  unfold CategoryTheory.End at f g ⊢
  simpa [Category.assoc] using hcancel

theorem test_homOfEq_id {C : Type*} [Category C]
    {X X' : C} (hX : X = X') :
    Quiver.homOfEq (𝟙 X) hX hX = 𝟙 X' := by
  cases hX
  rfl

theorem testFreePathHom_cast {V : Type u} [q : Quiver.{v} V]
    {a b a' b' : Quiver.Symmetrify V}
    (p : @Quiver.Path (Quiver.Symmetrify V)
      (@Quiver.symmetrifyQuiver V q) a b)
    (ha : a = a') (hb : b = b') :
    (@testFreePathHom V q (show V from a') (show V from b')
      (@Quiver.Path.cast (Quiver.Symmetrify V)
        (@Quiver.symmetrifyQuiver V q) a b a' b' ha hb p)) =
      Quiver.homOfEq
        (@testFreePathHom V q (show V from a) (show V from b) p)
        (congrArg (Quiver.FreeGroupoid.of V).obj ha)
        (congrArg (Quiver.FreeGroupoid.of V).obj hb) := by
  cases ha
  cases hb
  rfl

theorem testFreePathHom_cast_loop_eq_one {V : Type u} [q : Quiver.{v} V]
    {a a' : Quiver.Symmetrify V}
    (p : @Quiver.Path (Quiver.Symmetrify V)
      (@Quiver.symmetrifyQuiver V q) a a)
    (ha : a = a') (hb : a = a')
    (hp : @testFreePathHom V q (show V from a) (show V from a) p = 𝟙 _) :
    @testFreePathHom V q (show V from a') (show V from a')
      (@Quiver.Path.cast (Quiver.Symmetrify V)
        (@Quiver.symmetrifyQuiver V q) a a a' a' ha hb p) = 𝟙 _ := by
  rw [testFreePathHom_cast, hp]
  have hproof :
      congrArg (Quiver.FreeGroupoid.of V).obj ha =
        congrArg (Quiver.FreeGroupoid.of V).obj hb :=
    Subsingleton.elim _ _
  cases hproof
  apply test_homOfEq_id

theorem testQuotientFreePathHom_eq_one_of_value_one {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) (rawBassSerreOrbitRoot G H)}
    (hp : quotientRawPathValue G H p = 1) :
    @testFreePathHom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H)
      (rawBassSerreOrbitRoot G H) (rawBassSerreOrbitRoot G H) p = 𝟙 _ := by
  let L := testQuotientPathLift G H (1 : H) p
  have hL : testQuotientPathLift G H (1 : H) p = L := rfl
  have hvalue := testQuotientPathLift_value G H (1 : H) p
  change quotientRawPathValue G H p = L.1⁻¹ * (1 : H) at hvalue
  rcases L with ⟨v, r⟩
  rw [hp] at hvalue
  have hinv : v⁻¹ = (1 : H) := by
    simpa using hvalue.symm
  have hv : v = (1 : H) := by
    simpa using congrArg (fun x : H => x⁻¹) hinv
  cases hv
  have hmap := testQuotientPathLift_map G H (1 : H) p
  rw [hL] at hmap
  let r' : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) _ _ := r
  have hraw :
      @testFreePathHom (RawBassSerreVertex G)
        (rawBassSerreQuiver G) _ _ r' = 𝟙 _ := by
    letI : Subsingleton (End
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          ((1 : H).1 • rawTreeRepresentative G H
            (rawBassSerreOrbitRoot G H)))) :=
      testRawFreeGroupoid_end_subsingleton_at G _
    exact @Subsingleton.elim _
      (testRawFreeGroupoid_end_subsingleton_at G
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          ((1 : H).1 • rawTreeRepresentative G H
            (rawBassSerreOrbitRoot G H)))) _ _
  have hfun := testRawOrbitFreeGroupoidFunctor_map_path G H
    (a := show Quiver.Symmetrify (RawBassSerreVertex G) from
      (1 : H).1 • rawTreeRepresentative G H (rawBassSerreOrbitRoot G H))
    (b := show Quiver.Symmetrify (RawBassSerreVertex G) from
      (1 : H).1 • rawTreeRepresentative G H (rawBassSerreOrbitRoot G H)) r'
  simp only [hraw, Functor.map_id, test_homOfEq_id] at hfun
  have hproj :
      @testFreePathHom (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) _ _
        ((rawBassSerreOrbitSymmPrefunctor G H).mapPath r) = 𝟙 _ := by
    exact hfun.symm
  dsimp at hmap
  let x : RawBassSerreVertex G :=
    (1 : H).1 • rawTreeRepresentative G H (rawBassSerreOrbitRoot G H)
  let x' : Quiver.Symmetrify (RawBassSerreVertex G) := x
  let q : Quiver.Symmetrify (RawBassSerreOrbitVertex G H) :=
    (rawBassSerreOrbitSymmPrefunctor G H).obj x'
  let qpath : @Quiver.Path
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) q q :=
    (rawBassSerreOrbitSymmPrefunctor G H).mapPath r'
  have hproj' :
      @testFreePathHom (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H) q q qpath = 𝟙 _ := by
    simpa [qpath, q, x, x', r'] using hproj
  have hcast := testFreePathHom_cast_loop_eq_one
    (V := RawBassSerreOrbitVertex G H)
    (q := rawBassSerreOrbitQuiver.inst G H)
    (a := q) (a' := rawBassSerreOrbitRoot G H) qpath
    (by
      change actionOrbitMk H (RawBassSerreVertex G)
        ((1 : H).1 • rawTreeRepresentative G H
          (rawBassSerreOrbitRoot G H)) = rawBassSerreOrbitRoot G H
      exact test_rawTreeRepresentative_smul_orbit G H
        (rawBassSerreOrbitRoot G H) (1 : H))
    (by
      change actionOrbitMk H (RawBassSerreVertex G)
        ((1 : H).1 • rawTreeRepresentative G H
          (rawBassSerreOrbitRoot G H)) = rawBassSerreOrbitRoot G H
      exact test_rawTreeRepresentative_smul_orbit G H
        (rawBassSerreOrbitRoot G H) (1 : H)) hproj'
  rw [← hmap]
  exact hcast

theorem testFreePathHom_eq_quotient_map
    {V : Type u} [q : Quiver V] {a b : Quiver.Symmetrify V}
    (p : @Quiver.Path (Quiver.Symmetrify V)
      (@Quiver.symmetrifyQuiver V q) a b) :
    testFreePathHom (q := q) p =
      (CategoryTheory.Quotient.functor (@Quiver.FreeGroupoid.redStep V q)).map p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      simp only [testFreePathHom, Prefunctor.mapPath]
      rw [ih]
      cases e using Sum.rec <;> rfl

theorem testOrbitFreePathHom_eq_quotient_map
    {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    @testFreePathHom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b p =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver G H))).map p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      simp only [testFreePathHom]
      rw [ih]
      cases e using Sum.rec <;> rfl

/- theorem testOrbitRawPathValue_eq_quotient_map
    {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    quotientRawPathValue G H p =
      quotientPathValue G H
        ((CategoryTheory.Quotient.functor
          (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver G H))).map p) := by
  induction p with
  | nil =>
      exact (quotientRawPathValue_nil G H _).trans (by rfl)
  | @cons b c p e ih =>
      cases e with
      | inl e =>
          have hraw := @quotientRawPathValue_cons _ G _ H a b c
            (show @Quiver.Path (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a b from p)
            (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) b c e)
          have hmap :
              (CategoryTheory.Quotient.functor
                (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver G H))).map
                  (@Quiver.Path.cons (Quiver.Symmetrify
                    (RawBassSerreOrbitVertex G H))
                    (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                      (rawBassSerreOrbitQuiver.inst G H)) a b c p
                    (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                      (rawBassSerreOrbitQuiver.inst G H) b c e)) =
                (CategoryTheory.Quotient.functor
                  (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver G H))).map p ≫
                  (Quiver.FreeGroupoid.of
                    (RawBassSerreOrbitVertex G H)).map e := by
            rfl
          change quotientRawPathValue G H
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) b c e)) =
            quotientPathValue G H
              ((CategoryTheory.Quotient.functor
                (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver G H))).map
                (@Quiver.Path.cons (Quiver.Symmetrify
                  (RawBassSerreOrbitVertex G H))
                  (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H)) a b c p
                  (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H) b c e)))
          rw [hraw, hmap, quotientPathValue_comp,
            quotientPathValue_of, ih]
      | inr e =>
          have hraw := @quotientRawPathValue_cons _ G _ H a b c
            (show @Quiver.Path (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a b from p)
            (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) b c e)
          have hmap :
              (CategoryTheory.Quotient.functor
                (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver G H))).map
                  (@Quiver.Path.cons (Quiver.Symmetrify
                    (RawBassSerreOrbitVertex G H))
                    (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                      (rawBassSerreOrbitQuiver.inst G H)) a b c p
                    (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                      (rawBassSerreOrbitQuiver.inst G H) b c e)) =
                (CategoryTheory.Quotient.functor
                  (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver G H))).map p ≫
                  Groupoid.inv ((Quiver.FreeGroupoid.of
                    (RawBassSerreOrbitVertex G H)).map e) := by
            rfl
          change quotientRawPathValue G H
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) b c e)) =
            quotientPathValue G H
              ((CategoryTheory.Quotient.functor
                (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver G H))).map
                (@Quiver.Path.cons (Quiver.Symmetrify
                  (RawBassSerreOrbitVertex G H))
                  (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H)) a b c p
                  (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H) b c e)))
          rw [hraw, hmap, quotientPathValue_comp,
            quotientPathValue_inv, quotientPathValue_of, ih]

-/

theorem testQuotientRawPathValue_testFreePathHom
    {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    quotientRawPathValue G H p =
      quotientPathValue G H
        (@testFreePathHom (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H) a b p) := by
  induction p with
  | nil =>
      have hnil : quotientRawPathValue G H
          (@Quiver.Path.nil (Quiver.Symmetrify
            (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H)) a) = 1 :=
        quotientRawPathValue_nil G H a
      change quotientRawPathValue G H
          (@Quiver.Path.nil (Quiver.Symmetrify
            (RawBassSerreOrbitVertex G H))
            (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H)) a) =
        quotientPathValue G H
          (@testFreePathHom (RawBassSerreOrbitVertex G H)
            (rawBassSerreOrbitQuiver.inst G H) a a
            (@Quiver.Path.nil (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a))
      rw [hnil]
      change (1 : H) = 1
      rfl
  | @cons b c p e ih =>
      cases e using Sum.rec with
      | inl e =>
          have hraw := @quotientRawPathValue_cons _ G _ H a b c
            (show @Quiver.Path (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a b from p)
            (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) b c e)
          change quotientRawPathValue G H
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) b c e)) =
            quotientPathValue G H
              (@testFreePathHom (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H) a c
                (@Quiver.Path.cons (Quiver.Symmetrify
                  (RawBassSerreOrbitVertex G H))
                  (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H)) a b c p
                  (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H) b c e)))
          rw [hraw]
          change quotientSymmEdgeLabel G H
                (@Quiver.Hom.toPos (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) b c e) *
              quotientRawPathValue G H p =
            quotientPathValue G H
              (testFreePathHom p ≫
                (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e)
          rw [quotientPathValue_comp, quotientPathValue_of,
            quotientSymmEdgeLabel, ih]
      | inr e =>
          have hraw := @quotientRawPathValue_cons _ G _ H a b c
            (show @Quiver.Path (Quiver.Symmetrify
              (RawBassSerreOrbitVertex G H))
              (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H)) a b from p)
            (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
              (rawBassSerreOrbitQuiver.inst G H) c b e)
          change quotientRawPathValue G H
              (@Quiver.Path.cons (Quiver.Symmetrify
                (RawBassSerreOrbitVertex G H))
                (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H)) a b c p
                (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) c b e)) =
            quotientPathValue G H
              (@testFreePathHom (RawBassSerreOrbitVertex G H)
                (rawBassSerreOrbitQuiver.inst G H) a c
                (@Quiver.Path.cons (Quiver.Symmetrify
                  (RawBassSerreOrbitVertex G H))
                  (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H)) a b c p
                  (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                    (rawBassSerreOrbitQuiver.inst G H) c b e)))
          rw [hraw]
          change quotientSymmEdgeLabel G H
                (@Quiver.Hom.toNeg (RawBassSerreOrbitVertex G H)
                  (rawBassSerreOrbitQuiver.inst G H) c b e) *
              quotientRawPathValue G H p =
            quotientPathValue G H
              (testFreePathHom p ≫
                Groupoid.inv ((Quiver.FreeGroupoid.of
                  (RawBassSerreOrbitVertex G H)).map e))
          rw [quotientPathValue_comp, quotientPathValue_inv,
            quotientPathValue_of, quotientSymmEdgeLabel, ih]

theorem testKuroshFreePartHom_kernel
    {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H)
    (hx : kuroshFreePartHom G H x = 1) :
    x = 1 := by
  obtain ⟨p, hp⟩ :=
    (CategoryTheory.Quotient.full_functor
      (@Quiver.FreeGroupoid.redStep
        (RawBassSerreOrbitVertex G H) (rawBassSerreOrbitQuiver G H))).map_surjective x
  have hvalue : quotientRawPathValue G H p = 1 := by
    have hq : quotientPathValue G H
        ((CategoryTheory.Quotient.functor
          (@Quiver.FreeGroupoid.redStep
            (RawBassSerreOrbitVertex G H) (rawBassSerreOrbitQuiver G H))).map p) = 1 := by
      rw [← kuroshFreePartHom_apply G H]
      rw [hp]
      exact hx
    rw [testQuotientRawPathValue_testFreePathHom G H p,
      testOrbitFreePathHom_eq_quotient_map G H p]
    exact hq
  have hpath : testFreePathHom p = 𝟙 _ :=
    testQuotientFreePathHom_eq_one_of_value_one G H (p := p) hvalue
  calc
    x = (CategoryTheory.Quotient.functor
      (@Quiver.FreeGroupoid.redStep
        (RawBassSerreOrbitVertex G H) (rawBassSerreOrbitQuiver G H))).map p := hp.symm
    _ = 𝟙 _ := by
      rw [← testOrbitFreePathHom_eq_quotient_map G H p]
      exact hpath

theorem testKuroshFreePartHom_injective
    {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G)) :
    Function.Injective (kuroshFreePartHom G H) := by
  intro x y hxy
  have hkernel : kuroshFreePartHom G H (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hxy' : x * y⁻¹ = 1 := testKuroshFreePartHom_kernel G H (x * y⁻¹) hkernel
  exact (mul_inv_eq_one.mp hxy')

end GraphCoveringTheory.Kurosh
