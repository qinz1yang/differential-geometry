import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringComponent

/-!
# The component refinement of one old piece

Lane P1W (P1 wiring), tier T2, assembly.

From `WiringData T i F P` (`nonempty_wiringData`) and `0 < δ ≤ δ₀`: the pieces are indexed by
`Fin P.pieceCount ⊕ T.OwnedSide i` (`WiringData.base`, `WiringData.map`: the planar pieces with
bases `(P.base j).shrink δ`, the collar pieces with base `(planarBase 2).shrink (10 δ / ℓ)`), the
seams by `Fin P.cutCount ⊕ T.OwnedSide i` (sides `wiringSide`, flows `WiringData.flow`), the
external sides by the owned sides. Each field of the `SyncedData` is one lemma below; the port
collars are the side collars of `(T.reparam id).shrink δ` (`WiringData.port_collar`), so
`exists_componentRefinement` gives the frozen tier T2, and
`exists_componentRefinement_of_orientable` its orientable-base form.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.Wiring

theorem sideCollar_shrink_reparam {W : CompactCarrier.{u}} (T : TorusPresentation W) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : T.Side) (p : Torus × EuclideanHalfSpace 1) :
    ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).sideCollar s p =
      T.sideCollar s (p.1, halfSpaceScale hδ p.2) := by
  rcases s with k | k | k <;> rfl

theorem sidePiece_shrink_reparam {W : CompactCarrier.{u}} (T : TorusPresentation W) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : T.Side) :
    ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).sidePiece s =
      T.sidePiece s := by
  rcases s with k | k | k <;> rfl

def portEquiv {W : CompactCarrier.{u}} (T : TorusPresentation W) (i : Fin T.components.count)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    T.OwnedSide i ≃
      ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by
    rw [sidePiece_shrink_reparam]
    exact Iff.rfl

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {i : Fin T.components.count}
  {F : CircleFibration T.cutCarrier (T.components.piece i)} {D : BaseMorseData F.base}
  {P : PlanarCore D} [Fact (0 < D.level 0)] (Wd : WiringData T i F P) {δ : ℝ} (hδ : 0 < δ)
  (hδ1 : δ ≤ 1) (hδ0 : δ ≤ Wd.δ₀)

namespace WiringData

omit [Fact (0 < D.level 0)] in
theorem eta_pos_of (D' : BaseMorseData F.base) [Fact (0 < D'.level 0)] (hδ' : 0 < δ) :
    0 < 10 * δ / D'.level 0 := by
  have : 0 < D'.level 0 := Fact.out
  positivity

include hδ0 in
theorem eta_le : 10 * δ / D.level 0 ≤ 1 := by
  have h : 0 < D.level 0 := Fact.out
  rw [div_le_one h]
  linarith [Wd.δ₀_le_level]

def base : ∀ x : Fin P.pieceCount ⊕ T.OwnedSide i, PlanarBase.{u} (Sum.elim P.kind (fun _ => 2) x)
  | .inl j => (P.base j).shrink hδ hδ1
  | .inr _ => (planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)

def map : ∀ x, (Wd.base hδ hδ1 hδ0 x).surface.Carrier × Circle → T.components.piece i
  | .inl j => Wd.Φ j
  | .inr s => collarPieceMap (D.level 0) (Wd.K s)

def flow : Fin P.cutCount ⊕ T.OwnedSide i → ℝ →
    (T.components.piece i ≃ₘ⟮T.cutCarrier.model, T.cutCarrier.model⟯ T.components.piece i)
  | .inl c => (PlanarCore.cutLift F P c).flow
  | .inr s => (PlanarCore.bottomLift F P (Wd.βj s) (Wd.βl s) (Wd.βh s)).flow

def side : Fin P.cutCount ⊕ T.OwnedSide i → Bool →
    Σ x : Fin P.pieceCount ⊕ T.OwnedSide i, Fin (Sum.elim P.kind (fun _ => 2) x) :=
  wiringSide P.kind P.cutSide fun s => ⟨Wd.βj s, Wd.βl s⟩

theorem cutRange (c : Fin P.cutCount) (b : Bool) :
    range (sideTorus (P.base (P.cutSide c b).1) (P.cutSide c b).2 (Wd.Φ (P.cutSide c b).1)) =
      F.projection ⁻¹' range (fun θ => P.cut c (θ, 0)) := by
  refine range_sideTorus_eq F _ (P.injective_ι _) (Wd.projΦ _) (Wd.rangeΦ _) _
    (σ := P.cutSigma c b) fun t => ?_
  rw [show halfZero = halfPoint 0 le_rfl from rfl, P.cutSigma_spec c b t 0 le_rfl one_pos]
  cases b <;> simp

theorem collarRange (s : T.OwnedSide i) :
    range (sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)) 1
      (collarPieceMap (D.level 0) (Wd.K s))) = F.projection ⁻¹' zeroSec P ⟨Wd.βj s, Wd.βl s⟩ := by
  rw [← Wd.top_range s]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [sideTorus_collarPiece]
    exact ⟨(t.1⁻¹, t.2), rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1⁻¹, p.2), ?_⟩
    rw [sideTorus_collarPiece]
    simp only [inv_inv]
    rfl

theorem bottomRange (s : T.OwnedSide i) :
    range (sideTorus (P.base (Wd.βj s)) (Wd.βl s) (Wd.Φ (Wd.βj s))) =
      F.projection ⁻¹' zeroSec P ⟨Wd.βj s, Wd.βl s⟩ :=
  (projection_preimage_zeroSec F P (Wd.βh s) (Wd.projΦ _) (Wd.rangeΦ _)).symm

omit [Fact (0 < D.level 0)] in
theorem kind_mem (x : Fin P.pieceCount ⊕ T.OwnedSide i) :
    Sum.elim P.kind (fun _ => 2) x ∈ ({1, 2, 3} : Finset ℕ) := by
  rcases x with j | s
  · exact P.kind_mem j
  · change (2 : ℕ) ∈ ({1, 2, 3} : Finset ℕ)
    decide

theorem smooth_map (x : Fin P.pieceCount ⊕ T.OwnedSide i) :
    ContMDiff ((SurfaceModel.model (Wd.base hδ hδ1 hδ0 x).surface.kind).prod (𝓡 1))
      T.cutCarrier.model ∞ (Wd.map hδ hδ1 hδ0 x) := by
  rcases x with j | s
  · exact Wd.smoothΦ j
  · exact contMDiff_collarPieceMap (D.level 0) (Wd.smoothK s)

theorem bijective_map (x : Fin P.pieceCount ⊕ T.OwnedSide i) (q) :
    Bijective (mfderiv ((SurfaceModel.model (Wd.base hδ hδ1 hδ0 x).surface.kind).prod (𝓡 1))
      T.cutCarrier.model (Wd.map hδ hδ1 hδ0 x) q) := by
  rcases x with j | s
  · exact Wd.bijΦ j q
  · exact bijective_mfderiv_collarPieceMap (D.level 0) (Wd.smoothK s) (Wd.bijK s) q

theorem injective_map (x : Fin P.pieceCount ⊕ T.OwnedSide i) :
    Injective (Wd.map hδ hδ1 hδ0 x) := by
  rcases x with j | s
  · exact Wd.injΦ j
  · exact injective_collarPieceMap (D.level 0) (Wd.injK s)

theorem covers_map : ⋃ x, range (Wd.map hδ hδ1 hδ0 x) = univ := by
  refine eq_univ_of_forall fun z => ?_
  rcases le_total (portHeight F D z) (D.level 0) with hz | hz
  · obtain ⟨s, hs⟩ := Wd.cover z hz
    obtain ⟨q, hq⟩ : z.val ∈ range (fun q => (Wd.K s q).val) := by
      rw [Wd.region s]
      exact hs
    have hzK : z ∈ range (collarPieceMap (D.level 0) (Wd.K s)) := by
      rw [range_collarPieceMap]
      exact ⟨q, Subtype.ext hq⟩
    exact mem_iUnion.mpr ⟨Sum.inr s, hzK⟩
  · have hzc : F.projection z ∈ ⋃ j, range (P.ι j) := by
      rw [P.iUnion_range_ι]
      exact hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzc
    have hzΦ : z ∈ range (Wd.Φ j) := by
      rw [Wd.rangeΦ j]
      exact hj
    exact mem_iUnion.mpr ⟨Sum.inl j, hzΦ⟩

theorem sides_bijective :
    Bijective (Sum.elim (uncurry Wd.side) fun e => (⟨Sum.inr e, (0 : Fin 2)⟩ :
      Σ x : Fin P.pieceCount ⊕ T.OwnedSide i, Fin (Sum.elim P.kind (fun _ => 2) x))) :=
  wiringSide_bijective P.kind P.cutSide P.cutSide_injective _ (fun s c b => Wd.βh s c b)
    (fun s s' h => Wd.β_inj s s' h) (fun w hw => Wd.β_surj w.1 w.2 hw)

theorem flow_add (c : Fin P.cutCount ⊕ T.OwnedSide i) (a b : ℝ) (x : T.components.piece i) :
    Wd.flow c (a + b) x = Wd.flow c a (Wd.flow c b x) := by
  rcases c with c | s
  · exact (PlanarCore.cutLift F P c).flow_add a b x
  · exact (PlanarCore.bottomLift F P _ _ _).flow_add a b x

theorem sync_left (c : Fin P.cutCount ⊕ T.OwnedSide i) (t v : Circle) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1) :
    Wd.map hδ hδ1 hδ0 (Wd.side c true).1 ((Wd.base hδ hδ1 hδ0 _).collar (Wd.side c true).2
      (t, halfPoint r hr), v) = Wd.flow c (-(δ * r)) (Wd.map hδ hδ1 hδ0 (Wd.side c true).1
        ((Wd.base hδ hδ1 hδ0 _).collar (Wd.side c true).2 (t, halfZero), v)) := by
  rcases c with c | s
  · change Wd.Φ (P.cutSide c false).1 (((P.base (P.cutSide c false).1).shrink hδ hδ1).collar
      (P.cutSide c false).2 (t, halfPoint r hr), v) =
      (PlanarCore.cutLift F P c).flow (-(δ * r)) (Wd.Φ (P.cutSide c false).1
        (((P.base (P.cutSide c false).1).shrink hδ hδ1).collar (P.cutSide c false).2
          (t, halfZero), v))
    rw [shrink_collar_halfPoint, shrink_collar_halfZero]
    have h := Wd.cutSync (P.cutSide c false).1 (P.cutSide c false).2 c false rfl t v (δ * r)
      (mul_nonneg hδ.le hr) (by nlinarith)
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h
  · exact collarPiece_sync_one (D.level 0) (Wd.K s)
      (fun a x => (PlanarCore.bottomLift F P (Wd.βj s) (Wd.βl s) (Wd.βh s)).flow a x) hδ hδ0
      (hδ0.trans Wd.δ₀_le_level) (Wd.topK s) (eta_pos_of D hδ) (Wd.eta_le hδ0) t v hr hr1

theorem sync_right (c : Fin P.cutCount ⊕ T.OwnedSide i) (t v : Circle) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1) :
    Wd.map hδ hδ1 hδ0 (Wd.side c false).1 ((Wd.base hδ hδ1 hδ0 _).collar (Wd.side c false).2
      (t, halfPoint r hr), v) = Wd.flow c (δ * r) (Wd.map hδ hδ1 hδ0 (Wd.side c false).1
        ((Wd.base hδ hδ1 hδ0 _).collar (Wd.side c false).2 (t, halfZero), v)) := by
  rcases c with c | s
  · change Wd.Φ (P.cutSide c true).1 (((P.base (P.cutSide c true).1).shrink hδ hδ1).collar
      (P.cutSide c true).2 (t, halfPoint r hr), v) =
      (PlanarCore.cutLift F P c).flow (δ * r) (Wd.Φ (P.cutSide c true).1
        (((P.base (P.cutSide c true).1).shrink hδ hδ1).collar (P.cutSide c true).2
          (t, halfZero), v))
    rw [shrink_collar_halfPoint, shrink_collar_halfZero]
    have h := Wd.cutSync (P.cutSide c true).1 (P.cutSide c true).2 c true rfl t v (δ * r)
      (mul_nonneg hδ.le hr) (by nlinarith)
    simp only [↓reduceIte] at h
    exact h
  · change Wd.Φ (Wd.βj s) (((P.base (Wd.βj s)).shrink hδ hδ1).collar (Wd.βl s)
      (t, halfPoint r hr), v) =
      (PlanarCore.bottomLift F P (Wd.βj s) (Wd.βl s) (Wd.βh s)).flow (δ * r)
        (Wd.Φ (Wd.βj s) (((P.base (Wd.βj s)).shrink hδ hδ1).collar (Wd.βl s) (t, halfZero), v))
    rw [shrink_collar_halfPoint, shrink_collar_halfZero]
    exact Wd.bottomSync (Wd.βj s) (Wd.βl s) (Wd.βh s) t v (δ * r) (mul_nonneg hδ.le hr)
      (by nlinarith)

theorem range_eq (c : Fin P.cutCount ⊕ T.OwnedSide i) :
    range (sideTorus (Wd.base hδ hδ1 hδ0 (Wd.side c true).1) (Wd.side c true).2
      (Wd.map hδ hδ1 hδ0 (Wd.side c true).1)) =
    range (sideTorus (Wd.base hδ hδ1 hδ0 (Wd.side c false).1) (Wd.side c false).2
      (Wd.map hδ hδ1 hδ0 (Wd.side c false).1)) := by
  rcases c with c | s
  · change range (sideTorus ((P.base (P.cutSide c false).1).shrink hδ hδ1)
      (P.cutSide c false).2 (Wd.Φ (P.cutSide c false).1)) =
      range (sideTorus ((P.base (P.cutSide c true).1).shrink hδ hδ1) (P.cutSide c true).2
        (Wd.Φ (P.cutSide c true).1))
    rw [sideTorus_shrink, sideTorus_shrink, Wd.cutRange c false, Wd.cutRange c true]
  · change range (sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ)
      (Wd.eta_le hδ0)) 1 (collarPieceMap (D.level 0) (Wd.K s))) =
      range (sideTorus ((P.base (Wd.βj s)).shrink hδ hδ1) (Wd.βl s) (Wd.Φ (Wd.βj s)))
    rw [Wd.collarRange hδ hδ0 s, sideTorus_shrink, Wd.bottomRange s]

theorem injOn_sweep (c : Fin P.cutCount ⊕ T.OwnedSide i) :
    InjOn (fun y : Torus × ℝ => Wd.flow c (δ * y.2)
      (sideTorus (Wd.base hδ hδ1 hδ0 (Wd.side c true).1) (Wd.side c true).2
        (Wd.map hδ hδ1 hδ0 (Wd.side c true).1) y.1)) signedCollarSource := by
  rcases c with c | s
  · change InjOn (fun y : Torus × ℝ => (PlanarCore.cutLift F P c).flow (δ * y.2)
      (sideTorus ((P.base (P.cutSide c false).1).shrink hδ hδ1) (P.cutSide c false).2
        (Wd.Φ (P.cutSide c false).1) y.1)) signedCollarSource
    rw [sideTorus_shrink]
    refine injOn_liftSweep F (P.cut_source c) (PlanarCore.cutLift F P c)
      (injective_sideTorus _ _ (Wd.injΦ _)) (fun t => ?_) hδ
      (by rw [PlanarCore.cutLift_width]; exact hδ0.trans Wd.δ₀_le_width)
    have h : sideTorus (P.base (P.cutSide c false).1) (P.cutSide c false).2
        (Wd.Φ (P.cutSide c false).1) t ∈ range (sideTorus (P.base (P.cutSide c false).1)
          (P.cutSide c false).2 (Wd.Φ (P.cutSide c false).1)) := ⟨t, rfl⟩
    rw [Wd.cutRange c false] at h
    obtain ⟨θ, hθ⟩ := h
    exact ⟨θ, hθ.symm⟩
  · change InjOn (fun y : Torus × ℝ =>
      (PlanarCore.bottomLift F P (Wd.βj s) (Wd.βl s) (Wd.βh s)).flow (δ * y.2)
        (sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)) 1
          (collarPieceMap (D.level 0) (Wd.K s)) y.1)) signedCollarSource
    refine injOn_liftSweep F (P.bottomBicollar_spec (Wd.βj s) (Wd.βl s) (Wd.βh s)).1
      (PlanarCore.bottomLift F P (Wd.βj s) (Wd.βl s) (Wd.βh s))
      (y := sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)) 1
        (collarPieceMap (D.level 0) (Wd.K s)))
      (injective_sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ)
        (Wd.eta_le hδ0)) 1 (injective_collarPieceMap (D.level 0) (Wd.injK s)))
      (fun t => ?_) hδ (by rw [PlanarCore.bottomLift_width]; exact hδ0.trans Wd.δ₀_le_width)
    have h : sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)) 1
        (collarPieceMap (D.level 0) (Wd.K s)) t ∈ range (sideTorus
          ((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)) 1
            (collarPieceMap (D.level 0) (Wd.K s))) := ⟨t, rfl⟩
    rw [Wd.collarRange hδ hδ0 s, zeroSec_eq P (Wd.βh s)] at h
    obtain ⟨θ, hθ⟩ := h
    exact ⟨θ, hθ.symm⟩

theorem mem_collarTop {s : T.OwnedSide i} {z : T.components.piece i}
    (hz : D.level 0 ≤ portHeight F D z) (hzK : z ∈ range (collarPieceMap (D.level 0) (Wd.K s)))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ t, z = sideTorus ((planarBase.{u} 2 (Or.inl rfl)).shrink hη hη1) 1
      (collarPieceMap (D.level 0) (Wd.K s)) t := by
  obtain ⟨q', rfl⟩ := hzK
  change D.level 0 ≤ portHeight F D (Wd.K s (annulusProduct (D.level 0) q')) at hz
  change ∃ t, Wd.K s (annulusProduct (D.level 0) q') = _
  generalize annulusProduct (D.level 0) q' = w at hz ⊢
  have hmem : (Wd.K s w).val ∈ connectedComponentIn (lowSet F D)
      (T.sideCollar s.val (1, halfZero)) := by
    rw [← Wd.region s]
    exact ⟨w, rfl⟩
  have hle := val_mem_lowSet.mp (connectedComponentIn_subset _ _ hmem)
  have htop := Wd.top_eq s w (le_antisymm hle hz)
  obtain ⟨⟨a, b⟩, c⟩ := w
  change c = topPoint D at htop
  subst htop
  refine ⟨(a⁻¹, b), ?_⟩
  rw [sideTorus_collarPiece]
  simp only [inv_inv]
  rfl

theorem level_le_Φ (j : Fin P.pieceCount) (q) : D.level 0 ≤ portHeight F D (Wd.Φ j q) := by
  change D.level 0 ≤ D.f (F.projection (Wd.Φ j q))
  rw [Wd.projΦ]
  exact P.level_le_ι j q.1

theorem overlap (x x' : Fin P.pieceCount ⊕ T.OwnedSide i)
    (q : (Wd.base hδ hδ1 hδ0 x).surface.Carrier × Circle)
    (q' : (Wd.base hδ hδ1 hδ0 x').surface.Carrier × Circle)
    (h : Wd.map hδ hδ1 hδ0 x q = Wd.map hδ hδ1 hδ0 x' q') :
    (⟨x, q⟩ : Σ x, (Wd.base hδ hδ1 hδ0 x).surface.Carrier × Circle) = ⟨x', q'⟩ ∨
      ∃ c t, Wd.map hδ hδ1 hδ0 x q = sideTorus (Wd.base hδ hδ1 hδ0 (Wd.side c true).1)
        (Wd.side c true).2 (Wd.map hδ hδ1 hδ0 (Wd.side c true).1) t := by
  rcases x with j | s <;> rcases x' with j' | s'
  · change Wd.Φ j q = Wd.Φ j' q' at h
    by_cases hjj : j = j'
    · subst hjj
      left
      rw [Wd.injΦ j h]
    · right
      have hπ : P.ι j q.1 = P.ι j' q'.1 :=
        (Wd.projΦ j q).symm.trans ((congrArg F.projection h).trans (Wd.projΦ j' q'))
      obtain ⟨c, τ, hc⟩ := P.overlap j j' q.1 q'.1 hjj (Subtype.ext hπ)
      have hm : Wd.Φ j q ∈ range (sideTorus (P.base (P.cutSide c false).1)
          (P.cutSide c false).2 (Wd.Φ (P.cutSide c false).1)) := by
        rw [Wd.cutRange c false]
        exact ⟨τ, hc.symm.trans (Wd.projΦ j q).symm⟩
      obtain ⟨t', ht'⟩ := hm
      refine ⟨Sum.inl c, t', ?_⟩
      change Wd.Φ j q = sideTorus ((P.base (P.cutSide c false).1).shrink hδ hδ1)
        (P.cutSide c false).2 (Wd.Φ (P.cutSide c false).1) t'
      rw [sideTorus_shrink]
      exact ht'.symm
  · right
    change Wd.Φ j q = collarPieceMap (D.level 0) (Wd.K s') q' at h
    obtain ⟨t, ht⟩ := Wd.mem_collarTop (s := s') (h ▸ Wd.level_le_Φ j q) ⟨q', h.symm⟩
      (eta_pos_of D hδ) (Wd.eta_le hδ0)
    exact ⟨Sum.inr s', t, ht⟩
  · right
    change collarPieceMap (D.level 0) (Wd.K s) q = Wd.Φ j' q' at h
    obtain ⟨t, ht⟩ := Wd.mem_collarTop (s := s) (h.symm ▸ Wd.level_le_Φ j' q') ⟨q, rfl⟩
      (eta_pos_of D hδ) (Wd.eta_le hδ0)
    exact ⟨Sum.inr s, t, ht⟩
  · change collarPieceMap (D.level 0) (Wd.K s) q = collarPieceMap (D.level 0) (Wd.K s') q' at h
    by_cases hss : s = s'
    · subst hss
      left
      rw [injective_collarPieceMap (D.level 0) (Wd.injK s) h]
    · exfalso
      have hm : ∀ (s'' : T.OwnedSide i) (q'' : (planarBase.{u} 2 (Or.inl rfl)).surface.Carrier ×
          Circle), (collarPieceMap (D.level 0) (Wd.K s'') q'').val ∈
            connectedComponentIn (lowSet F D) (T.sideCollar s''.val (1, halfZero)) :=
        fun s'' q'' => by
          rw [← Wd.region s'']
          exact ⟨_, rfl⟩
      exact hss (Wd.disjoint s s' _ (hm s q) (h ▸ hm s' q'))

theorem port_collar (e : T.OwnedSide i) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    (collarPieceMap (D.level 0) (Wd.K e) (((planarBase.{u} 2 (Or.inl rfl)).shrink
      (eta_pos_of D hδ) (Wd.eta_le hδ0)).collar 0 (p.1.1, p.2), p.1.2)).val =
      ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).sideCollar
        e.val p := by
  obtain ⟨⟨t, v⟩, h⟩ := p
  have hr : 0 ≤ h.val 0 := h.2
  have hh : halfPoint (h.val 0) hr = h := halfPoint_eq_self h hr rfl
  have hp' : h.val 0 < 1 := hp
  rw [sideCollar_shrink_reparam]
  change (collarPieceMap (D.level 0) (Wd.K e) (((planarBase.{u} 2 (Or.inl rfl)).shrink
    (eta_pos_of D hδ) (Wd.eta_le hδ0)).collar 0 (t, h), v)).val =
      T.sideCollar e.val ((t, v), halfSpaceScale hδ h)
  rw [← hh, collarPiece_port_zero (D.level 0) (Wd.K e) hδ (hδ0.trans Wd.δ₀_le_level)
    (eta_pos_of D hδ) (Wd.eta_le hδ0) t v hr hp', halfSpaceScale_halfPoint]
  exact Wd.lowK e (t, v) _ (by
    change δ * h.val 0 < Wd.δ₀
    nlinarith [Wd.δ₀_pos])

include hδ1 in
theorem external_local (e : T.OwnedSide i) (t : Torus) :
    IsLocalDiffeomorphAt ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod
      (𝓡 1)) T.cutCarrier.model ∞
      (collarPieceMap (D.level 0) (Wd.K e))
      (((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)).collar 0
        (t.1, halfZero), t.2) := by
  let c : PartialDiffeomorph halfCollarModel T.cutCarrier.model (Torus × EuclideanHalfSpace 1)
      (T.components.piece i) ∞ :=
    ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).pieceCollar
      i (portEquiv T i hδ hδ1 e)
  have hcs : c.source = halfCollarSource := TorusPresentation.pieceCollar_source _ _ _
  have hca : ∀ q ∈ halfCollarSource, (c q).val =
      ((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).sideCollar
        e.val q := fun q hq => TorusPresentation.pieceCollar_apply _ _ _ hq
  refine isLocalDiffeomorphAt_of_comp_eq (collarPieceMap (D.level 0) (Wd.K e))
    (trivCollar (S := (planarBase.{u} 2 (Or.inl rfl)).surface)
      (((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)).collar 0)
      (Diffeomorph.refl ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod
        (𝓡 1)) ((planarBase.{u} 2 (Or.inl rfl)).surface.Carrier × Circle) ∞))
    c (p := (t, halfZero)) ?_ ?_ ?_
  · have hA := trivCollar_source (S := (planarBase.{u} 2 (Or.inl rfl)).surface)
      (((planarBase.{u} 2 (Or.inl rfl)).shrink (eta_pos_of D hδ) (Wd.eta_le hδ0)).source_eq 0)
      (Diffeomorph.refl ((SurfaceModel.model (planarBase.{u} 2 (Or.inl rfl)).surface.kind).prod
        (𝓡 1)) ((planarBase.{u} 2 (Or.inl rfl)).surface.Carrier × Circle) ∞)
    rw [hA]
    exact zero_mem_halfCollarSource t
  · rw [hcs]
    exact zero_mem_halfCollarSource t
  · intro q hq
    have hq2 : q ∈ halfCollarSource := by
      have h := hq.2
      rwa [hcs] at h
    apply Subtype.ext
    rw [hca q hq2]
    exact Wd.port_collar hδ hδ1 hδ0 e q hq2

def syncedData :
    SyncedData (((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1).Component
      i) where
  ι := Fin P.pieceCount ⊕ T.OwnedSide i
  nonempty := ⟨Sum.inl Wd.nonempty.some⟩
  γ := Fin P.cutCount ⊕ T.OwnedSide i
  ε := T.OwnedSide i
  kind := Sum.elim P.kind fun _ => 2
  kind_mem := WiringData.kind_mem
  base := Wd.base hδ hδ1 hδ0
  map := Wd.map hδ hδ1 hδ0
  smooth := Wd.smooth_map hδ hδ1 hδ0
  mfderiv_bijective := Wd.bijective_map hδ hδ1 hδ0
  injective := Wd.injective_map hδ hδ1 hδ0
  covers := Wd.covers_map hδ hδ1 hδ0
  side := Wd.side
  ext := fun e => ⟨Sum.inr e, (0 : Fin 2)⟩
  sides_bijective := Wd.sides_bijective
  flow := Wd.flow
  flow_add := Wd.flow_add
  rate := δ
  sync_left := Wd.sync_left hδ hδ1 hδ0
  sync_right := Wd.sync_right hδ hδ1 hδ0
  range_eq := Wd.range_eq hδ hδ1 hδ0
  injOn := Wd.injOn_sweep hδ hδ1 hδ0
  external_local := fun e t => Wd.external_local hδ hδ1 hδ0 e t
  overlap := Wd.overlap hδ hδ1 hδ0

end WiringData

theorem exists_componentRefinement (T : TorusPresentation W) (i : Fin T.components.count)
    (F : CircleFibration T.cutCarrier (T.components.piece i)) {D : BaseMorseData F.base}
    (P : PlanarCore D) :
    ∃ δ₀ > 0, ∀ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1), δ ≤ δ₀ →
      Nonempty (((T.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink hδ hδ1)
        |>.ComponentRefinement i) := by
  have : Fact (0 < D.level 0) := ⟨D.level_zero_pos⟩
  obtain ⟨Wd⟩ := nonempty_wiringData T i F P
  exact ⟨Wd.δ₀, Wd.δ₀_pos, fun δ hδ hδ1 hδ0 =>
    ⟨(Wd.syncedData hδ hδ1 hδ0).toComponentRefinement (portEquiv T i hδ hδ1)
      fun e p hp => Wd.port_collar hδ hδ1 hδ0 e p hp⟩⟩

theorem exists_componentRefinement_of_orientable (G : RawGraphPresentation W)
    (i : Fin G.components.count)
    (o : ManifoldOrientation (SurfaceModel.model (G.fibration i).base.kind)
      (G.fibration i).base.Carrier 2) :
    ∃ δ₀ > 0, ∀ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1), δ ≤ δ₀ →
      Nonempty (((G.toTorusPresentation.reparam fun _ => Diffeomorph.refl torusModel Torus ∞).shrink
        hδ hδ1).ComponentRefinement i) := by
  obtain ⟨D, ⟨P⟩⟩ := CoreDecomposition.exists_planarCore_of_orientable o
  exact exists_componentRefinement G.toTorusPresentation i (G.fibration i) P

end GC.Seifert.Wiring
