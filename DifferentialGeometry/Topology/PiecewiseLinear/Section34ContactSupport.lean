import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentTrapping
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear


theorem IsAnnulusOn.ends_isCompact {M : Type*} [TopologicalSpace M] {A A₀ A₁ : Set M}
    (hA : IsAnnulusOn A A₀ A₁) : IsCompact A₀ ∧ IsCompact A₁ := by
  obtain ⟨φ, rfl, rfl⟩ := hA
  have hc (t : ℝ) : IsCompact
      {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 | (p.2 : ℝ) = t} :=
    (isClosed_eq (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact
  exact ⟨((hc 0).image φ.continuous).image continuous_subtype_val,
    ((hc 1).image φ.continuous).image continuous_subtype_val⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}


theorem exists_section34_contact_support
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') :
    ∃ O : Set M₂, IsOpen O ∧ IsCompact (closure O) ∧
      frontier (Tp e₀) ∩ G (ends e₀).2 '' Bb e₀ ⊆ O ∧
      closure O ⊆ interior (Sp e₀) ∩ interior (Q (ends e₀).1) ∩
        interior (Q (ends e₀).2) ∧
      Disjoint (closure O) (G (ends e₀).1 '' CpBd (ends e₀).1) ∧
      (∀ d, d ≠ e₀ → ((ends e₀).2 = (ends d).1 ∨ (ends e₀).2 = (ends d).2) →
        Disjoint (closure O) (G (ends e₀).2 '' Sn d)) ∧
      Disjoint (closure O) (G (ends e₀).2 '' (Bb₀ e₀ ∪ Bb₁ e₀)) := by
  have hSpcomp := section34_outer_tube_isCompact hprep hpack e₀
  have hTpcomp := section34_inner_tube_isCompact hprep hpack e₀
  obtain ⟨-, -, -, -, hCp, -, -, -, hends, -, -, htor, hSnCc, hSndis, -, hBb, -, hBbSn, -⟩ :=
    hprep
  obtain ⟨hG, hQ, hcross, -, -, -, htrace, -, hBSp, -, hGp, -⟩ := hpack
  let b := (ends e₀).2
  let Z := frontier (Tp e₀) ∩ G b '' Bb e₀
  have hSncomp (d : Section34EdgeIndex 𝒦 𝒦') : IsCompact (Sn d) := by
    obtain ⟨k⟩ := (htor d).2.1
    exact isCompact_iff_compactSpace.mpr k.symm.compactSpace
  have hBbCc : Bb e₀ ⊆ Cc b :=
    ((hBbSn e₀).1.trans interior_subset).trans (hSnCc e₀ b (Or.inr rfl))
  have hZ : IsCompact Z :=
    ((hBb e₀).2.isCompact.image_of_continuousOn ((hG b).continuousOn.mono hBbCc)).inter_left
      isClosed_frontier
  have hfirst : IsClosed (G (ends e₀).1 '' CpBd (ends e₀).1) := by
    rw [((hCp _).image_boundary_interior (hGp _)).1]
    exact isClosed_frontier
  have hZfirst : Disjoint Z (G (ends e₀).1 '' CpBd (ends e₀).1) := by
    apply disjoint_left.mpr
    intro x hx hxA
    have hxB : x ∈ G b '' CpBd b := image_mono (hBb e₀).1 hx.2
    exact hx.1.2 ((htrace e₀ ⟨hxA, hxB⟩).2)
  have hforeign (d : Section34EdgeIndex 𝒦 𝒦') (hd : d ≠ e₀)
      (hdb : b = (ends d).1 ∨ b = (ends d).2) : Disjoint (G b '' Bb e₀) (G b '' Sn d) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' := (hG b).injOn (hSnCc d b hdb hy) (hBbCc hx) hyx
    subst y
    exact disjoint_left.mp (hSndis e₀ d hd.symm) (interior_subset ((hBbSn e₀).1 hx)) hy
  let J := {d : Section34EdgeIndex 𝒦 𝒦' // b = (ends d).1 ∨ b = (ends d).2}
  let _ : Finite J := section34_incident_edges_finite (fun d => (hends d).2.1) b
  let I := {d : Section34EdgeIndex 𝒦 𝒦' //
    d ≠ e₀ ∧ (b = (ends d).1 ∨ b = (ends d).2)}
  let _ : Finite I := Finite.of_injective (fun d : I => (⟨d.1, d.2.2⟩ : J))
    (fun _ _ h => Subtype.ext (congrArg (fun d : J => d.1) h))
  let F := ⋃ d : I, G b '' Sn d.1
  have hF : IsCompact F := isCompact_iUnion fun d : I =>
    (hSncomp d.1).image_of_continuousOn ((hG b).continuousOn.mono (hSnCc d.1 b d.2.2))
  have hZF : Disjoint Z F := by
    apply disjoint_left.mpr
    intro x hx hxF
    obtain ⟨d, hd⟩ := mem_iUnion.mp hxF
    exact disjoint_left.mp (hforeign d.1 d.2.1 d.2.2) hx.2 hd
  let R := G b '' (Bb₀ e₀ ∪ Bb₁ e₀)
  have hR : IsCompact R :=
    (((hBb e₀).2.ends_isCompact).1.union ((hBb e₀).2.ends_isCompact).2).image_of_continuousOn
      ((hG b).continuousOn.mono ((union_subset (hBb e₀).2.first_subset
        (hBb e₀).2.second_subset).trans hBbCc))
  have hZR : Disjoint Z R := disjoint_left.mpr fun x hx hxR =>
    disjoint_left.mp (hBSp e₀).2 hxR (hTpcomp.isClosed.frontier_subset hx.1)
  have hGBopen : IsOpen (G b '' interior (Sn e₀)) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      ((hG b).continuousOn.mono (interior_subset.trans (hSnCc e₀ b (Or.inr rfl))))
      ((hG b).injOn.mono (interior_subset.trans (hSnCc e₀ b (Or.inr rfl))))
  have hQa : G b '' Bb e₀ ⊆ interior (Q (ends e₀).1) :=
    (image_mono (hBbSn e₀).1).trans
      (interior_maximal ((image_mono interior_subset).trans (hcross e₀).1) hGBopen)
  have hQb : G b '' Bb e₀ ⊆ interior (Q b) :=
    (image_mono (hBbSn e₀).1).trans (interior_maximal
      ((image_mono (interior_subset.trans (hSnCc e₀ b (Or.inr rfl)))).trans (hQ b)) hGBopen)
  let V := (interior (Sp e₀) ∩ interior (Q (ends e₀).1) ∩ interior (Q b)) \
    (G (ends e₀).1 '' CpBd (ends e₀).1 ∪ (R ∪ F))
  have hVbase : IsOpen (interior (Sp e₀) ∩ interior (Q (ends e₀).1) ∩ interior (Q b)) :=
    (isOpen_interior.inter isOpen_interior).inter isOpen_interior
  have hV : IsOpen V := hVbase.sdiff (hfirst.union (hR.isClosed.union hF.isClosed))
  have hZV : Z ⊆ V := by
    intro x hx
    refine ⟨⟨⟨(hBSp e₀).1 hx.2, hQa hx.2⟩, hQb hx.2⟩, ?_⟩
    rintro (hA | hR | hF)
    · exact disjoint_left.mp hZfirst hx hA
    · exact disjoint_left.mp hZR hx hR
    · exact disjoint_left.mp hZF hx hF
  obtain ⟨O, hO, hZO, hOV⟩ := hZ.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hZV)
  have hOS : closure O ⊆ Sp e₀ := fun x hx => interior_subset (hOV hx).1.1.1
  refine ⟨O, hO, hSpcomp.of_isClosed_subset
    isClosed_closure hOS, hZO, fun x hx => (hOV hx).1, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun x hx hxA => (hOV hx).2 (Or.inl hxA)
  · intro d hd hdb
    exact disjoint_left.mpr fun x hx hxd => (hOV hx).2
      (Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨d, hd, hdb⟩, hxd⟩)))
  · exact disjoint_left.mpr fun x hx hxR => (hOV hx).2 (Or.inr (Or.inl hxR))

end DifferentialGeometry.Topology.PiecewiseLinear
