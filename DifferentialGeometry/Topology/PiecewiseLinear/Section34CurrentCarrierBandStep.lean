import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentCarrierBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentSeamMarkedBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentBandForbiddenBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamFillingTraceMotion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

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

theorem exists_section34_current_carrier_band_step
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (I : Set (Fin (cnt e)))
    (hlt : 1 < Nat.card I) (Ψ : M₂ ≃ₜ M₂) {K : Set M₂}
    (hK : IsCompact K) (hKS : K ⊆ interior (Sp e)) (hfix : EqOn Ψ id Kᶜ)
    (hΨ : IsPLOn 3 3 Ψ (interior (G (ends e).1 '' Cc (ends e).1)))
    (hrim : Disjoint K (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hout : Disjoint K
      (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)))
    (hkeep : ∀ i : I, Disjoint K (Pg e i.1.val))
    (hcarry : ∀ i : I, CarriesFundamentalGroupOnto (Pg e i.1.val) (Sp e))
    (htrace : G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) =
      ⋃ i : I, Pg e i.1.val) :
    ∃ (J : Set I) (Φ : M₂ ≃ₜ M₂) (K₁ : Set M₂), Nat.card J < Nat.card I ∧
      IsCompact K₁ ∧ K₁ ⊆ interior (Sp e) ∧ EqOn Φ id K₁ᶜ ∧
      IsPLOn 3 3 Φ (interior (G (ends e).1 '' Cc (ends e).1)) ∧
      Disjoint K₁ (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)) ∧
      Disjoint K₁ (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) ∧
      Disjoint K₁ (closure (G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e)) ∧
      (∀ j : J, Disjoint K₁ (Pg e j.1.1.val)) ∧
      (∀ j : J, ∀ x ∈ Pg e j.1.1.val, Φ =ᶠ[𝓝 x] id) ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ Φ '' (Ψ '' (G (ends e).2 '' CpBd (ends e).2)) =
        ⋃ j : J, Pg e j.1.1.val := by
  obtain ⟨i, j, hij, D, F, hFA, hDB, hfill⟩ :=
    exists_section34_current_carrier_band_filling hprep hpack e I hlt Ψ hK hKS hfix hΨ
      hrim hkeep hcarry htrace
  obtain ⟨-, -, hCpCc, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hGp, -, -, -, -, -, -, hPg, hdis, -⟩ := id hpack
  have hSpCc : Sp e ⊆ G (ends e).1 '' Cc (ends e).1 := by
    rw [(htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hcellB := ((hCp (ends e).2).image (hGp (ends e).2)).image_of_supported_isPLOn
    Ψ hΨ isOpen_interior hK.isClosed (hKS.trans (interior_mono hSpCc)) hfix
  have hseams : Disjoint K (Pg e i.1.val ∪ Pg e j.1.val) :=
    disjoint_union_right.mpr ⟨hkeep i, hkeep j⟩
  have hnear : ∀ x ∈ Pg e i.1.val ∪ Pg e j.1.val, Ψ =ᶠ[𝓝 x] id := by
    intro x hx
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds
      (disjoint_right.mp hseams hx)] with y hy
    exact hfix hy
  have hij' : i.1.val ≠ j.1.val := fun heq => hij (Subtype.ext (Fin.ext heq))
  have hmarked := section34_current_seam_marked_band_filling hprep hpack e
    i.1.isLt j.1.isLt hij' Ψ hnear hcellB hfill
  obtain ⟨hZ, hZsheet, hZfaces⟩ := section34_current_band_forbidden_boundary hprep hpack e
    i.1.isLt j.1.isLt Ψ (fun _ hx => hfix (disjoint_right.mp hseams hx))
    hcellB hfill hFA hDB
  have hBrim : Ψ '' (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) =
      G (ends e).2 '' (Bb₀ e ∪ Bb₁ e) :=
    (image_congr fun _ hx => hfix (disjoint_right.mp hrim hx)).trans (image_id' _)
  have houtside : Ψ '' (G (ends e).2 '' CpBd (ends e).2) \
      Ψ '' (G (ends e).2 '' Bb e) =
      G (ends e).2 '' CpBd (ends e).2 \ G (ends e).2 '' Bb e := by
    rw [← image_sdiff Ψ.injective]
    exact (image_congr fun _ hx => hfix
      (disjoint_right.mp hout (subset_closure hx))).trans (image_id' _)
  rw [hBrim, houtside] at hZ hZsheet hZfaces
  have hAs : G (ends e).1 '' CpBd (ends e).1 ⊆ G (ends e).1 '' Cc (ends e).1 :=
    image_mono ((hCp _).boundary_subset.trans (hCpCc _).2.1)
  have hpair : Pairwise fun k l : I => Disjoint (Pg e k.1.val) (Pg e l.1.val) :=
    fun k l hkl => hdis e k.1.val k.1.isLt l.1.val l.1.isLt
      (fun heq => hkl (Subtype.ext (Fin.ext heq)))
  obtain ⟨J, Φ, K₁, hlt', hK₁, hK₁S, hfix₁, hΦ, -, hkeep₁, hgerms, htrace₁, havoid, -⟩ :=
    hmarked.exists_second_trace_motion_avoiding hAs
      (fun k : I => (hPg e k.1.val k.1.isLt).1) hpair htrace hZ hZsheet hZfaces
  obtain ⟨havoidRims, havoidOut⟩ := disjoint_union_right.mp havoid
  obtain ⟨havoidA, havoidB⟩ := disjoint_union_right.mp havoidRims
  exact ⟨J, Φ, K₁, hlt', hK₁, hK₁S, hfix₁, hΦ, havoidA, havoidB, havoidOut,
    hkeep₁, hgerms, htrace₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
