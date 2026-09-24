import DifferentialGeometry.Topology.PiecewiseLinear.Section34SmallSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusFrontierSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLDerivedNeighborhoodExhaustion.exists_marked_nested_piercing_annuli
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D F₀ F₁ D₀ D₁ : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O)
    (hF₀ : IsPolyhedralSphere (n := 3) 2 F₀) (hF₁ : IsPolyhedralSphere (n := 3) 2 F₁)
    (hF₀U : F₀ ⊆ U) (hF₁U : F₁ ⊆ U) (hCF₀ : C ⊆ F₀) (hCF₁ : C ⊆ F₁)
    (hD₀ : IsClosed D₀) (hD₁ : IsClosed D₁)
    (hfront₀ : F₀ ∩ frontier D₁ = C) (hfront₁ : F₁ ∩ frontier D₀ = C)
    (hin₀ : C ⊆ closure (F₀ ∩ interior D₁)) (hout₀ : C ⊆ closure (F₀ \ D₁))
    (hin₁ : C ⊆ closure (F₁ ∩ interior D₀)) (hout₁ : C ⊆ closure (F₁ \ D₀)) :
    ∃ S T A A₀ A₁ B B₀ B₁ L L₀ L₁ : Set X,
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) T C U ∧
      T ⊆ interior S ∧ IsTopologicalSolidTorus S ∧ IsTopologicalSolidTorus T ∧ S ⊆ O ∧
      (A = F₀ ∩ T ∧ IsAnnulusOn A A₀ A₁ ∧ C ⊆ A \ (A₀ ∪ A₁)) ∧
      (B ⊆ F₁ ∧ IsAnnulusOn B B₀ B₁) ∧
      T ∩ F₁ ⊆ B \ (B₀ ∪ B₁) ∧
      (B ⊆ interior S ∧ B₀ ∪ B₁ ⊆ S \ T) ∧
      (IsAnnulusOn L L₀ L₁ ∧ L ⊆ B ∩ interior T) ∧ (C ⊆ L \ (L₀ ∪ L₁)) ∧
      (A₀ ⊆ interior D₁ ∧ A₁ ∩ D₁ = ∅) ∧ IsConnected (B ∩ D₀) ∧ IsConnected (B \ D₀) := by
  have hCne : C.Nonempty := by
    obtain ⟨P, hP⟩ := hC
    obtain ⟨x, hx⟩ := hP.nonempty
    exact ⟨P.piece.map x, P.piece.bijOn.mapsTo hx⟩
  obtain ⟨S, hS, htS, hSO⟩ :=
    h.exists_solidTorus_regularNeighborhood_subset_open hU hC hD hDU hCD hO hCO
  have hCS : C ⊆ interior S := subset_interior_iff_mem_nhdsSet.mpr hS.mem_nhdsSet
  obtain ⟨V, hV, -, hVS, hVB⟩ := h.exists_solidTorus_regularNeighborhood_with_circle_levels
    hU hC hD hDU hCD isOpen_interior hCS (fun _ : Unit => F₁)
    (fun _ => hF₁) (fun _ => hF₁U) (fun _ => hCF₁)
  have hCV : C ⊆ interior V := subset_interior_iff_mem_nhdsSet.mpr hV.mem_nhdsSet
  obtain ⟨φB, tB, htB, hlevelB⟩ := hVB ()
  obtain ⟨B₀, B₁, hB, hCB, -, -, hconn⟩ :=
    exists_isAnnulusOn_of_crossing_trace hD₀ hCne hCV hfront₁ hin₁ hout₁ φB htB hlevelB
  have hBV : B₀ ∪ B₁ ⊆ V ∩ F₁ := union_subset hB.first_subset hB.second_subset
  have hBo : IsOpen (B₀ ∪ B₁)ᶜ :=
    (hB.isCompact_first.isClosed.union hB.isCompact_second.isClosed).isOpen_compl
  have hCO' : C ⊆ interior V ∩ (B₀ ∪ B₁)ᶜ := fun x hx => ⟨hCV hx, (hCB hx).2⟩
  obtain ⟨T, hT, htT, hTV, hTA⟩ := h.exists_solidTorus_regularNeighborhood_with_circle_levels
    hU hC hD hDU hCD (isOpen_interior.inter hBo) hCO' (fun _ : Unit => F₀)
    (fun _ => hF₀) (fun _ => hF₀U) (fun _ => hCF₀)
  have hCT : C ⊆ interior T := subset_interior_iff_mem_nhdsSet.mpr hT.mem_nhdsSet
  obtain ⟨φA, tA, htA, hlevelA⟩ := hTA ()
  obtain ⟨A₀, A₁, hA, hCA, hA₀, hA₁, -⟩ :=
    exists_isAnnulusOn_of_crossing_trace hD₁ hCne hCT hfront₀ hin₀ hout₀ φA htA hlevelA
  obtain ⟨W, -, -, hWT, hWL⟩ := h.exists_solidTorus_regularNeighborhood_with_annular_cores
    hU hC hD hDU hCD isOpen_interior hCT (fun _ : Unit => F₁)
    (fun _ => hF₁) (fun _ => hF₁U) (fun _ => hCF₁)
  obtain ⟨L₀, L₁, hL, hCL⟩ := hWL ()
  have hTS : T ⊆ interior S := fun x hx => (hVS (interior_subset (hTV hx).1.1)).1
  refine ⟨S, T, T ∩ F₀, A₀, A₁, V ∩ F₁, B₀, B₁, W ∩ F₁, L₀, L₁,
    hS, hT, hTS, htS, htT, hSO.trans inter_subset_left,
    ⟨inter_comm _ _, hA, hCA⟩, ⟨inter_subset_right, hB⟩, ?_, ?_, ?_, hCL,
    ⟨hA₀, hA₁⟩, hconn⟩
  · intro x hx
    exact ⟨⟨interior_subset (hTV hx.1).1.1, hx.2⟩, (hTV hx.1).1.2⟩
  · refine ⟨fun x hx => (hVS hx.1).1, fun x hx => ?_⟩
    exact ⟨interior_subset (hVS (hBV hx).1).1, fun hxT => (hTV hxT).1.2 hx⟩
  · refine ⟨hL, fun x hx => ?_⟩
    have hxT : x ∈ interior T := (hWT hx.1).1
    exact ⟨⟨interior_subset (hTV (interior_subset hxT)).1.1, hx.2⟩, hxT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
