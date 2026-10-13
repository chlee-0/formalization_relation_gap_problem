import D2RelationGap.ArbMoves
import D2RelationGap.FoxFilling

/-!
Fox filling comparison on the arbitrary-rank tagged target: collar incidence,
block propagation, block-subcomplex fillings and the Fox reduction. Ports the
Collar/Filling/Assembly sections of `FoxFilling`; its generic survivor and filter
lemmas are reused. OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
-/
noncomputable section
namespace D2RelationGap.ArbFilling
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open FoxFilling (Spans survivor filter_apply_zero filter_apply_eq)

section Collar
open ArbCells ArbMoves
variable {m k : ℕ} (w : Fin k → ArbRose.AWord m)

/-- The actual sorted triangle carrying a displayed cell. -/
def cellTri (c : CellIndex w) : Triangle (target w) := (triangleEquiv w).symm c

theorem cellTri_face (c : CellIndex w) : triangleFace (cellTri w c) = cellFace w c :=
  congrArg Subtype.val ((triangleFaceEquiv (target w)).apply_symm_apply ((cellFaceEquiv w) c))

theorem cellTri_equiv (t : Triangle (target w)) : cellTri w (triangleEquiv w t) = t :=
  (triangleEquiv w).symm_apply_apply t

theorem cellTri_injective : Function.Injective (cellTri w) := (triangleEquiv w).symm.injective

/-- Membership of a triangle in the private block `l` (tags only `0` or `l+1`). -/
def InBlock (l : Fin k) (t : Triangle (target w)) : Prop := cellBlock w (triangleEquiv w t) = l

instance (l : Fin k) : DecidablePred (InBlock w l) := fun t =>
  inferInstanceAs (Decidable (cellBlock w (triangleEquiv w t) = l))

theorem cell_tags (c : CellIndex w) (x : Ambient) (hx : x ∈ cellFace w c) :
    x.1 = 0 ∨ x.1 = (cellBlock w c).val+1 := by
  rcases c with ⟨t,j,i⟩ | ⟨j,i⟩
  · fin_cases t <;> simp only [cellFace, upper, wall, cap, Finset.mem_insert,
      Finset.mem_singleton] at hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact Or.inl rfl | exact Or.inr rfl
  · fin_cases i <;> simp only [cellFace, sphere, Finset.mem_insert,
      Finset.mem_singleton] at hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact Or.inl rfl | exact Or.inr rfl

theorem cell_private (c : CellIndex w) : ∃ x ∈ cellFace w c, x.1 = (cellBlock w c).val+1 := by
  have h := cell_block w c
  have hm : (cellBlock w c).val+1 ∈ blocks (cellFace w c) := by rw [h]; simp
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hm
  exact ⟨x, (Finset.mem_filter.mp hx).1, he⟩

theorem cellBlock_of_vertex (c : CellIndex w) (x : Ambient) (hx : x ∈ cellFace w c) (l : Fin k)
    (hl : x.1 = l.val+1) : cellBlock w c = l := by
  rcases cell_tags w c x hx with h | h
  · omega
  · exact Fin.ext (by omega)

theorem inBlock_tags (l : Fin k) (t : Triangle (target w)) (ht : InBlock w l t)
    (x : Ambient) (hx : x ∈ triangleFace t) : x.1 = 0 ∨ x.1 = l.val+1 := by
  rw [← cellTri_equiv w t, cellTri_face] at hx
  have h := cell_tags w _ x hx
  rwa [ht] at h

theorem inBlock_of_vertex (l : Fin k) (t : Triangle (target w)) (x : Ambient)
    (hx : x ∈ triangleFace t) (hl : x.1 = l.val+1) : InBlock w l t := by
  rw [← cellTri_equiv w t, cellTri_face] at hx
  exact cellBlock_of_vertex w _ x hx l hl

theorem inBlock_of_tags (l : Fin k) (t : Triangle (target w))
    (h : ∀ x ∈ triangleFace t, x.1 = 0 ∨ x.1 = l.val+1) : InBlock w l t := by
  obtain ⟨x, hx, hb⟩ := cell_private w (triangleEquiv w t)
  have hx' : x ∈ triangleFace t := by rw [← cellTri_equiv w t, cellTri_face]; exact hx
  rcases h x hx' with h0 | h1
  · omega
  · exact inBlock_of_vertex w l t x hx' h1

theorem center_eq_iff (j l : Fin k) : center j = center l ↔ j = l := by
  constructor
  · intro h; exact Fin.ext (by have := congrArg (fun z : Ambient => z.1) h; simpa [center] using this)
  · rintro rfl; rfl

theorem next_injective {j : Fin k} {i m : Position w j} (h : next w i = next w m) : i = m := by
  have hv := congrArg Fin.val h
  unfold next at hv
  have hi := i.isLt
  have hm := m.isLt
  apply Fin.ext
  split_ifs at hv <;> simp only at hv <;> omega

/-- A cell of a NONEMPTY block containing one of its private vertices is a collar cell. -/
theorem not_sphere (l : Fin k) (hw : w l ≠ []) (j : EmptyIndex w) (i : Fin 4) (x : Ambient)
    (hx : x ∈ cellFace w (.inr (j,i))) (hl : x.1 = l.val+1) : False := by
  have h := cellBlock_of_vertex w _ x hx l hl
  change j.val = l at h
  exact hw (h ▸ j.property)

abbrev capCell {l : Fin k} (i : Position w l) : CellIndex w := .inl (2, ⟨l, i⟩)
abbrev upperCell {l : Fin k} (i : Position w l) : CellIndex w := .inl (0, ⟨l, i⟩)
abbrev wallCell {l : Fin k} (i : Position w l) : CellIndex w := .inl (1, ⟨l, i⟩)

/-- Radial edge `{c, t_(i+1)}` lies only in the caps `B_i` and `B_(i+1)`. -/
theorem radial_cells {l : Fin k} (i : Position w l) (c : CellIndex w)
    (h1 : center l ∈ cellFace w c) (h2 : top l (next w i).val ∈ cellFace w c) :
    c = capCell w i ∨ c = capCell w (next w i) := by
  rcases c with ⟨t,j,m⟩ | ⟨j,m⟩
  · fin_cases t
    · simp [cellFace, upper] at h1
    · simp [cellFace, wall] at h1
    · simp only [cellFace, cap, Finset.mem_insert, Finset.mem_singleton] at h1 h2
      rcases h1 with h1 | h1 | h1
      · have hjl := (center_eq_iff l j).mp h1
        subst hjl
        simp only [top_eq_iff, true_and] at h2
        rcases h2 with h2 | h2 | h2
        · exact absurd h2 (top_ne_center _ _ _)
        · right; congr; exact (Fin.ext h2).symm
        · left; congr; exact (next_injective w (Fin.ext h2)).symm
      · exact absurd h1 (center_ne_top _ _ _)
      · exact absurd h1 (center_ne_top _ _ _)
  · exact (not_sphere w l (position_nonempty w i) j m _ h1 rfl).elim

/-- Top edge `{t_i, t_(i+1)}` lies only in `U_i` and `B_i`. -/
theorem top_cells {l : Fin k} (i : Position w l) (c : CellIndex w)
    (h1 : top l i.val ∈ cellFace w c) (h2 : top l (next w i).val ∈ cellFace w c) :
    c = upperCell w i ∨ c = capCell w i := by
  rcases c with ⟨t,j,m⟩ | ⟨j,m⟩
  · have hjl : j = l := by
      have := cellBlock_of_vertex w (.inl (t,⟨j,m⟩)) _ h1 l rfl
      exact this
    subst hjl
    fin_cases t
    · simp only [cellFace, upper, Finset.mem_insert, Finset.mem_singleton, top_eq_iff,
        true_and] at h1 h2
      left
      congr
      rcases h1 with h1 | h1 | h1
      · exact (Fin.ext h1).symm
      · have hi : i = next w m := Fin.ext h1
        subst hi
        exfalso
        rcases h2 with h2 | h2 | h2
        · exact next_next_ne w m (Fin.ext h2)
        · exact next_ne w (next w m) (Fin.ext h2)
        · exact top_ne_base _ _ _ h2
      · exact absurd h1 (top_ne_base _ _ _)
    · simp only [cellFace, wall, Finset.mem_insert, Finset.mem_singleton, top_eq_iff,
        true_and] at h1 h2
      exfalso
      rcases h1 with h1 | h1 | h1
      · rcases h2 with h2 | h2 | h2
        · exact next_ne w i (Fin.ext (h2.trans h1.symm))
        · exact top_ne_base _ _ _ h2
        · exact top_ne_base _ _ _ h2
      · exact top_ne_base _ _ _ h1
      · exact top_ne_base _ _ _ h1
    · simp only [cellFace, cap, Finset.mem_insert, Finset.mem_singleton, top_eq_iff,
        true_and] at h1 h2
      right
      congr
      rcases h1 with h1 | h1 | h1
      · exact absurd h1 (top_ne_center _ _ _)
      · exact (Fin.ext h1).symm
      · have hi : i = next w m := Fin.ext h1
        subst hi
        exfalso
        rcases h2 with h2 | h2 | h2
        · exact top_ne_center _ _ _ h2
        · exact next_next_ne w m (Fin.ext h2)
        · exact next_ne w (next w m) (Fin.ext h2)
  · exact (not_sphere w l (position_nonempty w i) j m _ h1 rfl).elim

/-- Diagonal edge `{t_i, v_(i+1)}` lies only in `U_i` and `W_i`. -/
theorem diagonal_cells {l : Fin k} (i : Position w l) (c : CellIndex w)
    (h1 : top l i.val ∈ cellFace w c) (h2 : base (bottom w l (next w i).val) ∈ cellFace w c) :
    c = upperCell w i ∨ c = wallCell w i := by
  rcases c with ⟨t,j,m⟩ | ⟨j,m⟩
  · have hjl : j = l := cellBlock_of_vertex w (.inl (t,⟨j,m⟩)) _ h1 l rfl
    subst hjl
    fin_cases t
    · simp only [cellFace, upper, Finset.mem_insert, Finset.mem_singleton, top_eq_iff,
        true_and] at h1 h2
      left
      congr
      rcases h1 with h1 | h1 | h1
      · exact (Fin.ext h1).symm
      · have hi : i = next w m := Fin.ext h1
        subst hi
        exfalso
        rcases h2 with h2 | h2 | h2
        · exact base_ne_top _ _ _ h2
        · exact base_ne_top _ _ _ h2
        · exact bottom_distinct w (next w m) (base_injective h2).symm
      · exact absurd h1 (top_ne_base _ _ _)
    · simp only [cellFace, wall, Finset.mem_insert, Finset.mem_singleton, top_eq_iff,
        true_and] at h1
      right
      congr
      rcases h1 with h1 | h1 | h1
      · exact (Fin.ext h1).symm
      · exact absurd h1 (top_ne_base _ _ _)
      · exact absurd h1 (top_ne_base _ _ _)
    · simp only [cellFace, cap, Finset.mem_insert, Finset.mem_singleton] at h2
      exfalso
      rcases h2 with h2 | h2 | h2
      · exact base_ne_center _ _ h2
      · exact base_ne_top _ _ _ h2
      · exact base_ne_top _ _ _ h2
  · exact (not_sphere w l (position_nonempty w i) j m _ h1 rfl).elim

/-- The actual sorted edge on two distinct vertices of an actual face. -/
def pairEdge (a b : Ambient) (hne : a ≠ b) (h : ({a, b} : Finset Ambient) ∈ target w) :
    Edge (target w) :=
  if hlt : a < b then ⟨a, b, hlt, h⟩
  else ⟨b, a, lt_of_le_of_ne (not_lt.mp hlt) hne.symm, by rwa [Finset.pair_comm]⟩

theorem pairEdge_spans (a b : Ambient) (hne : a ≠ b) (h : ({a, b} : Finset Ambient) ∈ target w)
    (t : Triangle (target w)) :
    Spans (pairEdge w a b hne h) t ↔ a ∈ triangleFace t ∧ b ∈ triangleFace t := by
  unfold pairEdge Spans
  split_ifs
  · rfl
  · exact and_comm

theorem pairEdge_private (a b : Ambient) (hne : a ≠ b) (h : ({a, b} : Finset Ambient) ∈ target w)
    (ha : a.1 ≠ 0) :
    ¬ ((pairEdge w a b hne h).src.1 = 0 ∧ (pairEdge w a b hne h).dst.1 = 0) := by
  unfold pairEdge
  split_ifs
  · exact fun hh => ha hh.1
  · exact fun hh => ha hh.2

theorem mem_cellTri {c : CellIndex w} {x : Ambient} (hx : x ∈ cellFace w c) :
    x ∈ triangleFace (cellTri w c) := by rwa [cellTri_face]

/-- Vanishing propagates around a nonempty collar: caps through radial edges, then
upper cells through top edges, then wall cells through diagonal edges. -/
theorem block_zero {K : Type*} [Field K] (lam : Ambient → Ambient → K)
    (hl : ∀ t : Triangle (target w), lam t.v0 t.v1 ≠ 0) (l : Fin k) (hn : 0 < 3*(w l).length)
    (y : Triangle (target w) →₀ K)
    (hd : ∀ e : Edge (target w), ¬ (e.src.1 = 0 ∧ e.dst.1 = 0) → boundaryTwo (target w) lam y e = 0)
    (h0 : y (cellTri w (capCell w (⟨0, hn⟩ : Position w l))) = 0) :
    ∀ c : CellIndex w, cellBlock w c = l → y (cellTri w c) = 0 := by
  have others : ∀ (e : Edge (target w)) (c : CellIndex w) (good : CellIndex w)
      (hgood : y (cellTri w good) = 0)
      (hcls : ∀ c', (e.src ∈ cellFace w c' ∧ e.dst ∈ cellFace w c') → c' = good ∨ c' = c)
      (t' : Triangle (target w)), t' ≠ cellTri w c → Spans e t' → y t' = 0 := by
    intro e c good hgood hcls t' hne hs
    obtain ⟨ha, hb⟩ := hs
    rw [← cellTri_equiv w t', cellTri_face] at ha hb
    rcases hcls _ ⟨ha, hb⟩ with h | h
    · rw [← cellTri_equiv w t', h]; exact hgood
    · exact (hne (by rw [← cellTri_equiv w t', h])).elim
  have step : ∀ i : Position w l, y (cellTri w (capCell w i)) = 0 →
      y (cellTri w (capCell w (next w i))) = 0 := by
    intro i hi
    have hne : center l ≠ top l (next w i).val := center_ne_top _ _ _
    let e := pairEdge w _ _ hne (radial_face w (next w i))
    apply survivor lam hl y e _ (hd e (pairEdge_private w _ _ hne _ (by simp [center])))
    · exact (pairEdge_spans w _ _ hne _ _).mpr
        ⟨mem_cellTri w (by simp [cellFace, cap]), mem_cellTri w (by simp [cellFace, cap])⟩
    · apply others e _ (capCell w i) hi
      intro c' hc'
      have hh := (pairEdge_spans w _ _ hne (radial_face w (next w i)) (cellTri w c')).mp
        ⟨mem_cellTri w hc'.1, mem_cellTri w hc'.2⟩
      rw [cellTri_face] at hh
      exact radial_cells w i c' hh.1 hh.2
  have caps : ∀ i : Position w l, y (cellTri w (capCell w i)) = 0 := by
    have hall : ∀ m (hm : m < 3*(w l).length), y (cellTri w (capCell w (⟨m, hm⟩ : Position w l))) = 0 := by
      intro m
      induction m with
      | zero => intro hm; exact h0
      | succ m ih =>
        intro hm
        have hm' : m < 3*(w l).length := by omega
        have he : next w (⟨m, hm'⟩ : Position w l) = ⟨m+1, hm⟩ := by
          apply Fin.ext; rw [next_val]; exact Nat.mod_eq_of_lt hm
        rw [← he]
        exact step _ (ih hm')
    intro i
    exact hall i.val i.isLt
  have uppers : ∀ i : Position w l, y (cellTri w (upperCell w i)) = 0 := by
    intro i
    have hne : top l i.val ≠ top l (next w i).val := fun h =>
      next_ne w i (Fin.ext ((top_eq_iff l l _ _).mp h).2.symm)
    let e := pairEdge w _ _ hne (top_edge_face w i)
    apply survivor lam hl y e _ (hd e (pairEdge_private w _ _ hne _ (by simp [top])))
    · exact (pairEdge_spans w _ _ hne _ _).mpr
        ⟨mem_cellTri w (by simp [cellFace, upper]), mem_cellTri w (by simp [cellFace, upper])⟩
    · apply others e _ (capCell w i) (caps i)
      intro c' hc'
      have hh := (pairEdge_spans w _ _ hne (top_edge_face w i) (cellTri w c')).mp
        ⟨mem_cellTri w hc'.1, mem_cellTri w hc'.2⟩
      rw [cellTri_face] at hh
      exact (top_cells w i c' hh.1 hh.2).symm
  have walls : ∀ i : Position w l, y (cellTri w (wallCell w i)) = 0 := by
    intro i
    have hne : top l i.val ≠ base (bottom w l (next w i).val) := top_ne_base _ _ _
    let e := pairEdge w _ _ hne (diagonal_face w i)
    apply survivor lam hl y e _ (hd e (pairEdge_private w _ _ hne _ (by simp [top])))
    · exact (pairEdge_spans w _ _ hne _ _).mpr
        ⟨mem_cellTri w (by simp [cellFace, wall]), mem_cellTri w (by simp [cellFace, wall])⟩
    · apply others e _ (upperCell w i) (uppers i)
      intro c' hc'
      have hh := (pairEdge_spans w _ _ hne (diagonal_face w i) (cellTri w c')).mp
        ⟨mem_cellTri w hc'.1, mem_cellTri w hc'.2⟩
      rw [cellTri_face] at hh
      exact diagonal_cells w i c' hh.1 hh.2
  intro c hc
  rcases c with ⟨t,j,m⟩ | ⟨j,m⟩
  · change j = l at hc
    subst hc
    fin_cases t
    · exact uppers m
    · exact walls m
    · exact caps m
  · change j.val = l at hc
    have hw : w l ≠ [] := by intro h; simp [h] at hn
    exact (hw (hc ▸ j.property)).elim

end Collar

section Filling
open ArbCells ArbMoves ArbTransport
variable {m k : ℕ} (w : Fin k → ArbRose.AWord m)

/-- The rose together with the private cells of ONE block, as an actual subcomplex. -/
def blockComplex (l : Fin k) : PreAbstractSimplicialComplex Ambient where
  faces := {s | s ∈ target w ∧ ∀ x ∈ s, x.1 = 0 ∨ x.1 = l.val+1}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨((target w).isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    exact ⟨((target w).isRelLowerSet_faces hs.1).2 hts ht, fun x hx => hs.2 x (hts hx)⟩

theorem block_le (l : Fin k) : (blockComplex w l).map id ≤ target w := by
  rintro s ⟨t, ht, rfl⟩
  show Finset.image id t ∈ target w
  rw [Finset.image_id]
  exact ht.1

theorem rose_le_block (l : Fin k) : (ArbRose.rose m).map base ≤ blockComplex w l := by
  rintro s ⟨t, ht, rfl⟩
  refine ⟨base_face w t ht, fun x hx => ?_⟩
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact Or.inl rfl

theorem cell_in_block {l : Fin k} (i : Position w l) (t : Fin 3) :
    cellFace w (.inl (t, ⟨l, i⟩)) ∈ blockComplex w l := by
  refine ⟨cell_face w _, fun x hx => ?_⟩
  have h := cell_tags w _ x hx
  exact h

theorem base0_block (l : Fin k) : ({base 0} : Finset Ambient) ∈ blockComplex w l :=
  ⟨(root w).property, fun x hx => Or.inl (by rw [Finset.mem_singleton.mp hx]; rfl)⟩

/-- Actual relator moves INSIDE the block subcomplex. -/
theorem block_moves (l : Fin k) (he : w l ≠ []) :
    Nonempty (Moves (mapPath base (rose_le_block w l) (ArbRose.wordPath (w l)))
      (.refl (base 0) (base0_block w l))) :=
  relator_moves_in w l (blockComplex w l) (rose_le_block w l) (fun q => cell_in_block w q 1)
    (fun q => cell_in_block w q 0) (fun q => cell_in_block w q 2) he _

theorem mapPath_id_comp {U : Type*} [LinearOrder U] {A : PreAbstractSimplicialComplex U}
    {B C : PreAbstractSimplicialComplex Ambient} (f : U → Ambient) (hf : A.map f ≤ B)
    (hg : B.map id ≤ C) (hfg : A.map f ≤ C) {u v : U} (p : Path A u v) :
    mapPath id hg (mapPath f hf p) = mapPath f hfg p := by
  induction p with
  | refl => rfl
  | cons h p ih => exact congrArg (Path.cons _) ih

theorem triangle_sorted {K : Type*} [Field K] (tau : Transport (K := K) (target w))
    (u v x : Ambient) (h : ({u, v, x} : Finset Ambient) ∈ target w) (h1 : u < v) (h2 : v < x) :
    SimplicialTransport.triangle tau u v x h = Finsupp.single ⟨u, v, x, h1, h2, h⟩ 1 := by
  simp [SimplicialTransport.triangle, h1, h2]

/-- The block filling: actual move filling in the block subcomplex, pushed forward. -/
def blockFilling {K : Type*} [Field K] (tau : Transport (K := K) (target w)) (l : Fin k)
    (he : w l ≠ []) : Triangle (target w) →₀ K :=
  triangleMap tau id (block_le w l)
    (PathChains.filling (pullback tau id (block_le w l)) (Classical.choice (block_moves w l he)))

theorem blockFilling_support {K : Type*} [Field K] (tau : Transport (K := K) (target w))
    (l : Fin k) (he : w l ≠ []) (t : Triangle (target w)) (ht : blockFilling w tau l he t ≠ 0) :
    InBlock w l t := by
  classical
  unfold blockFilling triangleMap at ht
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply] at ht
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  simp only [id] at hs
  rw [Finsupp.smul_apply, triangle_sorted w tau _ _ _ _ s.ordered01 s.ordered12,
    Finsupp.single_apply] at hs
  split_ifs at hs with heq
  · apply inBlock_of_tags
    intro x hx
    rw [← heq] at hx
    exact s.face.2 x (by simpa [triangleFace] using hx)
  · simp at hs

theorem blockFilling_boundary {K : Type*} [Field K] (tau : Transport (K := K) (target w))
    (l : Fin k) (he : w l ≠ []) :
    boundaryTwo (target w) (coeff tau) (blockFilling w tau l he) =
      PathChains.chain tau (mappedWord w l) := by
  have h1 := LinearMap.congr_fun (map_boundary_two tau id (block_le w l))
    (PathChains.filling (pullback tau id (block_le w l)) (Classical.choice (block_moves w l he)))
  simp only [LinearMap.comp_apply] at h1
  unfold blockFilling
  rw [h1, PathChains.filling_boundary, map_sub, StellarSubdivision.map_path_chain,
    mapPath_id_comp base (rose_le_block w l) (block_le w l) (baseMap w)]
  simp [PathChains.chain, mappedWord]

/-- The rose inclusion only reaches edges with both endpoints in block zero. -/
theorem roseMap_base {K : Type*} [Field K] (q : Fin m → Kˣ) (x : Fin m → K) (e : Edge (target w))
    (he : roseMap w q x e ≠ 0) : e.src.1 = 0 ∧ e.dst.1 = 0 := by
  by_contra hb
  apply he
  change Finsupp.mapDomain (includeEdge w) (ArbRose.roseMap q x) e = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨f, rfl⟩
  exact hb ⟨rfl, rfl⟩

end Filling

section Assembly
open ArbCells ArbMoves ArbTransport
variable {m k : ℕ} (w : Fin k → ArbRose.AWord m)

/-- Blockwise support and vanishing of the boundary on every non-rose edge. -/
def Good {K : Type*} [Field K] (lam : Ambient → Ambient → K) (l : Fin k)
    (y : Triangle (target w) →₀ K) : Prop :=
  (∀ t, y t ≠ 0 → InBlock w l t) ∧
    ∀ e : Edge (target w), ¬ (e.src.1 = 0 ∧ e.dst.1 = 0) → boundaryTwo (target w) lam y e = 0

theorem good_vanish {K : Type*} [Field K] (lam : Ambient → Ambient → K)
    (hl : ∀ t : Triangle (target w), lam t.v0 t.v1 ≠ 0) (l : Fin k) (hn : 0 < 3*(w l).length)
    (y : Triangle (target w) →₀ K) (hy : Good w lam l y)
    (h0 : y (cellTri w (capCell w (⟨0, hn⟩ : Position w l))) = 0) : y = 0 := by
  ext t
  by_contra hyt
  have hb := hy.1 t hyt
  apply hyt
  rw [← cellTri_equiv w t]
  exact block_zero w lam hl l hn y hy.2 h0 _ hb

theorem good_sub {K : Type*} [Field K] (lam : Ambient → Ambient → K) (l : Fin k)
    (y f : Triangle (target w) →₀ K) (a : K) (hy : Good w lam l y) (hf : Good w lam l f) :
    Good w lam l (y - a • f) := by
  constructor
  · intro t ht
    by_cases h1 : y t = 0
    · by_cases h2 : f t = 0
      · exact (ht (by simp [h1, h2])).elim
      · exact hf.1 t h2
    · exact hy.1 t h1
  · intro e he
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, hy.2 e he, hf.2 e he]
    simp

/-- Arbitrary-rank selected private-edge/filling comparison: for raw words over `Fin m`
killed by a character χ, injectivity of the algebraic left Fox map implies injectivity
of the defined weighted d2 of their tagged target with the χ transport. -/
theorem comparison (χ : FreeGroup (Fin m) →* ℂ)
    (hk : ∀ j, value (ArbRose.transport (fun i => GenericFox.unitsChar χ (FreeGroup.of i)))
      (ArbRose.wordPath (w j)) = 1)
    (hfox : Function.Injective
      (Fintype.linearCombination ℂ (fun j => GenericFox.D χ (ArbRose.freeWord (w j))))) :
    Function.Injective (boundaryTwo (target w) (coeff (transport w _ hk))) := by
  set qu : Fin m → ℂˣ := fun i => GenericFox.unitsChar χ (FreeGroup.of i)
  set tau := transport w qu hk
  set lam : Ambient → Ambient → ℂ := coeff tau
  have hl : ∀ t : Triangle (target w), lam t.v0 t.v1 ≠ 0 := fun t => coeff_ne_zero tau _ _
  set D : Fin k → Fin m → ℂ := fun l => GenericFox.D χ (ArbRose.freeWord (w l))
  have hbt : ∀ a : Fin k → ℂ,
      Fintype.linearCombination ℂ (fun j => GenericFox.D χ (ArbRose.freeWord (w j))) a =
        ∑ l, a l • D l := by
    intro a
    simp [Fintype.linearCombination_apply, D]
  have hD : ∀ l, D l ≠ 0 := by
    intro l h
    have h1 : Fintype.linearCombination ℂ (fun j => GenericFox.D χ (ArbRose.freeWord (w j)))
        (Pi.single l 1) =
        Fintype.linearCombination ℂ (fun j => GenericFox.D χ (ArbRose.freeWord (w j))) 0 := by
      rw [hbt, map_zero]
      simp [Pi.single_apply, h]
    have h2 := congrFun (hfox h1) l
    simp at h2
  have hne : ∀ l, w l ≠ [] := by
    intro l h
    apply hD l
    simp [D, h]
  have hn : ∀ l, 0 < 3*(w l).length := fun l => by
    have := List.length_pos_iff_ne_nil.mpr (hne l); omega
  let cap0 : Fin k → Triangle (target w) :=
    fun l => cellTri w (capCell w (⟨0, hn l⟩ : Position w l))
  let F : Fin k → Triangle (target w) →₀ ℂ := fun l => blockFilling w tau l (hne l)
  have hFb : ∀ l, boundaryTwo (target w) lam (F l) = roseMap w qu (D l) :=
    fun l => (blockFilling_boundary w tau l (hne l)).trans (word_chain w χ hk (w l))
  have hFg : ∀ l, Good w lam l (F l) := by
    intro l
    refine ⟨blockFilling_support w tau l (hne l), fun e he => ?_⟩
    rw [hFb]
    by_contra hz
    exact he (roseMap_base w _ _ e hz)
  have hF0 : ∀ l, F l (cap0 l) ≠ 0 := by
    intro l h0
    have hz := good_vanish w lam hl l (hn l) (F l) (hFg l) h0
    have hb := hFb l
    rw [hz, map_zero] at hb
    apply hD l
    apply roseMap_injective w qu
    rw [← hb, map_zero]
  rw [injective_iff_map_eq_zero]
  intro z hz
  let y : Fin k → Triangle (target w) →₀ ℂ := fun l => z.filter (InBlock w l)
  have hyg : ∀ l, Good w lam l (y l) := by
    intro l
    constructor
    · intro t ht
      by_contra hb
      exact ht (by simp [y, hb])
    · intro e he
      have hx : ∃ x, (x = e.src ∨ x = e.dst) ∧ x.1 ≠ 0 := by
        by_cases hs : e.src.1 = 0
        · exact ⟨e.dst, Or.inr rfl, fun hd => he ⟨hs, hd⟩⟩
        · exact ⟨e.src, Or.inl rfl, hs⟩
      obtain ⟨x, hxe, hx0⟩ := hx
      have hspan : ∀ t, FoxFilling.Spans e t → x ∈ triangleFace t := by
        intro t hs
        rcases hxe with rfl | rfl
        · exact hs.1
        · exact hs.2
      by_cases hxl : x.1 = l.val+1
      · rw [FoxFilling.filter_apply_eq lam z (InBlock w l) e
          (fun t hs => inBlock_of_vertex w l t x (hspan t hs) hxl), hz]
        rfl
      · apply FoxFilling.filter_apply_zero lam z (InBlock w l) e
        intro t hs hb
        rcases inBlock_tags w l t hb x (hspan t hs) with h | h
        · exact hx0 h
        · exact hxl h
  let a : Fin k → ℂ := fun l => y l (cap0 l) / F l (cap0 l)
  have hya : ∀ l, y l = a l • F l := by
    intro l
    have hv := good_vanish w lam hl l (hn l) (y l - a l • F l)
      (good_sub w lam l (y l) (F l) (a l) (hyg l) (hFg l)) (by
        change y l (cap0 l) - a l • F l (cap0 l) = 0
        simp only [a, smul_eq_mul]
        rw [div_mul_cancel₀ _ (hF0 l), sub_self])
    exact sub_eq_zero.mp hv
  have hzs : z = ∑ l, y l := by
    ext t
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (cellBlock w (triangleEquiv w t))]
    · exact (Finsupp.filter_apply_pos (InBlock w (cellBlock w (triangleEquiv w t))) (f := z)
        (rfl : InBlock w (cellBlock w (triangleEquiv w t)) t)).symm
    · intro l _ hl
      exact Finsupp.filter_apply_neg (InBlock w l) (f := z) (show ¬ InBlock w l t from fun h => hl h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hzero : Fintype.linearCombination ℂ (fun j => GenericFox.D χ (ArbRose.freeWord (w j))) a = 0 := by
    apply roseMap_injective w qu
    rw [map_zero, hbt, map_sum]
    have h2 : boundaryTwo (target w) lam z = 0 := hz
    rw [hzs, map_sum] at h2
    rw [← h2]
    apply Finset.sum_congr rfl
    intro l _
    rw [hya, map_smul, map_smul, hFb]
  have ha : a = 0 := hfox (hzero.trans (map_zero _).symm)
  rw [hzs]
  apply Finset.sum_eq_zero
  intro l _
  rw [hya, ha, Pi.zero_apply, zero_smul]

end Assembly

end D2RelationGap.ArbFilling
