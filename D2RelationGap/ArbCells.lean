import D2RelationGap.ArbRose
import D2RelationGap.PresentationCells

/-!
Privately tagged U/W/B collars and empty-word spheres on the ARBITRARY-rank rose
(`ArbRose`), for any tuple of raw words over `Fin m`. This ports `PresentationCells`
(the rank-five construction) verbatim where the proofs are rose-independent.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
-/
noncomputable section
namespace D2RelationGap.ArbCells
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open PresentationRose (Noncollapsed node_distinct)

abbrev Ambient := ℕ ×ₗ ℕ
variable {m k : ℕ} (w : Fin k → ArbRose.AWord m)

def base (v : ℕ) : Ambient := (0,v)
def center (j : Fin k) : Ambient := (j.val+1,0)
def top (j : Fin k) (i : ℕ) : Ambient := (j.val+1,i+1)

abbrev Position (j : Fin k) := Fin (3*(w j).length)
abbrev CollarIndex := Σ j : Fin k, Position w j
abbrev EmptyIndex := {j : Fin k // w j = []}

def next {j : Fin k} (i : Position w j) : Position w j :=
  if h : i.val+1 < 3*(w j).length then ⟨i.val+1,h⟩
  else ⟨0,by have hi := i.isLt; omega⟩

theorem position_length {j : Fin k} (i : Position w j) : 3 ≤ 3*(w j).length := by
  have hi := i.isLt
  omega

theorem next_ne {j : Fin k} (i : Position w j) : next w i ≠ i := by
  unfold next
  split_ifs with h
  · intro he; have hh := congrArg Fin.val he; simp only at hh; omega
  · intro he; have hh := congrArg Fin.val he; simp only at hh
    have hn := position_length w i
    omega

def bottom (j : Fin k) (i : ℕ) : ℕ :=
  PolygonSource.node (ArbRose.wordPath (w j)) i

theorem bottom_zero (j : Fin k) : bottom w j 0 = 0 := PolygonSource.node_zero _
theorem bottom_end (j : Fin k) : bottom w j (3*(w j).length) = 0 := by
  simpa only [bottom,ArbRose.word_length] using PolygonSource.node_length (ArbRose.wordPath (w j))

theorem bottom_next {j : Fin k} (i : Position w j) :
    bottom w j (next w i).val = bottom w j (i.val+1) := by
  unfold next
  split_ifs with h
  · rfl
  · have hn : i.val+1 = 3*(w j).length := by have hi := i.isLt; omega
    simp only [hn,bottom_zero,bottom_end]

theorem bottom_edge {j : Fin k} (i : Position w j) :
    ({bottom w j i.val,bottom w j (next w i).val} : Finset ℕ) ∈ ArbRose.rose m := by
  rw [bottom_next]
  exact PolygonSource.node_consecutive_face (ArbRose.wordPath (w j)) i.val
    (by rw [ArbRose.word_length]; exact i.isLt)

theorem bottom_distinct {j : Fin k} (i : Position w j) :
    bottom w j i.val ≠ bottom w j (next w i).val := by
  rw [bottom_next]
  exact node_distinct (ArbRose.wordPath (w j)) (ArbRose.word_noncollapsed _) i.val
    (by rw [ArbRose.word_length]; exact i.isLt)

@[simp] theorem base_injective : Function.Injective base := by
  intro x y h
  exact congrArg (fun z : Ambient => z.2) h

@[simp] theorem base_ne_top (v : ℕ) (j : Fin k) (i : ℕ) : base v ≠ top j i := by
  intro h; have hh := congrArg (fun z : Ambient => z.1) h; simp [base,top] at hh
@[simp] theorem base_ne_center (v : ℕ) (j : Fin k) : base v ≠ center j := by
  intro h; have hh := congrArg (fun z : Ambient => z.1) h; simp [base,center] at hh
@[simp] theorem center_ne_top (j l : Fin k) (i : ℕ) : center j ≠ top l i := by
  intro h; have hh := congrArg (fun z : Ambient => z.2) h; simp [center,top] at hh

theorem top_eq_iff (j l : Fin k) (i m : ℕ) : top j i = top l m ↔ j = l ∧ i = m := by
  constructor
  · intro h
    have h1 := congrArg (fun z : Ambient => z.1) h
    have h2 := congrArg (fun z : Ambient => z.2) h
    exact ⟨Fin.ext (by simpa [top] using h1),by simpa [top] using h2⟩
  · rintro ⟨rfl,rfl⟩; rfl

def upper {j : Fin k} (i : Position w j) : Finset Ambient :=
  {top j i.val,top j (next w i).val,base (bottom w j (next w i).val)}
def wall {j : Fin k} (i : Position w j) : Finset Ambient :=
  {top j i.val,base (bottom w j (next w i).val),base (bottom w j i.val)}
def cap {j : Fin k} (i : Position w j) : Finset Ambient :=
  {center j,top j i.val,top j (next w i).val}

def sphere (j : EmptyIndex w) : Fin 4 → Finset Ambient
  | 0 => {top j.val 0,top j.val 1,top j.val 2}
  | 1 => {base 0,top j.val 1,top j.val 2}
  | 2 => {base 0,top j.val 0,top j.val 2}
  | 3 => {base 0,top j.val 0,top j.val 1}

abbrev CellIndex := (Fin 3 × CollarIndex w) ⊕ (EmptyIndex w × Fin 4)

def cellFace : CellIndex w → Finset Ambient
  | .inl (t,⟨_j,i⟩) => match t with | 0 => upper w i | 1 => wall w i | 2 => cap w i
  | .inr (j,i) => sphere w j i

def cellBlock : CellIndex w → Fin k
  | .inl (_,⟨j,_⟩) => j
  | .inr (j,_) => j.val

/-- Faces: images of rose faces in block zero, and subsets of displayed collar cells. -/
def target : PreAbstractSimplicialComplex Ambient where
  faces := {s | s.Nonempty ∧ ((∃ t ∈ ArbRose.rose m, s ⊆ t.image base) ∨
    ∃ f : CellIndex w, s ⊆ cellFace w f)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    rcases hs.2 with ⟨r,hr,h⟩ | ⟨f,h⟩
    · exact ⟨ht,Or.inl ⟨r,hr,hts.trans h⟩⟩
    · exact ⟨ht,Or.inr ⟨f,hts.trans h⟩⟩

theorem upper_card {j : Fin k} (i : Position w j) : (upper w i).card = 3 := by
  have hn : top j i.val ≠ top j (next w i).val := by
    intro h; exact next_ne w i (Fin.ext ((top_eq_iff j j _ _).mp h).2.symm)
  simp [upper,hn,Ne.symm (base_ne_top _ _ _)]

theorem wall_card {j : Fin k} (i : Position w j) : (wall w i).card = 3 := by
  have hn : base (bottom w j (next w i).val) ≠ base (bottom w j i.val) :=
    fun h => bottom_distinct w i (base_injective h).symm
  simp [wall,hn,Ne.symm (base_ne_top _ _ _)]

theorem cap_card {j : Fin k} (i : Position w j) : (cap w i).card = 3 := by
  have hn : top j i.val ≠ top j (next w i).val := by
    intro h; exact next_ne w i (Fin.ext ((top_eq_iff j j _ _).mp h).2.symm)
  simp [cap,hn]

theorem sphere_card (j : EmptyIndex w) (i : Fin 4) : (sphere w j i).card = 3 := by
  fin_cases i <;> simp [sphere,top_eq_iff]

theorem cell_card (t : CellIndex w) : (cellFace w t).card = 3 := by
  rcases t with ⟨t,_j,i⟩ | ⟨j,i⟩
  · fin_cases t
    · exact upper_card w i
    · exact wall_card w i
    · exact cap_card w i
  · exact sphere_card w j i

theorem cell_face (t : CellIndex w) : cellFace w t ∈ target w :=
  ⟨by rw [← Finset.card_pos, cell_card]; omega, Or.inr ⟨t,Finset.Subset.refl _⟩⟩

/-- Every actual three-vertex face is a displayed collar/cap/sphere cell. -/
theorem triangle_exhaustive (s : Finset Ambient) (hs : s ∈ target w) (hc : s.card = 3) :
    ∃ f : CellIndex w, s = cellFace w f := by
  rcases hs.2 with ⟨r,hr,h⟩ | ⟨f,h⟩
  · have h1 := (Finset.card_le_card h).trans (Finset.card_image_le.trans
      (ArbRose.dimension_at_most_one m r hr))
    omega
  · exact ⟨f, Finset.eq_of_subset_of_card_le h (by rw [hc, cell_card])⟩

theorem base_face (s : Finset ℕ) (hs : s ∈ ArbRose.rose m) : s.image base ∈ target w :=
  ⟨hs.1.image _, Or.inl ⟨s,hs,Finset.Subset.refl _⟩⟩

theorem baseMap : (ArbRose.rose m).map base ≤ target w := by
  rintro s ⟨t,ht,rfl⟩
  exact base_face w t ht

theorem upper_face {j : Fin k} (i : Position w j) : upper w i ∈ target w :=
  cell_face w (.inl (0,⟨j,i⟩))
theorem wall_face {j : Fin k} (i : Position w j) : wall w i ∈ target w :=
  cell_face w (.inl (1,⟨j,i⟩))
theorem cap_face {j : Fin k} (i : Position w j) : cap w i ∈ target w :=
  cell_face w (.inl (2,⟨j,i⟩))
theorem sphere_face (j : EmptyIndex w) (i : Fin 4) : sphere w j i ∈ target w :=
  cell_face w (.inr (j,i))

theorem vertical_face {j : Fin k} (i : Position w j) :
    ({top j i.val,base (bottom w j i.val)} : Finset Ambient) ∈ target w :=
  pair_mem_of_face (target w) _ (wall_face w i) _ _ (by simp [wall]) (by simp [wall])
theorem radial_face {j : Fin k} (i : Position w j) :
    ({center j,top j i.val} : Finset Ambient) ∈ target w :=
  pair_mem_of_face (target w) _ (cap_face w i) _ _ (by simp [cap]) (by simp [cap])
theorem top_edge_face {j : Fin k} (i : Position w j) :
    ({top j i.val,top j (next w i).val} : Finset Ambient) ∈ target w :=
  pair_mem_of_face (target w) _ (upper_face w i) _ _ (by simp [upper]) (by simp [upper])
theorem diagonal_face {j : Fin k} (i : Position w j) :
    ({top j i.val,base (bottom w j (next w i).val)} : Finset Ambient) ∈ target w :=
  pair_mem_of_face (target w) _ (wall_face w i) _ _ (by simp [wall]) (by simp [wall])

theorem sphere_edge (j : EmptyIndex w) (i : Fin 3) :
    ({base 0,top j.val i.val} : Finset Ambient) ∈ target w := by
  fin_cases i
  · exact pair_mem_of_face (target w) _ (sphere_face w j 3) _ _ (by simp [sphere]) (by simp [sphere])
  · exact pair_mem_of_face (target w) _ (sphere_face w j 3) _ _ (by simp [sphere]) (by simp [sphere])
  · exact pair_mem_of_face (target w) _ (sphere_face w j 1) _ _ (by simp [sphere]) (by simp [sphere])

def root : Vertex (target w) := ⟨base 0,by simpa using base_face w {0} (ArbRose.root_face m)⟩

/-- Old raw-word paths include into this SAME target without any word reduction. -/
def mappedWord (j : Fin k) : Path (target w) (base 0) (base 0) :=
  mapPath base (baseMap w) (ArbRose.wordPath (w j))

theorem position_nonempty {j : Fin k} (i : Position w j) : w j ≠ [] := by
  intro h
  have hi := i.isLt
  simp [h] at hi

@[simp] theorem top_ne_base (j : Fin k) (i : ℕ) (v : ℕ) : top j i ≠ base v :=
  (base_ne_top v j i).symm
@[simp] theorem top_ne_center (j l : Fin k) (i : ℕ) : top j i ≠ center l :=
  (center_ne_top l j i).symm
@[simp] theorem center_ne_base (j : Fin k) (v : ℕ) : center j ≠ base v :=
  (base_ne_center v j).symm

theorem next_next_ne {j : Fin k} (i : Position w j) : next w (next w i) ≠ i := by
  intro h
  have hh := congrArg Fin.val h
  have hn := position_length w i
  have hi := i.isLt
  by_cases h1 : i.val+1 < 3*(w j).length
  · by_cases h2 : i.val+2 < 3*(w j).length
    · have h2' : i.val+1+1 < 3*(w j).length := by omega
      simp only [next,dite_eq_left h1,dite_eq_left h2'] at hh
      omega
    · have h2' : ¬ i.val+1+1 < 3*(w j).length := by omega
      simp only [next,dite_eq_left h1,dite_eq_right h2'] at hh
      omega
  · have h2 : 1 < 3*(w j).length := by omega
    simp only [next,dite_eq_right h1,dite_eq_left h2] at hh
    omega

theorem cyclic_pair_injective {j : Fin k} (i l : Position w j)
    (he : ({i.val,(next w i).val} : Finset ℕ) = {l.val,(next w l).val}) : i = l := by
  by_cases h : i = l
  · exact h
  have hi : i = next w l := by
    have hh : i.val ∈ ({l.val,(next w l).val} : Finset ℕ) := he ▸ (by simp)
    rcases Finset.mem_insert.mp hh with hh | hh
    · exact (h (Fin.ext hh)).elim
    · exact Fin.ext (Finset.mem_singleton.mp hh)
  have hl : l = next w i := by
    have hh : l.val ∈ ({i.val,(next w i).val} : Finset ℕ) := he.symm ▸ (by simp)
    rcases Finset.mem_insert.mp hh with hh | hh
    · exact (h (Fin.ext hh.symm)).elim
    · exact Fin.ext (Finset.mem_singleton.mp hh)
  exact (next_next_ne w l (by rw [← hi,← hl])).elim

/-- Reads private top positions from an actual face; bottom/center tags disappear. -/
def topPositions (j : Fin k) (s : Finset Ambient) : Finset ℕ :=
  (s.filter (fun x => x.1 = j.val+1 ∧ 0 < x.2)).image (fun x => x.2-1)

theorem upper_positions {j : Fin k} (i : Position w j) :
    topPositions j (upper w i) = {i.val,(next w i).val} := by
  ext n
  simp only [topPositions,Finset.mem_image,Finset.mem_filter,upper,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    rcases hx with rfl | rfl | rfl
    · simp [top]
    · simp [top]
    · have hh := hp.1; simp [base] at hh
  · rintro (rfl | rfl)
    · exact ⟨top j i.val,⟨by simp,by simp [top]⟩,by simp [top]⟩
    · exact ⟨top j (next w i).val,⟨by simp,by simp [top]⟩,by simp [top]⟩
theorem wall_positions {j : Fin k} (i : Position w j) : topPositions j (wall w i) = {i.val} := by
  ext n
  simp only [topPositions,Finset.mem_image,Finset.mem_filter,wall,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    rcases hx with rfl | rfl | rfl
    · simp [top]
    · have hh := hp.1; simp [base] at hh
    · have hh := hp.1; simp [base] at hh
  · rintro rfl
    exact ⟨top j i.val,⟨by simp,by simp [top]⟩,by simp [top]⟩
theorem cap_positions {j : Fin k} (i : Position w j) :
    topPositions j (cap w i) = {i.val,(next w i).val} := by
  ext n
  simp only [topPositions,Finset.mem_image,Finset.mem_filter,cap,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    rcases hx with rfl | rfl | rfl
    · have hh := hp.2; simp [center] at hh
    · simp [top]
    · simp [top]
  · rintro (rfl | rfl)
    · exact ⟨top j i.val,⟨by simp,by simp [top]⟩,by simp [top]⟩
    · exact ⟨top j (next w i).val,⟨by simp,by simp [top]⟩,by simp [top]⟩

theorem upper_injective {j : Fin k} : Function.Injective (upper w (j := j)) := by
  intro i l he
  exact cyclic_pair_injective w i l (by simpa only [upper_positions] using congrArg (topPositions j) he)
theorem wall_injective {j : Fin k} : Function.Injective (wall w (j := j)) := by
  intro i l he
  have hh := congrArg (topPositions j) he
  rw [wall_positions,wall_positions] at hh
  exact Fin.ext (Finset.singleton_inj.mp hh)
theorem cap_injective {j : Fin k} : Function.Injective (cap w (j := j)) := by
  intro i l he
  exact cyclic_pair_injective w i l (by simpa only [cap_positions] using congrArg (topPositions j) he)

theorem upper_ne_wall {j : Fin k} (i l : Position w j) : upper w i ≠ wall w l := by
  intro he
  have hh := congrArg (topPositions j) he
  rw [upper_positions,wall_positions] at hh
  have hi : i.val = l.val := Finset.mem_singleton.mp (hh ▸ (by simp : i.val ∈ ({i.val,(next w i).val} : Finset ℕ)))
  have hn : (next w i).val = l.val := Finset.mem_singleton.mp (hh ▸ (by simp : (next w i).val ∈ ({i.val,(next w i).val} : Finset ℕ)))
  exact next_ne w i (Fin.ext (hn.trans hi.symm))
theorem upper_ne_cap {j : Fin k} (i l : Position w j) : upper w i ≠ cap w l := by
  intro he
  have hh : center j ∈ upper w i := he.symm ▸ (by simp [cap])
  simp [upper] at hh
theorem wall_ne_cap {j : Fin k} (i l : Position w j) : wall w i ≠ cap w l := by
  intro he
  have hh : center j ∈ wall w i := he.symm ▸ (by simp [cap])
  simp [wall] at hh

/-- The PRIVATE block coordinate is retained by every triangle family. -/
def blocks (s : Finset Ambient) : Finset ℕ :=
  (s.filter (fun x => 0 < x.1)).image (fun x => x.1)

theorem blocks_of_tags (s : Finset Ambient) (j : Fin k)
    (ht : ∀ x ∈ s, x.1 = 0 ∨ x.1 = j.val+1)
    (hw : ∃ x ∈ s, x.1 = j.val+1) : blocks s = {j.val+1} := by
  ext n
  simp only [blocks,Finset.mem_image,Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    rcases ht x hx with h | h
    · omega
    · exact h
  · rintro rfl
    obtain ⟨x,hx,he⟩ := hw
    exact ⟨x,⟨hx,by omega⟩,he⟩

theorem upper_block {j : Fin k} (i : Position w j) : blocks (upper w i) = {j.val+1} := by
  apply blocks_of_tags _ j
  · intro x hx
    simp only [upper,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact ⟨top j i.val,by simp [upper],rfl⟩
theorem wall_block {j : Fin k} (i : Position w j) : blocks (wall w i) = {j.val+1} := by
  apply blocks_of_tags _ j
  · intro x hx
    simp only [wall,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  · exact ⟨top j i.val,by simp [wall],rfl⟩
theorem cap_block {j : Fin k} (i : Position w j) : blocks (cap w i) = {j.val+1} := by
  apply blocks_of_tags _ j
  · intro x hx
    simp only [cap,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Or.inr rfl
  · exact ⟨center j,by simp [cap],rfl⟩
theorem sphere_block (j : EmptyIndex w) (i : Fin 4) : blocks (sphere w j i) = {j.val.val+1} := by
  apply blocks_of_tags _ j.val
  · intro x hx
    fin_cases i <;> simp only [sphere,Finset.mem_insert,Finset.mem_singleton] at hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact Or.inr rfl | exact Or.inl rfl
  · fin_cases i
    · exact ⟨top j.val 0,by simp [sphere],rfl⟩
    · exact ⟨top j.val 1,by simp [sphere],rfl⟩
    · exact ⟨top j.val 0,by simp [sphere],rfl⟩
    · exact ⟨top j.val 0,by simp [sphere],rfl⟩


theorem cell_block (t : CellIndex w) : blocks (cellFace w t) = {(cellBlock w t).val+1} := by
  rcases t with ⟨t,_j,i⟩ | ⟨j,i⟩
  · fin_cases t
    · exact upper_block w i
    · exact wall_block w i
    · exact cap_block w i
  · exact sphere_block w j i

theorem sphere_injective (j : EmptyIndex w) : Function.Injective (sphere w j) := by
  intro i l he
  fin_cases i <;> fin_cases l
  all_goals first | rfl | (
    have hh := congrArg Finset.card he
    norm_num [sphere,top_eq_iff] at hh)
  all_goals
    have hh := congrArg (fun s => top j.val 0 ∈ s) he
    simp [sphere,top_eq_iff] at hh
  all_goals
    have hh := congrArg (fun s => top j.val 1 ∈ s) he
    simp [sphere,top_eq_iff] at hh
  all_goals
    have hh := congrArg (fun s => top j.val 2 ∈ s) he
    simp [sphere,top_eq_iff] at hh

/-- A genuine bijective cell enumeration, including repeated and empty relators. -/
theorem cellFace_injective : Function.Injective (cellFace w) := by
  intro a b he
  have hj : cellBlock w a = cellBlock w b := by
    have hh := congrArg blocks he
    rw [cell_block,cell_block] at hh
    have hh' := Finset.singleton_inj.mp hh
    exact Fin.ext (by omega)
  rcases a with ⟨t,j,i⟩ | ⟨j,i⟩ <;> rcases b with ⟨u,l,m⟩ | ⟨l,m⟩
  · change j = l at hj
    subst l
    fin_cases t <;> fin_cases u
    · have h := upper_injective w he; subst m; rfl
    · exact (upper_ne_wall w i m he).elim
    · exact (upper_ne_cap w i m he).elim
    · exact (upper_ne_wall w m i he.symm).elim
    · have h := wall_injective w he; subst m; rfl
    · exact (wall_ne_cap w i m he).elim
    · exact (upper_ne_cap w m i he.symm).elim
    · exact (wall_ne_cap w m i he.symm).elim
    · have h := cap_injective w he; subst m; rfl
  · change j = l.val at hj
    exact (position_nonempty w i (hj ▸ l.property)).elim
  · change j.val = l at hj
    exact (position_nonempty w m (hj ▸ j.property)).elim
  · change j.val = l.val at hj
    have hs : j = l := Subtype.ext hj
    subst l
    have h := sphere_injective w j he
    subst m
    rfl

def cellToFace (t : CellIndex w) : FaceOfCard (target w) 3 :=
  ⟨cellFace w t,cell_face w t,cell_card w t⟩

def cellFaceEquiv : CellIndex w ≃ FaceOfCard (target w) 3 := Equiv.ofBijective (cellToFace w) (by
  constructor
  · intro a b he
    exact cellFace_injective w (congrArg Subtype.val he)
  · rintro ⟨s,hs,hc⟩
    obtain ⟨f,he⟩ := triangle_exhaustive w s hs hc
    exact ⟨f,Subtype.ext he.symm⟩)

/-- Actual sorted triangles, not an invented cellular boundary type. -/
def triangleEquiv : Triangle (target w) ≃ CellIndex w :=
  (triangleFaceEquiv (target w)).trans (cellFaceEquiv w).symm


end D2RelationGap.ArbCells
