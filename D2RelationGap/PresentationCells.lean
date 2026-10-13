import D2RelationGap.PresentationRose

/-!
Actual privately tagged U/W/B collars and empty-word spheres on the checked rose.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
Original transport, finite relator contractions and degree-two Fox comparisons
are separate obligations; no geometric or relation-gap theorem is claimed.
-/
noncomputable section
namespace D2RelationGap.PresentationCells
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open PresentationRose

abbrev Ambient := ℕ ×ₗ ℕ
variable {k : ℕ} (w : Fin k → Word)

/-- Block zero is the ORIGINAL rose, not another graph. -/
def base (v : PresentationRose.Ambient) : Ambient := (0,v.val)
def center (j : Fin k) : Ambient := (j.val+1,0)
def top (j : Fin k) (i : ℕ) : Ambient := (j.val+1,i+1)

abbrev Position (j : Fin k) := Fin (3*(w j).length)
abbrev CollarIndex := Σ j : Fin k, Position w j
abbrev EmptyIndex := {j : Fin k // w j = []}
abbrev FacetIndex := (Gen × Fin 3) ⊕ ((Fin 3 × CollarIndex w) ⊕ (EmptyIndex w × Fin 4))

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

def bottom (j : Fin k) (i : ℕ) : PresentationRose.Ambient :=
  PolygonSource.node (wordPath (w j)) i

theorem bottom_zero (j : Fin k) : bottom w j 0 = 0 := PolygonSource.node_zero _
theorem bottom_end (j : Fin k) : bottom w j (3*(w j).length) = 0 := by
  simpa only [bottom,word_length] using PolygonSource.node_length (wordPath (w j))

theorem bottom_next {j : Fin k} (i : Position w j) :
    bottom w j (next w i).val = bottom w j (i.val+1) := by
  unfold next
  split_ifs with h
  · rfl
  · have hn : i.val+1 = 3*(w j).length := by have hi := i.isLt; omega
    simp only [hn,bottom_zero,bottom_end]

theorem bottom_edge {j : Fin k} (i : Position w j) :
    ({bottom w j i.val,bottom w j (next w i).val} : Finset PresentationRose.Ambient) ∈ rose := by
  rw [bottom_next]
  exact PolygonSource.node_consecutive_face (wordPath (w j)) i.val (by rw [word_length]; exact i.isLt)

theorem bottom_distinct {j : Fin k} (i : Position w j) :
    bottom w j i.val ≠ bottom w j (next w i).val := by
  rw [bottom_next]
  exact node_distinct (wordPath (w j)) (word_noncollapsed _) i.val (by rw [word_length]; exact i.isLt)

@[simp] theorem base_injective : Function.Injective base := by
  intro x y h
  apply Fin.ext
  exact congrArg (fun z : Ambient => z.2) h

@[simp] theorem base_ne_top (v : PresentationRose.Ambient) (j : Fin k) (i : ℕ) : base v ≠ top j i := by
  intro h; have hh := congrArg (fun z : Ambient => z.1) h; simp [base,top] at hh
@[simp] theorem base_ne_center (v : PresentationRose.Ambient) (j : Fin k) : base v ≠ center j := by
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

def facet : FacetIndex w → Finset Ambient
  | .inl (g,i) => (petal g i).image base
  | .inr (.inl (t,⟨_j,i⟩)) => match t with | 0 => upper w i | 1 => wall w i | 2 => cap w i
  | .inr (.inr (j,i)) => sphere w j i

def target : PreAbstractSimplicialComplex Ambient where
  faces := {s | s.Nonempty ∧ ∃ f : FacetIndex w, s ⊆ facet w f}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨f,hf⟩ := hs.2
    exact ⟨ht,f,hts.trans hf⟩

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

theorem facet_nonempty (f : FacetIndex w) : (facet w f).Nonempty := by
  rcases f with ⟨g,i⟩ | (⟨t,j,i⟩ | ⟨j,i⟩)
  · exact (petal_face g i).1.image _
  · fin_cases t <;> exact Finset.insert_nonempty _ _
  · fin_cases i <;> exact Finset.insert_nonempty _ _

theorem facet_face (f : FacetIndex w) : facet w f ∈ target w :=
  ⟨facet_nonempty w f,f,Finset.Subset.refl _⟩

theorem facet_card_le (f : FacetIndex w) : (facet w f).card ≤ 3 := by
  rcases f with ⟨g,i⟩ | (⟨t,j,i⟩ | ⟨j,i⟩)
  · apply (Finset.card_image_le).trans
    fin_cases i <;> cases g <;> decide
  · fin_cases t
    · exact (upper_card w i).le
    · exact (wall_card w i).le
    · exact (cap_card w i).le
  · exact (sphere_card w j i).le

theorem dimension (s : Finset Ambient) (hs : s ∈ target w) : s.card ≤ 3 := by
  obtain ⟨f,hf⟩ := hs.2
  exact (Finset.card_le_card hf).trans (facet_card_le w f)

/-- Every actual three-vertex face is a displayed collar/cap/sphere cell.
This is exhaustiveness, not yet an injective basis reindexing. -/
theorem triangle_exhaustive (s : Finset Ambient) (hs : s ∈ target w) (hc : s.card = 3) :
    (∃ (j : Fin k) (i : Position w j), s = upper w i ∨ s = wall w i ∨ s = cap w i) ∨
    ∃ (j : EmptyIndex w) (i : Fin 4), s = sphere w j i := by
  obtain ⟨f,hf⟩ := hs.2
  have he : s = facet w f := Finset.eq_of_subset_of_card_le hf (by rw [hc]; exact facet_card_le w f)
  rcases f with ⟨g,i⟩ | (⟨t,j,i⟩ | ⟨j,i⟩)
  · have hh : ((petal g i).image base).card ≤ 2 :=
      Finset.card_image_le.trans (dimension_at_most_one _ (petal_face g i))
    change s = (petal g i).image base at he
    rw [← he,hc] at hh; omega
  · left; refine ⟨j,i,?_⟩
    fin_cases t
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  · exact Or.inr ⟨j,i,he⟩

/-- Literal finite support even though the tagged ambient type is infinite. -/
def support : Finset Ambient := Finset.univ.biUnion (facet w)

theorem active_iff (x : Ambient) : ({x} : Finset Ambient) ∈ target w ↔ x ∈ support w := by
  change ({x} : Finset Ambient).Nonempty ∧ (∃ f, {x} ⊆ facet w f) ↔ x ∈ support w
  simp [support,Finset.mem_biUnion]

def vertexEquiv : Vertex (target w) ≃ {x // x ∈ support w} where
  toFun x := ⟨x.val,(active_iff w x.val).mp x.property⟩
  invFun x := ⟨x.val,(active_iff w x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance finiteVertices : Finite (Vertex (target w)) := Finite.of_equiv _ (vertexEquiv w).symm
instance finiteEdges : Finite (Edge (target w)) := LiftedImageStep.edges_finite (target w)
instance finiteTriangles : Finite (Triangle (target w)) := LiftedImageStep.triangles_finite (target w)

/-- The actual original rose embeds facewise, retaining its raw path conventions. -/
theorem base_face (s : Finset PresentationRose.Ambient) (hs : s ∈ rose) : s.image base ∈ target w := by
  obtain ⟨g,i,hi⟩ := hs.2
  exact ⟨hs.1.image _,Sum.inl (g,i),Finset.image_subset_image hi⟩


theorem baseMap : rose.map base ≤ target w := by
  rintro s ⟨t,ht,rfl⟩
  exact base_face w t ht

theorem upper_face {j : Fin k} (i : Position w j) : upper w i ∈ target w :=
  facet_face w (.inr (.inl (0,⟨j,i⟩)))
theorem wall_face {j : Fin k} (i : Position w j) : wall w i ∈ target w :=
  facet_face w (.inr (.inl (1,⟨j,i⟩)))
theorem cap_face {j : Fin k} (i : Position w j) : cap w i ∈ target w :=
  facet_face w (.inr (.inl (2,⟨j,i⟩)))
theorem sphere_face (j : EmptyIndex w) (i : Fin 4) : sphere w j i ∈ target w :=
  facet_face w (.inr (.inr (j,i)))

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

def root : Vertex (target w) := ⟨base 0,by simpa using base_face w {0} (singleton_face 0)⟩

def basePath (v : PresentationRose.Ambient) : Path (target w) (base 0) (base v) :=
  mapPath base (baseMap w) (PresentationRose.rootPaths ⟨v,singleton_face v⟩)

def topPath {j : Fin k} (i : Position w j) : Path (target w) (base 0) (top j i.val) :=
  append (basePath w (bottom w j i.val))
    (single (by simpa [Finset.pair_comm] using vertical_face w i))

def centerPath {j : Fin k} (i : Position w j) : Path (target w) (base 0) (center j) :=
  append (topPath w i) (single (by simpa [Finset.pair_comm] using radial_face w i))

def spherePath (j : EmptyIndex w) (i : Fin 3) : Path (target w) (base 0) (top j.val i.val) :=
  single (sphere_edge w j i)

/-- Root paths are built from real facet edges, never from ambient finiteness. -/
theorem reachable (x : Vertex (target w)) : Nonempty (Path (target w) (base 0) x.val) := by
  obtain ⟨f,hf⟩ := x.property.2
  have hx : x.val ∈ facet w f := hf (by simp)
  rcases f with ⟨g,i⟩ | (⟨t,j,i⟩ | ⟨j,i⟩)
  · obtain ⟨v,_,he⟩ := Finset.mem_image.mp hx
    rw [← he]
    exact ⟨basePath w v⟩
  · fin_cases t
    · simp only [facet,upper,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact ⟨topPath w i⟩
      · rw [h]; exact ⟨topPath w (next w i)⟩
      · rw [h]; exact ⟨basePath w _⟩
    · simp only [facet,wall,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact ⟨topPath w i⟩
      · rw [h]; exact ⟨basePath w _⟩
      · rw [h]; exact ⟨basePath w _⟩
    · simp only [facet,cap,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · rw [h]; exact ⟨centerPath w i⟩
      · rw [h]; exact ⟨topPath w i⟩
      · rw [h]; exact ⟨topPath w (next w i)⟩
  · fin_cases i <;> simp only [facet,sphere,Finset.mem_insert,Finset.mem_singleton] at hx
    all_goals rcases hx with h | h | h
    all_goals rw [h]
    all_goals first | exact ⟨spherePath w j 0⟩ | exact ⟨spherePath w j 1⟩ |
      exact ⟨spherePath w j 2⟩ | exact ⟨basePath w 0⟩

def rootPaths (x : Vertex (target w)) : Path (target w) (root w).val x.val :=
  Classical.choice (reachable w x)

/-- Old raw-word paths include into this SAME target without any word reduction. -/
def mappedWord (j : Fin k) : Path (target w) (base 0) (base 0) :=
  mapPath base (baseMap w) (wordPath (w j))


/-- There are n top vertices plus one center, or three private sphere vertices. -/
def privateSupport (j : Fin k) : Finset Ambient :=
  if w j = [] then (Finset.range 3).image (top j)
  else insert (center j) ((Finset.range (3*(w j).length)).image (top j))
def palette : Finset Ambient :=
  Finset.univ.image base ∪ Finset.univ.biUnion (privateSupport w)

theorem private_tag (j : Fin k) (x : Ambient) (hx : x ∈ privateSupport w j) : x.1 = j.val+1 := by
  unfold privateSupport at hx
  split_ifs at hx with h
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; rfl
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · rfl
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; rfl

theorem position_nonempty {j : Fin k} (i : Position w j) : w j ≠ [] := by
  intro h
  have hi := i.isLt
  simp [h] at hi

theorem base_mem_palette (v : PresentationRose.Ambient) : base v ∈ palette w := by
  simp [palette]
theorem private_mem_palette (j : Fin k) (x : Ambient) (hx : x ∈ privateSupport w j) : x ∈ palette w := by
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hx⟩)
theorem top_mem_private {j : Fin k} (i : Position w j) : top j i.val ∈ privateSupport w j := by
  simp only [privateSupport,ite_eq_right (position_nonempty w i),Finset.mem_insert]
  exact Or.inr (Finset.mem_image.mpr ⟨i.val,Finset.mem_range.mpr i.isLt,rfl⟩)
theorem center_mem_private {j : Fin k} (i : Position w j) : center j ∈ privateSupport w j := by
  simp [privateSupport,position_nonempty w i]
theorem sphere_mem_private (j : EmptyIndex w) (i : Fin 3) : top j.val i.val ∈ privateSupport w j.val := by
  simp only [privateSupport,ite_eq_left j.property]
  exact Finset.mem_image.mpr ⟨i.val,Finset.mem_range.mpr i.isLt,rfl⟩

theorem facet_subset_palette (f : FacetIndex w) : facet w f ⊆ palette w := by
  intro x hx
  rcases f with ⟨g,i⟩ | (⟨t,j,i⟩ | ⟨j,i⟩)
  · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact base_mem_palette w v
  · fin_cases t <;> simp only [facet,upper,wall,cap,Finset.mem_insert,Finset.mem_singleton] at hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact base_mem_palette w _ |
      exact private_mem_palette w _ _ (top_mem_private w i) |
      exact private_mem_palette w _ _ (top_mem_private w (next w i)) |
      exact private_mem_palette w _ _ (center_mem_private w i)
  · fin_cases i <;> simp only [facet,sphere,Finset.mem_insert,Finset.mem_singleton] at hx
    all_goals rcases hx with rfl | rfl | rfl
    all_goals first | exact base_mem_palette w _ |
      exact private_mem_palette w _ _ (sphere_mem_private w j 0) |
      exact private_mem_palette w _ _ (sphere_mem_private w j 1) |
      exact private_mem_palette w _ _ (sphere_mem_private w j 2)

theorem palette_active (x : Ambient) (hx : x ∈ palette w) : ({x} : Finset Ambient) ∈ target w := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    simpa using base_face w {v} (singleton_face v)
  · obtain ⟨j,_,hx⟩ := Finset.mem_biUnion.mp hx
    unfold privateSupport at hx
    split_ifs at hx with he
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact vertex_mem_of_face (target w) _ (sphere_edge w ⟨j,he⟩ ⟨i,Finset.mem_range.mp hi⟩) _ (by simp)
    · have hn : 0 < 3*(w j).length := by have hh := List.length_pos_iff_ne_nil.mpr he; omega
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact vertex_mem_of_face (target w) _ (cap_face w (⟨0,hn⟩ : Position w j)) _ (by simp [cap])
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        exact vertex_mem_of_face (target w) _ (cap_face w (⟨i,Finset.mem_range.mp hi⟩ : Position w j)) _ (by simp [cap])

theorem support_eq_palette : support w = palette w := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨f,_,hf⟩ := Finset.mem_biUnion.mp hx
    exact facet_subset_palette w f hf
  · intro x hx
    exact (active_iff w x).mp (palette_active w x hx)

theorem private_card (j : Fin k) : (privateSupport w j).card =
    if w j = [] then 3 else 3*(w j).length+1 := by
  have hin : Function.Injective (top j) := fun i m h => ((top_eq_iff j j i m).mp h).2
  have hn : center j ∉ (Finset.range (3*(w j).length)).image (top j) := by
    simp only [Finset.mem_image]; rintro ⟨i,_,he⟩; exact center_ne_top j j i he.symm
  unfold privateSupport
  split_ifs with h
  · rw [Finset.card_image_of_injective _ hin,Finset.card_range]
  · rw [Finset.card_insert_of_notMem hn,Finset.card_image_of_injective _ hin,Finset.card_range]

theorem private_disjoint (j l : Fin k) (h : j ≠ l) : Disjoint (privateSupport w j) (privateSupport w l) := by
  apply Finset.disjoint_left.mpr
  intro x hj hl
  apply h
  exact Fin.ext (by have hh := (private_tag w j x hj).symm.trans (private_tag w l x hl); omega)

theorem rose_private_disjoint : Disjoint (Finset.univ.image base) (Finset.univ.biUnion (privateSupport w)) := by
  apply Finset.disjoint_left.mpr
  intro x hr hp
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  have hh := private_tag w j (base v) hj
  simp [base] at hh

theorem active_count : Nat.card (Vertex (target w)) =
    11 + ∑ j : Fin k, if w j = [] then 3 else 3*(w j).length+1 := by
  rw [Nat.card_congr (vertexEquiv w),Nat.card_eq_fintype_card,Fintype.card_coe,
    support_eq_palette,palette,Finset.card_union_of_disjoint (rose_private_disjoint w),
    Finset.card_image_of_injective _ base_injective]
  rw [Finset.card_biUnion (fun j _ l _ hjl => private_disjoint w j l hjl)]
  simp only [Finset.card_univ,Fintype.card_fin,private_card]

/-- Repeated words still have different private cells because list indices persist. -/
theorem repeated_block_collision_rejected (j l : Fin k) (h : j ≠ l) (i m : ℕ) : top j i ≠ top l m :=
  fun he => h ((top_eq_iff j l i m).mp he).1

/-- An empty relator keeps its sphere; it has no collar center. -/
theorem empty_center_rejected (j : Fin k) (he : w j = []) : ({center j} : Finset Ambient) ∉ target w := by
  intro hc
  have hp : center j ∈ palette w := by rw [← support_eq_palette]; exact (active_iff w _).mp hc
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hp
    exact base_ne_center v j hv
  · obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp hp
    have hjl : j = l := Fin.ext (by have hh := private_tag w l (center j) hl; change j.val+1 = l.val+1 at hh; omega)
    subst l
    simp only [privateSupport,ite_eq_left he,Finset.mem_image] at hl
    obtain ⟨i,_,hi⟩ := hl
    exact center_ne_top j j i hi.symm

/-- No relators means the actual target still has no triangles. -/
theorem no_relators_no_triangles (w : Fin 0 → Word) : IsEmpty (Triangle (target w)) := ⟨fun t => by
  have hh := triangle_exhaustive w _ t.face (triangleFace_card t)
  rcases hh with ⟨j,_,_⟩ | ⟨j,_,_⟩
  · exact Fin.elim0 j
  · exact Fin.elim0 j.val⟩


@[simp] theorem top_ne_base (j : Fin k) (i : ℕ) (v : PresentationRose.Ambient) : top j i ≠ base v :=
  (base_ne_top v j i).symm
@[simp] theorem top_ne_center (j l : Fin k) (i : ℕ) : top j i ≠ center l :=
  (center_ne_top l j i).symm
@[simp] theorem center_ne_base (j : Fin k) (v : PresentationRose.Ambient) : center j ≠ base v :=
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


abbrev CellIndex := (Fin 3 × CollarIndex w) ⊕ (EmptyIndex w × Fin 4)
def cellFace (t : CellIndex w) : Finset Ambient := facet w (.inr t)
def cellBlock : CellIndex w → Fin k
  | .inl (_,⟨j,_⟩) => j
  | .inr (j,_) => j.val

theorem cell_face (t : CellIndex w) : cellFace w t ∈ target w := facet_face w (.inr t)
theorem cell_card (t : CellIndex w) : (cellFace w t).card = 3 := by
  rcases t with ⟨t,_j,i⟩ | ⟨j,i⟩
  · fin_cases t
    · exact upper_card w i
    · exact wall_card w i
    · exact cap_card w i
  · exact sphere_card w j i

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
    rcases triangle_exhaustive w s hs hc with ⟨j,i,he | he | he⟩ | ⟨j,i,he⟩
    · exact ⟨.inl (0,⟨j,i⟩),Subtype.ext he.symm⟩
    · exact ⟨.inl (1,⟨j,i⟩),Subtype.ext he.symm⟩
    · exact ⟨.inl (2,⟨j,i⟩),Subtype.ext he.symm⟩
    · exact ⟨.inr (j,i),Subtype.ext he.symm⟩)

/-- Actual sorted triangles, not an invented cellular boundary type. -/
def triangleEquiv : Triangle (target w) ≃ CellIndex w :=
  (triangleFaceEquiv (target w)).trans (cellFaceEquiv w).symm

theorem triangle_count : Nat.card (Triangle (target w)) =
    9*(∑ j : Fin k, (w j).length) + 4*Nat.card (EmptyIndex w) := by
  rw [Nat.card_congr (triangleEquiv w),Nat.card_eq_fintype_card]
  simp only [CellIndex,Fintype.card_sum,Fintype.card_prod,CollarIndex,Fintype.card_sigma,
    Position,Fintype.card_fin]
  rw [← Nat.card_eq_fintype_card (α := EmptyIndex w),← Finset.mul_sum]
  omega

/-- A nonempty word has no extra top vertex past its cyclic boundary. -/
theorem unused_top_rejected (j : Fin k) (hw : w j ≠ []) :
    ({top j (3*(w j).length)} : Finset Ambient) ∉ target w := by
  intro hc
  have hp : top j (3*(w j).length) ∈ palette w := by
    rw [← support_eq_palette]; exact (active_iff w _).mp hc
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hp
    exact base_ne_top v j _ hv
  · obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp hp
    have hjl : j = l := Fin.ext (by have hh := private_tag w l _ hl; change j.val+1 = l.val+1 at hh; omega)
    subst l
    simp only [privateSupport,ite_eq_right hw,Finset.mem_insert,Finset.mem_image] at hl
    rcases hl with h | ⟨i,hi,he⟩
    · exact top_ne_center j j _ h
    · have hn := ((top_eq_iff j j _ _).mp he).2
      have hi' := Finset.mem_range.mp hi
      omega

theorem length_map {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    (f : V → Ambient) (hf : A.map f ≤ target w) {u v : V} (p : Path A u v) :
    PolygonSource.length (mapPath f hf p) = PolygonSource.length p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp only [mapPath,PolygonSource.length,ih]

theorem mappedWord_length (j : Fin k) : PolygonSource.length (mappedWord w j) = 3*(w j).length := by
  rw [mappedWord,length_map,word_length]

theorem raw_cancel_kept :
    PolygonSource.length (mappedWord (fun _ : Fin 1 => [pos .x1,neg .x1]) 0) = 6 := by
  rw [mappedWord_length]; rfl


/-- Removing the empty-word sphere loses an actual sorted triangle. -/
theorem empty_sphere_dropped_rejected :
    ¬ IsEmpty (Triangle (target (fun _ : Fin 1 => ([] : Word)))) := by
  intro h
  exact h.false ((triangleEquiv (fun _ : Fin 1 => ([] : Word))).symm (.inr (⟨0,rfl⟩,0)))

theorem raw_cancel_reduction_rejected :
    PolygonSource.length (mappedWord (fun _ : Fin 1 => [pos .x1,neg .x1]) 0) ≠ 0 := by
  rw [raw_cancel_kept]
  decide

end D2RelationGap.PresentationCells
