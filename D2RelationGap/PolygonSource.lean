import D2RelationGap.TriangleAttachment

/-!
Finite polygon sources and ordinary rational cycle spans.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Joint source/move-strip/cap and original-character/geometric
adequacy remain open; no relation-gap or universal geometric theorem is asserted.
-/
noncomputable section
namespace D2RelationGap.PolygonSource
open OrientedSimplices SimplicialTransport IntegerHeights EdgePaths BasedLoops TriangleAttachment
variable {V : Type*} [LinearOrder V]

def augmentation (A : PreAbstractSimplicialComplex V) : (Vertex A →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun _ => (1 : ℚ))

theorem augmentation_boundary (A : PreAbstractSimplicialComplex V) :
    (augmentation A).comp (ordinaryOne A) = 0 := by
  apply Finsupp.lhom_ext
  intro e c
  simp [augmentation,ordinaryOne,boundaryOne,VoltageChains.baseOne,incidence]

def rootedSection (A : PreAbstractSimplicialComplex V) (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val) :
    (Vertex A →₀ ℚ) →ₗ[ℚ] Edge A →₀ ℚ :=
  Finsupp.linearCombination ℚ (fun x => PathChains.chain (PathChains.trivialTransport A) (paths x))

theorem rooted_section_boundary (A : PreAbstractSimplicialComplex V) (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val) (z : Vertex A →₀ ℚ) :
    ordinaryOne A (rootedSection A r paths z) = z - augmentation A z • point r.val r.property := by
  have hh : (ordinaryOne A).comp (rootedSection A r paths) =
      LinearMap.id - (LinearMap.toSpanSingleton ℚ (Vertex A →₀ ℚ) (point r.val r.property)).comp (augmentation A) := by
    apply Finsupp.lhom_ext
    intro x c
    simp only [LinearMap.comp_apply,rootedSection,Finsupp.linearCombination_single,map_smul]
    have h := PathChains.chain_boundary (PathChains.trivialTransport (K := ℚ) A) (paths x)
    rw [ordinary_coeff,trivial_value,Units.val_one,one_smul] at h
    change ordinaryOne A (PathChains.chain (PathChains.trivialTransport A) (paths x)) =
      point x.val x.property - point r.val r.property at h
    simp [h,augmentation,LinearMap.toSpanSingleton,point,smul_sub]
  exact LinearMap.congr_fun hh z

theorem ordinary_range_eq_augmentation_kernel (A : PreAbstractSimplicialComplex V) (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val) :
    (ordinaryOne A).range = (augmentation A).ker := by
  apply le_antisymm
  · rintro z ⟨e,rfl⟩
    exact LinearMap.congr_fun (augmentation_boundary A) e
  · intro z hz
    refine ⟨rootedSection A r paths z,?_⟩
    simpa [show augmentation A z = 0 from hz] using rooted_section_boundary A r paths z

omit [LinearOrder V] in
theorem augmentation_surjective (A : PreAbstractSimplicialComplex V) (r : Vertex A) :
    Function.Surjective (augmentation A) := by
  intro c
  exact ⟨Finsupp.single r c,by simp [augmentation]⟩

/-- Connected actual finite chains with equally many edges and vertices have a
one-dimensional ordinary cycle space; no spanning tree is assumed. -/
theorem cycle_kernel_finrank_one (A : PreAbstractSimplicialComplex V)
    [Fintype (Vertex A)] [Fintype (Edge A)] (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val)
    (hcount : Fintype.card (Edge A) = Fintype.card (Vertex A)) :
    Module.finrank ℚ (ordinaryOne A).ker = 1 := by
  have ha := (augmentation A).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (augmentation_surjective A r),finrank_top,Module.finrank_self,
    Module.finrank_finsupp_self] at ha
  have hb := (ordinaryOne A).finrank_range_add_finrank_ker
  rw [ordinary_range_eq_augmentation_kernel A r paths,Module.finrank_finsupp_self] at hb
  omega

theorem cycle_span_of_counts (A : PreAbstractSimplicialComplex V)
    [Fintype (Vertex A)] [Fintype (Edge A)] (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val)
    (hcount : Fintype.card (Edge A) = Fintype.card (Vertex A))
    (g : Edge A →₀ ℚ) (hg : ordinaryOne A g = 0) (hne : g ≠ 0) : CycleSpan A g := by
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    (cycle_kernel_finrank_one A r paths hcount) (show g ∈ (ordinaryOne A).ker from hg) hne
  intro z hz
  have hm : z ∈ Submodule.span ℚ {g} := by rw [← hspan]; exact hz
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨c,0,by simpa using hc.symm⟩

abbrev Index (n : ℕ) := Fin (n+3)
def next (n : ℕ) (i : Index n) : Index n :=
  if h : i.val+1 < n+3 then ⟨i.val+1,h⟩ else 0

theorem next_ne (n : ℕ) (i : Index n) : next n i ≠ i := by
  unfold next
  split_ifs with h
  · intro he; have hh := congrArg Fin.val he; simp only at hh; omega
  · intro he; have hh := congrArg Fin.val he; simp only [Fin.val_zero] at hh; omega

def polygon (n : ℕ) : PreAbstractSimplicialComplex (Index n) where
  faces := {s | s.Nonempty ∧ ∃ i : Index n, s ⊆ {i,next n i}}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨i,hi⟩ := hs.2
    exact ⟨ht,i,hts.trans hi⟩

theorem pair_face (n : ℕ) (i : Index n) : ({i,next n i} : Finset (Index n)) ∈ polygon n :=
  ⟨Finset.insert_nonempty _ _,i,Finset.Subset.refl _⟩

theorem singleton_face (n : ℕ) (i : Index n) : ({i} : Finset (Index n)) ∈ polygon n :=
  ⟨Finset.singleton_nonempty _,i,by simp⟩

def vertexEquiv (n : ℕ) : Vertex (polygon n) ≃ Index n where
  toFun := Subtype.val
  invFun i := ⟨i,singleton_face n i⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vertex_count (n : ℕ) : Nat.card (Vertex (polygon n)) = n+3 := by
  rw [Nat.card_congr (vertexEquiv n),Nat.card_fin]

def cell (n : ℕ) (i : Index n) : Edge (polygon n) :=
  if h : i.val+1 < n+3 then ⟨i,⟨i.val+1,h⟩,by change i.val < i.val+1; omega,by simpa only [next,dite_eq_left h] using pair_face n i⟩
  else ⟨0,i,by have hh := i.isLt; change 0 < i.val; omega,
    by simpa only [next,dite_eq_right h,Finset.pair_comm] using pair_face n i⟩

def cellIndex (n : ℕ) (e : Edge (polygon n)) : Index n :=
  if e.src = 0 ∧ e.dst.val = n+2 then e.dst else e.src

theorem cellIndex_cell (n : ℕ) (i : Index n) : cellIndex n (cell n i) = i := by
  unfold cellIndex cell
  split_ifs with h h0 h0
  · have hi0 : i.val = 0 := congrArg Fin.val h0.1
    have hval := h0.2
    simp only at hi0 hval
    omega
  · rfl
  · rfl
  · have hh : i.val = n+2 := by omega
    exact (h0 ⟨rfl,hh⟩).elim

theorem cell_surjective (n : ℕ) : Function.Surjective (cell n) := by
  intro e
  obtain ⟨i,hi⟩ := e.face.2
  have hs : e.src = i ∨ e.src = next n i := by simpa using hi (by simp)
  have hd : e.dst = i ∨ e.dst = next n i := by simpa using hi (by simp)
  refine ⟨i,?_⟩
  rcases hs with hs | hs <;> rcases hd with hd | hd
  · exact (e.ordered.ne (hs.trans hd.symm)).elim
  · by_cases h : i.val+1 < n+3
    · rw [cell,dite_eq_left h]
      simp only [next,dite_eq_left h] at hd
      exact Edge.ext hs.symm hd.symm
    · simp only [next,dite_eq_right h] at hd
      have he := e.ordered
      rw [hs,hd] at he
      have hh := i.isLt
      change i.val < 0 at he
      omega
  · by_cases h : i.val+1 < n+3
    · simp only [next,dite_eq_left h] at hs
      have he := e.ordered
      rw [hs,hd] at he
      change i.val+1 < i.val at he
      omega
    · rw [cell,dite_eq_right h]
      simp only [next,dite_eq_right h] at hs
      exact Edge.ext hs.symm hd.symm
  · exact (e.ordered.ne (hs.trans hd.symm)).elim

def edgeEquiv (n : ℕ) : Edge (polygon n) ≃ Index n :=
  (Equiv.ofBijective (cell n) ⟨Function.LeftInverse.injective (cellIndex_cell n),cell_surjective n⟩).symm

theorem edge_count (n : ℕ) : Nat.card (Edge (polygon n)) = n+3 := by
  rw [Nat.card_congr (edgeEquiv n),Nat.card_fin]

theorem face_card_le_two (n : ℕ) (s : Finset (Index n)) (hs : s ∈ polygon n) : s.card ≤ 2 := by
  obtain ⟨i,hi⟩ := hs.2
  exact (Finset.card_le_card hi).trans Finset.card_le_two

theorem triangles_empty (n : ℕ) : IsEmpty (Triangle (polygon n)) :=
  ⟨fun t => by
    have h := face_card_le_two n _ t.face
    have hc := triangleFace_card t
    change ({t.v0,t.v1,t.v2} : Finset (Index n)).card = 3 at hc
    omega⟩



abbrev last (n : ℕ) : Index n := ⟨n+2,by omega⟩
abbrev base (n : ℕ) : Vertex (polygon n) := ⟨0,singleton_face n 0⟩

theorem consecutive_face (n k : ℕ) (hk : k+1 < n+3) :
    ({(⟨k,by omega⟩ : Index n),⟨k+1,hk⟩} : Finset (Index n)) ∈ polygon n := by
  simpa only [next,dite_eq_left hk] using pair_face n (⟨k,by omega⟩ : Index n)

def down (n : ℕ) : (k : ℕ) → (hk : k < n+3) → Path (polygon n) ⟨k,hk⟩ 0
  | 0,_ => .refl 0 (singleton_face n 0)
  | k+1,hk => .cons (v := (⟨k,by omega⟩ : Index n))
      (by simpa only [Finset.pair_comm] using consecutive_face n k hk) (down n k (by omega))

def rootPaths (n : ℕ) (x : Vertex (polygon n)) : Path (polygon n) 0 x.val :=
  reverse (down n x.val.val x.val.isLt)

theorem consecutive_chain (n k : ℕ) (hk : k+1 < n+3) :
    SourceExpansion.oedge (polygon n) (⟨k,by omega⟩ : Index n) ⟨k+1,hk⟩ (consecutive_face n k hk) =
      Finsupp.single (cell n ⟨k,by omega⟩) 1 := by
  have hlt : (⟨k,by omega⟩ : Index n) < ⟨k+1,hk⟩ := by change k < k+1; omega
  simp only [SourceExpansion.oedge,edge,dite_eq_left hlt,cell,dite_eq_left hk]

theorem cell_ne_last (n k : ℕ) (hk : k+1 < n+3) : cell n ⟨k,by omega⟩ ≠ cell n (last n) := by
  intro he
  have hh := congrArg (cellIndex n) he
  rw [cellIndex_cell,cellIndex_cell] at hh
  have hv := congrArg Fin.val hh
  change k = n+2 at hv
  omega

theorem down_chain_last_zero (n k : ℕ) (hk : k < n+3) :
    PathChains.chain (PathChains.trivialTransport (K := ℚ) (polygon n)) (down n k hk) (cell n (last n)) = 0 := by
  induction k with
  | zero => simp [down,PathChains.chain]
  | succ k ih =>
    simp only [down,PathChains.chain,ordinary_coeff,one_smul,Finsupp.add_apply,ih,add_zero]
    have hh := edge_reverse (PathChains.trivialTransport (K := ℚ) (polygon n))
      (⟨k,by omega⟩ : Index n) ⟨k+1,hk⟩ (consecutive_face n k hk)
    rw [ordinary_coeff,one_smul] at hh
    change SourceExpansion.oedge (polygon n) ⟨k+1,hk⟩ (⟨k,by omega⟩ : Index n) _ =
      -SourceExpansion.oedge (polygon n) (⟨k,by omega⟩ : Index n) ⟨k+1,hk⟩ _ at hh
    rw [consecutive_chain n k hk] at hh
    change (SourceExpansion.oedge (polygon n) ⟨k+1,hk⟩ (⟨k,by omega⟩ : Index n) _) (cell n (last n)) = 0
    rw [hh]
    simp [cell_ne_last n k hk]

theorem closing_face (n : ℕ) : ({0,last n} : Finset (Index n)) ∈ polygon n := by
  simpa [next,last,Finset.pair_comm] using pair_face n (last n)

def loop (n : ℕ) : Path (polygon n) 0 0 := .cons (closing_face n) (down n (n+2) (by omega))
def generator (n : ℕ) : Edge (polygon n) →₀ ℚ :=
  PathChains.chain (PathChains.trivialTransport (polygon n)) (loop n)

theorem generator_last_coeff (n : ℕ) : generator n (cell n (last n)) = 1 := by
  have hlt : (0 : Index n) < last n := by change 0 < n+2; omega
  have he : SourceExpansion.oedge (polygon n) 0 (last n) (closing_face n) = Finsupp.single (cell n (last n)) 1 := by
    simp [SourceExpansion.oedge,edge,hlt,cell,last]
  rw [generator,loop,PathChains.chain,ordinary_coeff,one_smul]
  change ((SourceExpansion.oedge (polygon n) 0 (last n) (closing_face n) +
    PathChains.chain (PathChains.trivialTransport (K := ℚ) (polygon n)) (down n (n+2) (by omega))) :
      Edge (polygon n) →₀ ℚ) (cell n (last n)) = 1
  rw [he,Finsupp.add_apply,down_chain_last_zero]
  simp

theorem generator_nonzero (n : ℕ) : generator n ≠ 0 := by
  intro he
  have hh := congrArg (fun z : Edge (polygon n) →₀ ℚ => z (cell n (last n))) he
  rw [generator_last_coeff] at hh
  norm_num at hh

theorem generator_cycle (n : ℕ) : ordinaryOne (polygon n) (generator n) = 0 := by
  have hh := ordinary_chain_boundary (loop n)
  simpa [generator] using hh

theorem generator_cycle_span (n : ℕ) : CycleSpan (polygon n) (generator n) := by
  let := Fintype.ofFinite (Vertex (polygon n))
  let := LiftedImageStep.edges_finite (polygon n)
  let := Fintype.ofFinite (Edge (polygon n))
  have hc : Fintype.card (Edge (polygon n)) = Fintype.card (Vertex (polygon n)) := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,edge_count,vertex_count]
  exact cycle_span_of_counts (polygon n) (base n) (rootPaths n) hc (generator n) (generator_cycle n) (generator_nonzero n)

theorem zero_generator_span_rejected (n : ℕ) : ¬ CycleSpan (polygon n) 0 := by
  let := triangles_empty n
  intro hs
  obtain ⟨c,b,hb⟩ := hs (generator n) (generator_cycle n)
  have hb0 : b = 0 := Subsingleton.elim _ _
  exact generator_nonzero n (by simpa [hb0] using hb)



section Trace
variable {A : PreAbstractSimplicialComplex V}

def length {u v : V} : Path A u v → ℕ
  | .refl _ _ => 0
  | .cons _ p => length p+1

def node {u v : V} : Path A u v → ℕ → V
  | .refl u _,_ => u
  | @Path.cons _ _ _ u _ _ _ _,0 => u
  | .cons _ p,k+1 => node p k

theorem node_zero {u v : V} (p : Path A u v) : node p 0 = u := by cases p <;> rfl

theorem node_length {u v : V} (p : Path A u v) : node p (length p) = v := by
  induction p with
  | refl => rfl
  | cons h p ih => exact ih

theorem node_consecutive_face {u v : V} (p : Path A u v) (k : ℕ) (hk : k < length p) :
    ({node p k,node p (k+1)} : Finset V) ∈ A := by
  induction p generalizing k with
  | refl => simp only [length] at hk; omega
  | cons h p ih =>
    cases k with
    | zero => simpa only [node,node_zero] using h
    | succ k => exact ih k (by simp only [length] at hk; omega)

/-- Two repeated initial positions and the terminal root give at least three
source vertices even for an empty/stuttering target loop. -/
def label {r : V} (p : Path A r r) (k : ℕ) : V :=
  if k < 2 then r else node p (k-2)
def labels {r : V} (p : Path A r r) (i : Index (length p)) : V := label p i.val

theorem label_zero {r : V} (p : Path A r r) : label p 0 = r := by simp [label]
theorem label_one {r : V} (p : Path A r r) : label p 1 = r := by simp [label]
theorem label_shift {r : V} (p : Path A r r) (k : ℕ) : label p (k+2) = node p k := by simp [label]
theorem label_last {r : V} (p : Path A r r) : label p (length p+2) = r := by
  rw [label_shift,node_length]

theorem label_consecutive_face {r : V} (p : Path A r r) (k : ℕ) (hk : k < length p+2) :
    ({label p k,label p (k+1)} : Finset V) ∈ A := by
  by_cases h0 : k = 0
  · subst k; simpa [label,node_zero] using startActive p
  by_cases h1 : k = 1
  · subst k
    simpa [label,node_zero] using startActive p
  obtain ⟨j,rfl⟩ : ∃ j, k = j+2 := ⟨k-2,by omega⟩
  have he : j+2+1 = (j+1)+2 := by omega
  rw [he,label_shift,label_shift]
  exact node_consecutive_face p j (by omega)

theorem labels_next_face {r : V} (p : Path A r r) (i : Index (length p)) :
    ({labels p i,labels p (next (length p) i)} : Finset V) ∈ A := by
  by_cases h : i.val+1 < length p+3
  · simpa only [labels,next,dite_eq_left h] using label_consecutive_face p i.val (by omega)
  · have hi : i.val = length p+2 := by have hh := i.isLt; omega
    change ({label p i.val,label p (next (length p) i).val} : Finset V) ∈ A
    rw [next,dite_eq_right h]
    change ({label p i.val,label p 0} : Finset V) ∈ A
    rw [hi,label_last,label_zero]
    simpa using startActive p

theorem labels_face {r : V} (p : Path A r r) : (polygon (length p)).map (labels p) ≤ A := by
  rintro s ⟨t,ht,rfl⟩
  obtain ⟨i,hi⟩ := ht.2
  apply (A.isRelLowerSet_faces (labels_next_face p i)).2
  · simpa only [Finset.image_insert,Finset.image_singleton] using Finset.image_subset_image hi
  · exact Finset.image_nonempty.mpr ht.1



variable {K : Type*} [Field K]
def descendValue (tau : Transport (K := K) A) (f : ℕ → V) : ℕ → Kˣ
  | 0 => 1
  | k+1 => tau.unit (f (k+1)) (f k) * descendValue tau f k

theorem descendValue_shift (tau : Transport (K := K) A) (f : ℕ → V) (k : ℕ) :
    descendValue tau f (k+1) = descendValue tau (fun j => f (j+1)) k * tau.unit (f 1) (f 0) := by
  induction k with
  | zero => simp [descendValue]
  | succ k ih =>
    change tau.unit (f (k+1+1)) (f (k+1)) * descendValue tau f (k+1) =
      (tau.unit (f (k+1+1)) (f (k+1)) * descendValue tau (fun j => f (j+1)) k) * tau.unit (f 1) (f 0)
    rw [ih,mul_assoc]

theorem descendValue_node (tau : Transport (K := K) A) {u v : V} (p : Path A u v) :
    descendValue tau (node p) (length p) = (value tau p)⁻¹ := by
  induction p with
  | refl => simp [length,descendValue,value]
  | @cons u v w h p ih =>
    rw [length,descendValue_shift]
    have hs : (fun j => node (.cons h p) (j+1)) = node p := by funext j; rfl
    rw [hs,ih]
    simp only [node,node_zero,value,unit_reverse tau u v h,mul_inv_rev]

theorem descendValue_labels (tau : Transport (K := K) A) {r : V} (p : Path A r r) :
    descendValue tau (label p) (length p+2) = (value tau p)⁻¹ := by
  have hs : (fun j => label p (j+1+1)) = node p := by
    funext j
    simpa only [Nat.add_assoc,show 1+1=2 from rfl] using label_shift p j
  rw [show length p+2=(length p+1)+1 by omega,descendValue_shift,descendValue_shift,hs,descendValue_node]
  simp [label,node_zero,diagonal_unit tau r (startActive p)]

theorem down_target_value (tau : Transport (K := K) A) {r : V} (p : Path A r r)
    (k : ℕ) (hk : k < length p+3) :
    value (pullback tau (labels p) (labels_face p)) (down (length p) k hk) = descendValue tau (label p) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (pullback tau (labels p) (labels_face p)).unit ⟨k+1,hk⟩ (⟨k,by omega⟩ : Index (length p)) *
      value (pullback tau (labels p) (labels_face p)) (down (length p) k (by omega)) =
        tau.unit (label p (k+1)) (label p k) * descendValue tau (label p) k
    rw [ih]
    rfl

theorem mapped_loop_value (tau : Transport (K := K) A) {r : V} (p : Path A r r) :
    value tau (mapPath (labels p) (labels_face p) (loop (length p))) = (value tau p)⁻¹ := by
  rw [value_mapPath]
  change (pullback tau (labels p) (labels_face p)).unit 0 (last (length p)) *
    value (pullback tau (labels p) (labels_face p)) (down (length p) (length p+2) _) = _
  rw [down_target_value,descendValue_labels]
  simp [pullback,labels,last,label_last,label_zero,diagonal_unit tau r (startActive p)]

theorem mapped_loop_detects (tau : Transport (K := K) A) {r : V} (p : Path A r r) :
    value tau (mapPath (labels p) (labels_face p) (loop (length p))) ≠ 1 ↔ value tau p ≠ 1 := by
  rw [mapped_loop_value]
  simp



/-- Reversing the polygon generator matches the target loop's supplied value exactly. -/
theorem mapped_forward_loop_value (tau : Transport (K := K) A) {r : V} (p : Path A r r) :
    value tau (mapPath (labels p) (labels_face p) (reverse (loop (length p)))) = value tau p := by
  rw [value_mapPath,StellarSubdivision.value_reverse]
  have hh := mapped_loop_value tau p
  rw [value_mapPath] at hh
  rw [hh,inv_inv]

end Trace

def forwardLoop (n : ℕ) : Path (polygon n) 0 0 := reverse (loop n)
def forwardGenerator (n : ℕ) : Edge (polygon n) →₀ ℚ :=
  PathChains.chain (PathChains.trivialTransport (polygon n)) (forwardLoop n)

theorem forward_generator_eq (n : ℕ) : forwardGenerator n = -generator n := by
  have hh := StellarSubdivision.chain_reverse (PathChains.trivialTransport (K := ℚ) (polygon n)) (loop n)
  rw [trivial_value,inv_one,Units.val_one,one_smul] at hh
  exact hh

theorem forward_cycle_span (n : ℕ) : CycleSpan (polygon n) (forwardGenerator n) := by
  intro z hz
  obtain ⟨c,b,hb⟩ := generator_cycle_span n z hz
  refine ⟨-c,b,?_⟩
  rw [forward_generator_eq,neg_smul,smul_neg,neg_neg]
  exact hb

/-- The graph, active count, span and mapped value are constructed for every
actual target loop, including the empty path and repeated target vertices. -/
theorem exists_mapped_polygon {K : Type*} [Field K] (A : PreAbstractSimplicialComplex V)
    (tau : Transport (K := K) A) {r : V} (p : Path A r r) :
    ∃ (n : ℕ) (f : Index n → V) (hf : (polygon n).map f ≤ A),
      CycleSpan (polygon n) (forwardGenerator n) ∧
      value tau (mapPath f hf (forwardLoop n)) = value tau p := by
  exact ⟨length p,labels p,labels_face p,forward_cycle_span (length p),mapped_forward_loop_value tau p⟩

/-- Counting only target path steps would omit the three distinct padding positions. -/
theorem omitted_padding_vertices_rejected : Nat.card (Vertex (polygon 0)) ≠ 2 := by
  rw [vertex_count]; decide

/-- The inverse traversal has inverse value; the forward label comparison cannot
be used without reversing the polygon path. -/
theorem wrong_generator_direction_rejected :
    let tau := scaledCycleTransport (Units.mk0 (2 : ℚ) (by norm_num))
    value tau (mapPath (labels cycleLoop) (labels_face cycleLoop) (loop (length cycleLoop))) ≠ value tau cycleLoop := by
  dsimp only
  rw [mapped_loop_value]
  have hh := scaled_cycle_holonomy (Units.mk0 (2 : ℚ) (by norm_num))
  change value (scaledCycleTransport (Units.mk0 (2 : ℚ) (by norm_num))) cycleLoop = _ at hh
  rw [hh]
  intro he
  have hc := congrArg (fun q : ℚˣ => (q : ℚ)) he
  norm_num at hc



/-- The polygon source has a genuine ordinary cycle; it is not yet an exact Moore source. -/
theorem unfilled_polygon_exactness_rejected (n : ℕ) :
    (ordinaryTwo (polygon n)).range ≠ (ordinaryOne (polygon n)).ker := by
  intro hex
  exact zero_generator_span_rejected n ((zero_span_iff_exactness (polygon n)).mpr hex)

/-- A target square witness cannot simply be reused as a source derivation: the
unfilled polygon itself admits no finite square contraction. -/
theorem source_square_moves_rejected (n : ℕ) :
    ¬ Nonempty (Moves (append (forwardLoop n) (forwardLoop n)) (.refl 0 (singleton_face n 0))) := by
  rintro ⟨m⟩
  exact unfilled_polygon_exactness_rejected n
    (exactness_of_square_moves (polygon n) (base n) (forwardLoop n) (forward_cycle_span n) m)

def complex (n : ℕ) : AbstractSimplicialComplex (Index n) where
  toPreAbstractSimplicialComplex := polygon n
  singleton_mem := singleton_face n

theorem dimension_at_most_two (n : ℕ) : SimplicialImages.AtMostTwo (polygon n) :=
  fun s hs => (face_card_le_two n s hs).trans (by omega)

end D2RelationGap.PolygonSource
