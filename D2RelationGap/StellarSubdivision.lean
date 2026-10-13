import D2RelationGap.SourceExpansion

/-!
Actual arbitrary-edge stellar subdivision and finite-path/chain comparisons.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Complete refined target maps/geometric adequacy remain open.
-/
noncomputable section
namespace D2RelationGap.StellarSubdivision
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops IntegerHeights
variable {V K : Type*} [LinearOrder V] [Field K]
abbrev Ambient (V : Type*) := Bool ×ₗ V
abbrev old (x : V) : Ambient V := SourceExpansion.old x
abbrev fresh (u : V) : Ambient V := SourceExpansion.fresh u
abbrev collapse (p : Ambient V) : V := SourceExpansion.retract p


omit [LinearOrder V] in
@[simp] theorem collapse_old (x : V) : collapse (old x) = x := rfl
omit [LinearOrder V] in
@[simp] theorem collapse_fresh (u : V) : collapse (fresh u) = u := rfl

omit [LinearOrder V] in
theorem old_injective : Function.Injective (old (V := V)) := by
  intro x y he
  exact congrArg (fun p => (ofLex p).2) he

omit [LinearOrder V] in
theorem fresh_ne_old (u x : V) : fresh u ≠ old x := by
  intro he
  have hb := congrArg (fun p => (ofLex p).1) he
  exact Bool.false_ne_true hb

/-- Old faces containing the chosen edge disappear. New faces are the subfaces
of cones over actual old faces containing the edge, also excluding that old edge. -/
def subdivision (A : PreAbstractSimplicialComplex V) (u v : V) :
    PreAbstractSimplicialComplex (Ambient V) where
  faces := {s | ¬ ({old u,old v} : Finset (Ambient V)) ⊆ s ∧
    (s ∈ A.map old ∨ s.Nonempty ∧ ∃ t ∈ A, ({u,v} : Finset V) ⊆ t ∧
      s ⊆ insert (fresh u) (t.image old))}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rcases hs.2 with hs | hs
      · exact ((A.map old).isRelLowerSet_faces hs).1
      · exact hs.1
    · intro t hts ht
      refine ⟨fun h => hs.1 (h.trans hts), ?_⟩
      rcases hs.2 with hs | ⟨_,q,hq,hpair,hsq⟩
      · exact Or.inl (((A.map old).isRelLowerSet_faces hs).2 hts ht)
      · exact Or.inr ⟨ht,q,hq,hpair,hts.trans hsq⟩

theorem old_pair_subset_image_iff (u v : V) (s : Finset V) :
    ({old u,old v} : Finset (Ambient V)) ⊆ s.image old ↔ ({u,v} : Finset V) ⊆ s := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.mem_image, old_injective.eq_iff]
  simp

theorem old_face (A : PreAbstractSimplicialComplex V) (u v : V) (s : Finset V)
    (hs : s ∈ A) (ha : ¬ ({u,v} : Finset V) ⊆ s) : s.image old ∈ subdivision A u v :=
  ⟨fun h => ha ((old_pair_subset_image_iff u v s).mp h), Or.inl ⟨s,hs,rfl⟩⟩

theorem cone_face (A : PreAbstractSimplicialComplex V) (u v : V) (t : Finset V)
    (ht : t ∈ A) (hp : ({u,v} : Finset V) ⊆ t) (s : Finset (Ambient V))
    (hne : s.Nonempty) (hsub : s ⊆ insert (fresh u) (t.image old))
    (ha : ¬ ({old u,old v} : Finset (Ambient V)) ⊆ s) : s ∈ subdivision A u v :=
  ⟨ha, Or.inr ⟨hne,t,ht,hp,hsub⟩⟩

theorem avoids_singleton (u v x : V) (huv : u ≠ v) :
    ¬ ({u,v} : Finset V) ⊆ {x} := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_singleton]
  rintro ⟨hu,hv⟩
  exact huv (hu.trans hv.symm)

theorem old_vertex (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (x : V) (hx : ({x} : Finset V) ∈ A) : ({old x} : Finset (Ambient V)) ∈ subdivision A u v := by
  simpa using old_face A u v {x} hx (avoids_singleton u v x huv)

theorem avoids_fresh_pair (u v w : V) (huv : u ≠ v) :
    ¬ ({old u,old v} : Finset (Ambient V)) ⊆ {fresh u,old w} := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.mem_insert, Finset.mem_singleton]
  rintro ⟨hu,hv⟩
  have hu' : old u = old w := hu.resolve_left (fresh_ne_old u u).symm
  have hv' : old v = old w := hv.resolve_left (fresh_ne_old u v).symm
  exact huv (old_injective (hu'.trans hv'.symm))

theorem new_edge (A : PreAbstractSimplicialComplex V) (u v w : V) (huv : u ≠ v)
    (h : ({u,v,w} : Finset V) ∈ A) :
    ({fresh u,old w} : Finset (Ambient V)) ∈ subdivision A u v := by
  apply cone_face A u v {u,v,w} h (by simp) _ (by simp) _ (avoids_fresh_pair u v w huv)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp))

theorem new_end_edges (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) :
    ({fresh u,old u} : Finset (Ambient V)) ∈ subdivision A u v ∧
    ({fresh u,old v} : Finset (Ambient V)) ∈ subdivision A u v := by
  constructor
  · exact new_edge A u v u huv (by simpa [Finset.insert_comm, Finset.pair_comm] using h)
  · exact new_edge A u v v huv (by simpa using h)

theorem collapse_face (A : PreAbstractSimplicialComplex V) (u v : V) :
    (subdivision A u v).map collapse ≤ A := by
  rintro s ⟨t,ht,rfl⟩
  rcases ht.2 with ⟨q,hq,rfl⟩ | ⟨hne,q,hq,hpair,hsub⟩
  · simpa [Finset.image_image, Function.comp_def, collapse, old, SourceExpansion.old,
      SourceExpansion.retract] using hq
  · apply (A.isRelLowerSet_faces hq).2
    · intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      have hh := hsub hp
      rcases Finset.mem_insert.mp hh with rfl | hh
      · change u ∈ q
        exact hpair (by simp)
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hh
        exact hy
    · exact hne.image collapse

theorem removed_old_edge (A : PreAbstractSimplicialComplex V) (u v : V) :
    ({old u,old v} : Finset (Ambient V)) ∉ subdivision A u v := fun h => h.1 (Finset.Subset.refl _)

theorem old_inclusion_rejected (A : PreAbstractSimplicialComplex V) (u v : V)
    (h : ({u,v} : Finset V) ∈ A) : ¬ A.map old ≤ subdivision A u v := by
  intro hf
  exact removed_old_edge A u v (by simpa using image_mem old hf _ h)

theorem pair_subset_iff (u v x y : V) (huv : u ≠ v) :
    ({u,v} : Finset V) ⊆ {x,y} ↔ (x=u ∧ y=v) ∨ (x=v ∧ y=u) := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hu,hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (huv rfl)
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
    · exact False.elim (huv rfl)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp

/-- Actual finite replacement paths; the chosen edge is replaced in both directions. -/
def edgePath (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (x y : V) (h : ({x,y} : Finset V) ∈ A) : Path (subdivision A u v) (old x) (old y) := by
  classical
  by_cases hxy : x=u ∧ y=v
  · rcases hxy with ⟨hx,hy⟩
    subst x
    subst y
    obtain ⟨h0,h1⟩ := new_end_edges A u v huv h
    exact Path.cons (by simpa [Finset.pair_comm] using h0) (single h1)
  · by_cases hyx : x=v ∧ y=u
    · rcases hyx with ⟨hx,hy⟩
      subst x
      subst y
      obtain ⟨h0,h1⟩ := new_end_edges A u v huv (by simpa [Finset.pair_comm] using h)
      exact Path.cons (by simpa [Finset.pair_comm] using h1) (single h0)
    · exact single (by simpa using (old_face A u v {x,y} h
        (fun hp => ((pair_subset_iff u v x y huv).mp hp).elim hxy hyx)))

def liftPath (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    {x y : V} : Path A x y → Path (subdivision A u v) (old x) (old y)
  | .refl x hx => .refl (old x) (old_vertex A u v huv x hx)
  | @Path.cons _ _ _ x z _ h p => append (edgePath A u v huv x z h) (liftPath A u v huv p)

def transport (A : PreAbstractSimplicialComplex V) (u v : V) (tau : Transport (K := K) A) :
    Transport (K := K) (subdivision A u v) := pullback tau collapse (collapse_face A u v)

theorem edgePath_value (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (x y : V) (h : ({x,y} : Finset V) ∈ A) :
    value (transport A u v tau) (edgePath A u v huv x y h) = tau.unit x y := by
  classical
  unfold edgePath
  split_ifs with hxy hyx
  · rcases hxy with ⟨hx,hy⟩
    subst x
    subst y
    have hu := diagonal_unit tau u (vertex_mem_of_face A _ h u (by simp))
    simp [transport, pullback, value, single, collapse, old, fresh,
      SourceExpansion.old, SourceExpansion.fresh, SourceExpansion.retract, hu]
  · rcases hyx with ⟨hx,hy⟩
    subst x
    subst y
    have hu := diagonal_unit tau u (vertex_mem_of_face A _ h u (by simp))
    simp [transport, pullback, value, single, collapse, old, fresh,
      SourceExpansion.old, SourceExpansion.fresh, SourceExpansion.retract, hu]
  · simp [transport, pullback, value, single, collapse, old, SourceExpansion.old,
      SourceExpansion.retract]

theorem liftPath_value (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) {x y : V} (p : Path A x y) :
    value (transport A u v tau) (liftPath A u v huv p) = value tau p := by
  induction p with
  | refl => rfl
  | cons h p ih => rw [liftPath, value_append, edgePath_value, ih, value]



theorem liftPath_append (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    {x y z : V} (p : Path A x y) (q : Path A y z) :
    liftPath A u v huv (append p q) = append (liftPath A u v huv p) (liftPath A u v huv q) := by
  induction p with
  | refl => rfl
  | cons h p ih => simp only [append,liftPath,ih,append_assoc]

/-- Collapse of a replacement path differs by stutters, with an actual finite witness. -/
def collapse_edgePath_moves (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (x y : V) (h : ({x,y} : Finset V) ∈ A) :
    Moves (mapPath collapse (collapse_face A u v) (edgePath A u v huv x y h)) (single h) := by
  classical
  unfold edgePath
  split_ifs with hxy hyx
  · rcases hxy with ⟨hx,hy⟩
    subst x
    subst y
    change Moves (Path.cons (by simpa using vertex_mem_of_face A _ h u (by simp)) (single h)) (single h)
    exact Moves.stutter (vertex_mem_of_face A _ h u (by simp)) (single h)
  · rcases hyx with ⟨hx,hy⟩
    subst x
    subst y
    change Moves (Path.cons h (Path.cons (by simpa using vertex_mem_of_face A _ h u (by simp))
      (Path.refl u (vertex_mem_of_face A _ h u (by simp))))) (single h)
    exact Moves.prepend h (Moves.stutter (vertex_mem_of_face A _ h u (by simp))
      (Path.refl u (vertex_mem_of_face A _ h u (by simp))))
  · exact Moves.refl _

def collapse_liftPath_moves (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    {x y : V} (p : Path A x y) :
    Moves (mapPath collapse (collapse_face A u v) (liftPath A u v huv p)) p := by
  induction p with
  | refl => exact Moves.refl _
  | cons h p ih =>
    rw [liftPath,mapPath_append]
    exact Moves.trans (Moves.suffix _ (collapse_edgePath_moves A u v huv _ _ h))
      (Moves.prepend h ih)

theorem collapse_liftPath_class (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    {x y : V} (p : Path A x y) :
    mapClass collapse (collapse_face A u v) (Quotient.mk _ (liftPath A u v huv p)) = Quotient.mk _ p :=
  Quotient.sound ⟨collapse_liftPath_moves A u v huv p⟩

theorem collapse_boundary_two (A : PreAbstractSimplicialComplex V) (u v : V)
    (tau : Transport (K := K) A) :
    (boundaryTwo A (coeff tau)).comp (triangleMap tau collapse (collapse_face A u v)) =
      (edgeMap tau collapse (collapse_face A u v)).comp
        (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))) :=
  map_boundary_two tau collapse (collapse_face A u v)

section ChainNaturality
variable {U : Type*} [LinearOrder U]

/-- The actual unit-correct oriented edge map, including reversed/collapsed images. -/
theorem map_oriented_edge {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B)
    (x y : U) (h : ({x,y} : Finset U) ∈ A) :
    edgeMap tau f hf (edge (pullback tau f hf) x y h) =
      edge tau (f x) (f y) (by simpa using image_mem f hf _ h) := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs : edge (pullback tau f hf) x y h = Finsupp.single ⟨x,y,hxy,h⟩ 1 := by
      simp [edge,hxy]
    rw [hs]
    simp [edgeMap]
  · simp [edge]
  · have hs : edge (pullback tau f hf) x y h =
        -(coeff tau (f x) (f y) • Finsupp.single ⟨y,x,hyx,by simpa [Finset.pair_comm] using h⟩ 1) := by
      simp [edge,hyx,not_lt_of_gt hyx,coeff,pullback]
    rw [hs,map_neg,map_smul]
    simp only [edgeMap,Finsupp.linearCombination_single,one_smul]
    rw [edge_reverse tau (f y) (f x)]

theorem map_path_chain {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B)
    {x y : U} (p : Path A x y) :
    edgeMap tau f hf (PathChains.chain (pullback tau f hf) p) =
      PathChains.chain tau (mapPath f hf p) := by
  induction p with
  | refl => simp [PathChains.chain,mapPath]
  | cons h p ih =>
    simp only [PathChains.chain,mapPath,map_add,map_smul]
    rw [map_oriented_edge,ih]
    rfl

end ChainNaturality

/-- Only active vertices are included; there is no old face-map assumption. -/
def oldVertex (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (x : Vertex A) : Vertex (subdivision A u v) := ⟨old x.val, old_vertex A u v huv _ x.property⟩


theorem vertex_form (A : PreAbstractSimplicialComplex V) (u v : V)
    (p : Vertex (subdivision A u v)) : p.val = fresh u ∨ ∃ x, old x = p.val := by
  rcases p.property.2 with ⟨t,ht,he⟩ | ⟨_,t,ht,hpair,hsub⟩
  · have hp : p.val ∈ t.image old := by change t.image old = {p.val} at he; rw [he]; simp
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hp
    exact Or.inr ⟨x,hx⟩
  · rcases Finset.mem_insert.mp (hsub (by simp : p.val ∈ ({p.val} : Finset (Ambient V)))) with hp | hp
    · exact Or.inl hp
    · obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hp
      exact Or.inr ⟨x,hx⟩

def vertexEncode (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) : Vertex A ⊕ Unit → Vertex (subdivision A u v)
  | .inl x => oldVertex A u v huv x
  | .inr _ => ⟨fresh u,vertex_mem_of_face _ _ (new_end_edges A u v huv h).1 _ (by simp)⟩

theorem vertexEncode_bijective (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) : Function.Bijective (vertexEncode A u v huv h) := by
  constructor
  · intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact old_injective (congrArg Subtype.val he)
      | inr y => exact False.elim ((fresh_ne_old u x.val).symm (congrArg Subtype.val he))
    | inr x =>
      cases y with
      | inl y => exact False.elim ((fresh_ne_old u y.val) (congrArg Subtype.val he))
      | inr y => rfl
  · rintro ⟨p,hp⟩
    rcases vertex_form A u v ⟨p,hp⟩ with he | ⟨x,he⟩
    · change p = fresh u at he
      subst p
      exact ⟨.inr (),rfl⟩
    · change old x = p at he
      subst p
      exact ⟨.inl (mapVertex collapse (collapse_face A u v) ⟨old x,hp⟩),rfl⟩

theorem vertices_finite (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) [Finite (Vertex A)] : Finite (Vertex (subdivision A u v)) :=
  Finite.of_surjective _ (vertexEncode_bijective A u v huv h).2

theorem vertex_count (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) [Finite (Vertex A)] :
    Nat.card (Vertex (subdivision A u v)) = Nat.card (Vertex A) + 1 := by
  have he := Nat.card_congr (Equiv.ofBijective _ (vertexEncode_bijective A u v huv h))
  simpa using he.symm

theorem cone_card_le (u : V) (t : Finset V) (s : Finset (Ambient V))
    (w : V) (hw : w ∈ t) (hsub : s ⊆ insert (fresh u) (t.image old)) (hsw : old w ∉ s) :
    s.card ≤ t.card := by
  have hnew : fresh u ∉ t.image old := by
    rintro hm
    obtain ⟨x,_,he⟩ := Finset.mem_image.mp hm
    exact fresh_ne_old u x he.symm
  have hmem : old w ∈ insert (fresh u) (t.image old) :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hw)
  have he := Finset.card_erase_add_one hmem
  rw [Finset.card_insert_of_notMem hnew, Finset.card_image_of_injective _ old_injective] at he
  have hs : s ⊆ (insert (fresh u) (t.image old)).erase (old w) := by
    intro p hp
    exact Finset.mem_erase.mpr ⟨fun he => hsw (he ▸ hp), hsub hp⟩
  have hh := Finset.card_le_card hs
  omega

theorem dimension_at_most_two (A : PreAbstractSimplicialComplex V) (u v : V)
    (hA : SimplicialImages.AtMostTwo A) : SimplicialImages.AtMostTwo (subdivision A u v) := by
  intro s hs
  rcases hs.2 with ⟨t,ht,rfl⟩ | ⟨_,t,ht,hpair,hsub⟩
  · exact Finset.card_image_le.trans (hA t ht)
  · by_cases hu : old u ∈ s
    · have hv : old v ∉ s := by
        intro hv
        exact hs.1 (by simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,hu,hv])
      exact (cone_card_le u t s v (hpair (by simp)) hsub hv).trans (hA t ht)
    · exact (cone_card_le u t s u (hpair (by simp)) hsub hu).trans (hA t ht)

/-- Actual root paths on the subdivided source, including the fresh vertex. -/
def rootPaths (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (p : Vertex (subdivision A u v)) : Path (subdivision A u v) (old r.val) p.val :=
  append (liftPath A u v huv (paths (mapVertex collapse (collapse_face A u v) p)))
    (single (by
      rcases vertex_form A u v p with hp | ⟨x,hx⟩
      · change ({old (collapse p.val),p.val} : Finset (Ambient V)) ∈ subdivision A u v
        rw [hp]
        simpa [Finset.pair_comm,collapse,fresh,SourceExpansion.fresh,SourceExpansion.retract]
          using (new_end_edges A u v huv h).1
      · change ({old (collapse p.val),p.val} : Finset (Ambient V)) ∈ subdivision A u v
        rw [← hx]
        simpa [collapse,old,SourceExpansion.old,SourceExpansion.retract] using old_vertex A u v huv x (by
          have ht := image_mem collapse (collapse_face A u v) {p.val} p.property
          simpa [← hx,collapse,old,SourceExpansion.old,SourceExpansion.retract] using ht)))

def vertexLift (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v) :
    (Vertex A →₀ K) →ₗ[K] Vertex (subdivision A u v) →₀ K :=
  Finsupp.lmapDomain K K (oldVertex A u v huv)

/-- The weighted degree-one section is made from actual replacement path chains. -/
def edgeLift (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) : (Edge A →₀ K) →ₗ[K] Edge (subdivision A u v) →₀ K :=
  Finsupp.linearCombination K fun e =>
    PathChains.chain (transport A u v tau) (edgePath A u v huv e.src e.dst e.face)

theorem edgeLift_boundary (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) :
    (boundaryOne (subdivision A u v) (coeff (transport A u v tau))).comp (edgeLift A u v huv tau) =
      (vertexLift (K := K) A u v huv).comp (boundaryOne A (coeff tau)) := by
  apply Finsupp.lhom_ext
  intro e c
  simp only [LinearMap.comp_apply,edgeLift,Finsupp.linearCombination_single,map_smul,
    PathChains.chain_boundary,edgePath_value]
  simp [vertexLift,Finsupp.lmapDomain_apply,oldVertex,point,boundaryOne,
    VoltageChains.baseOne,incidence,coeff,smul_sub,Finsupp.mapDomain_sub]

theorem collapse_edgePath_chain (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (x y : V) (h : ({x,y} : Finset V) ∈ A) :
    PathChains.chain tau (mapPath collapse (collapse_face A u v) (edgePath A u v huv x y h)) =
      edge tau x y h := by
  classical
  unfold edgePath
  split_ifs with hxy hyx
  · rcases hxy with ⟨hx,hy⟩
    subst x
    subst y
    have hu := coeff_diagonal tau u (vertex_mem_of_face A _ h u (by simp))
    have hzero : edge tau u u (by simpa using vertex_mem_of_face A _ h u (by simp)) = 0 := by simp [edge]
    simp [mapPath,PathChains.chain,single,collapse,old,fresh,SourceExpansion.old,
      SourceExpansion.fresh,SourceExpansion.retract,hzero,hu]
  · rcases hyx with ⟨hx,hy⟩
    subst x
    subst y
    have hzero : edge tau u u (by simpa using vertex_mem_of_face A _ h u (by simp)) = 0 := by simp [edge]
    simp [mapPath,PathChains.chain,single,collapse,old,fresh,SourceExpansion.old,
      SourceExpansion.fresh,SourceExpansion.retract,hzero]
  · simp [mapPath,PathChains.chain,single,collapse,old,SourceExpansion.old,SourceExpansion.retract]

theorem collapse_edgeLift (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) :
    (edgeMap tau collapse (collapse_face A u v)).comp (edgeLift A u v huv tau) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro e c
  have hn := map_path_chain tau collapse (collapse_face A u v) (edgePath A u v huv e.src e.dst e.face)
  change edgeMap tau collapse (collapse_face A u v)
    (PathChains.chain (transport A u v tau) (edgePath A u v huv e.src e.dst e.face)) = _ at hn
  rw [collapse_edgePath_chain] at hn
  simp only [LinearMap.comp_apply,edgeLift,Finsupp.linearCombination_single,map_smul,hn,LinearMap.id_apply]
  simp [edge,e.ordered]

theorem edgeLift_injective (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) : Function.Injective (edgeLift A u v huv tau) := by
  intro z w he
  have hz := LinearMap.congr_fun (collapse_edgeLift A u v huv tau) z
  have hw := LinearMap.congr_fun (collapse_edgeLift A u v huv tau) w
  exact hz.symm.trans ((congrArg (edgeMap tau collapse (collapse_face A u v)) he).trans hw)


theorem fresh_vertex_requires_edge (A : PreAbstractSimplicialComplex V) (u v : V) :
    ({fresh u} : Finset (Ambient V)) ∈ subdivision A u v → ({u,v} : Finset V) ∈ A := by
  intro h
  rcases h.2 with ⟨t,ht,he⟩ | ⟨_,t,ht,hpair,_⟩
  · have hm : fresh u ∈ t.image old := by change t.image old = {fresh u} at he; rw [he]; simp
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hm
    exact False.elim (fresh_ne_old u x hx.symm)
  · exact (A.isRelLowerSet_faces ht).2 hpair (by simp)

theorem omitted_source_edge_rejected (A : PreAbstractSimplicialComplex V) (u v : V)
    (h : ({u,v} : Finset V) ∉ A) : ({fresh u} : Finset (Ambient V)) ∉ subdivision A u v :=
  fun hp => h (fresh_vertex_requires_edge A u v hp)

theorem collapsed_selected_vertex_rejected (A : PreAbstractSimplicialComplex V) (u : V) :
    ({old u} : Finset (Ambient V)) ∉ subdivision A u u := by
  simpa using removed_old_edge A u u


theorem split_triangle_left (A : PreAbstractSimplicialComplex V) (u v w : V) (huv : u ≠ v)
    (hwv : w ≠ v) (h : ({u,v,w} : Finset V) ∈ A) :
    ({old u,fresh u,old w} : Finset (Ambient V)) ∈ subdivision A u v := by
  apply cone_face A u v {u,v,w} h (by simp) _ (by simp)
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp))
    · simp
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp))
  · intro hp
    have hv := hp (by simp : old v ∈ ({old u,old v} : Finset (Ambient V)))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · exact huv (old_injective hv).symm
    · exact (fresh_ne_old u v).symm hv
    · exact hwv (old_injective hv).symm

theorem split_triangle_right (A : PreAbstractSimplicialComplex V) (u v w : V) (huv : u ≠ v)
    (hwu : w ≠ u) (h : ({u,v,w} : Finset V) ∈ A) :
    ({fresh u,old v,old w} : Finset (Ambient V)) ∈ subdivision A u v := by
  apply cone_face A u v {u,v,w} h (by simp) _ (by simp)
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · simp
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp))
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp))
  · intro hp
    have hu := hp (by simp : old u ∈ ({old u,old v} : Finset (Ambient V)))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with hu | hu | hu
    · exact (fresh_ne_old u u).symm hu
    · exact huv (old_injective hu)
    · exact hwu (old_injective hu).symm

theorem wrong_split_triangle_rejected (A : PreAbstractSimplicialComplex V) (u v : V) :
    ({fresh u,old u,old v} : Finset (Ambient V)) ∉ subdivision A u v := by
  intro h
  exact h.1 (by simp)

theorem six_source_vertex_count :
    Nat.card (Vertex (subdivision SixVertexSource.source (0 : Fin 6) 1)) = 7 := by
  rw [vertex_count _ 0 1 (by decide) (SixVertexSource.pair_face 0 1), SixVertexSource.active_vertex_count]

theorem six_source_dimension : SimplicialImages.AtMostTwo (subdivision SixVertexSource.source (0 : Fin 6) 1) :=
  dimension_at_most_two _ 0 1 SixVertexSource.dimension_at_most_two

theorem six_source_lifted_generator_value :
    value (transport SixVertexSource.source (0 : Fin 6) 1 SixVertexSource.signTransport)
      (liftPath SixVertexSource.source 0 1 (by decide) SixVertexSource.generatorPath) = -1 := by
  rw [liftPath_value]
  exact SixVertexSource.generator_value

theorem omitted_fresh_vertex_count_rejected :
    Nat.card (Vertex (subdivision SixVertexSource.source (0 : Fin 6) 1)) ≠
      Nat.card (Vertex SixVertexSource.source) := by
  rw [six_source_vertex_count, SixVertexSource.active_vertex_count]
  decide


theorem edgePath_forward (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (h : ({u,v} : Finset V) ∈ A) : edgePath A u v huv u v h =
      Path.cons (by simpa [Finset.pair_comm] using (new_end_edges A u v huv h).1)
        (single (new_end_edges A u v huv h).2) := by
  classical
  unfold edgePath
  rw [dite_eq_left ⟨rfl,rfl⟩]

theorem edgePath_unchosen (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (x y : V) (h : ({x,y} : Finset V) ∈ A) (ha : ¬ ({u,v} : Finset V) ⊆ {x,y}) :
    edgePath A u v huv x y h = single (by simpa using old_face A u v {x,y} h ha) := by
  classical
  unfold edgePath
  split_ifs with hxy hyx
  · rcases hxy with ⟨hx,hy⟩
    subst x
    subst y
    exact False.elim (ha (Finset.Subset.refl _))
  · rcases hyx with ⟨hx,hy⟩
    subst x
    subst y
    exact False.elim (ha (by simp [Finset.pair_comm]))
  · rfl

theorem sorted_pair_subset (u v x y : V) (huv : u < v) (hxy : x < y)
    (hp : ({u,v} : Finset V) ⊆ {x,y}) : u=x ∧ v=y := by
  rcases (pair_subset_iff u v x y (ne_of_lt huv)).mp hp with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ⟨hx.symm,hy.symm⟩
  · subst x
    subst y
    exact False.elim (lt_asymm huv hxy)

theorem triangle_pair_cases (u v x y z : V) (huv : u ≠ v)
    (hp : ({u,v} : Finset V) ⊆ {x,y,z}) :
    ({u,v} : Finset V) ⊆ {x,y} ∨ ({u,v} : Finset V) ⊆ {x,z} ∨ ({u,v} : Finset V) ⊆ {y,z} := by
  have hu := hp (by simp : u ∈ ({u,v} : Finset V))
  have hv := hp (by simp : v ∈ ({u,v} : Finset V))
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (huv rfl)
  · exact Or.inl (by simp [Finset.pair_comm])
  · exact Or.inr (Or.inl (by simp [Finset.pair_comm]))
  · exact Or.inl (by simp [Finset.pair_comm])
  · exact False.elim (huv rfl)
  · exact Or.inr (Or.inr (by simp [Finset.pair_comm]))
  · exact Or.inr (Or.inl (by simp [Finset.pair_comm]))
  · exact Or.inr (Or.inr (by simp [Finset.pair_comm]))
  · exact False.elim (huv rfl)

/-- Literal one- or two-triangle moves between replacement edge paths. -/
def triangleMoves (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (x y z : V) (hxy : x < y) (hyz : y < z) (ht : ({x,y,z} : Finset V) ∈ A) :
    Moves (append
      (edgePath A u v (ne_of_lt huv) x y (pair_mem_of_face A _ ht _ _ (by simp) (by simp)))
      (edgePath A u v (ne_of_lt huv) y z (pair_mem_of_face A _ ht _ _ (by simp) (by simp))))
      (edgePath A u v (ne_of_lt huv) x z (pair_mem_of_face A _ ht _ _ (by simp) (by simp))) := by
  classical
  by_cases h01 : ({u,v} : Finset V) ⊆ {x,y}
  · obtain ⟨hx,hy⟩ := sorted_pair_subset u v x y huv hxy h01
    subst x
    subst y
    have hn02 : ¬ ({u,v} : Finset V) ⊆ {u,z} := by
      intro hp
      exact (ne_of_lt hyz) (sorted_pair_subset u v u z huv (lt_trans huv hyz) hp).2
    have hn12 : ¬ ({u,v} : Finset V) ⊆ {v,z} := by
      intro hp
      exact (ne_of_lt huv) (sorted_pair_subset u v v z huv hyz hp).1
    rw [edgePath_forward, edgePath_unchosen _ _ _ _ _ _ _ hn12,
      edgePath_unchosen _ _ _ _ _ _ _ hn02]
    exact Moves.trans (Moves.prepend _ (Moves.triangle
      (split_triangle_right A u v z (ne_of_lt huv) (ne_of_gt (lt_trans huv hyz)) ht)
      (Path.refl (old z) (old_vertex A u v (ne_of_lt huv) z (vertex_mem_of_face A _ ht z (by simp))))))
      (Moves.triangle (split_triangle_left A u v z (ne_of_lt huv) (ne_of_gt hyz) ht)
        (Path.refl (old z) (old_vertex A u v (ne_of_lt huv) z (vertex_mem_of_face A _ ht z (by simp)))))
  · by_cases h02 : ({u,v} : Finset V) ⊆ {x,z}
    · obtain ⟨hx,hz⟩ := sorted_pair_subset u v x z huv (lt_trans hxy hyz) h02
      subst x
      subst z
      have hn12 : ¬ ({u,v} : Finset V) ⊆ {y,v} := by
        intro hp
        exact (ne_of_lt hxy) (sorted_pair_subset u v y v huv hyz hp).1
      have ht' : ({u,v,y} : Finset V) ∈ A := by
        convert ht using 1
        ext p
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
      have hleft := split_triangle_left A u v y (ne_of_lt huv) (ne_of_lt hyz) ht'
      have hright : ({fresh u,old y,old v} : Finset (Ambient V)) ∈ subdivision A u v := by
        convert split_triangle_right A u v y (ne_of_lt huv) (ne_of_gt hxy) ht' using 1
        ext p
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
      rw [edgePath_unchosen _ _ _ _ _ _ _ h01, edgePath_unchosen _ _ _ _ _ _ _ hn12,
        edgePath_forward]
      exact Moves.trans (Moves.symm (Moves.triangle hleft
        (single (by simpa using old_face A u v {y,v} (pair_mem_of_face A _ ht y v (by simp) (by simp)) hn12))))
        (Moves.prepend _ (Moves.triangle hright
          (Path.refl (old v) (old_vertex A u v (ne_of_lt huv) v (vertex_mem_of_face A _ ht v (by simp))))))
    · by_cases h12 : ({u,v} : Finset V) ⊆ {y,z}
      · obtain ⟨hy,hz⟩ := sorted_pair_subset u v y z huv hyz h12
        subst y
        subst z
        have ht' : ({u,v,x} : Finset V) ∈ A := by
          convert ht using 1
          ext p
          simp only [Finset.mem_insert,Finset.mem_singleton]
          tauto
        have hleft : ({old x,old u,fresh u} : Finset (Ambient V)) ∈ subdivision A u v := by
          convert split_triangle_left A u v x (ne_of_lt huv) (ne_of_lt (lt_trans hxy huv)) ht' using 1
          ext p
          simp only [Finset.mem_insert,Finset.mem_singleton]
          tauto
        have hright : ({old x,fresh u,old v} : Finset (Ambient V)) ∈ subdivision A u v := by
          convert split_triangle_right A u v x (ne_of_lt huv) (ne_of_lt hxy) ht' using 1
          ext p
          simp only [Finset.mem_insert,Finset.mem_singleton]
          tauto
        rw [edgePath_unchosen _ _ _ _ _ _ _ h01,edgePath_forward,
          edgePath_unchosen _ _ _ _ _ _ _ h02]
        exact Moves.trans (Moves.triangle hleft (single (new_end_edges A u v (ne_of_lt huv)
            (pair_mem_of_face A _ ht u v (by simp) (by simp))).2))
          (Moves.triangle hright (Path.refl (old v)
            (old_vertex A u v (ne_of_lt huv) v (vertex_mem_of_face A _ ht v (by simp)))))
      · have hn : ¬ ({u,v} : Finset V) ⊆ {x,y,z} := fun hp =>
          (triangle_pair_cases u v x y z (ne_of_lt huv) hp).elim h01 (fun he => he.elim h02 h12)
        rw [edgePath_unchosen _ _ _ _ _ _ _ h01,edgePath_unchosen _ _ _ _ _ _ _ h12,
          edgePath_unchosen _ _ _ _ _ _ _ h02]
        exact Moves.triangle (by simpa using old_face A u v {x,y,z} ht hn)
          (Path.refl (old z) (old_vertex A u v (ne_of_lt huv) z (vertex_mem_of_face A _ ht z (by simp))))

def triangleLift (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (tau : Transport (K := K) A) (t : Triangle A) : Triangle (subdivision A u v) →₀ K :=
  PathChains.filling (transport A u v tau)
    (triangleMoves A u v huv t.v0 t.v1 t.v2 t.ordered01 t.ordered12 t.face)

def twoLift (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (tau : Transport (K := K) A) : (Triangle A →₀ K) →ₗ[K] Triangle (subdivision A u v) →₀ K :=
  Finsupp.linearCombination K (triangleLift A u v huv tau)

theorem twoLift_boundary (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (tau : Transport (K := K) A) :
    (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))).comp (twoLift A u v huv tau) =
      (edgeLift A u v (ne_of_lt huv) tau).comp (boundaryTwo A (coeff tau)) := by
  apply Finsupp.lhom_ext
  intro t c
  simp [twoLift,triangleLift,PathChains.filling_boundary,PathChains.chain_append,edgePath_value,
    boundaryTwo_single,edgeLift,face01,face02,face12,smul_sub,smul_add,smul_smul,coeff]
  abel


theorem value_reverse {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {x y : V} (p : Path A x y) : value tau (reverse p) = (value tau p)⁻¹ := by
  have h := value_moves tau (reverse_right_cancel p)
  rw [value_append] at h
  change value tau p * value tau (reverse p) = 1 at h
  apply mul_left_cancel (a := value tau p)
  rw [h,mul_inv_cancel]

theorem chain_reverse {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    {x y : V} (p : Path A x y) : PathChains.chain tau (reverse p) =
      -((↑((value tau p)⁻¹) : K) • PathChains.chain tau p) := by
  induction p with
  | refl => simp [reverse,PathChains.chain,value]
  | @cons x z y h p ih =>
    simp only [reverse,PathChains.chain_append,value_reverse,single,PathChains.chain,
      smul_zero,add_zero,ih]
    rw [edge_reverse tau z x (by simpa [Finset.pair_comm] using h)]
    simp [value,mul_inv_rev,Units.val_mul,coeff,smul_add,smul_smul]

theorem edgePath_reverse (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (x y : V) (h : ({x,y} : Finset V) ∈ A) : reverse (edgePath A u v huv x y h) =
      edgePath A u v huv y x (by simpa [Finset.pair_comm] using h) := by
  classical
  by_cases hxy : x=u ∧ y=v
  · rcases hxy with ⟨hx,hy⟩
    subst x
    subst y
    simp [edgePath,huv,huv.symm,reverse,append,single]
  · by_cases hyx : x=v ∧ y=u
    · rcases hyx with ⟨hx,hy⟩
      subst x
      subst y
      simp [edgePath,huv,huv.symm,reverse,append,single]
    · simp [edgePath,hxy,hyx,and_comm,reverse,append,single]

theorem edgeLift_oriented (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (x y : V) (h : ({x,y} : Finset V) ∈ A) :
    edgeLift A u v huv tau (edge tau x y h) =
      PathChains.chain (transport A u v tau) (edgePath A u v huv x y h) := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · simp [edgeLift,edge,hxy]
  · have ha : ¬ ({u,v} : Finset V) ⊆ {x,x} := by simpa using avoids_singleton u v x huv
    rw [edgePath_unchosen _ _ _ _ _ _ _ ha]
    simp [edge,PathChains.chain,single]
  · have hs : edge tau x y h = -(coeff tau x y •
        Finsupp.single ⟨y,x,hyx,by simpa [Finset.pair_comm] using h⟩ 1) := by
      simp [edge,hyx,not_lt_of_gt hyx]
    rw [hs,map_neg,map_smul]
    simp only [edgeLift,Finsupp.linearCombination_single,one_smul]
    rw [← edgePath_reverse A u v huv x y h,chain_reverse,edgePath_value]
    simp [coeff,smul_smul]


theorem fresh_lt_old (u x : V) : fresh u < old x := by
  apply Prod.Lex.lt_iff.mpr
  exact Or.inl (by decide : false < true)

theorem new_edge_link (A : PreAbstractSimplicialComplex V) (u v w : V)
    (h : ({fresh u,old w} : Finset (Ambient V)) ∈ subdivision A u v) :
    ({u,v,w} : Finset V) ∈ A := by
  rcases h.2 with ⟨t,ht,he⟩ | ⟨_,t,ht,hpair,hsub⟩
  · have hm : fresh u ∈ t.image old := by change t.image old = {fresh u,old w} at he; rw [he]; simp
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hm
    exact False.elim (fresh_ne_old u x hx.symm)
  · have hm := hsub (by simp : old w ∈ ({fresh u,old w} : Finset (Ambient V)))
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact False.elim ((fresh_ne_old u w).symm hm)
    · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
      have he' := old_injective he
      subst x
      apply (A.isRelLowerSet_faces ht).2
      · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
        exact ⟨hpair (by simp),hpair (by simp),hx⟩
      · simp

theorem edge_dst_old (A : PreAbstractSimplicialComplex V) (u v : V)
    (e : Edge (subdivision A u v)) (he : e.src = fresh u) : ∃ w, old w = e.dst := by
  rcases vertex_form A u v ⟨e.dst,vertex_mem_of_face _ _ e.face _ (by simp)⟩ with hd | hd
  · exact False.elim ((ne_of_lt e.ordered) (he.trans hd.symm))
  · exact hd

theorem anchor_face (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (p : Vertex (subdivision A u v)) :
    ({p.val,old (collapse p.val)} : Finset (Ambient V)) ∈ subdivision A u v := by
  rcases vertex_form A u v p with hp | ⟨x,hx⟩
  · have ha : ({u,v} : Finset V) ∈ A := fresh_vertex_requires_edge A u v (by simpa [hp] using p.property)
    rw [hp]
    simpa [collapse,fresh,SourceExpansion.fresh,SourceExpansion.retract] using (new_end_edges A u v huv ha).1
  · rw [← hx]
    simpa [← hx,collapse,old,SourceExpansion.old,SourceExpansion.retract] using p.property

theorem anchor_coeff (A : PreAbstractSimplicialComplex V) (u v : V)
    (tau : Transport (K := K) A) (p : Vertex (subdivision A u v)) :
    coeff (transport A u v tau) p.val (old (collapse p.val)) = 1 ∧
    coeff (transport A u v tau) (old (collapse p.val)) p.val = 1 := by
  have h := coeff_diagonal tau (collapse p.val) (mapVertex collapse (collapse_face A u v) p).property
  exact ⟨h,h⟩

theorem homotopy_face (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (e : Edge (subdivision A u v)) (hs : e.src = fresh u) (hv : collapse e.dst ≠ v) :
    ({e.src,old u,e.dst} : Finset (Ambient V)) ∈ subdivision A u v := by
  obtain ⟨w,hw⟩ := edge_dst_old A u v e hs
  have he : ({fresh u,old w} : Finset (Ambient V)) ∈ subdivision A u v := by
    simpa [hs,← hw] using e.face
  have hwv : w ≠ v := by simpa [← hw,collapse,old,SourceExpansion.old,SourceExpansion.retract] using hv
  have ht := split_triangle_left A u v w huv hwv (new_edge_link A u v w he)
  rw [hs,← hw]
  convert ht using 1
  ext p
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

def anchor (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (p : Vertex (subdivision A u v)) : Edge (subdivision A u v) →₀ K :=
  edge (transport A u v tau) p.val (old (collapse p.val)) (anchor_face A u v huv p)

def homotopyTriangle (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (e : Edge (subdivision A u v)) : Triangle (subdivision A u v) →₀ K :=
  if hs : e.src = fresh u then
    if hv : collapse e.dst = v then 0
    else triangle (transport A u v tau) e.src (old u) e.dst (homotopy_face A u v huv e hs hv)
  else 0

/-- The contraction identity is checked on actual edge generators. -/
theorem homotopy_generator (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (e : Edge (subdivision A u v)) :
    boundaryTwo (subdivision A u v) (coeff (transport A u v tau)) (homotopyTriangle A u v huv tau e) +
      coeff (transport A u v tau) e.src e.dst •
        anchor A u v huv tau ⟨e.dst,vertex_mem_of_face _ _ e.face _ (by simp)⟩ -
      anchor A u v huv tau ⟨e.src,vertex_mem_of_face _ _ e.face _ (by simp)⟩ =
      edgeLift A u v huv tau (edge tau (collapse e.src) (collapse e.dst)
        (by simpa using image_mem collapse (collapse_face A u v) _ e.face)) - Finsupp.single e 1 := by
  rw [edgeLift_oriented]
  rcases e with ⟨p,q,hord,hface⟩
  have hp := vertex_form A u v ⟨p,vertex_mem_of_face _ _ hface _ (by simp)⟩
  have hq := vertex_form A u v ⟨q,vertex_mem_of_face _ _ hface _ (by simp)⟩
  have hcanon : edge (transport A u v tau) p q hface = Finsupp.single ⟨p,q,hord,hface⟩ 1 := by
    simp [edge,hord]
  rcases hp with hp | ⟨x,hx⟩
  · change p = fresh u at hp
    subst p
    rcases hq with hq | ⟨w,hw⟩
    · change q = fresh u at hq
      subst q
      exact False.elim ((lt_irrefl _) hord)
    · change old w = q at hw
      subst q
      have hc := anchor_coeff A u v tau ⟨fresh u,vertex_mem_of_face _ _ hface _ (by simp)⟩
      have hc0 : coeff (transport A u v tau) (fresh u) (old u) = 1 := hc.1
      have hc1 : coeff (transport A u v tau) (old u) (fresh u) = 1 := hc.2
      have hz : edge (transport A u v tau) (old w) (old w)
          (by simpa using vertex_mem_of_face _ _ hface (old w) (by simp)) = 0 := by simp [edge]
      by_cases hwv : w=v
      · subst w
        have he := pair_mem_of_face A _ (new_edge_link A u v v hface) u v (by simp) (by simp)
        change _ = PathChains.chain (transport A u v tau) (edgePath A u v huv u v he) - _
        have hHT : homotopyTriangle A u v huv tau ⟨fresh u,old v,hord,hface⟩ = 0 := by
          unfold homotopyTriangle
          rw [dite_eq_left (show (⟨fresh u,old v,hord,hface⟩ : Edge (subdivision A u v)).src = fresh u from rfl),
            dite_eq_left (show collapse (⟨fresh u,old v,hord,hface⟩ : Edge (subdivision A u v)).dst = v from rfl)]
        rw [edgePath_forward,hHT]
        simp only [map_zero,anchor,collapse_old,collapse_fresh,PathChains.chain,single,
          smul_zero,add_zero,hz,hc1,one_smul]
        rw [edge_reverse (transport A u v tau) (fresh u) (old u) (new_end_edges A u v huv he).1]
        simp only [hc1,one_smul,hcanon,add_sub_cancel_right,zero_sub]
      · have ha : ¬ ({u,v} : Finset V) ⊆ {u,w} := by
          rw [pair_subset_iff u v u w huv]
          simp [huv,hwv]
        have hA : ({u,w} : Finset V) ∈ A :=
          pair_mem_of_face A _ (new_edge_link A u v w hface) u w (by simp) (by simp)
        change _ = PathChains.chain (transport A u v tau) (edgePath A u v huv u w hA) - _
        let ed : Edge (subdivision A u v) := ⟨fresh u,old w,hord,hface⟩
        have hs : ed.src = fresh u := rfl
        have hv : collapse ed.dst ≠ v := hwv
        have ht := homotopy_face A u v huv ed hs hv
        have hHT : homotopyTriangle A u v huv tau ed =
            triangle (transport A u v tau) (fresh u) (old u) (old w) ht := by
          unfold homotopyTriangle
          rw [dite_eq_left hs,dite_eq_right hv]
        rw [edgePath_unchosen _ _ _ _ _ _ _ ha,hHT]
        simp only [PathChains.chain,single,smul_zero,add_zero,anchor,collapse_old,collapse_fresh,hz]
        rw [triangle_boundary]
        simp only [hc0,one_smul,hcanon]
        abel
  · change old x = p at hx
    subst p
    rcases hq with hq | ⟨y,hy⟩
    · change q = fresh u at hq
      subst q
      exact False.elim ((not_lt_of_gt (fresh_lt_old u x)) hord)
    · change old y = q at hy
      subst q
      have ha : ¬ ({u,v} : Finset V) ⊆ {x,y} := by
        intro hp
        exact hface.1 (by simpa using (old_pair_subset_image_iff u v {x,y}).mpr hp)
      have hA : ({x,y} : Finset V) ∈ A := by
        simpa using image_mem collapse (collapse_face A u v) {old x,old y} hface
      change _ = PathChains.chain (transport A u v tau) (edgePath A u v huv x y hA) - _
      rw [edgePath_unchosen _ _ _ _ _ _ _ ha]
      have hz0 : edge (transport A u v tau) (old x) (old x)
          (by simpa using vertex_mem_of_face _ _ hface (old x) (by simp)) = 0 := by simp [edge]
      have hz1 : edge (transport A u v tau) (old y) (old y)
          (by simpa using vertex_mem_of_face _ _ hface (old y) (by simp)) = 0 := by simp [edge]
      simp only [homotopyTriangle,dite_eq_right (fresh_ne_old u x).symm,map_zero,anchor,collapse_old,
        PathChains.chain,single,smul_zero,add_zero,hz0,hz1,hcanon,sub_self]


def zeroHomotopy (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) :
    (Vertex (subdivision A u v) →₀ K) →ₗ[K] Edge (subdivision A u v) →₀ K :=
  Finsupp.linearCombination K (anchor A u v huv tau)

def oneHomotopy (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) :
    (Edge (subdivision A u v) →₀ K) →ₗ[K] Triangle (subdivision A u v) →₀ K :=
  Finsupp.linearCombination K (homotopyTriangle A u v huv tau)

theorem homotopy_identity (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) :
    (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))).comp (oneHomotopy A u v huv tau) +
      (zeroHomotopy A u v huv tau).comp (boundaryOne (subdivision A u v) (coeff (transport A u v tau))) =
      (edgeLift A u v huv tau).comp (edgeMap tau collapse (collapse_face A u v)) - LinearMap.id := by
  apply Finsupp.lhom_ext
  intro e c
  have h := congrArg (fun z : Edge (subdivision A u v) →₀ K => c • z) (homotopy_generator A u v huv tau e)
  simpa [zeroHomotopy,oneHomotopy,LinearMap.comp_apply,boundaryOne,VoltageChains.baseOne,
    incidence,edgeMap,smul_add,smul_sub,smul_smul,add_sub_assoc] using h

/-- Exactness on the subdivided complex is derived, not assumed. -/
theorem weighted_exactness_preserved (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (tau : Transport (K := K) A)
    (hex : (boundaryTwo A (coeff tau)).range = (boundaryOne A (coeff tau)).ker) :
    (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))).range =
      (boundaryOne (subdivision A u v) (coeff (transport A u v tau))).ker := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w,rfl⟩ := hz
    exact LinearMap.congr_fun (unit_boundary_chain (transport A u v tau)) w
  · intro z hz
    have hz0 : boundaryOne (subdivision A u v) (coeff (transport A u v tau)) z = 0 := hz
    have hrz : boundaryOne A (coeff tau) (edgeMap tau collapse (collapse_face A u v) z) = 0 := by
      have h := LinearMap.congr_fun (map_boundary_one tau collapse (collapse_face A u v)) z
      change boundaryOne A (coeff tau) (edgeMap tau collapse (collapse_face A u v) z) =
        vertexMap collapse (collapse_face A u v)
          (boundaryOne (subdivision A u v) (coeff (transport A u v tau)) z) at h
      simpa [hz0] using h
    have hm : edgeMap tau collapse (collapse_face A u v) z ∈ (boundaryTwo A (coeff tau)).range := by
      rw [hex]
      exact hrz
    obtain ⟨w,hw⟩ := hm
    refine ⟨twoLift A u v huv tau w - oneHomotopy A u v (ne_of_lt huv) tau z, ?_⟩
    have h2 := LinearMap.congr_fun (twoLift_boundary A u v huv tau) w
    simp only [LinearMap.comp_apply] at h2
    rw [hw] at h2
    have hH := LinearMap.congr_fun (homotopy_identity A u v (ne_of_lt huv) tau) z
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.id_apply,
      hz0,map_zero,add_zero] at hH
    rw [map_sub,h2,hH]
    abel

theorem weighted_exactness_reflected (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A)
    (hex : (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))).range =
      (boundaryOne (subdivision A u v) (coeff (transport A u v tau))).ker) :
    (boundaryTwo A (coeff tau)).range = (boundaryOne A (coeff tau)).ker := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w,rfl⟩ := hz
    exact LinearMap.congr_fun (unit_boundary_chain tau) w
  · intro z hz
    have hz0 : boundaryOne A (coeff tau) z = 0 := hz
    have hm : edgeLift A u v huv tau z ∈
        (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))).range := by
      rw [hex]
      have h := LinearMap.congr_fun (edgeLift_boundary A u v huv tau) z
      simpa [hz0] using h
    obtain ⟨w,hw⟩ := hm
    refine ⟨triangleMap tau collapse (collapse_face A u v) w, ?_⟩
    have h := LinearMap.congr_fun (collapse_boundary_two A u v tau) w
    simp only [LinearMap.comp_apply] at h
    rw [hw] at h
    exact h.trans (LinearMap.congr_fun (collapse_edgeLift A u v huv tau) z)

theorem weighted_exactness_iff (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (tau : Transport (K := K) A) :
    (boundaryTwo (subdivision A u v) (coeff (transport A u v tau))).range =
        (boundaryOne (subdivision A u v) (coeff (transport A u v tau))).ker ↔
      (boundaryTwo A (coeff tau)).range = (boundaryOne A (coeff tau)).ker :=
  ⟨weighted_exactness_reflected A u v (ne_of_lt huv) tau, weighted_exactness_preserved A u v huv tau⟩

theorem transport_trivial (A : PreAbstractSimplicialComplex V) (u v : V) :
    transport A u v (PathChains.trivialTransport (K := K) A) =
      PathChains.trivialTransport (K := K) (subdivision A u v) := rfl

theorem ordinary_exactness_iff (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v) :
    (ordinaryTwo (subdivision A u v)).range = (ordinaryOne (subdivision A u v)).ker ↔
      (ordinaryTwo A).range = (ordinaryOne A).ker := by
  have h := weighted_exactness_iff A u v huv (PathChains.trivialTransport (K := ℚ) A)
  rw [transport_trivial,ordinary_coeff,ordinary_coeff] at h
  exact h

theorem ordinary_exactness_preserved (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u < v)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) :
    (ordinaryTwo (subdivision A u v)).range = (ordinaryOne (subdivision A u v)).ker :=
  (ordinary_exactness_iff A u v huv).mpr hex

theorem six_source_exactness :
    (ordinaryTwo (subdivision SixVertexSource.source (0 : Fin 6) 1)).range =
      (ordinaryOne (subdivision SixVertexSource.source (0 : Fin 6) 1)).ker :=
  ordinary_exactness_preserved _ 0 1 (by decide) SixVertexSource.ordinary_chain_exactness

theorem omitted_original_exactness_rejected :
    (ordinaryTwo (subdivision cycleComplex (0 : Fin 3) 1)).range ≠
      (ordinaryOne (subdivision cycleComplex (0 : Fin 3) 1)).ker := by
  intro hex
  exact IntegerHeights.omitted_chain_exactness_rejected ((ordinary_exactness_iff _ 0 1 (by decide)).mp hex)


/-- Naturality for the actual defined based-loop groups, not for geometric pi1 or G. -/
theorem holonomy_pullback (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (r : Vertex A) :
    holonomy (transport A u v tau) (oldVertex A u v huv r) =
      (holonomy tau r).comp (BasedLoops.map collapse (collapse_face A u v) (oldVertex A u v huv r)) := by
  exact (holonomy_natural tau collapse (collapse_face A u v) (oldVertex A u v huv r)).symm

theorem collapse_loop_surjective (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (r : Vertex A) :
    Function.Surjective (BasedLoops.map collapse (collapse_face A u v) (oldVertex A u v huv r)) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro p
  refine ⟨Quotient.mk _ (liftPath A u v huv p), ?_⟩
  exact collapse_liftPath_class A u v huv p


/-- A lift of a raw loop representative; no map on old quotient classes is assumed. -/
def liftedLoop (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (r : Vertex A) (p : Path A r.val r.val) : Loop (subdivision A u v) (oldVertex A u v huv r) :=
  Quotient.mk _ (liftPath A u v huv p)

theorem liftedLoop_holonomy (A : PreAbstractSimplicialComplex V) (u v : V) (huv : u ≠ v)
    (tau : Transport (K := K) A) (r : Vertex A) (p : Path A r.val r.val) :
    holonomy (transport A u v tau) (oldVertex A u v huv r) (liftedLoop A u v huv r p) = value tau p :=
  liftPath_value A u v huv tau p

/-- The proved source preservation feeds the existing chain-model obstruction.
A map into an original presentation with detection is still an explicit obligation. -/
theorem no_detecting_subdivision_image {W : Type*} [LinearOrder W]
    (A : PreAbstractSimplicialComplex V) [Finite (Vertex A)] (u v : V) (huv : u < v)
    (he : ({u,v} : Finset V) ∈ A) (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker) (p : Path A r.val r.val)
    (f : Ambient V → W) (tau : Transport (K := K) ((subdivision A u v).map f))
    (hdetect : holonomy (pullback tau f (le_refl _)) (oldVertex A u v (ne_of_lt huv) r)
      (liftedLoop A u v (ne_of_lt huv) r p) ≠ 1) :
    ¬ Function.Injective (boundaryTwo ((subdivision A u v).map f) (coeff tau)) := by
  let := vertices_finite A u v (ne_of_lt huv) he
  intro h2
  exact hdetect (VoltageTower.source_holonomy_trivial (subdivision A u v)
    (oldVertex A u v (ne_of_lt huv) r) (rootPaths A u v (ne_of_lt huv) he r paths)
    (ordinary_exactness_preserved A u v huv hex) W f tau h2 (liftedLoop A u v (ne_of_lt huv) r p))

/-- Even flat trivial replacement transport fails to preserve a supplied sign edge. -/
theorem changed_transport_rejected :
    let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
    let tau := gaugeTransport (K := ℚ) A (fun x => if x=0 then 1 else -1)
    value (PathChains.trivialTransport (K := ℚ) (subdivision A 0 1))
      (edgePath A 0 1 (by decide) 0 1 (Finset.insert_nonempty _ _)) ≠ tau.unit 0 1 := by
  dsimp only
  rw [IntegerHeights.trivial_value]
  intro he
  have hh := congrArg (fun q : ℚˣ => (q : ℚ)) he
  norm_num [gaugeTransport] at hh

end D2RelationGap.StellarSubdivision
