import D2RelationGap.PolygonSource

/-!
Actual finite trace comparisons and source refinement adapters.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. A joint exact filled-source/map construction and original
character/geometric adequacy remain open; target moves are not source moves.
-/
noncomputable section
namespace D2RelationGap.SourceRefinement
open OrientedSimplices SimplicialTransport IntegerHeights EdgePaths BasedLoops
open PolygonSource TriangleAttachment
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

def steps {A : PreAbstractSimplicialComplex V} {u v : V} : Path A u v → List V
  | .refl _ _ => []
  | @Path.cons _ _ _ u _ _ _ p => u :: steps p

def vertices {A : PreAbstractSimplicialComplex V} {u v : V} : Path A u v → List V
  | .refl u _ => [u]
  | @Path.cons _ _ _ u _ _ _ p => u :: vertices p

theorem vertices_head {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    (vertices p).head? = some u := by cases p <;> rfl

theorem vertices_nonempty {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    vertices p ≠ [] := by
  intro h
  have hh := vertices_head p
  rw [h] at hh
  cases hh

theorem vertices_eq_steps_end {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    vertices p = steps p ++ [v] := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [vertices,steps,List.cons_append] using congrArg (List.cons _) ih

/-- The complete finite trace determines a path with fixed endpoints; face proofs are propositions. -/
theorem vertices_injective {A : PreAbstractSimplicialComplex V} {u v : V} :
    Function.Injective (vertices (A := A) (u := u) (v := v)) := by
  intro p
  induction p with
  | refl u hu =>
    intro q he
    cases q with
    | refl => rfl
    | cons h q =>
      have hh : vertices q = [] := List.cons.inj he |>.2 |>.symm
      exact (vertices_nonempty q hh).elim
  | @cons u w v h p ih =>
    intro q he
    cases q with
    | refl =>
      have hh : vertices p = [] := List.cons.inj he |>.2
      exact (vertices_nonempty p hh).elim
    | @cons _ t _ hq q =>
      have ht : vertices p = vertices q := List.cons.inj he |>.2
      have hw : w = t := Option.some.inj (by simpa only [vertices_head] using congrArg List.head? ht)
      subst t
      have hp := ih ht
      cases hp
      rfl

theorem vertices_append {A : PreAbstractSimplicialComplex V} {u v w : V}
    (p : Path A u v) (q : Path A v w) : vertices (append p q) = steps p ++ vertices q := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [append,vertices,steps,List.cons_append] using congrArg (List.cons _) (ih q)

theorem vertices_single {A : PreAbstractSimplicialComplex V} {u v : V}
    (h : ({u,v} : Finset V) ∈ A) : vertices (single h) = [u,v] := rfl

theorem vertices_reverse {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    vertices (reverse p) = (vertices p).reverse := by
  induction p with
  | refl => rfl
  | @cons u w v h p ih =>
    rw [reverse,vertices_append,vertices_single]
    change steps (reverse p) ++ ([w] ++ [u]) = (u :: vertices p).reverse
    rw [← List.append_assoc,← vertices_eq_steps_end,ih,List.reverse_cons]

theorem vertices_map {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) :
    vertices (mapPath f hf p) = (vertices p).map f := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,vertices,List.map_cons] using congrArg (List.cons _) ih

/-- A purely finite vertex sequence; used to compare actual path data without endpoint casts. -/
def descendingVertices (f : ℕ → V) : ℕ → List V
  | 0 => [f 0]
  | k+1 => f (k+1) :: descendingVertices f k

omit [LinearOrder V] in
theorem descending_shift (f : ℕ → V) (k : ℕ) :
    descendingVertices f (k+1) = descendingVertices (fun j => f (j+1)) k ++ [f 0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change f (k+1+1) :: descendingVertices f (k+1) =
      (f (k+1+1) :: descendingVertices (fun j => f (j+1)) k) ++ [f 0]
    rw [ih]; rfl

theorem descending_node {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    descendingVertices (node p) (length p) = (vertices p).reverse := by
  induction p with
  | refl => rfl
  | cons h p ih =>
    rw [length,descending_shift]
    have hs : (fun j => node (.cons h p) (j+1)) = node p := by funext j; rfl
    rw [hs,ih]
    simp only [node,vertices,List.reverse_cons]

theorem descending_labels {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    descendingVertices (label p) (length p+2) = (vertices p).reverse ++ [r,r] := by
  have hs : (fun j => label p (j+1+1)) = node p := by
    funext j
    simpa only [Nat.add_assoc,show 1+1=2 from rfl] using label_shift p j
  rw [show length p+2=(length p+1)+1 by omega,descending_shift,descending_shift,hs,descending_node]
  simp only [Nat.zero_add,label_one,label_zero,List.append_assoc,List.cons_append,List.nil_append]

theorem down_mapped_vertices {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r)
    (k : ℕ) (hk : k < length p+3) :
    vertices (mapPath (labels p) (labels_face p) (down (length p) k hk)) = descendingVertices (label p) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change label p (k+1) :: vertices (mapPath (labels p) (labels_face p) (down (length p) k (by omega))) =
      label p (k+1) :: descendingVertices (label p) k
    rw [ih]

theorem mapped_forward_vertices {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    vertices (mapPath (labels p) (labels_face p) (forwardLoop (length p))) = [r,r] ++ vertices p ++ [r] := by
  have hh : vertices (mapPath (labels p) (labels_face p) (loop (length p))) =
      r :: ((vertices p).reverse ++ [r,r]) := by
    change r :: vertices (mapPath (labels p) (labels_face p) (down (length p) (length p+2) _)) = _
    rw [down_mapped_vertices,descending_labels]
  rw [forwardLoop,vertices_map,vertices_reverse,List.map_reverse,← vertices_map (labels p) (labels_face p) (loop (length p)),hh]
  simp only [List.reverse_cons,List.reverse_append,List.reverse_nil,
    List.reverse_reverse,List.nil_append,List.cons_append]

def padded {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) : Path A r r :=
  .cons (v := r) (by simpa using startActive p) (.cons (v := r) (by simpa using startActive p)
    (append p (single (u := r) (v := r) (by simpa using startActive p))))

theorem padded_vertices {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    vertices (padded p) = [r,r] ++ vertices p ++ [r] := by
  rw [padded,vertices,vertices,vertices_append,vertices_single,vertices_eq_steps_end p]
  simp only [List.cons_append,List.nil_append,List.append_assoc]

theorem mapped_forward_eq_padded {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    mapPath (labels p) (labels_face p) (forwardLoop (length p)) = padded p :=
  vertices_injective ((mapped_forward_vertices p).trans (padded_vertices p).symm)

/-- Only two leading and one trailing literal stutter are removed. -/
def remove_padding {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) : Moves (padded p) p := by
  unfold padded
  refine .trans (.stutter (startActive p) _) (.trans (.stutter (startActive p) _) ?_)
  simpa only [single,append_right_refl] using prefixMoves p (Moves.stutter (startActive p) (.refl r (startActive p)))

def mapped_forward_moves {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    Moves (mapPath (labels p) (labels_face p) (forwardLoop (length p))) p := by
  rw [mapped_forward_eq_padded]
  exact remove_padding p

theorem mapped_forward_class {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r) :
    Quotient.mk (pathSetoid A r r) (mapPath (labels p) (labels_face p) (forwardLoop (length p))) =
      Quotient.mk _ p := Quotient.sound ⟨mapped_forward_moves p⟩

/-- The result remains a derivation IN THE TARGET complex, never in the unfilled polygon. -/
def mapped_square_moves {A : PreAbstractSimplicialComplex V} {r : V} (p : Path A r r)
    (m : Moves (append p p) (.refl r (startActive p))) :
    Moves (mapPath (labels p) (labels_face p) (append (forwardLoop (length p)) (forwardLoop (length p))))
      (.refl r (startActive p)) := by
  rw [mapPath_append]
  exact .trans (.suffix _ (mapped_forward_moves p)) (.trans (prefixMoves p (mapped_forward_moves p)) m)



/-- An actual computed prism transfers arbitrary ordinary cycle spans. The
expanded span is proved, not an extra premise in a retraction interface. -/
theorem cycle_span_of_retraction {U : Type*} [LinearOrder U]
    {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (r : V → U) (hr : B.map r ≤ A) (i : U → V) (hi : A.map i ≤ B)
    (hk : B.map (i ∘ r) ≤ B) (hc : SourceExpansion.EdgeContiguous B (i ∘ r))
    (g : Edge A →₀ ℚ) (hspan : CycleSpan A g) : CycleSpan B (SourceExpansion.emap i hi g) := by
  intro z hz
  have hrz : ordinaryOne A (SourceExpansion.emap r hr z) = 0 := by
    have h := LinearMap.congr_fun (SourceExpansion.ordinary_map_one r hr) z
    simpa [hz] using h
  obtain ⟨c,b,hb⟩ := hspan _ hrz
  refine ⟨c,SourceExpansion.tmap i hi b - SourceExpansion.prismOne B (i ∘ r) hc z,?_⟩
  have h2 := LinearMap.congr_fun (SourceExpansion.ordinary_map_two i hi) b
  have hp := LinearMap.congr_fun (SourceExpansion.prism_identity B (i ∘ r) hk hc) z
  have hcomp := LinearMap.congr_fun (SourceExpansion.emap_comp r hr i hi hk) z
  simp only [LinearMap.comp_apply] at h2 hcomp
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.id_apply,hz,map_zero,add_zero] at hp
  rw [← hcomp,hb,map_add,map_smul,← h2] at hp
  rw [map_sub,hp]
  abel

theorem cycle_span_expansion_preserved (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) (g : Edge A →₀ ℚ) (hspan : CycleSpan A g) :
    CycleSpan (SourceExpansion.expansion A u v)
      (SourceExpansion.emap SourceExpansion.old (SourceExpansion.old_face A u v) g) :=
  cycle_span_of_retraction SourceExpansion.retract (SourceExpansion.retract_face A u v huv)
    SourceExpansion.old (SourceExpansion.old_face A u v) (SourceExpansion.expansion_map_retraction A u v huv)
    (SourceExpansion.expansion_contiguous A u v) g hspan

/-- The transferred generator is the chain of the actual retained source loop. -/
theorem cycle_span_expanded_loop (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) {r : V} (p : Path A r r)
    (hspan : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) p)) :
    CycleSpan (SourceExpansion.expansion A u v)
      (PathChains.chain (PathChains.trivialTransport (SourceExpansion.expansion A u v))
        (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) p)) := by
  have h := cycle_span_expansion_preserved A u v huv _ hspan
  have hm := StellarSubdivision.map_path_chain
    (PathChains.trivialTransport (K := ℚ) (SourceExpansion.expansion A u v))
    SourceExpansion.old (SourceExpansion.old_face A u v) p
  change SourceExpansion.emap SourceExpansion.old (SourceExpansion.old_face A u v)
      (PathChains.chain (PathChains.trivialTransport A) p) =
    PathChains.chain (PathChains.trivialTransport (SourceExpansion.expansion A u v))
      (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) p) at hm
  rw [hm] at h
  exact h

/-- The inverse-direction error remains detectable on actual finite move classes. -/
theorem wrong_inverse_moves_rejected :
    ¬ Nonempty (Moves (mapPath (labels cycleLoop) (labels_face cycleLoop) (loop (length cycleLoop))) cycleLoop) := by
  rintro ⟨m⟩
  exact wrong_generator_direction_rejected
    (value_moves (scaledCycleTransport (Units.mk0 (2 : ℚ) (by norm_num))) m)

def trianglePath : Path (⊤ : PreAbstractSimplicialComplex (Fin 3)) 0 0 :=
  .cons (v := 1) (Finset.insert_nonempty _ _) (.cons (v := 2) (Finset.insert_nonempty _ _)
    (.cons (v := 0) (Finset.insert_nonempty _ _) (.refl 0 (Finset.singleton_nonempty _))))

def trianglePath_null : Moves trianglePath (.refl 0 (Finset.singleton_nonempty _)) :=
  .trans (.triangle (u := 0) (v := 1) (w := 2) (Finset.insert_nonempty _ _)
    (.cons (v := 0) (Finset.insert_nonempty _ _) (.refl 0 (Finset.singleton_nonempty _))))
    (.backtrack (u := 0) (v := 2) (Finset.insert_nonempty _ _) (.refl 0 (Finset.singleton_nonempty _)))

def trianglePath_square : Moves (append trianglePath trianglePath) (.refl 0 (Finset.singleton_nonempty _)) :=
  .trans (.suffix trianglePath trianglePath_null) trianglePath_null

/-- A concrete target triangle supplies square moves after projection, while the
actual unfilled polygon still has no source square moves. -/
theorem target_square_adapter_is_not_source_lift :
    Nonempty (Moves (mapPath (labels trianglePath) (labels_face trianglePath)
      (append (forwardLoop (length trianglePath)) (forwardLoop (length trianglePath))))
      (.refl 0 (Finset.singleton_nonempty _))) ∧
    ¬ Nonempty (Moves (append (forwardLoop (length trianglePath)) (forwardLoop (length trianglePath)))
      (.refl 0 (singleton_face (length trianglePath) 0))) :=
  ⟨⟨mapped_square_moves trianglePath trianglePath_square⟩,source_square_moves_rejected (length trianglePath)⟩



/-- Equality of elements in the actual DEFINED target loop group, under its
actual face-map homomorphism; no pi1 or G equivalence is assumed. -/
theorem mapped_forward_loop_group {A : PreAbstractSimplicialComplex V} (r : Vertex A)
    (p : Path A r.val r.val) :
    BasedLoops.map (labels p) (labels_face p) (base (length p))
      (Quotient.mk _ (forwardLoop (length p))) = Quotient.mk _ p :=
  Quotient.sound ⟨mapped_forward_moves p⟩

theorem exists_mapped_polygon_with_moves (A : PreAbstractSimplicialComplex V) {r : V} (p : Path A r r) :
    ∃ (n : ℕ) (f : Index n → V) (hf : (polygon n).map f ≤ A) (hr : f 0 = r),
      CycleSpan (polygon n) (forwardGenerator n) ∧
        Nonempty (Moves (hr ▸ mapPath f hf (forwardLoop n) : Path A r r) p) :=
  ⟨length p,labels p,labels_face p,rfl,forward_cycle_span (length p),⟨mapped_forward_moves p⟩⟩

/-- Equality under one supplied holonomy is insufficient to manufacture finite moves. -/
theorem equal_unit_value_is_not_move_adequacy :
    value cycleTransport (append cycleLoop cycleLoop) =
      value cycleTransport (.refl 0 (cycleBase.property)) ∧
    ¬ Nonempty (Moves (append cycleLoop cycleLoop) (.refl 0 (cycleBase.property))) := by
  constructor
  · rw [value_append,cycleLoop_value]
    simp [value]
  · rintro ⟨m⟩
    let q : ℚˣ := Units.mk0 2 (by norm_num)
    have hv := scaled_cycle_holonomy q
    change value (scaledCycleTransport q) cycleLoop = q at hv
    have hm := value_moves (scaledCycleTransport q) m
    rw [value_append,hv] at hm
    have hc := congrArg (fun t : ℚˣ => (t : ℚ)) hm
    norm_num [q,value] at hc

end D2RelationGap.SourceRefinement
